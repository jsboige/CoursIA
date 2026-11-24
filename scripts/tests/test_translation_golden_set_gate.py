"""Tests de la garde golden set de traduction (#22009, arbitrage #22216).

Arbitrage FINAL de la review myia-ai-01 du 2026-10-26 (demandes 1 + 2) : la
garde `translation-golden-set-drift` est ADVISORY pure -- le `--check`
integral (empreintes, orphelins, structure des paires) SIGNALE la derive sur
la PR sans bloquer -- et la REGENERATION du JSON vit dans le cron du
catalogue (catalog-cron.yml, branche chore/catalog-refresh-pending), meme
modele que COURSE_CATALOG.generated.* (#19901, regle catalog-pr-hygiene) :
une branche de contenu ne regenere pas un fichier genere.

Une forme intermediaire « jambe bloquante sur la structure seule »
(--check-structure + jambe advisory empreintes) a ete implantee sur cette
branche puis retiree : meme limitee aux paires, elle exigeait la
regeneration SUR BRANCHE du fichier genere a chaque paire ajoutee ou
retiree -- exactement le geste que catalog-pr-hygiene interdit pour le
catalogue.

Ces tests pin : la semantique du script (`--check` vert a jour, rouge sur
derive d'empreintes, de structure ou d'orphelins, rouge si le JSON est
absent) et la declaration du registre (UNE seule garde, NON bloquante,
marqueur advisory dans le nom pour pr_gate, argv sur `--check`).
"""

from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parents[1]
CI_DIR = SCRIPTS_DIR / "ci"

_script = importlib.util.spec_from_file_location(
    "build_golden_set", SCRIPTS_DIR / "translation" / "build_golden_set.py")
build_golden_set = importlib.util.module_from_spec(_script)
_script.loader.exec_module(build_golden_set)


def _fixture_data() -> dict:
    return {
        "pairs": [
            {"kind": "lean", "fr": "a/Foo.lean", "en": "a/Foo_en.lean",
             "sha1_fr": "f1", "sha1_en": "e1"},
            {"kind": "readme", "fr": "b/README.md", "en": "b/README.en.md",
             "sha1_fr": "f2", "sha1_en": "e2"},
            {"kind": "notebook", "fr": "c/Nb.ipynb", "en": "c/Nb_en.ipynb",
             "sha1_fr": "f3", "sha1_en": "e3",
             "sources_sha1_fr": "sf3", "sources_sha1_en": "se3"},
        ],
        "counts": {"notebook": 1, "readme": 1, "lean": 1},
        "orphans_en": ["d/Orphan_en.lean"],
    }


def _prepare(tmp_path, data) -> Path:
    out = tmp_path / "translation_golden_set.json"
    out.write_text(json.dumps(data, ensure_ascii=False, indent=1) + "\n",
                   encoding="utf-8")
    return out


def _run(monkeypatch, tmp_path, committed, argv):
    """Pose un JSON commite et un arbre simulé, rend le verdict du mode."""
    monkeypatch.setattr(build_golden_set, "OUTPUT",
                        _prepare(tmp_path, committed))
    monkeypatch.setattr(build_golden_set, "collect", lambda: _fixture_data())
    return build_golden_set.main(argv)


def test_check_vert_quand_le_json_est_a_jour(monkeypatch, tmp_path, capsys):
    """JSON commite == arbre : rc=0."""
    rc = _run(monkeypatch, tmp_path, _fixture_data(), ["--check"])
    assert rc == 0
    assert "GOLDEN-SET OK" in capsys.readouterr().out


def test_check_rouge_sur_derive_d_empreintes(monkeypatch, tmp_path, capsys):
    """Edition d'un fichier apparie = nouvelles empreintes, memes paires.

    La garde advisory doit SIGNALER la derive (rc=1) -- c'est son role :
    rien ne redevient silencieux sous l'arbitrage #22216.
    """
    drifted = _fixture_data()
    drifted["pairs"][0]["sha1_fr"] = "f1-edite"
    drifted["pairs"][2]["sources_sha1_en"] = "se3-edite"

    rc = _run(monkeypatch, tmp_path, drifted, ["--check"])
    assert rc == 1, "la derive d'empreinte doit etre signalee (advisory)"
    assert "GOLDEN-SET DRIFT" in capsys.readouterr().out


def test_check_rouge_sur_paire_retiree(monkeypatch, tmp_path):
    """Retirer une paire de l'arbre sans regenerer : derive signalee."""
    stale = _fixture_data()
    stale["pairs"].pop(1)
    stale["counts"]["readme"] = 0

    rc = _run(monkeypatch, tmp_path, stale, ["--check"])
    assert rc == 1


def test_check_rouge_sur_paire_ajoutee(monkeypatch, tmp_path):
    """Ajouter une paire a l'arbre sans regenerer : derive signalee.

    Sous la forme intermediaire structure-seule, ce cas etait le seul
    bloquant ; en advisory finale il reste SIGNALE (rc=1), la resorption
    appartient au cron du catalogue.
    """
    stale = _fixture_data()
    stale["pairs"] = stale["pairs"][:2]
    stale["counts"]["notebook"] = 0

    rc = _run(monkeypatch, tmp_path, stale, ["--check"])
    assert rc == 1


def test_check_rouge_sur_derive_d_orphelins(monkeypatch, tmp_path):
    """Un `_en` sans contrepartie FR entre ou sort : derive signalee."""
    stale = _fixture_data()
    stale["orphans_en"] = []
    rc = _run(monkeypatch, tmp_path, stale, ["--check"])
    assert rc == 1


def test_json_absent_rouge(monkeypatch, tmp_path):
    monkeypatch.setattr(build_golden_set, "OUTPUT",
                        tmp_path / "absent.json")
    monkeypatch.setattr(build_golden_set, "collect", lambda: _fixture_data())
    assert build_golden_set.main(["--check"]) == 1


def test_registre_une_seule_garde_advisory_non_bloquante():
    """La declaration du registre porte l'arbitrage final : UNE garde,
    NON bloquante, sur le `--check` integral."""
    sys.path.insert(0, str(CI_DIR))
    from fast_lane_registry import TRANCHE26

    assert len(TRANCHE26) == 1, (
        "l'arbitrage final #22216 attend UNE garde advisory (la forme "
        "deux-jambes structure-seule a ete retiree)")
    assert not any(g.blocking for g in TRANCHE26), (
        "aucune jambe du golden set ne doit etre bloquante")

    drift = TRANCHE26[0]
    assert drift.name == "translation-golden-set-drift (advisory, non-blocking)"
    assert drift.argv == [
        "python", "scripts/translation/build_golden_set.py", "--check"]

    # Le caractere advisory doit se lire dans le NOM (pr_gate classe par nom :
    # sans le marqueur, le check resterait requis).
    sys.path.insert(0, str(SCRIPTS_DIR))
    import pr_gate
    advisory_jobs = pr_gate.derive_advisory_jobs()
    assert pr_gate._is_advisory_name(drift.name, advisory_jobs), (
        "la garde doit porter le marqueur advisory dans son nom")
