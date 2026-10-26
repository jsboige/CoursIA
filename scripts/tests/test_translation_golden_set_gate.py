"""Tests de la garde golden set de traduction (#22009, arbitrage #22216).

La review du 2026-10-26 sur la PR #22216 arbitre la forme de la garde : la
jambe BLOQUANTE ne compare que la STRUCTURE des paires (kind, fr, en) -- une
PR qui edite un fichier apparie sans ajouter ni retirer de paire ne rougit
pas -- et la derive d'empreintes se lit en ADVISORY. Ces tests pin les deux
jambes : semantique du script (`--check-structure` muet sur les empreintes,
rouge sur les paires) et declaration du registre (deux gardes, bloquante sur
`--check-structure`, advisory nommee comme telle pour `pr_gate`).
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


def test_check_structure_est_muet_sur_la_derive_d_empreintes(
        monkeypatch, tmp_path, capsys):
    """Edition d'un fichier apparie = nouvelles empreintes, memes paires.

    La jambe bloquante doit rester verte (c'est le friction que l'arbitrage
    #22216 retire) ; la jambe advisory doit, elle, signaler la derive.
    """
    drifted = _fixture_data()
    drifted["pairs"][0]["sha1_fr"] = "f1-edite"
    drifted["pairs"][2]["sources_sha1_en"] = "se3-edite"

    rc = _run(monkeypatch, tmp_path, drifted, ["--check-structure"])
    assert rc == 0, "une derive d'empreinte ne doit pas rouger la bloquante"
    assert "STRUCTURE OK" in capsys.readouterr().out

    rc = _run(monkeypatch, tmp_path, drifted, ["--check"])
    assert rc == 1, "la jambe advisory doit signaler la derive d'empreinte"


def test_check_structure_rouge_sur_paire_retiree(monkeypatch, tmp_path):
    """Retirer une paire de l'arbre sans regenerer = rouge bloquant."""
    stale = _fixture_data()
    stale["pairs"].pop(1)
    stale["counts"]["readme"] = 0

    rc = _run(monkeypatch, tmp_path, stale, ["--check-structure"])
    assert rc == 1


def test_check_structure_rouge_sur_paire_ajoutee(monkeypatch, tmp_path):
    """Ajouter une paire a l'arbre sans regenerer = rouge bloquant."""
    stale = _fixture_data()
    stale["pairs"] = stale["pairs"][:2]
    stale["counts"]["notebook"] = 0

    rc = _run(monkeypatch, tmp_path, stale, ["--check-structure"])
    assert rc == 1


def test_orphan_ajoute_ne_rougit_pas_la_bloquante(monkeypatch, tmp_path):
    """Un `_en` sans contrepartie FR n'est pas une paire (arbitrage #22216).

    La structure bloquante ne compare que les paires ; l'orphelin vit dans
    la jambe advisory.
    """
    stale = _fixture_data()
    stale["orphans_en"] = []
    rc = _run(monkeypatch, tmp_path, stale, ["--check-structure"])
    assert rc == 0
    rc = _run(monkeypatch, tmp_path, stale, ["--check"])
    assert rc == 1


def test_json_absent_rougit_les_deux_jambes(monkeypatch, tmp_path):
    monkeypatch.setattr(build_golden_set, "OUTPUT",
                        tmp_path / "absent.json")
    monkeypatch.setattr(build_golden_set, "collect", lambda: _fixture_data())
    assert build_golden_set.main(["--check-structure"]) == 1
    assert build_golden_set.main(["--check"]) == 1


def test_registre_deux_jambes_bloquante_sur_structure_advisory_sur_empreintes():
    """La declaration du registre porte l'arbitrage : deux gardes distinctes."""
    sys.path.insert(0, str(CI_DIR))
    from fast_lane_registry import TRANCHE26

    by_name = {g.name: g for g in TRANCHE26}
    assert len(TRANCHE26) == 2, (
        "l'arbitrage #22216 attend DEUX jambes (structure bloquante + "
        "empreintes advisory)")

    drift = by_name["translation-golden-set-drift"]
    assert drift.blocking is True
    assert "--check-structure" in drift.argv

    fingerprints = by_name[
        "translation-golden-set-fingerprints (advisory, non-blocking)"]
    assert fingerprints.blocking is False
    assert fingerprints.argv == [
        "python", "scripts/translation/build_golden_set.py", "--check"]

    # Le caractere advisory doit se lire dans le NOM (pr_gate classe par nom :
    # sans le marqueur, le check resterait requis).
    sys.path.insert(0, str(SCRIPTS_DIR))
    import pr_gate
    advisory_jobs = pr_gate.derive_advisory_jobs()
    assert not pr_gate._is_advisory_name(drift.name, advisory_jobs), (
        "la jambe bloquante ne doit pas etre classee advisory")
    assert pr_gate._is_advisory_name(fingerprints.name, advisory_jobs), (
        "la jambe advisory doit porter le marqueur dans son nom")
