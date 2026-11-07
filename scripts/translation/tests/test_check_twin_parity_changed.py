#!/usr/bin/env python3
"""Tests for ``scripts/translation/check_twin_parity_changed.py`` (#19116).

Le garde evalue les paires jumeau FR/<lang> touchees par le diff d'une PR.
Ces tests couvrent la PARTIE PROPRE au garde : derivation des candidats
depuis les chemins modifies, filtre disque, et semantique de sortie de
``main`` (rouge sur paire driftée, vert sur re-rendu T4, vert quand aucune
paire n'est touchee). Les invariants eux-memes sont couverts par
``test_check_translation_parity.py`` (Epic #10038 grain B) et ne sont pas
re-testes ici.

Les temoins fondateurs (#18844 drift CODE_DRIFT d0d7a23d, #19115 re-rendu
T4) sont rejeues sur l'arbre reel en developpement ; ici les memes formes
sont reproduites sur des notebooks minimaux hermetiques.
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
TRANSLATION_DIR = HERE.parent
CI_DIR = HERE.parents[1] / "ci"
sys.path.insert(0, str(TRANSLATION_DIR))
sys.path.insert(0, str(CI_DIR))

import check_twin_parity_changed as t  # noqa: E402
import check_translation_parity as p  # noqa: E402
from fast_lane_registry import TRANCHE17  # noqa: E402


# ---------------------------------------------------------------------------
# Helpers — notebook builders (patron test_check_translation_parity.py)
# ---------------------------------------------------------------------------


def _write_nb(path: Path, cells: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    path.write_text(json.dumps(nb, ensure_ascii=False), encoding="utf-8")


def _md_cell(cid: str, source: str) -> dict:
    return {
        "cell_type": "markdown",
        "id": cid,
        "metadata": {},
        "source": [line + "\n" for line in source.split("\n")],
    }


def _code_cell(cid: str, source: str, outputs: list | None = None,
               execution_count: int | None = 1) -> dict:
    return {
        "cell_type": "code",
        "id": cid,
        "metadata": {},
        "execution_count": execution_count,
        "outputs": outputs if outputs is not None else [],
        "source": [line + "\n" for line in source.split("\n") if line],
    }


def _out(text: str) -> dict:
    return {"output_type": "stream", "name": "stdout", "text": [text]}


# ---------------------------------------------------------------------------
# Derivation des candidats (pure)
# ---------------------------------------------------------------------------


def test_derive_twin_changed_candidates_its_source():
    pairs = t.derive_candidate_pairs(
        ["MyIA.AI.Notebooks/GenAI/CaseStudies/Medical-Chatbot/"
         "medical_chatbot_en.ipynb"])
    assert pairs == {("MyIA.AI.Notebooks/GenAI/CaseStudies/Medical-Chatbot/"
                      "medical_chatbot.ipynb",
                      "MyIA.AI.Notebooks/GenAI/CaseStudies/Medical-Chatbot/"
                      "medical_chatbot_en.ipynb", "en")}


def test_derive_source_changed_candidates_all_langs():
    pairs = t.derive_candidate_pairs(["Notebooks/foo.ipynb"])
    langs = {lang for _, _, lang in pairs}
    assert langs == set(p.TARGET_LANGS)
    assert ("Notebooks/foo.ipynb", "Notebooks/foo_en.ipynb", "en") in pairs


def test_derive_ignores_non_notebooks():
    assert t.derive_candidate_pairs(
        ["scripts/ci/x.py", "README.md", "docs/a.ipynb.bak"]) == set()


def test_derive_output_artifact_is_source_not_twin():
    """``foo_en_output.ipynb`` (artefact papermill tolere) n'est PAS un
    jumeau : son stem finit par ``_output``, le suffixe de langue ne matche
    pas en fin de stem. Il ne candidate que des jumeaux inexistants."""
    pairs = t.derive_candidate_pairs(["Notebooks/foo_en_output.ipynb"])
    assert ("Notebooks/foo_en_output.ipynb", "Notebooks/foo_en_output_en.ipynb",
            "en") in pairs
    assert all(trd != "Notebooks/foo_en_output.ipynb" for _, trd, _ in pairs)


# ---------------------------------------------------------------------------
# Filtre disque
# ---------------------------------------------------------------------------


def test_existing_pairs_keeps_only_complete_pairs(tmp_path):
    (tmp_path / "a.ipynb").write_text("{}", encoding="utf-8")
    (tmp_path / "a_en.ipynb").write_text("{}", encoding="utf-8")
    # b : jumeau absent -> candidate ecartee
    (tmp_path / "b.ipynb").write_text("{}", encoding="utf-8")
    candidates = {("a.ipynb", "a_en.ipynb", "en"),
                  ("b.ipynb", "b_en.ipynb", "en")}
    kept = t.existing_pairs(tmp_path, candidates)
    assert [(src.name, trd.name, lang) for src, trd, _, lang in kept] == \
        [("a.ipynb", "a_en.ipynb", "en")]


# ---------------------------------------------------------------------------
# main() — semantique de sortie (git court-circuite par monkeypatch)
# ---------------------------------------------------------------------------


SRC_CELLS = [_md_cell("c1", "# Titre\n\nParagraphe."),
             _code_cell("c2", "x = 1\nprint(x)")]
TRD_CELLS_OK = [_md_cell("c1", "# Title\n\nParagraph."),
                _code_cell("c2", "x = 1\nprint(x)")]
TRD_CELLS_DRIFTED = [_md_cell("c1", "# Title\n\nParagraph."),
                     # re-execution native : le code a derive d'un byte
                     _code_cell("c2", "x = 2\nprint(x)")]


def _run_main(tmp_path, monkeypatch, changed, trd_cells):
    _write_nb(tmp_path / "demo.ipynb", SRC_CELLS)
    _write_nb(tmp_path / "demo_en.ipynb", trd_cells)
    monkeypatch.setattr(t, "changed_notebooks", lambda rr, d: changed)
    rc = t.main(["--repo-root", str(tmp_path), "--diff", "fake...range"])
    return rc


def test_main_red_on_drifted_twin(tmp_path, monkeypatch, capsys):
    """Forme #18844 : jumeau re-execute nativement (code derive) -> rouge."""
    rc = _run_main(tmp_path, monkeypatch, ["demo_en.ipynb"], TRD_CELLS_DRIFTED)
    assert rc == 1
    out = capsys.readouterr().out
    assert "CODE_DRIFT" in out
    assert "demo (en)" in out


def test_main_green_on_t4_rerender(tmp_path, monkeypatch):
    """Forme #19115 : re-rendu T4 propre -> vert."""
    rc = _run_main(tmp_path, monkeypatch, ["demo_en.ipynb"], TRD_CELLS_OK)
    assert rc == 0


def test_main_green_when_source_only_changes_and_twin_follows(
        tmp_path, monkeypatch):
    """Re-executer le FR sans toucher l'EN doit AUSSI evaluer la paire : si
    le jumeau suit (re-rendu T4), vert ; le chemin source declenche bien la
    paire (affichee dans le compte)."""
    _write_nb(tmp_path / "demo.ipynb", SRC_CELLS)
    _write_nb(tmp_path / "demo_en.ipynb", TRD_CELLS_OK)
    monkeypatch.setattr(t, "changed_notebooks", lambda rr, d: ["demo.ipynb"])
    rc = t.main(["--repo-root", str(tmp_path), "--diff", "fake...range"])
    assert rc == 0


def test_main_green_no_pair_touched(tmp_path, monkeypatch, capsys):
    """Notebook sans jumeau modifie : aucune paire, vert explicite."""
    _write_nb(tmp_path / "solo.ipynb", SRC_CELLS)
    monkeypatch.setattr(t, "changed_notebooks", lambda rr, d: ["solo.ipynb"])
    rc = t.main(["--repo-root", str(tmp_path), "--diff", "fake...range"])
    assert rc == 0
    assert "0 paire" in capsys.readouterr().out


def test_main_red_on_unreadable_twin(tmp_path, monkeypatch):
    """Jumeau illisible -> READ_ERROR bloquant, jamais un faux vert."""
    _write_nb(tmp_path / "demo.ipynb", SRC_CELLS)
    (tmp_path / "demo_en.ipynb").write_text("{pas du json", encoding="utf-8")
    monkeypatch.setattr(t, "changed_notebooks", lambda rr, d: ["demo_en.ipynb"])
    rc = t.main(["--repo-root", str(tmp_path), "--diff", "fake...range"])
    assert rc == 1


# ---------------------------------------------------------------------------
# Cablage de la tranche 17 dans le moteur (#19118)
#
# Un garde enregistre mais jamais somme par le moteur ne tourne jamais : le
# defaut est silencieux par construction, et ``twin-parity-guard`` est
# ``blocking=True`` sur ``**/*.ipynb`` -- son omission future ne se verrait
# nulle part. Ces deux tests ferment ce trou.
# ---------------------------------------------------------------------------


def test_tranche17_enregistree_avec_contrat():
    """Le contrat du garde : blocage, base requise, warn_rc, argv de diff."""
    assert len(TRANCHE17) == 1
    guard = TRANCHE17[0]
    assert guard.name == "twin-parity-guard"
    assert guard.blocking is True
    assert guard.needs_base is True
    assert guard.warn_rc == (2,)
    assert "--diff" in guard.argv and "{base_ref}...HEAD" in guard.argv
    assert "**/*.ipynb" in guard.paths
    assert "scripts/translation/check_twin_parity_changed.py" in guard.paths


def test_tranche17_est_absorbee():
    """`blocking=True` sans `absorbed=True` est une declaration sans effet.

    Le job always-on lance `fast_lane.py --shadow`, et le moteur calcule
    `effective_shadow = args.shadow and not guard.absorbed` : un garde non
    absorbe emet sous `fast-lane (ombre): ` avec une conclusion NEUTRE et
    n'entre pas dans `blocking_failed`. Le garde tournait donc en observation
    permanente alors que son contrat annonce un blocage -- il n'aurait pas
    arrete une PR de la forme #18844.

    Falsifiabilite : retirer `absorbed=True` du registre rougit ce test.
    """
    assert TRANCHE17[0].absorbed is True, (
        "twin-parity-guard declare blocking=True mais sans absorbed=True : "
        "le moteur l'emet en ombre avec une conclusion neutre, il ne bloque rien"
    )


def test_tranche17_cablee_dans_le_moteur():
    # Import + somme : la lecture se fait par TOKEN, jamais par adjacence
    # litterale. La parite d'origine (« TRANCHE17, Guard, ») rougissait des
    # qu'une tranche posterieure s'inserait entre TRANCHE17 et Guard -- or
    # l'objet surveille est l'omission de cablage, pas l'ordre des tranches
    # (meme correctif que TRANCHE16, #19118).
    #
    # Falsifiabilite : retirer `+ TRANCHE17` de la somme rougit ce test.
    src = (CI_DIR / "fast_lane.py").read_text(encoding="utf-8")
    imported = re.search(r"from fast_lane_registry import \((.*?)\)", src, re.S)
    assert imported, "bloc d'import de fast_lane_registry introuvable"
    names = [n.strip() for n in imported.group(1).replace("\n", " ").split(",")]
    assert "TRANCHE17" in names, "TRANCHE17 importee mais absente : cablage rompu"
    summed = re.search(r"\bguards = \[(.*?)\]", src, re.S)
    assert summed, "expression de somme des tranches introuvable"
    assert re.search(r"\+\s*TRANCHE17\b", summed.group(1)), "TRANCHE17 non sommee par le moteur"


# ---------------------------------------------------------------------------
# Volet registre twin_pairs.d (#24911)
#
# La derivation par suffixe est aveugle aux paires C#↔Python declarees (aucun
# suffixe de langue) : un cote modifie ne candidate que des jumeaux _en/_es
# inexistants -> filtre disque -> 0 paire -> faux VERT. Temoin fondateur :
# #24869 (enrichissement C# seul de Z3-04-Strings-Regex, garde SUCCESS, cron
# rouge 24 h plus tard). Ces tests rejouent la forme sur un mini-depot git
# jetable, registre et attestations compris.
# ---------------------------------------------------------------------------

REG_PAIR_NAME = "Twin-01 Pair Fixture"
REG_PY = "NB/Twin-01-Python.ipynb"
REG_CS = "NB/Twin-01-CSharp.ipynb"


def _git_ok(tmp_path, *args):
    r = subprocess.run(["git", *args], cwd=tmp_path,
                       capture_output=True, text=True, encoding="utf-8")
    assert r.returncode == 0, f"git {args} : {r.stderr}"
    return r.stdout.strip()


def _seal(reg_dir, py_sha, cs_sha):
    """Ecrit l'entree de paire avec l'attestation scellee aux SHAs donnes."""
    reg_dir.mkdir(parents=True, exist_ok=True)
    (reg_dir / "twin-01.yaml").write_text(
        f'- name: "{REG_PAIR_NAME}"\n'
        '  family: Test\n'
        f'  python: {REG_PY}\n'
        f'  csharp: {REG_CS}\n'
        '  parity_level: native-both\n'
        '  audits:\n'
        '    - date: "2026-11-06"\n'
        '      by: test\n'
        f'      python_sha: "{py_sha}"\n'
        f'      csharp_sha: "{cs_sha}"\n',
        encoding="utf-8")


def _repo_sealed_pair(tmp_path, py_cells=None, cs_cells=None,
                      stale_py_sha=False):
    """Mini-depot git : paire committee + registre scelle au blob reel.

    ``stale_py_sha=True`` simule une paire DEJA en drift cote python sur le
    base (attestation qui ne correspond plus au blob committe).
    """
    _git_ok(tmp_path, "init", "-q")
    _git_ok(tmp_path, "config", "user.email", "t@example.invalid")
    _git_ok(tmp_path, "config", "user.name", "t")
    _git_ok(tmp_path, "config", "core.autocrlf", "false")
    _write_nb(tmp_path / REG_PY, py_cells if py_cells is not None else SRC_CELLS)
    _write_nb(tmp_path / REG_CS, cs_cells if cs_cells is not None else SRC_CELLS)
    py_sha = _git_ok(tmp_path, "hash-object", "--", REG_PY)
    cs_sha = _git_ok(tmp_path, "hash-object", "--", REG_CS)
    if stale_py_sha:
        # un SHA qui ne correspond a aucun blob committe : lettres en tete
        # pour rester une chaîne YAML (des zéros seuls seraient parsés int).
        py_sha = "deadbeef" + "0" * 32
    reg_dir = tmp_path / "reg"
    _seal(reg_dir, py_sha, cs_sha)
    _git_ok(tmp_path, "add", "-A")
    _git_ok(tmp_path, "commit", "-qm", "base")
    return reg_dir


def test_24911_unit_derive_registry_pairs_match_par_membre(tmp_path):
    reg = tmp_path / "reg"
    reg.mkdir()
    (reg / "p.yaml").write_text(
        '- name: "P1"\n'
        '  family: T\n'
        '  python: NB/A-Python.ipynb\n'
        '  csharp: NB/A-CSharp.ipynb\n'
        '  parity_level: native-both\n',
        encoding="utf-8")
    matches, incident = t.derive_registry_pairs(
        reg, ["NB/A-CSharp.ipynb", "NB/solo.ipynb"])
    assert incident is None
    assert [m["name"] for m in matches] == ["P1"]
    # normalisation des separateurs : un chemin Windows matche aussi
    matches, incident = t.derive_registry_pairs(reg, ["NB\\A-Python.ipynb"])
    assert incident is None and len(matches) == 1


def test_24911_unit_registre_absent_ne_change_rien(tmp_path):
    matches, incident = t.derive_registry_pairs(
        tmp_path / "inexistant", ["NB/A-CSharp.ipynb"])
    assert matches == [] and incident is None


def test_24911_unit_registre_illisible_est_un_incident(tmp_path):
    reg = tmp_path / "reg"
    reg.mkdir()
    (reg / "p.yaml").write_text("pas: [du: yaml", encoding="utf-8")
    matches, incident = t.derive_registry_pairs(reg, ["NB/A-CSharp.ipynb"])
    assert matches == []
    assert incident is not None


def test_24911_edition_unilatérale_de_paire_déclarée_rouge(tmp_path, capsys):
    """Forme #24869 : enrichissement d'UN seul cote, sans rescelle -> rouge."""
    reg_dir = _repo_sealed_pair(tmp_path)
    _write_nb(tmp_path / REG_CS, [_md_cell("c1", "# Titre\n\nLecture ajoutee.")])
    _git_ok(tmp_path, "add", "-A")
    _git_ok(tmp_path, "commit", "-qm", "enrich C# seul")
    rc = t.main(["--repo-root", str(tmp_path), "--registry", str(reg_dir),
                 "--diff", "HEAD~1...HEAD"])
    assert rc == 1
    out = capsys.readouterr().out
    assert REG_PAIR_NAME in out
    assert "DRIFT_INTRODUCED" in out


def test_24911_rescelle_dans_la_meme_pr_reste_vert(tmp_path):
    """Toucher un cote ET resceller l'attestation au nouveau blob -> vert.

    C'est la convention que le garde rend enfin visible au moment de la PR :
    toute PR qui touche un membre d'une paire declaree rescelle
    l'attestation dans la meme PR (cf #24840).
    """
    reg_dir = _repo_sealed_pair(tmp_path)
    new_cs_cells = [_md_cell("c1", "# Titre\n\nEncore une lecture.")]
    _write_nb(tmp_path / REG_CS, new_cs_cells)
    new_cs_sha = _git_ok(tmp_path, "hash-object", "--", REG_CS)
    _seal(reg_dir, _git_ok(tmp_path, "hash-object", "--", REG_PY), new_cs_sha)
    _git_ok(tmp_path, "add", "-A")
    _git_ok(tmp_path, "commit", "-qm", "enrich C# + rescelle")
    rc = t.main(["--repo-root", str(tmp_path), "--registry", str(reg_dir),
                 "--diff", "HEAD~1...HEAD"])
    assert rc == 0


def test_24911_drift_preexistant_hors_diff_non_evalue(tmp_path, capsys):
    """Un notebook hors de toute paire declaree -> 0 paire registre, vert."""
    reg_dir = _repo_sealed_pair(tmp_path)
    _write_nb(tmp_path / "NB/solo.ipynb", SRC_CELLS)
    _git_ok(tmp_path, "add", "-A")
    _git_ok(tmp_path, "commit", "-qm", "solo")
    rc = t.main(["--repo-root", str(tmp_path), "--registry", str(reg_dir),
                 "--diff", "HEAD~1...HEAD"])
    assert rc == 0
    assert "0 paire(s) declaree(s)" in capsys.readouterr().out


def test_24911_drift_preexistant_au_base_reste_advisory(tmp_path, capsys):
    """Drift deja present cote python au base, PR touche CE meme cote sans
    rescelle : le drift du head reste un sous-ensemble de celui du base ->
    DRIFT_PRE_EXISTING, vert -- c'est l'etat que le cron suit sur main, pas
    un drift introduit par la PR."""
    reg_dir = _repo_sealed_pair(tmp_path, stale_py_sha=True)
    _write_nb(tmp_path / REG_PY, [_md_cell("c1", "# Titre\n\nEncore.")])
    _git_ok(tmp_path, "add", "-A")
    _git_ok(tmp_path, "commit", "-qm", "touche python deja driftant")
    rc = t.main(["--repo-root", str(tmp_path), "--registry", str(reg_dir),
                 "--diff", "HEAD~1...HEAD"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "DRIFT_PRE_EXISTING" in out


def test_24911_registre_illisible_sort_en_2(tmp_path):
    """Registre present mais malforme : incident d'entree (rc 2), jamais un
    faux vert -- meme contrat que le diff illisible."""
    reg = tmp_path / "reg"
    reg.mkdir()
    (reg / "p.yaml").write_text("pas: [du: yaml", encoding="utf-8")
    rc = t.main(["--repo-root", str(tmp_path), "--registry", str(reg),
                 "--diff", "HEAD~1...HEAD"])
    assert rc == 2
