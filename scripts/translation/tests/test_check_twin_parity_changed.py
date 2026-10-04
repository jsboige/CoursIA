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
