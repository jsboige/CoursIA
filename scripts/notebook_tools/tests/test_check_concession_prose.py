"""Tests for check_concession_prose.py — the F1 correction of Epic #21424 T5.

The point of this file is the F1 correction. The organ delivered in #21425
(closed as a duplicate of T1) counted the concession lines present in the
notebook AT HEAD of the commit, mixing inherited stock with added flow. The
clusterManager-Myia review measured it on the founding commit 6eb23754b7:
FIVE concession lines match at head, ALL of them already present at the
parent 6eb23754b7^ -- the diff adds exactly ONE ("Le cote honnete du
verdict...").

So the three controls required by issue #21433 are:

  1. POSITIVE — 6eb23754b7 adds exactly one concession line, and it is the
     one the review named.
  2. NEGATIVE — ordinary prose does not fire.
  3. NEGATIVE — a concession line ALREADY PRESENT at the parent is NOT
     counted: the diff proves nothing about it.

Control 1 is measured on the real commit (git replay, skipped when the
clone does not carry it); controls 2 and 3 are pure-function tests on
synthetic notebooks, so they run everywhere.

The logic under test is mostly the pure ``analyze`` — no kernel, no
network. The git replay of control 1 is the only part that needs a clone.
"""
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from check_concession_prose import (
    CONCESSION_RE,
    SELF_TEST_COMMIT,
    SELF_TEST_NOTEBOOK,
    SELF_TEST_PARENT,
    _added_lines,
    _cell_source,
    _markdown_cells,
    _normalize,
    analyze,
    analyze_commit,
)

REPO_ROOT = Path(__file__).resolve().parents[3]


def _md_cell(cell_id, *lines):
    return {"cell_type": "markdown", "id": cell_id,
            "source": [line + "\n" for line in lines[:-1]] + [lines[-1]]}


def _nb(*cells):
    return {"cells": list(cells)}


# --- the motif -------------------------------------------------------------

def test_concession_re_fires_on_the_admission_shapes():
    positives = [
        "## Note honnete : la cellule 5 a ete executee partiellement",
        "**Mode simulation** -- la branche Anthropic n'est pas testee ici",
        "API non configuree, merci de renseigner OPENAI_API_KEY",
        "cle api absente sur la machine d'execution",
        "execution sautee (le modele n'est pas disponible)",
        "ce carnet a des limites : la jambe QC n'est pas executee",
        "placeholder pour les exemples reels",
    ]
    for line in positives:
        assert CONCESSION_RE.search(_normalize(line)), line


def test_concession_re_is_silent_on_ordinary_prose():
    ordinary = [
        "Cette cellule calcule la moyenne du tableau ci-dessus.",
        "Le tableau suivant resume les mesures par sous-groupe.",
        "On applique ensuite la formule decrite dans la section precedente.",
    ]
    for line in ordinary:
        assert not CONCESSION_RE.search(_normalize(line)), line


def test_concession_re_is_accent_and_case_blind():
    assert CONCESSION_RE.search(_normalize("Le CÔTÉ Honnête du verdict"))
    assert CONCESSION_RE.search(_normalize("Exécution SAutée (API non configurée)"))


# --- the F1 correction, on synthetic notebooks -----------------------------

def test_added_concession_line_is_counted():
    base = _nb(_md_cell("a", "## Introduction"))
    head = _nb(_md_cell("a", "## Introduction",
                        "Le cote honnete du verdict est nuance."))
    row = analyze(base, head)
    assert row["n_concessions"] == 1
    assert "honnete" in row["concessions"][0]["line"].lower()


def test_pre_existing_concession_line_is_not_counted():
    """The heart of the F1 correction: inherited stock proves nothing."""
    head = _nb(_md_cell("a", "## Introduction",
                        "Le cote honnete du verdict est nuance."))
    row = analyze(head, head)
    assert row["n_concessions"] == 0
    assert row["notebook_added_concessions"] == []


def test_ordinary_added_prose_is_not_counted():
    base = _nb(_md_cell("a", "## Introduction"))
    head = _nb(_md_cell("a", "## Introduction",
                        "Le tableau suivant resume les mesures."))
    assert analyze(base, head)["n_concessions"] == 0


def test_a_cell_added_in_an_existing_notebook_is_counted():
    base = _nb(_md_cell("a", "## Introduction"))
    head = _nb(_md_cell("a", "## Introduction"),
               _md_cell("b", "Le cote honnete du verdict est nuance."))
    row = analyze(base, head)
    assert row["n_concessions"] == 1
    assert row["concessions"][0]["cell"] == "b"


def test_a_notebook_added_by_the_commit_has_no_added_finding():
    """No baseline, so no line is proven added: the finding changes kind."""
    head = _nb(_md_cell("a", "Le cote honnete du verdict est nuance."))
    row = analyze(None, head)
    assert row["n_concessions"] == 0
    assert row["n_notebook_added"] == 1


def test_code_cells_are_not_prose():
    base = _nb(_md_cell("a", "## Introduction"))
    head = _nb(_md_cell("a", "## Introduction"),
               {"cell_type": "code", "id": "c",
                "source": ["print('execution sautee')\n"]})
    assert analyze(base, head)["n_concessions"] == 0


def test_added_lines_is_a_line_diff_not_a_whole_cell_rewrite():
    base = "## A\nligne une\nligne deux\n"
    head = "## A\nligne une\nligne honnete ajoutee\nligne deux\n"
    added = _added_lines(base, head)
    assert len(added) == 1
    assert "honnete" in added[0]


def test_cell_source_accepts_both_nbformat_shapes():
    assert _cell_source({"source": ["a\n", "b"]}) == "a\nb"
    assert _cell_source({"source": "a\nb"}) == "a\nb"
    assert _cell_source({}) == ""


def test_markdown_cells_ignores_code_cells():
    nb = _nb(_md_cell("a", "x"), {"cell_type": "code", "id": "c",
                                  "source": ["y = 1\n"]})
    assert set(_markdown_cells(nb)) == {"a"}


# --- the replay of the founding commit -------------------------------------

def _git(*args):
    proc = subprocess.run(["git"] + list(args), cwd=str(REPO_ROOT),
                          capture_output=True, text=True, encoding="utf-8",
                          errors="replace")
    return proc.returncode == 0


def test_founding_commit_adds_exactly_one_concession_line():
    """Control 1 of issue #21433, measured on the real commit.

    The review measured FIVE concession lines at head and ONE added by the
    diff. If this test ever finds more than one, the diff logic drifted.
    """
    if not (_git("cat-file", "-e", SELF_TEST_COMMIT)
            and _git("cat-file", "-e", SELF_TEST_PARENT)):
        print("SKIP: reference commits not in this clone")
        return
    rows = analyze_commit(SELF_TEST_COMMIT, cwd=str(REPO_ROOT))
    target = [r for r in rows if r["notebook"] == SELF_TEST_NOTEBOOK]
    assert target, "the founding commit does not touch the expected notebook"
    total = sum(r["n_concessions"] for r in target)
    assert total == 1, "expected exactly one added concession line, got %d" % total
    line = target[0]["concessions"][0]["line"]
    assert "honn" in line.lower(), line
