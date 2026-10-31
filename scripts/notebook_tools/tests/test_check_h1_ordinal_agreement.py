"""Tests for scripts/notebook_tools/check_h1_ordinal_agreement.py.

Why this test file exists
-------------------------
Issue #22291 had no organ: three sessions hand-fixed 18 disagreing H1s
(#22357 / #22364 / #22365) and the same class reappeared, undetected, in eleven
notebooks of `GameTheory/Dynamics/`. The predicate that was missing is one line
-- compare the ordinal the H1 announces with the ordinal the filename carries --
and everything below pins it, plus the two decisions that keep the report
readable.

Two of those decisions are load-bearing and would each be lost silently by a
"simplification":

  1. **`generic` is not `drift`.** `# Notebook 9: ...` on `Sudoku-09-...` names
     the right ordinal with a word that fits every series in the repository.
     Folding it into `drift` would make `--fail` refuse a tree whose labels are
     merely interchangeable, not lying -- and the fix is a naming-convention
     decision, not a renumbering.
  2. **The H1 is searched in every markdown cell.** The repository convention
     puts the navigation block first, so the title sits below it in cell 0 (and
     in the Dynamics C# notebook, four lines down). A scanner that reads only
     the first cell reports `missing_h1` for a notebook that has a perfectly
     good title -- which is exactly the error this organ was built to stop
     making by hand: the 2026-10-29 sweep on #22291 published "aucun H1" for
     that notebook, and it was wrong.

The repo-level test asserts **invariants, not counts**: the number of drifting
notebooks is meant to fall to zero as the class is repaired, so a test that
pins it would have to be edited by the very PR that proves the organ works.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import check_h1_ordinal_agreement as organ  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parents[3]


def _notebook(*markdown_sources):
    return {
        "cells": [{"cell_type": "markdown", "source": [s]} for s in markdown_sources]
    }


def _write(tmp_path, name, nb):
    p = tmp_path / name
    p.write_text(json.dumps(nb), encoding="utf-8")
    return p


# ---------------------------------------------------------------- predicate


def test_self_test_still_passes():
    """The organ's own controls (13 at time of writing) stay green."""
    assert organ.self_test() == 0


def test_self_test_reports_its_failures(monkeypatch):
    """A self-test that cannot fail is decoration -- prove the control bites."""
    monkeypatch.setattr(organ, "H1_ID_RE", organ.re.compile(r"^$"))
    assert organ.self_test() == 1


def test_ordinal_drift_is_detected(tmp_path):
    p = _write(tmp_path, "GameTheory-03b-Chambres-Murs-Chemins-Lean-Python.ipynb",
               _notebook("# GameTheory 3c : Chambres"))
    found = organ.classify(p, json.loads(p.read_text(encoding="utf-8")))
    assert found["kind"] == "drift"
    assert found["says"] == "gametheory-3c"
    assert found["file_says"] == "gametheory-3b"


def test_series_reclass_is_drift_not_generic(tmp_path):
    """A whole-series move (`Dynamics/` from `GameTheory-06x`) is the defect."""
    p = _write(tmp_path, "Dynamics-06-Preuves-Bornees-Cout-du-Raisonnement-Python.ipynb",
               _notebook("# GameTheory-06j — Preuves bornees"))
    found = organ.classify(p, json.loads(p.read_text(encoding="utf-8")))
    assert found["kind"] == "drift"
    assert found["says"] == "gametheory-6j"


def test_zero_initial_and_separator_are_neutral(tmp_path):
    """`KNOTS-01` / `# KNOTS-01` and `Search-09e` / `# Search 9e` are healthy."""
    for name, h1 in (
        ("KNOTS-01-Conway-Proofs-Lean-Python.ipynb", "# KNOTS-01 — Conway"),
        ("Search-09e-Komlos-Lean.ipynb", "# Search 9e — Discrepance"),
        ("GameTheory-16f-Munkres-Assignment-Python.ipynb", "# GameTheory 16f — Kuhn-Munkres"),
    ):
        p = _write(tmp_path, name, _notebook(h1))
        assert organ.classify(p, json.loads(p.read_text(encoding="utf-8"))) is None, h1


def test_generic_series_word_is_its_own_bucket(tmp_path):
    p = _write(tmp_path, "Sudoku-11-Choco-Python.ipynb",
               _notebook("# Notebook 11: Resolution de Sudoku avec Choco"))
    found = organ.classify(p, json.loads(p.read_text(encoding="utf-8")))
    assert found["kind"] == "generic"
    assert found["says"] == "notebook-11"


def test_generic_word_with_wrong_ordinal_is_drift(tmp_path):
    """The `generic` exemption is about the WORD, never about the ordinal."""
    p = _write(tmp_path, "Sudoku-11-Choco-Python.ipynb",
               _notebook("# Notebook 17: Resolution de Sudoku"))
    found = organ.classify(p, json.loads(p.read_text(encoding="utf-8")))
    assert found["kind"] == "drift"


def test_bare_numeral_after_a_language_word_is_ambiguous(tmp_path):
    """`Lean 4` may be the language version -- a case to decide in writing."""
    p = _write(tmp_path, "Lean-01-Setup-Lean-Python.ipynb",
               _notebook("# Lean 4 - Installation et Configuration"))
    found = organ.classify(p, json.loads(p.read_text(encoding="utf-8")))
    assert found["kind"] == "ambiguous"


def test_prose_title_is_not_a_disagreement(tmp_path):
    """No identifier at all is a title gap, not drift -- and not reported here."""
    p = _write(tmp_path, "Lean-38-Capstone-Geometry-Lean-Python.ipynb",
               _notebook("# Capstone Geometry — l'escalier"))
    assert organ.classify(p, json.loads(p.read_text(encoding="utf-8"))) is None


def test_h1_below_the_navigation_block_is_found(tmp_path):
    """Repository convention: nav first, title underneath, same cell."""
    p = _write(
        tmp_path,
        "Dynamics-01-Jeux-Repetes-Folk-Theorem-CSharp.ipynb",
        _notebook(
            "**Navigation** : [Index](README.md)\n\n# GameTheory-6c (C#) : Jeux Repetes\n",
            "## Objectifs d'apprentissage",
        ),
    )
    found = organ.classify(p, json.loads(p.read_text(encoding="utf-8")))
    assert found is not None and found["kind"] == "drift"
    assert found["h1"] == "# GameTheory-6c (C#) : Jeux Repetes"


def test_no_h1_at_all_is_its_own_bucket(tmp_path):
    p = _write(tmp_path, "ICT-35-HumorCausalProbe-Pilot-Python.ipynb",
               _notebook("> **Statut epistemique** — sans verdict", "## Contexte"))
    found = organ.classify(p, json.loads(p.read_text(encoding="utf-8")))
    assert found["kind"] == "missing_h1"


def test_notebook_without_series_identity_is_out_of_scope(tmp_path):
    p = _write(tmp_path, "Diagnostic-Medical.ipynb", _notebook("# CC1 - IA Exploratoire"))
    assert organ.classify(p, json.loads(p.read_text(encoding="utf-8"))) is None


# ----------------------------------------------------------------- exit code


def test_fail_only_counts_drift(tmp_path, monkeypatch, capsys):
    """`--fail` is the ordinal contract: a generic word alone must not red it."""
    p = _write(tmp_path, "Sudoku-11-Choco-Python.ipynb",
               _notebook("# Notebook 11: Resolution de Sudoku"))
    monkeypatch.setattr(sys, "argv",
                        ["check_h1_ordinal_agreement.py", "--paths", str(p), "--fail"])
    assert organ.main() == 0

    q = _write(tmp_path, "Dynamics-03-Sympathie-vs-Engagement-Python.ipynb",
               _notebook("# GameTheory-06d : Sympathie"))
    monkeypatch.setattr(sys, "argv",
                        ["check_h1_ordinal_agreement.py", "--paths", str(q), "--fail"])
    assert organ.main() == 1


def test_json_shape_is_stable(tmp_path, monkeypatch, capsys):
    p = _write(tmp_path, "Dynamics-03-Sympathie-vs-Engagement-Python.ipynb",
               _notebook("# GameTheory-06d : Sympathie"))
    monkeypatch.setattr(sys, "argv",
                        ["check_h1_ordinal_agreement.py", "--paths", str(p), "--json"])
    assert organ.main() == 0
    payload = json.loads(capsys.readouterr().out)
    assert set(payload["counts"]) == {"drift", "generic", "ambiguous", "missing_h1", "unreadable"}
    assert payload["counts"]["unreadable"] == 0
    assert payload["unreadable"] == []
    assert payload["counts"]["drift"] == 1
    assert payload["drift"][0]["file"].endswith("Dynamics-03-Sympathie-vs-Engagement-Python.ipynb")


def test_unreadable_notebook_is_counted_not_dropped(tmp_path, monkeypatch, capsys):
    """Silence must be measurable: a corrupt notebook leaves the denominator.

    Before this counter, `scan()` did `except Exception: continue` and a
    truncated JSON simply disappeared -- the exact failure the repo-invariant
    test warns about ("an empty result must mean a clean tree, not a bad glob").
    """
    _write(tmp_path, "Dynamics-03-Sympathie-vs-Engagement-Python.ipynb",
           _notebook("# GameTheory-06d : Sympathie"))
    broken = tmp_path / "Dynamics-04-Nav-Python.ipynb"
    broken.write_text('{"cells": [', encoding="utf-8")

    monkeypatch.setattr(sys, "argv",
                        ["check_h1_ordinal_agreement.py", "--paths",
                         str(tmp_path / "Dynamics-03-Sympathie-vs-Engagement-Python.ipynb"),
                         str(broken), "--json"])
    assert organ.main() == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["counts"]["drift"] == 1
    assert payload["counts"]["unreadable"] == 1
    assert payload["unreadable"][0]["file"].endswith("Dynamics-04-Nav-Python.ipynb")
    assert "JSONDecodeError" in payload["unreadable"][0]["error"]


# ----------------------------------------------------------- repo invariants


@pytest.fixture(scope="module")
def repo_findings():
    findings, unreadable = organ.scan()
    assert not unreadable, f"unparsable notebooks on the tree: {unreadable[:5]}"
    return findings


def test_the_organ_scans_the_repository_at_all(repo_findings):
    """Anti-silent-scan: an empty result must mean a clean tree, not a bad glob."""
    notebooks = [p for p in REPO_ROOT.glob(organ.SCAN_GLOB) if not organ.EXCLUDE_PARTS & set(p.parts)]
    assert len(notebooks) > 500
    # A totally silent scan over >500 notebooks would mean the predicate stopped
    # matching (the #22291 class is still open on the tree as of 2026-10-29).
    assert repo_findings, "no finding at all -- the predicate is probably dead"


def test_every_finding_re_derives_from_its_file(repo_findings):
    """No finding may outlive its own evidence."""
    for f in repo_findings:
        p = Path(f["file"])
        nb = json.loads(p.read_text(encoding="utf-8"))
        again = organ.classify(p, nb)
        assert again is not None, f"vanished on re-read: {p}"
        assert again["kind"] == f["kind"]


def test_bucket_coherence(repo_findings):
    """Each bucket's definition holds on the real corpus, not just on fixtures."""
    for f in repo_findings:
        if f["kind"] == "missing_h1":
            assert f["h1"] is None
            continue
        assert f["says"] != f["file_says"], f"flagged a healthy notebook: {f['file']}"
        said_series, _, said_ord = f["says"].partition("-")
        file_series, _, file_ord = f["file_says"].partition("-")
        if f["kind"] == "generic":
            assert said_series in organ.GENERIC_SERIES
            assert said_ord == file_ord, f"generic with a different ordinal: {f['file']}"
        if f["kind"] == "ambiguous":
            assert said_series in organ.VERSIONISH_WORDS
            # `ambiguous` is precisely the bucket where the numeral may NOT be
            # the file's ordinal: `Lean 4` on `Lean-01` is the founding case.
            assert said_ord.isdigit() and int(said_ord) <= organ.VERSION_MAX
            assert not any(c.isalpha() for c in said_ord), f"lettered numeral is not a version: {f['file']}"
        assert said_series or file_series  # never both empty


def test_a_notebook_is_never_reported_twice(repo_findings):
    files = [f["file"] for f in repo_findings]
    assert len(files) == len(set(files))


def test_the_dynamics_csharp_notebook_does_have_an_h1():
    """Regression pin on the measurement error this organ was built to stop.

    The 2026-10-29 hand sweep reported "aucun H1" for this notebook; the title
    is in cell 0, four lines below the navigation block. Whatever the H1 is
    eventually renamed to, it must keep being *found*.
    """
    p = (REPO_ROOT / "MyIA.AI.Notebooks/GameTheory/Dynamics"
         / "Dynamics-01-Jeux-Repetes-Folk-Theorem-CSharp.ipynb")
    assert p.exists(), "the notebook moved -- update this pin"
    nb = json.loads(p.read_text(encoding="utf-8"))
    h1 = organ.h1_of(nb)
    assert h1 is not None and h1.startswith("# ")


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
