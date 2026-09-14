"""Tests for scripts/notebook_tools/check_link_label_agreement.py -- deck scope.

Why this test file exists
-------------------------
The organ was blind to `slides/` (#15867): its `SCAN_GLOBS` covered notebooks,
series READMEs and `docs/`, so a deck could cite a notebook under a label that
names a *different* notebook and nothing looked. The deck convention makes this
the organ's home ground -- a deck cites `[Basename](../../MyIA.AI.Notebooks/...)`
and a rename that updates the href while leaving the label behind is exactly the
#13645 defect the organ exists for.

Two things are pinned here:

  1. **Coverage** -- decks are scanned, and the label predicate actually fires on
     a deck carrying a lying label.
  2. **The measured non-predicate** -- the existing ID-based comparison needed NO
     loosening for the deck form. It compares a family identifier extracted from
     BOTH sides, so the `.ipynb` extension and the glose outside the brackets
     never enter the comparison. A future "fix" that loosens it to a raw
     `label == basename` equality would break it: measured on `origin/main`
     2026-09-13, that naive form mismatches on 108 of 108 deck links.
  3. **Anti-silent-scan** -- `slides/` present but holding no deck must fail
     loudly rather than report a clean scan from an empty scope.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import check_link_label_agreement as organ  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parents[3]

DECK_GLOB = organ.DECK_GLOB


def test_deck_glob_targets_deck_files_only():
    """Deck-only scope: decks, not the `analysis/` / `.marp.md` working trees."""
    assert DECK_GLOB == "slides/**/slides.md"


def test_decks_reach_the_scan_on_the_repo():
    """Acceptance 1 (#15867): decks are part of the scanned set."""
    decks = sorted(REPO_ROOT.glob(DECK_GLOB))
    assert decks, "no deck matched the deck glob"
    assert all(p.name == "slides.md" for p in decks)
    assert len([p for p in decks if not organ.EXCLUDE_PARTS & set(p.parts)]) >= 17


def test_archived_deck_divergence_is_deliberate():
    """The two organs treat `_archive/` differently, and that is on purpose.

    `check_docs_links.py` validates archived READMEs (incident #9814) and so
    keeps `slides/S4-trading-algorithmique/_archive/slides.md` in scope; this
    organ excludes `_archive` for ALL its scopes, notebooks included, and
    widening that is a separate subject. The archived deck carries no `.ipynb`
    link, so the divergence costs nothing today -- pinned so it cannot start
    costing something silently.
    """
    archived = [
        p for p in REPO_ROOT.glob(DECK_GLOB) if organ.EXCLUDE_PARTS & set(p.parts)
    ]
    assert [p.relative_to(REPO_ROOT).as_posix() for p in archived] == [
        "slides/S4-trading-algorithmique/_archive/slides.md"
    ]
    assert organ.LINK_RE.findall(archived[0].read_text(encoding="utf-8")) == []


def test_repo_deck_links_produce_no_false_positive():
    """Acceptance 3 (#15867): the 108 existing deck links yield 0 findings.

    The deck labels are basenames; the organ must accept the form as-is.
    """
    findings = []
    for deck in sorted(REPO_ROOT.glob(DECK_GLOB)):
        if organ.EXCLUDE_PARTS & set(deck.parts):
            continue
        rel = deck.relative_to(REPO_ROOT).as_posix()
        findings += organ.check_text(deck.read_text(encoding="utf-8"), rel)
    assert findings == [], f"false positives on the existing decks: {findings}"


def test_lying_label_on_a_deck_is_detected():
    """A rename that updates the href and leaves the label behind must fire."""
    src = (
        "*Notebooks : [GameTheory-02-NormalForm]"
        "(../../MyIA.AI.Notebooks/GameTheory/GameTheory-09-BackwardInduction.ipynb).*\n"
    )
    findings = organ.check_text(src, "slides/05-theorie-des-jeux/slides.md")
    assert len(findings) == 1
    assert findings[0]["says"] == "gametheory-2"
    assert findings[0]["points_to"] == "gametheory-9"


def test_deck_basename_form_is_accepted_without_loosening():
    """The deck form passes on the existing predicate, not on a new one.

    Same family, same number, no letter -- and the `.ipynb` extension plus the
    glose outside the brackets are irrelevant to the comparison.
    """
    for src in (
        "*Notebooks : [GameTheory-02-NormalForm]"
        "(../../MyIA.AI.Notebooks/GameTheory/GameTheory-02-NormalForm.ipynb) (matrices).*\n",
        "[Infer-1b-Premiers-Modeles](../../MyIA.AI.Notebooks/Probas/Infer/"
        "Infer-1b-Premiers-Modeles.ipynb)\n",
    ):
        assert organ.check_text(src, "slides/x/slides.md") == []


def test_naive_basename_equality_would_false_positive():
    """Guard the measurement behind the design note above.

    If the predicate were ever rewritten as `label == target basename`, the deck
    corpus would light up: the label omits the extension.
    """
    label, target = "GameTheory-02-NormalForm", "GameTheory-02-NormalForm.ipynb"
    assert label != target  # the naive form would flag this healthy link
    src = f"*Notebooks : [{label}](../../MyIA.AI.Notebooks/GameTheory/{target}).*\n"
    assert organ.check_text(src, "slides/x/slides.md") == []


def test_empty_deck_scope_fails_loudly(tmp_path, monkeypatch, capsys):
    """Anti-silent-scan: no deck found under an existing `slides/` is an error."""
    (tmp_path / "slides" / "01-vide").mkdir(parents=True)
    monkeypatch.setattr(organ, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(sys, "argv", ["check_link_label_agreement.py"])
    assert organ.main() == 2
    assert "portee vide" in capsys.readouterr().err


def test_absent_deck_dir_is_not_an_error(tmp_path, monkeypatch):
    """A tree without `slides/` scans normally -- the guard is not a fixture tax."""
    monkeypatch.setattr(organ, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(sys, "argv", ["check_link_label_agreement.py"])
    assert organ.main() == 0


def test_self_test_still_passes():
    """The organ's own #13645 control is untouched by the scope widening."""
    assert organ.self_test() == 0


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
