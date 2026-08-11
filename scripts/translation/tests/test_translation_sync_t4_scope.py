"""Tests for the T4 scope-fix sub-grain of issue #10349.

Issue #10349 split into two grains :
- po-2025 owns guardrail 1 (``--require-translated`` opt-in flag in
  ``render_notebook.py`` to prevent writing a FR-clone) -- PR #10359.
- po-2023 owns scope-fix : T4 must iterate over per-CSV in-scope langs
  (from ``translations/PERIMETER.md``), not ``TARGET_LANGS`` globally.

This test verifies the **decision logic** the workflow uses : for a given
CSV (path) and a perimeter matrix, return the langs T4 should render. The
actual ``for lang in ...`` loop is inline in ``translation-sync.yml`` and
cannot be unit-tested without a workflow-runner; this test pins the
contract so that any refactor of the inline loop stays correct.

Mirrors the ``_resolve_perimeter`` test style in
``test_sync_translation_perimeter.py`` (c.199 PR #10347).

stdlib-only, hermetic via tmp_path. No network.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
TRANSLATION_DIR = HERE.parent
sys.path.insert(0, str(TRANSLATION_DIR))

import check_perimeter as p  # noqa: E402


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _write_perimeter(path: Path, content: str) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")
    return path


def _perimeter_md(rows: list[str]) -> str:
    header = "| CSV | en | es | ar | fa | zh | ru | pt | Source |"
    sep = "|---|---|---|---|---|---|---|---|---|"
    return "\n".join([header, sep] + rows) + "\n"


def _resolve_t4_scope(csv_path: Path, perimeter: dict[str, set[str]]) -> set[str]:
    """Mirror the decision logic in translation-sync.yml T4 step (post-fix).

    Reproduced verbatim from the YAML inline script (issue #10349 scope-fix) :

        rel_csv = csv_path.as_posix()
        in_scope = scope.get(rel_csv)
        if in_scope is None:
            # CSV not declared in PERIMETER.md => closed perimeter, no renders.
            ...continue / skip
        if not in_scope:
            # CSV declared but all langs out-of-scope.
            ...continue / skip
        ...iterate over sorted(in_scope)

    Returns the lang set T4 should iterate over, or empty set if the CSV
    should be skipped entirely. The skip vs empty distinction is observable
    in the workflow logs but not in the rendered artefact count.
    """
    rel_csv = csv_path.as_posix()
    in_scope = perimeter.get(rel_csv)
    if in_scope is None or not in_scope:
        return set()
    return in_scope


# ---------------------------------------------------------------------------
# T4 scope-fix — closed-perimeter semantics
# ---------------------------------------------------------------------------


def test_t4_scope_csv_with_en_only(tmp_path):
    """A CSV declared with **en** only renders ``en`` (not all TARGET_LANGS)."""
    perimeter_path = _write_perimeter(
        tmp_path / "PERIMETER.md",
        _perimeter_md([
            "| `translations/genai/finetuning.csv` | **en** | - | - | - | - | - | - | #10017 |",
        ]),
    )
    perimeter = p.parse_perimeter(perimeter_path)
    csv_path = Path("translations/genai/finetuning.csv")
    assert _resolve_t4_scope(csv_path, perimeter) == {"en"}


def test_t4_scope_csv_with_en_and_ru(tmp_path):
    """A CSV declared with **en** + **ru** renders both."""
    perimeter_path = _write_perimeter(
        tmp_path / "PERIMETER.md",
        _perimeter_md([
            "| `translations/genai/casestudies.csv` | **en** | - | - | - | - | **ru** | - | #10017 |",
        ]),
    )
    perimeter = p.parse_perimeter(perimeter_path)
    csv_path = Path("translations/genai/casestudies.csv")
    assert _resolve_t4_scope(csv_path, perimeter) == {"en", "ru"}


def test_t4_scope_csv_declared_but_all_out_of_scope(tmp_path):
    """A CSV row exists but with all ``-`` => T4 iterates over empty set (skip)."""
    perimeter_path = _write_perimeter(
        tmp_path / "PERIMETER.md",
        _perimeter_md([
            "| `translations/genai/audio.csv` | - | - | - | - | - | - | - | (pre-T3) |",
        ]),
    )
    perimeter = p.parse_perimeter(perimeter_path)
    csv_path = Path("translations/genai/audio.csv")
    # The in_scope set is present (row exists) but empty => skip branch.
    assert perimeter["translations/genai/audio.csv"] == set()
    assert _resolve_t4_scope(csv_path, perimeter) == set()


def test_t4_scope_csv_not_in_perimeter(tmp_path):
    """A CSV on disk but NOT in PERIMETER.md => T4 skips (closed perimeter)."""
    perimeter_path = _write_perimeter(
        tmp_path / "PERIMETER.md",
        _perimeter_md([
            "| `translations/genai/finetuning.csv` | **en** | - | - | - | - | - | - | #10017 |",
        ]),
    )
    perimeter = p.parse_perimeter(perimeter_path)
    csv_path = Path("translations/gametheory/gametheory.csv")
    # The CSV path is not a key in the matrix => .get returns None => skip.
    assert perimeter.get("translations/gametheory/gametheory.csv") is None
    assert _resolve_t4_scope(csv_path, perimeter) == set()


def test_t4_scope_real_repo_inventory():
    """Sanity check : on the real PERIMETER.md, only 4 CSVs have any in-scope
    langs, and the count of (csv, lang) cells is 6 (4 en + 2 ru). Guards
    against accidental widening of the perimeter by future edits.
    """
    repo_perimeter = Path("translations/PERIMETER.md")
    if not repo_perimeter.exists():
        pytest.skip("repo-level PERIMETER.md not present (test expects repo cwd)")
    perimeter = p.parse_perimeter(repo_perimeter)
    declared_with_scope = {k: v for k, v in perimeter.items() if v}
    assert len(declared_with_scope) == 4, (
        f"expected 4 CSVs with in-scope langs, got {len(declared_with_scope)}: "
        f"{list(declared_with_scope.keys())}"
    )
    total_cells = sum(len(v) for v in declared_with_scope.values())
    assert total_cells == 6, (
        f"expected 6 (csv, lang) in-scope cells (4 en + 2 ru), got {total_cells}"
    )


# ---------------------------------------------------------------------------
# Smoke test : the inline YAML in translation-sync.yml references parse_perimeter.
# ---------------------------------------------------------------------------


def test_translation_sync_yml_references_parse_perimeter():
    """The T4 step in translation-sync.yml MUST call ``parse_perimeter`` and
    MUST NOT hardcode ``TARGET_LANGS`` as the iteration set. This catches
    accidental reverts where someone re-introduces the old ``active_langs``
    global-list behavior (issue #10349 anti-regression).
    """
    yml_path = HERE.parent.parent.parent / ".github" / "workflows" / "translation-sync.yml"
    if not yml_path.exists():
        pytest.skip(f"{yml_path} not present (test expects repo cwd)")
    text = yml_path.read_text(encoding="utf-8")
    # The fix MUST call parse_perimeter (otherwise the scope-fix never happens).
    assert "parse_perimeter" in text, (
        "translation-sync.yml no longer references parse_perimeter -- "
        "issue #10349 scope-fix has been reverted?"
    )
    # The old buggy pattern MUST NOT appear : ``active_langs = list(mod.TARGET_LANGS)``.
    # If this regresses, T4 will render all TARGET_LANGS for every CSV regardless
    # of PERIMETER.md, which is the bug #10349 fixes.
    assert "active_langs = list(mod.TARGET_LANGS)" not in text, (
        "translation-sync.yml re-introduced the bug : "
        "active_langs = list(mod.TARGET_LANGS) -- see issue #10349."
    )


if __name__ == "__main__":
    pytest.main([__file__, "-v"])