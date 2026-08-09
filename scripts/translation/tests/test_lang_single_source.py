#!/usr/bin/env python3
r"""Single-source-of-truth tests for the target-language universe (#10109).

Two roles:

1. **Equivalence** -- every consumer's public lang list equals the canonical
   ``check_perimeter.TARGET_LANGS`` (so a divergence can never re-enter
   silently).

2. **Regression guard (acceptance #4)** -- FAIL if a language-list literal
   reappears outside the single source. The detector flags any ``list``/``tuple``
   literal whose set of string elements is a **superset of the 7 target langs**
   (i.e. the universe duplicated, possibly permuted -- the exact defect class:
   a positional ``zip``/``enumerate`` across two copies swaps translations
   without raising). It scans every ``.py`` under ``scripts/`` (excluding
   ``tests/`` fixtures and ``check_perimeter.py`` itself) and every ``.yml``
   under ``.github/`` for the same pattern as adjacent quoted codes.

Why superset-of-7 (not "any 2 lang codes"): a 2- or 3-lang list is a *subset*
with its own meaning (the RTL pair ``["ar","fa"]``, a non-Latin set), not a
duplicate of the universe. The defect is the *ordered universe* duplicated --
7/7. Subsets are out of scope and must stay expressible.
"""
import ast
import re
import sys
import warnings
from pathlib import Path

# scripts/translation/ on the path (tests/ -> parent).
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import check_perimeter as cp  # noqa: E402
import check_resync_only as cr  # noqa: E402
import check_translation_parity as ctp  # noqa: E402
import check_translation_sync as cts  # noqa: E402
import extract_cells_to_csv as ex  # noqa: E402
import multilingual_drift_audit as mda  # noqa: E402
import translate_csv as tc  # noqa: E402

# The canonical universe, pinned ONCE here (the test is allowed to name it; the
# production code is not). Ratified #4957 §1, CSV-schema column order.
CANON = ["en", "es", "ar", "fa", "zh", "ru", "pt"]
LANG_SET = set(CANON)

REPO_ROOT = Path(__file__).resolve().parents[3]
SINGLE_SOURCE = REPO_ROOT / "scripts" / "translation" / "check_perimeter.py"
THIS = Path(__file__).resolve()


# --- 1. the single source is the canonical ordered universe ------------------

def test_single_source_is_canonical():
    assert cp.TARGET_LANGS == CANON
    assert cp.PIVOT_LANG == "fr"
    assert cp.ALL_LANGS == [cp.PIVOT_LANG] + CANON


# --- 1b. every consumer equals the single source -----------------------------

def test_consumers_match_single_source():
    assert tc.TARGETS == cp.TARGET_LANGS
    assert cr.ALL_LANGS == tuple(cp.TARGET_LANGS)
    assert cr.PIVOT_LANG == cp.PIVOT_LANG
    assert ctp.TARGET_LANGS == cp.TARGET_LANGS
    assert cts.TARGET_LANGS == cp.TARGET_LANGS
    assert cts.PIVOT_LANG == cp.PIVOT_LANG
    assert cts.ALL_LANGS == [cp.PIVOT_LANG] + cp.TARGET_LANGS
    assert ex.PIVOT_LANG == cp.PIVOT_LANG
    assert ex.TARGET_LANGS == cp.TARGET_LANGS
    assert mda.LANGS == cp.TARGET_LANGS


# --- 2. regression guard: no universe literal outside the single source -----

def _is_universe_literal(node) -> bool:
    """True for a ``list``/``tuple`` AST node whose string elements include all
    7 target langs (the universe duplicated, possibly in another order)."""
    if not isinstance(node, (ast.List, ast.Tuple)):
        return False
    codes = {e.value for e in node.elts
             if isinstance(e, ast.Constant) and isinstance(e.value, str)}
    return LANG_SET <= codes  # superset of all 7


def test_no_universe_literal_in_scripts():
    """No ``.py`` under ``scripts/`` (bar the single source + tests) may carry
    the 7-lang universe as a literal -- it must come from ``check_perimeter``."""
    offenders = []
    for py in (REPO_ROOT / "scripts").rglob("*.py"):
        py = py.resolve()
        if py == SINGLE_SOURCE or py == THIS:
            continue
        if "tests" in py.relative_to(REPO_ROOT / "scripts").parts:
            continue  # test fixtures legitimately use lang lists
        try:
            # Suppress SyntaxWarnings from pre-existing warts (e.g. non-raw
            # regex strings) in scanned files -- they are not THIS test's
            # concern and must not surface as noise in CI.
            with warnings.catch_warnings():
                warnings.simplefilter("ignore", SyntaxWarning)
                tree = ast.parse(py.read_text(encoding="utf-8"))
        except (SyntaxError, OSError):
            continue
        for node in ast.walk(tree):
            if _is_universe_literal(node):
                offenders.append(f"{py.relative_to(REPO_ROOT)}:{node.lineno}")
    assert not offenders, (
        "language-universe literal(s) found outside the single source "
        f"(check_perimeter.TARGET_LANGS) -- import instead: {offenders}"
    )


# 6+ adjacent quoted lang codes = the universe literal in a YAML one-liner.
_YAML_LANG_RUN = re.compile(
    r'(["\'](?:en|es|ar|fa|zh|ru|pt)["\']\s*,?\s*){6,}'
)


def test_no_universe_literal_in_workflows():
    """No ``.yml`` under ``.github/`` may recite the 7-lang universe as a
    literal -- derive it via ``from check_perimeter import TARGET_LANGS``."""
    offenders = []
    for yml in (REPO_ROOT / ".github").rglob("*.yml"):
        for i, line in enumerate(yml.read_text(encoding="utf-8").splitlines(), 1):
            if _YAML_LANG_RUN.search(line):
                offenders.append(f"{yml.relative_to(REPO_ROOT)}:{i}")
    assert not offenders, (
        "language-universe literal(s) found in workflow YAML -- derive via "
        f"check_perimeter.TARGET_LANGS instead: {offenders}"
    )


if __name__ == "__main__":
    import pytest
    sys.exit(pytest.main([__file__, "-v"]))
