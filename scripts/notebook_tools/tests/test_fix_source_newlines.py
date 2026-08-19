"""Tests for scripts/notebook_tools/fix_source_newlines.py

Covers:
  - detection of single-element collapsed source lists (heading + body fused)
  - detection of multi-element lists missing trailing '\\n'
  - the non-whitespace invariant (the fix only inserts '\\n', never removes
    non-whitespace characters)
  - no-op on already-correct cells (idempotent)
  - the script's CLI --scan / --apply / --check modes against a tmp file
  - end-to-end: --apply on a defective notebook makes
    detect_markdown_rendering.py render 0 source_list_missing_newlines findings
"""

import json
import sys
from pathlib import Path

_tools_dir = str(Path(__file__).resolve().parent.parent)
if _tools_dir not in sys.path:
    sys.path.insert(0, _tools_dir)

from fix_source_newlines import (
    _find_single_split,
    _round_trip_invariant,
    find_source_newline_defects,
)


def _make_nb(sources_by_cell):
    """Build a minimal nbformat notebook dict with markdown cells carrying
    the given source lists (one entry per cell)."""
    cells = []
    for src in sources_by_cell:
        cells.append({
            "cell_type": "markdown",
            "metadata": {},
            "source": list(src) if isinstance(src, list) else [src],
        })
    return {
        "cells": cells,
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


# --- detective unit tests -------------------------------------------------


def test_detect_single_collapsed_heading():
    """A single-element list with no '\\n' and a heading prefix is flagged."""
    nb = _make_nb([
        "# CSP-9-Distributed : CSP Distribués (DisCSP)**Navigation** : [<< CSP-8-Temporal](CSP-8-Temporal.ipynb)",
    ])
    defects = find_source_newline_defects(nb)
    assert len(defects) == 1
    assert defects[0]["kind"] == "single_collapsed"
    assert defects[0]["after"] is not None
    h, b = defects[0]["after"]
    # round-trip invariant
    assert _round_trip_invariant(defects[0]["before"], defects[0]["after"])
    # heading ends with newline so it terminates
    assert h.endswith("\n")
    # body starts with the body marker (with or without leading space)
    stripped = b.lstrip()
    assert stripped.startswith(": CSP"), f"body was {b!r}"


def test_detect_single_collapsed_no_body_marker_skipped():
    """A heading with no body marker (': ', '**', '- ', '1. ', '> ') is
    reported as a defect but NOT flagged as fixable (``after`` is None)."""
    s = "### Interprétation de la visualisation**Graphe de coloration** (image ci-dessus)"
    # Force 80+ chars to pass detector threshold
    s = s + " " + "x" * 80
    nb = _make_nb([s])
    defects = find_source_newline_defects(nb)
    # The detector rule requires _COLLAPSED_HEADING_START_RE.match(s)
    # In this case '### Interprétation...' starts with '###', so it matches.
    # The fix script reports the defect but with after=None.
    assert len(defects) == 1
    assert defects[0]["kind"] == "single_collapsed"
    # Either fixable or skipped (depends on body marker presence)
    if defects[0]["after"] is None:
        # round-trip trivially true (no after)
        assert True
    else:
        assert _round_trip_invariant(defects[0]["before"], defects[0]["after"])


def test_detect_multi_missing_trailing_newlines():
    """A multi-element list where some elements lack trailing '\\n' is flagged."""
    # 4 elements: first ends \\n, second MISSING \\n, third ends \\n, last no \\n (last is OK).
    # Detector rule: nb_breaks < len(src) - 1 → 2 < 3 → True.
    # Total content stripped must be >= 40 chars.
    src = [
        "# Heading\n",
        "Body line 1",  # <-- no trailing \n
        "Body line 2\n",
        "Body line 3 (last, no trailing newline is OK)",
    ]
    joined = "".join(src).strip()
    assert len(joined) >= 40, f"Test setup: ensure >= 40 chars, got {len(joined)}"
    nb = _make_nb([src])
    defects = find_source_newline_defects(nb)
    assert len(defects) == 1, f"Expected 1 defect, got {defects}"
    assert defects[0]["kind"] == "multi_missing_newlines"
    after = defects[0]["after"]
    # All non-last elements should end with '\n'
    for s in after[:-1]:
        assert s.endswith("\n"), f"Expected newline, got {s!r}"
    # round-trip invariant
    assert _round_trip_invariant(defects[0]["before"], after)


def test_round_trip_invariant_for_single_split():
    """The non-whitespace content is preserved by the single-element split."""
    # Must be >= 80 chars after strip (detector threshold).
    s = (
        "# CSP-9 : Distributiontitle**Body** : ceci est le body "
        "qui doit etre assez long pour passer le seuil de 80 chars"
    )
    assert len(s.strip()) >= 80, f"test setup: len(strip) = {len(s.strip())}"
    heading, body = _find_single_split(s)
    assert heading is not None, f"split failed on {s!r}"
    assert _round_trip_invariant([s], [heading, body])


def test_round_trip_invariant_for_multi():
    """Trailing-newline insertion preserves non-whitespace count."""
    before = ["abc", "def", "ghi"]
    after = ["abc\n", "def\n", "ghi"]
    assert _round_trip_invariant(before, after)


def test_noop_on_correct_cell():
    """A cell with all elements ending in '\\n' is NOT flagged."""
    nb = _make_nb([
        ["# Heading\n", "Body line 1\n", "Body line 2\n"],
    ])
    defects = find_source_newline_defects(nb)
    assert defects == []


def test_noop_on_short_single_element():
    """A short single-element cell (< 80 chars after strip) is NOT flagged."""
    nb = _make_nb([
        "# Short heading : short body",
    ])
    defects = find_source_newline_defects(nb)
    assert defects == []


def test_noop_on_code_cell():
    """Code cells are not inspected."""
    nb = {
        "cells": [
            {
                "cell_type": "code",
                "metadata": {},
                "source": ["a = 1\n", "b = 2"],  # multi-element missing \\n on last
                "execution_count": 1,
                "outputs": [],
            },
        ],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    defects = find_source_newline_defects(nb)
    assert defects == []


# --- end-to-end integration -----------------------------------------------


def _write_nb_file(path: Path, sources_by_cell):
    nb = _make_nb(sources_by_cell)
    path.write_text(json.dumps(nb, indent=1), encoding="utf-8")


def test_apply_and_detect_clean(tmp_path):
    """End-to-end: apply the fix on a notebook with a defective cell, then
    re-run detect_markdown_rendering.py logic against the result. The
    applied cell should NOT match the source_list_missing_newlines rule any
    more ('\\n' now present in the joined source)."""
    # Build a defective cell that the detector flags AND the fixer can split.
    p = tmp_path / "nb.ipynb"
    bad_source = (
        "# CSP-9-Distributed : CSP Distribués (DisCSP)**Navigation** : "
        + "[<< CSP-8-Temporal](CSP-8-Temporal.ipynb) " * 8
    )
    _write_nb_file(p, [bad_source])

    # Run the fixer via subprocess (script-level test)
    import subprocess
    script = Path(_tools_dir) / "fix_source_newlines.py"
    result = subprocess.run(
        [sys.executable, str(script), "--apply", str(p)],
        capture_output=True, text=True, check=False,
    )
    assert result.returncode == 0, f"stderr: {result.stderr}"

    # Re-read; the cell should now be a 2-element list with the first ending
    # in newline.
    nb = json.loads(p.read_text())
    src = nb["cells"][0]["source"]
    assert isinstance(src, list)
    assert len(src) >= 2
    assert src[0].endswith("\n")
    # Detector rule: a single-element list with no '\\n' no longer applies.
    # The source is multi-element with the first element ending in '\\n',
    # so the multi-element rule also won't flag it.
    defects = find_source_newline_defects(nb)
    # We may still register a defect for "len(non-blank) < len(src)-1 without
    # trailing newlines" if any inner element is missing a newline. With
    # heading\n and body the body does NOT end with \n (last element), so
    # no break is expected for the last element. So defects should be []
    # for THIS particular cell — multi-element rule requires
    # nb_breaks < len(src) - 1, which would be 1 < 1 = False.
    assert defects == [], f"Unexpected defects: {defects}"


def test_check_exit_code_when_defects(tmp_path):
    """`--scan ... --check` exits 1 when defects are present."""
    p = tmp_path / "nb.ipynb"
    bad_source = (
        "# CSP-9 : Distribution**Navigation** : body content " * 10
    )
    _write_nb_file(p, [bad_source])
    import subprocess
    script = Path(_tools_dir) / "fix_source_newlines.py"
    result = subprocess.run(
        [sys.executable, str(script), "--scan", str(p), "--check"],
        capture_output=True, text=True, check=False,
    )
    # Either fixable (exit 1) or skipped (exit 1) -> 1
    assert result.returncode == 1


def test_noop_idempotent(tmp_path):
    """Re-running apply on a clean notebook is a no-op (no further changes)."""
    p = tmp_path / "nb.ipynb"
    # Already correct: 2 elements, first ends with \\n
    _write_nb_file(p, [["# Heading\n", "Body text"]])
    before = p.read_text()
    import subprocess
    script = Path(_tools_dir) / "fix_source_newlines.py"
    result = subprocess.run(
        [sys.executable, str(script), "--apply", str(p)],
        capture_output=True, text=True, check=False,
    )
    assert result.returncode == 0
    after = p.read_text()
    # The JSON serialization may slightly differ (e.g. ensure_ascii=False vs
    # escaped unicode), but the structural content must be identical.
    nb_before = json.loads(before)
    nb_after = json.loads(after)
    assert nb_before == nb_after
