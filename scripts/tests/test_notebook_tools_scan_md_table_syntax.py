# -*- coding: utf-8 -*-
"""Regression tests for scan_md_table_syntax fence tracking and nav exclusions.

Each test pins a false-positive class eliminated while closing sweep #15719
(corpus at 0 findings): phantom fence closes on info strings, list-indented
fences never opening, and wordless arrow navigation footers flagged as
ORPHAN_TABLE_ROW. The controls assert the scanner still catches the REAL
defect each fix could have swallowed.
"""

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "notebook_tools"))

from scan_md_table_syntax import detect_md_table_syntax  # noqa: E402


def _pathologies(lines):
    return [f["pathology"] for f in detect_md_table_syntax(lines)]


# ---------------------------------------------------------------------------
# Fix 1: an info-string fence line is CONTENT, not a close (CommonMark forbids
# an info string on the closing fence). bonnes-pratiques.md had the tracker
# inverted for the rest of the file: ```javascript "closed" a phantom fence
# and the JS `||` lines were scanned as table blocks.
# ---------------------------------------------------------------------------

def test_info_string_does_not_close_fence():
    lines = [
        "```",
        "const a = error.x ||",
        "          error.y || error.z;",
        "```javascript",
        "const b = p || q;",
        "```",
        "",
        "prose paragraph",
    ]
    assert _pathologies(lines) == [], _pathologies(lines)


def test_control_unfenced_pipe_lines_still_flagged():
    # Same `||` lines WITHOUT any fence around them must still be reported
    # (NO_SEP: >= 3 pipe-lines without separator).
    lines = [
        "prose",
        "const a = error.x ||",
        "          error.y || error.z;",
        "const b = p || q;",
        "prose",
    ]
    assert "NO_SEP" in _pathologies(lines)


# ---------------------------------------------------------------------------
# Fix 2: a fence indented to a list item's content indent (4-8 spaces) opens.
# structure-presentation.md charts sit inside list items; the 0-3 space cap
# left them "outside" any fence and their ASCII pipe/box-drawing lines were
# reported as NO_SEP table blocks.
# ---------------------------------------------------------------------------

def test_list_indented_fence_opens():
    lines = [
        "- **Graphique:** évolution",
        "    ```",
        "    ^",
        "    |        ○ Concurrent A",
        "    80|      ○",
        "    60|             □ Concurrent B",
        "    ```",
        "",
        "prose",
    ]
    assert _pathologies(lines) == [], _pathologies(lines)


# ---------------------------------------------------------------------------
# Fix 3: the wordless series footer ``[Risk Parity <](x) | [MLP >](y)`` is a
# navigation strip (arrow prev/next semantics), not an ORPHAN_TABLE_ROW
# continuation of the table above it (QC-Py-Cloud-10, #15719).
# ---------------------------------------------------------------------------

def test_arrow_nav_footer_not_orphan():
    lines = [
        "| Concept | Outil | Usage |",
        "|---|---|---|",
        "| A | `a()` | un |",
        "| B | `b()` | deux |",
        "",
        "[Risk Parity <](./03-Risk-Parity.ipynb) | [MLP Forecasting >](./05-MLP.ipynb)",
    ]
    assert _pathologies(lines) == [], _pathologies(lines)


def test_control_real_orphan_row_still_flagged():
    # A genuine orphan continuation row (column count within 1 of the header,
    # after a break) is still an ORPHAN_TABLE_ROW -- the nav exclusion must
    # not swallow real orphans.
    lines = [
        "| Concept | Outil | Usage |",
        "|---|---|---|",
        "| A | `a()` | un |",
        "",
        "*italic break*",
        "",
        "| B | `b()` | deux |",
    ]
    assert "ORPHAN_TABLE_ROW" in _pathologies(lines)
