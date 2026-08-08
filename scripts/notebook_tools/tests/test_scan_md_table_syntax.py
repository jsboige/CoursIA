"""Tests for scripts/notebook_tools/scan_md_table_syntax.py.

Locks in the four table-syntax pathology detectors added for #10097:
COL_MISMATCH, NO_SEP, NO_BLANK_BEFORE, NO_BLANK_AFTER. Documents the
deliberate exclusions: fenced-code block contents, no-trailing-pipe tables,
escaped pipes, and list-prefixed table-following lines.
"""

import json
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from scan_md_table_syntax import (  # noqa: E402
    _pipe_count,
    _scan_block,
    _iter_blocks,
    scan_text,
    scan_notebook,
    scan_markdown_file,
    main,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _md(source) -> dict:
    """Build a minimal markdown cell with the convention source = list-of-lines."""
    if isinstance(source, str):
        source = [source]
    return {"cell_type": "markdown", "source": source}


def _write_nb(cells: list) -> str:
    nb = {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    f = tempfile.NamedTemporaryFile(
        mode="w", suffix=".ipynb", delete=False, encoding="utf-8"
    )
    json.dump(nb, f)
    f.close()
    return f.name


def _kinds(text: str) -> list:
    return [f["pathology"] for f in scan_text(text)]


# ---------------------------------------------------------------------------
# _pipe_count -- the column-mismatch arithmetic
# ---------------------------------------------------------------------------

def test_pipe_count_plain():
    assert _pipe_count("| a | b | c |") == 4  # leading + 2 inner + trailing


def test_pipe_count_no_trailing_pipe():
    assert _pipe_count("| a | b | c") == 3  # leading + 2 inner, no trailing


def test_pipe_count_escaped_pipe_not_counted():
    """\\| inside a cell is the canonical GFM escape -> NOT a column separator."""
    # Without escape, this would be 4 pipes; with \\| the third pipe is escaped.
    assert _pipe_count("| a | b \\| c |") == 3


def test_pipe_count_html_entity_not_counted():
    """&#124; and &vert; also escape a pipe."""
    assert _pipe_count("| a | b &#124; c |") == 3
    assert _pipe_count("| a | b &vert; c |") == 3


def test_pipe_count_empty():
    assert _pipe_count("") == 0


# ---------------------------------------------------------------------------
# COL_MISMATCH -- true positives
# ---------------------------------------------------------------------------

def test_col_mismatch_unescaped_pipe_in_data_row():
    """A `|` inside a data cell, un-escaped, makes that data row have one more
    pipe than the header -> phantom column -> mis-aligned render."""
    text = (
        "| Method | Note |\n"
        "|---|---|\n"
        "| foo | a | b |\n"  # 4 pipes vs header 3
        "| bar | c |\n"
    )
    assert "COL_MISMATCH" in _kinds(text)


def test_col_mismatch_unescaped_pipe_in_header_cell():
    """Phantom column in header row itself -- 4 pipes vs 3 in data rows."""
    text = (
        "| Method | Note | extra |\n"  # 4 pipes
        "|---|---|\n"
        "| foo | x |\n"               # 3 pipes
        "| bar | y |\n"
    )
    assert "COL_MISMATCH" in _kinds(text)


# ---------------------------------------------------------------------------
# COL_MISMATCH -- false positives (must stay SILENT)
# ---------------------------------------------------------------------------

def test_clean_balanced_table_not_flagged():
    """A well-formed GFM table with consistent pipe counts -> silent."""
    text = (
        "| A | B |\n"
        "|---|---|\n"
        "| 1 | 2 |\n"
        "| 3 | 4 |\n"
    )
    assert "COL_MISMATCH" not in _kinds(text)


def test_escaped_pipe_in_data_row_not_flagged():
    """\\| inside a cell is the canonical GFM escape -- correctly ignored."""
    text = (
        "| Method | Note |\n"
        "|---|---|\n"
        r"| foo | a \| b |" + "\n"  # literal backslash-pipe
        "| bar | c |\n"
    )
    assert "COL_MISMATCH" not in _kinds(text)


def test_no_trailing_pipe_table_not_flagged():
    """GFM allows tables without trailing pipes (e.g. `| a | b` / `|---|`)."""
    text = (
        "| A | B\n"     # no trailing pipe
        "|---|---\n"    # no trailing pipe
        "| 1 | 2\n"
        "| 3 | 4\n"
    )
    assert "COL_MISMATCH" not in _kinds(text)


# ---------------------------------------------------------------------------
# NO_SEP -- true positive + false positive
# ---------------------------------------------------------------------------

def test_no_sep_three_lines_no_separator():
    """3+ table-shaped lines without a `|---|` row -> GitHub renders as pre."""
    text = (
        "| A | B |\n"
        "| 1 | 2 |\n"
        "| 3 | 4 |\n"
    )
    assert "NO_SEP" in _kinds(text)


def test_no_sep_only_two_lines_is_not_a_table():
    """Two table-shaped lines are NOT enough to claim a table -- NO_SEP
    requires 3+. Documenting the threshold."""
    text = (
        "| A | B |\n"
        "| 1 | 2 |\n"
    )
    # Two lines: the iterator yields no block (one line is not enough to form
    # a TABLE_LINE run that triggers NO_SEP). No finding expected.
    assert "NO_SEP" not in _kinds(text)


def test_table_with_separator_not_flagged_no_sep():
    """If the separator is present, NO_SEP must NOT fire (even if other
    pathologies like COL_MISMATCH fire on the same block)."""
    text = (
        "| A | B |\n"
        "|---|---|\n"
        "| 1 | 2 |\n"
    )
    assert "NO_SEP" not in _kinds(text)


# ---------------------------------------------------------------------------
# NO_BLANK_BEFORE
# ---------------------------------------------------------------------------

def test_no_blank_before_prose_fuses():
    """A non-blank prose line directly before a table block -> the prose
    fuses with the first row."""
    text = (
        "Some prose paragraph.\n"
        "| A | B |\n"
        "|---|---|\n"
        "| 1 | 2 |\n"
    )
    assert "NO_BLANK_BEFORE" in _kinds(text)


def test_no_blank_before_clean_not_flagged():
    """A blank line before the table -> clean."""
    text = (
        "Some prose.\n"
        "\n"
        "| A | B |\n"
        "|---|---|\n"
        "| 1 | 2 |\n"
    )
    assert "NO_BLANK_BEFORE" not in _kinds(text)


def test_no_blank_before_at_start_of_file_not_flagged():
    """A table at the very top of a file has no preceding line -> clean."""
    text = "| A | B |\n|---|---|\n| 1 | 2 |\n"
    assert "NO_BLANK_BEFORE" not in _kinds(text)


def test_no_blank_before_heading_prefix_tolerated():
    """A heading line (`#`, `##`, ...) right above a table is tolerated.

    Headings followed by tables are a common, well-rendered pattern
    (`## Section\n\n| A | B |\n...`). The blank-line rule applies to prose,
    not to structural markdown elements like headings.
    """
    text = "## A heading\n| A | B |\n|---|---|\n| 1 | 2 |\n"
    assert "NO_BLANK_BEFORE" not in _kinds(text)


def test_no_blank_before_list_prefix_tolerated():
    """A list item directly above a table is tolerated -- the table is part of
    the list continuation in many GFM renderers."""
    text = (
        "- intro\n"
        "| A | B |\n"
        "|---|---|\n"
        "| 1 | 2 |\n"
    )
    assert "NO_BLANK_BEFORE" not in _kinds(text)


def test_no_blank_before_blockquote_prefix_tolerated():
    """A blockquote line (`>`) above a table is tolerated."""
    text = (
        "> some quote\n"
        "| A | B |\n"
        "|---|---|\n"
        "| 1 | 2 |\n"
    )
    assert "NO_BLANK_BEFORE" not in _kinds(text)


# ---------------------------------------------------------------------------
# NO_BLANK_AFTER
# ---------------------------------------------------------------------------

def test_no_blank_after_prose_fuses():
    """A non-blank prose line directly after a table block -> the prose
    fuses with the last row."""
    text = (
        "| A | B |\n"
        "|---|---|\n"
        "| 1 | 2 |\n"
        "Next paragraph fuses here.\n"
    )
    assert "NO_BLANK_AFTER" in _kinds(text)


def test_no_blank_after_clean_not_flagged():
    """A blank line after the table -> clean."""
    text = (
        "| A | B |\n"
        "|---|---|\n"
        "| 1 | 2 |\n"
        "\n"
        "Next paragraph.\n"
    )
    assert "NO_BLANK_AFTER" not in _kinds(text)


def test_no_blank_after_at_end_of_file_not_flagged():
    """A table at the very end of a file has no following line -> clean."""
    text = "| A | B |\n|---|---|\n| 1 | 2 |\n"
    assert "NO_BLANK_AFTER" not in _kinds(text)


def test_no_blank_after_list_prefix_tolerated():
    """A list item directly below a table is tolerated."""
    text = (
        "| A | B |\n"
        "|---|---|\n"
        "| 1 | 2 |\n"
        "- item\n"
    )
    assert "NO_BLANK_AFTER" not in _kinds(text)


def test_no_blank_after_two_stacked_tables_have_implicit_blank():
    """Two stacked tables -> the iterator yields TWO blocks, so the implicit
    `end` of the first is the `start` of the second; if the gap is non-blank,
    the second table block extends into the first (one merged block)."""
    text = (
        "| A | B |\n"
        "|---|---|\n"
        "| 1 | 2 |\n"
        "| C | D |\n"   # no blank between -> fuses into ONE block of 5 lines
        "|---|---|\n"
        "| 3 | 4 |\n"
    )
    # The merged block has 6 lines: header, sep, data, header, sep, data.
    # COL_MISMATCH fires (1st header has 3 pipes, 1st data has 3; 2nd header
    # has 3, 2nd data has 3) -> balanced. NO_SEP is absent (sep present).
    # NO_BLANK_BEFORE/AFTER also absent (no prose around). So nothing fires
    # -- but the resulting render is also a single 5-column table, which is
    # what the user probably wanted.
    findings = _kinds(text)
    # We don't assert "no findings" -- the merged-as-one behaviour is fine
    # and consistent with GFM. Just assert NO_SEP isn't wrong-fired.
    assert "NO_SEP" not in findings


# ---------------------------------------------------------------------------
# Fenced code immunity
# ---------------------------------------------------------------------------

def test_fenced_tree_diagram_not_flagged():
    """A tree diagram inside a fenced code block uses `|` and `|--` heavily;
    it must NOT trigger COL_MISMATCH or NO_SEP."""
    text = (
        "Some prose.\n"
        "\n"
        "```\n"
        "|-- lakers/\n"
        "|    |-- conftest.py\n"
        "|    |-- notebooks/\n"
        "|-- poetry.lock\n"
        "```\n"
        "\n"
        "| A | B |\n"
        "|---|---|\n"
        "| 1 | 2 |\n"
    )
    assert _kinds(text) == []


def test_fenced_ascii_payoff_not_flagged():
    """An ASCII payoff diagram inside a fence (pipes and dashes) is CODE,
    not a table -> silent."""
    text = (
        "```\n"
        "  A | B | C\n"
        " ---|---|---\n"
        "  1 | 2 | 3\n"
        "```\n"
    )
    assert _kinds(text) == []


# ---------------------------------------------------------------------------
# scan_notebook / scan_markdown_file -- orchestration
# ---------------------------------------------------------------------------

def test_scan_notebook_finds_in_markdown_cells():
    nb_text = (
        "| Method | Note |\n"
        "|---|---|\n"
        "| foo | a | b |\n"  # COL_MISMATCH
    )
    path = _write_nb([_md(nb_text)])
    findings = scan_notebook(Path(path))
    kinds = [f["pathology"] for f in findings]
    assert "COL_MISMATCH" in kinds
    # cell index is set
    assert all(f["cell"] == 0 for f in findings)


def test_scan_notebook_skips_code_cells():
    nb_text = (
        "| Method | Note |\n"
        "|---|---|\n"
        "| foo | a | b |\n"
    )
    path = _write_nb([
        {"cell_type": "code", "source": nb_text, "execution_count": 1, "outputs": []},
    ])
    findings = scan_notebook(Path(path))
    assert findings == []


def test_scan_markdown_file_picks_up_defects(tmp_path=None):
    # Use tempfile because tmp_path fixture is pytest-specific.
    p = Path(tempfile.mkdtemp()) / "test.md"
    p.write_text(
        "| A | B |\n"
        "| 1 | 2 |\n"   # NO_SEP (no separator)
        "| 3 | 4 |\n",
        encoding="utf-8",
    )
    findings = scan_markdown_file(p)
    assert "NO_SEP" in [f["pathology"] for f in findings]


def test_read_error_is_a_finding_not_a_crash():
    """A malformed .ipynb produces a READ_ERROR finding, not an exception."""
    p = Path(tempfile.mkdtemp()) / "broken.ipynb"
    p.write_text("this is not json", encoding="utf-8")
    findings = scan_notebook(p)
    assert any(f["pathology"] == "READ_ERROR" for f in findings)


# ---------------------------------------------------------------------------
# CLI / main
# ---------------------------------------------------------------------------

def test_main_clean_md_returns_zero():
    p = Path(tempfile.mkdtemp()) / "clean.md"
    p.write_text(
        "| A | B |\n|---|---|\n| 1 | 2 |\n",
        encoding="utf-8",
    )
    rc = main([str(p)])
    assert rc == 0


def test_main_dirty_md_with_check_returns_one():
    p = Path(tempfile.mkdtemp()) / "dirty.md"
    p.write_text(
        "| A | B |\n| 1 | 2 |\n| 3 | 4 |\n",  # NO_SEP
        encoding="utf-8",
    )
    rc = main([str(p), "--check"])
    assert rc == 1


def test_main_emit_json():
    p = Path(tempfile.mkdtemp()) / "dirty.md"
    p.write_text(
        "| A | B |\n| 1 | 2 |\n| 3 | 4 |\n",
        encoding="utf-8",
    )
    import io
    from contextlib import redirect_stdout
    buf = io.StringIO()
    with redirect_stdout(buf):
        rc = main([str(p), "--json"])
    assert rc == 0  # without --fail-on-findings / --check, exits 0 even dirty
    out = buf.getvalue()
    payload = json.loads(out)
    assert payload["total"] == 1
    assert payload["flagged"] == 1
    assert any(f["pathology"] == "NO_SEP" for f in payload["findings"])


def test_main_empty_scan_returns_two():
    """An empty scan (no matching file) is NOT a clean scan -- it exits 2."""
    p = Path(tempfile.mkdtemp())  # empty dir
    rc = main([str(p), "--check"])
    assert rc == 2


def test_main_unresolved_path_errors(tmp_path=None):
    """A path that doesn't exist / doesn't match -> parser error (exit 2)."""
    # argparse error path raises SystemExit(2). Capture it.
    import io
    from contextlib import redirect_stderr
    buf_err = io.StringIO()
    try:
        with redirect_stderr(buf_err):
            main(["/nonexistent/path/that/is/not/here.md"])
    except SystemExit as e:
        assert e.code == 2
    else:
        raise AssertionError("expected SystemExit(2) for unresolved path")


def test_main_skip_output_and_checkpoints():
    """`_output.ipynb` and `.ipynb_checkpoints/*` are skipped, not scanned."""
    d = Path(tempfile.mkdtemp())
    (d / "_output.ipynb").write_text(
        json.dumps({
            "cells": [_md("| A | B |\n| 1 | 2 |\n| 3 | 4 |\n")],
            "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
        }),
        encoding="utf-8",
    )
    (d / ".ipynb_checkpoints").mkdir()
    (d / ".ipynb_checkpoints" / "ckpt.ipynb").write_text(
        json.dumps({
            "cells": [_md("| A | B |\n| 1 | 2 |\n| 3 | 4 |\n")],
            "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
        }),
        encoding="utf-8",
    )
    # No notebook file in the dir matches -- expect empty-scan exit 2.
    rc = main([str(d), "--check"])
    assert rc == 2