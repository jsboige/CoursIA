"""Tests for scripts/notebook_tools/scan_md_table_syntax.py -- GFM markdown table
syntax defect detector (#10097, sub-issue of #3966).

Tests cover:
  - the core ``detect_md_table_syntax`` line-list API (the 4 pathologies:
    COL_MISMATCH, NO_SEP, NO_BLANK_BEFORE, NO_BLANK_AFTER, each positive + clean);
  - the GFM-correct column counter (``_column_count``): backtick code spans,
    escaped ``\\|``, inline math ``$...$``, and borderless rows are NOT false
    positives;
  - the fence-aware block grouping (pipes inside ``` blocks are ignored);
  - the notebook / markdown walkers (``scan_notebook`` / ``scan_markdown``);
  - the CLI (``--json`` shape, ``--check`` exit codes, empty-scan exit 2).

Uses synthetic fragments (no real-notebook coupling) for isolation.
See #10097, #3966.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from scan_md_table_syntax import (  # noqa: E402
    _column_count,
    _find_table_blocks,
    _has_delimiter_pipe,
    detect_md_table_syntax,
    main,
    scan_markdown,
    scan_notebook,
)


# ---------------------------------------------------------------------------
# _column_count -- the GFM-correct column counter (the FP-control heart)
# ---------------------------------------------------------------------------

class TestColumnCount:
    def test_bordered_row(self):
        # | a | b | c | -> 3 columns
        assert _column_count("| a | b | c |") == 3

    def test_borderless_row(self):
        # Borderless rows are valid GFM and have the SAME column count.
        assert _column_count("a | b | c") == 3

    def test_single_column_with_text(self):
        assert _column_count("| only |") == 1

    def test_backtick_span_pipe_not_counted(self):
        # A | inside `...` is a literal, not a delimiter (GFM protects code
        # spans). This is the #10097 MGS-3 canonical case (`Crossover | Mutation`)
        # -- it must NOT inflate the column count.
        assert _column_count("| Scope | `Crossover | Mutation` | x |") == 3

    def test_escaped_pipe_not_counted(self):
        # \| is the GFM-correct literal pipe; the author did it right, it must
        # not be counted (Infer-4 cell[7] `P(S=T\|C=T)`).
        assert _column_count("| S | P(T\\|C) | note |") == 3

    def test_inline_math_pipe_not_counted(self):
        # A | inside $...$ is a LaTeX norm bar; cannot be escaped without
        # breaking the math, so it is excluded (non-actionable).
        assert _column_count("| $|x|$ | description |") == 2

    def test_multiple_backtick_spans(self):
        assert _column_count("| a | `b|c` | `d|e` |") == 3


# ---------------------------------------------------------------------------
# _has_delimiter_pipe / math-pipe exclusion -- the P(X|Y) false-positive guard
# ---------------------------------------------------------------------------

class TestHasDelimiterPipe:
    def test_real_table_row_has_delimiter_pipe(self):
        assert _has_delimiter_pipe("| a | b |") is True
        assert _has_delimiter_pipe("a | b | c") is True

    def test_conditional_probability_pipe_excluded(self):
        # ``P(X|Y)`` plain-text conditional notation: the pipe is a math bar,
        # not a delimiter. The dominant Probas false-positive source (#10097).
        assert _has_delimiter_pipe("- P(Cloudy | Rain=True) = **0.800**") is False
        assert _has_delimiter_pipe("calculez P(Sprinkler | Rain=True)") is False

    def test_big_o_set_notation_excluded(self):
        # ``O(|A| x |S|)`` complexity notation -- pipes are abs/norm bars.
        assert _has_delimiter_pipe("complexite O(|A| x |S|)") is False

    def test_inline_math_pipe_excluded(self):
        assert _has_delimiter_pipe("- $P(z_t | z_{t-1})$ transition") is False

    def test_table_row_with_conditional_in_cell_still_detected(self):
        # A real table cell may legitimately contain P(A|B); the OUTER cell
        # delimiters remain, so it is still a table row.
        assert _has_delimiter_pipe("| Var | P(A|B) | note |") is True

    def test_english_aside_still_has_delimiter_pipe(self):
        # "a | b" flowing prose is unchanged (still a candidate; the >=2-row
        # block rule handles it, not this guard).
        assert _has_delimiter_pipe("text a | text b") is True


class TestMathPipeBlockExclusion:
    def test_consecutive_conditional_probs_not_a_table(self):
        # Two consecutive ``P(X|Y)`` exercise lines must NOT be mistaken for a
        # 2-row table block (was the #10097 Probas NO_BLANK false positive).
        lines = [
            "**Resultats** :",
            "- P(Cloudy | Rain=True) = **0.800** -- observationnel",
            "- P(Cloudy | do(Rain=True)) = **0.500** -- interventionnel",
        ]
        assert detect_md_table_syntax(lines) == []

    def test_conditional_probs_above_real_table_not_flagged(self):
        # A ``P(X|Y)`` line directly before a real table must not be treated as
        # the table's first row (no NO_BLANK_BEFORE on the real table's account,
        # and no spurious block merging).
        lines = [
            "",
            "| Algorithme | Usage |",
            "|---|---|",
            "| naive | P(C|X) bayesien |",
        ]
        f = detect_md_table_syntax(lines)
        # The table is clean (blank before, has sep); no finding expected.
        assert [x for x in f if x["pathology"] == "NO_BLANK_BEFORE"] == []


# ---------------------------------------------------------------------------
# detect_md_table_syntax -- the 4 pathologies (positive + clean)
# ---------------------------------------------------------------------------

class TestDetectColMismatch:
    def test_bare_pipe_in_cell_flagged(self):
        # A BARE unescaped | in a cell -> genuine phantom column (true positive).
        lines = [
            "| a | b | c |",
            "|---|---|---|",
            "| 1 | x | y z | extra |",  # 4 cols vs 3
        ]
        f = detect_md_table_syntax(lines)
        p = [x for x in f if x["pathology"] == "COL_MISMATCH"]
        assert len(p) == 1
        assert p[0]["line"] == 3

    def test_backtick_pipe_not_flagged(self):
        # The MGS-3 canonical case: backtick-protected pipe renders fine, must
        # NOT be flagged (the #10097 preliminary sample miscounted it).
        lines = [
            "| Strat | Valeur | Note |",
            "|------|--------|------|",
            "| Scope | `Crossover | Mutation` | ok |",
        ]
        f = detect_md_table_syntax(lines)
        assert [x for x in f if x["pathology"] == "COL_MISMATCH"] == []

    def test_escaped_pipe_not_flagged(self):
        lines = [
            "| Var | CPT |",
            "|-----|-----|",
            "| S | P(T\\|C) |",
        ]
        f = detect_md_table_syntax(lines)
        assert [x for x in f if x["pathology"] == "COL_MISMATCH"] == []

    def test_borderless_data_row_not_flagged(self):
        # Header bordered, data borderless -> same 3 logical columns, NOT a
        # mismatch (valid GFM).
        lines = [
            "| a | b | c |",
            "|---|---|---|",
            "1 | 2 | 3",
        ]
        f = detect_md_table_syntax(lines)
        assert [x for x in f if x["pathology"] == "COL_MISMATCH"] == []


class TestDetectNoSep:
    def test_three_pipe_lines_no_sep_flagged(self):
        # 3+ pipe-lines, no |---| separator -> GFM renders as <pre>, not a table.
        lines = [
            "Some prose.",
            "",
            "| a | b |",
            "| 1 | 2 |",
            "| 3 | 4 |",
        ]
        f = detect_md_table_syntax(lines)
        p = [x for x in f if x["pathology"] == "NO_SEP"]
        assert len(p) == 1

    def test_valid_table_not_no_sep(self):
        lines = [
            "| a | b |",
            "|---|---|",
            "| 1 | 2 |",
        ]
        f = detect_md_table_syntax(lines)
        assert [x for x in f if x["pathology"] == "NO_SEP"] == []

    def test_two_pipe_lines_not_flagged(self):
        # A stray 2-line pipe snippet is not meant to be a table (3-line floor).
        lines = [
            "text a | text b",
            "more | stuff",
        ]
        f = detect_md_table_syntax(lines)
        assert [x for x in f if x["pathology"] == "NO_SEP"] == []


class TestDetectNoBlankBefore:
    def test_prose_directly_before_table_flagged(self):
        lines = [
            "This is a paragraph with no trailing blank.",
            "| a | b |",
            "|---|---|",
            "| 1 | 2 |",
        ]
        f = detect_md_table_syntax(lines)
        p = [x for x in f if x["pathology"] == "NO_BLANK_BEFORE"]
        assert len(p) == 1

    def test_blank_before_table_not_flagged(self):
        lines = [
            "Paragraph.",
            "",
            "| a | b |",
            "|---|---|",
            "| 1 | 2 |",
        ]
        f = detect_md_table_syntax(lines)
        assert [x for x in f if x["pathology"] == "NO_BLANK_BEFORE"] == []

    def test_heading_before_table_not_flagged(self):
        # A heading directly above a table is valid (no blank needed).
        lines = [
            "### Results",
            "| a | b |",
            "|---|---|",
            "| 1 | 2 |",
        ]
        f = detect_md_table_syntax(lines)
        assert [x for x in f if x["pathology"] == "NO_BLANK_BEFORE"] == []


class TestDetectNoBlankAfter:
    def test_prose_directly_after_table_flagged(self):
        lines = [
            "",
            "| a | b |",
            "|---|---|",
            "| 1 | 2 |",
            "Trailing paragraph glued to the table.",
        ]
        f = detect_md_table_syntax(lines)
        p = [x for x in f if x["pathology"] == "NO_BLANK_AFTER"]
        assert len(p) == 1

    def test_blank_after_table_not_flagged(self):
        lines = [
            "",
            "| a | b |",
            "|---|---|",
            "| 1 | 2 |",
            "",
            "Paragraph.",
        ]
        f = detect_md_table_syntax(lines)
        assert [x for x in f if x["pathology"] == "NO_BLANK_AFTER"] == []


class TestDetectClean:
    def test_clean_table_no_findings(self):
        lines = [
            "Intro.",
            "",
            "| a | b | c |",
            "|---|---|---|",
            "| 1 | 2 | 3 |",
            "| 4 | 5 | 6 |",
            "",
            "Outro.",
        ]
        assert detect_md_table_syntax(lines) == []

    def test_no_tables_no_findings(self):
        assert detect_md_table_syntax(["plain text", "no pipes here", ""]) == []


# ---------------------------------------------------------------------------
# _find_table_blocks -- fence awareness
# ---------------------------------------------------------------------------

class TestFindTableBlocks:
    def test_pipe_in_code_fence_ignored(self):
        # Pipes inside a ``` block are code, not table rows.
        lines = [
            "```",
            "| not | a | table |",
            "| 1 | 2 | 3 |",
            "| 4 | 5 | 6 |",
            "```",
        ]
        blocks = _find_table_blocks(lines)
        assert blocks == []

    def test_real_table_block_found(self):
        lines = [
            "",
            "| a | b |",
            "|---|---|",
            "| 1 | 2 |",
        ]
        blocks = _find_table_blocks(lines)
        assert len(blocks) == 1
        assert blocks[0]["has_sep"] is True


# ---------------------------------------------------------------------------
# Notebook / markdown walkers
# ---------------------------------------------------------------------------

def _write_nb(path, cells):
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {"cells": cells, "metadata": {"kernelspec": {"name": "python3"}},
          "nbformat": 4, "nbformat_minor": 5}
    path.write_text(json.dumps(nb), encoding="utf-8")


class TestScanNotebook:
    def test_finds_defect_in_markdown_cell(self, tmp_path):
        p = tmp_path / "nb.ipynb"
        _write_nb(p, [
            {"cell_type": "markdown", "source": [
                "| a | b |\n",
                "|---|---|\n",
                "| 1 | x | y |\n",  # COL_MISMATCH
            ]},
            {"cell_type": "code", "source": ["print('hi')"], "outputs": [],
             "execution_count": 1},
        ])
        r = scan_notebook(str(p))
        assert r["error"] is None
        assert len(r["findings"]) == 1
        assert r["findings"][0]["cell_index"] == 0
        assert r["findings"][0]["pathology"] == "COL_MISMATCH"

    def test_code_cell_not_scanned(self, tmp_path):
        p = tmp_path / "nb.ipynb"
        _write_nb(p, [
            {"cell_type": "code", "source": [
                "# | a | b |\n",
                "# | 1 | 2 | 3 | extra |\n",
            ], "outputs": [], "execution_count": 1},
        ])
        r = scan_notebook(str(p))
        assert r["findings"] == []

    def test_unreadable_notebook_returns_error(self, tmp_path):
        p = tmp_path / "broken.ipynb"
        p.write_text("{ not json", encoding="utf-8")
        r = scan_notebook(str(p))
        assert r["error"] is not None
        assert r["findings"] == []


class TestScanMarkdown:
    def test_finds_no_blank_before(self, tmp_path):
        p = tmp_path / "doc.md"
        p.write_text("Prose line.\n| a | b |\n|---|---|\n| 1 | 2 |\n",
                     encoding="utf-8")
        r = scan_markdown(str(p))
        assert r["error"] is None
        assert any(x["pathology"] == "NO_BLANK_BEFORE" for x in r["findings"])

    def test_clean_markdown(self, tmp_path):
        p = tmp_path / "doc.md"
        p.write_text("Intro.\n\n| a | b |\n|---|---|\n| 1 | 2 |\n\nOutro.\n",
                     encoding="utf-8")
        assert scan_markdown(str(p))["findings"] == []


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

class TestCli:
    def test_json_output_shape(self, tmp_path, capsys):
        p = tmp_path / "doc.md"
        p.write_text("Prose.\n| a | b |\n|---|---|\n| 1 | x | y |\n",
                     encoding="utf-8")
        rc = main([str(p), "--json"])
        out = json.loads(capsys.readouterr().out)
        assert rc == 0  # no --check -> always 0 on success
        assert out["total_findings"] >= 1
        assert out["files"][0]["path"] == str(p)

    def test_check_exits_one_on_finding(self, tmp_path):
        p = tmp_path / "doc.md"
        p.write_text("Prose.\n| a | b |\n|---|---|\n| 1 | x | y |\n",
                     encoding="utf-8")
        assert main([str(p), "--check"]) == 1

    def test_check_exits_zero_on_clean(self, tmp_path):
        p = tmp_path / "doc.md"
        p.write_text("Intro.\n\n| a | b |\n|---|---|\n| 1 | 2 |\n",
                     encoding="utf-8")
        assert main([str(p), "--check"]) == 0

    def test_empty_scan_exits_two(self, tmp_path):
        # A directory with no .ipynb/.md -> exit 2 (vacuous-zero guard).
        assert main([str(tmp_path)]) == 2

    def test_missing_path_exits_two(self):
        assert main(["definitely_does_not_exist_xyz123/"]) == 2
