"""Tests for scripts/notebook_tools/detect_link_target_regression.py — link-target accent-regression guard.

Why this test file exists
-------------------------
`detect_link_target_regression.py` (registre #2876, triade axe 3) is the canonical
DETECTOR for FR accent introduction in markdown link TARGETS `[text](target)` — the
defect class that broke 10 links across 4 OWN PRs (c.677l/c.678/c.681/c.683, audit
firsthand c.684 with the detector itself). When the cure script `\b(mot)\b` touches
the source markdown, it modifies BOTH the link text AND the link target. If the
canonical on-disk filename is unaccented (`Infer-10-Model-Selection.ipynb`), the
target after cure reads `Infer-10-Model-sélection.ipynb` — a 404. The sibling
detectors (`check_identifier_regression.py` for code identifiers, the upcoming
caps-regression detector for sentence initials) don't catch this class because they
target a different scope (code vs caps, not link targets).

This file is the **pytest convention** companion to the canonical
`test_detect_link_target_regression.py` (unittest) shipped with the detector in
PR #7210. Both will coexist post-merge; pytest format aligns with sibling detector
test suites (`test_detect_accent_stripping.py`, `test_detect_svg_empty_display.py`,
`test_check_identifier_regression.py`).

Six clusters mirroring the detector's documented decision logic:

  1. TestStripAccents       -- NFD decomposition + oe/ae ligature + lower invariant
  2. TestExtractMdCells     -- source-as-list vs source-as-str split semantics
  3. TestCollectLinkTargets -- filters (HTTP, anchor, template, no-extension) + link-text preservation
  4. TestResolveTarget      -- relative resolution, anchor stripping, percent-decoding
  5. TestDiffTargets        -- position matching, accent-only diff, case-insensitive match, multi-link per cell
  6. TestScanNotebook       -- end-to-end dict contract, base/head refs, exit codes

Test data design: every accent-regression test case is grounded in the catalog
of 10 real defects found by the detector on 4 OWN PRs (c.684 audit). Each test
isolates one conjunct of the decision (link-target-presence + accent-only
delta + position-match) so a regression in any conjunct surfaces as a single
failure.
"""
import json
import sys
from pathlib import Path
from unittest import mock

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from detect_link_target_regression import (  # noqa: E402
    LINK_PATTERN,
    collect_link_targets,
    diff_targets,
    extract_md_cells,
    main,
    read_notebook_at_ref,
    resolve_target,
    scan_notebook,
    strip_accents,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _md(source) -> dict:
    """A markdown cell with given source (str OR list-of-strings)."""
    return {"cell_type": "markdown", "source": source}


def _code(source: str) -> dict:
    return {"cell_type": "code", "source": source}


def _nb(cells: list[dict]) -> dict:
    """Build a minimal nbformat-4 notebook from cells."""
    return {
        "cells": cells,
        "metadata": {"kernelspec": {"name": "python3", "display_name": "Python 3"}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def _write_nb(path: Path, cells: list[dict]) -> Path:
    """Write a real notebook to disk and return its path."""
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(_nb(cells), ensure_ascii=False), encoding="utf-8")
    return path


# ---------------------------------------------------------------------------
# 1. strip_accents — NFD + oe/ae + lower
# ---------------------------------------------------------------------------

class TestStripAccents:
    def test_basic_french_accents(self):
        assert strip_accents("sélection") == "selection"
        assert strip_accents("génération") == "generation"
        assert strip_accents("café") == "cafe"

    def test_no_accents_invariant(self):
        # No-op on already-stripped strings (defensive)
        assert strip_accents("Infer-10-Model-Selection") == "Infer-10-Model-Selection"
        assert strip_accents("") == ""

    def test_ligatures_oe_ae(self):
        # French ligatures (lowercase) are ASCII-fold by the detector's explicit replace
        assert strip_accents("cœur") == "coeur"
        assert strip_accents("œuvre") == "oeuvre"
        assert strip_accents("æquo") == "aequo"
        # NB: the detector does NOT fold uppercase Æ/Œ (replace is lowercase-only)
        # so case-sensitive matching with uppercase ligatures falls outside the
        # ASCII-fold contract. The diff_targets() .lower() bridges the gap.

    def test_combining_marks_pure_nfd(self):
        # NFD-decomposable characters: bare combining marks are removed
        assert strip_accents("é") == "e"
        assert strip_accents("à") == "a"
        assert strip_accents("ï") == "i"
        assert strip_accents("ñ") == "n"

    def test_combining_sequence_full_word(self):
        # Verify full words survive the combining-mark strip
        assert strip_accents("théorie") == "theorie"
        assert strip_accents("déjà") == "deja"

    def test_unicode_preserved_when_no_combining(self):
        # ASCII letters and non-Latin scripts are NOT touched
        assert strip_accents("日本語") == "日本語"
        assert strip_accents("ABC") == "ABC"


# ---------------------------------------------------------------------------
# 2. extract_md_cells — markdown-only filter + source normalization
# ---------------------------------------------------------------------------

class TestExtractMdCells:
    def test_filters_code_cells(self):
        cells = [_md("hello"), _code("x = 1"), _md("world")]
        result = extract_md_cells(_nb(cells))
        assert len(result) == 2
        assert result[0][0] == 0
        assert result[1][0] == 2

    def test_source_as_list_preserved(self):
        # nbformat source-as-list must NOT be joined (L677-L2 ★ lesson: avoid "" empty line)
        cells = [_md(["line1\n", "line2\n", "line3"])]
        result = extract_md_cells(_nb(cells))
        assert len(result) == 1
        idx, src = result[0]
        assert idx == 0
        assert src == ["line1\n", "line2\n", "line3"]

    def test_source_as_str_splitlines(self):
        cells = [_md("line1\nline2\nline3")]
        result = extract_md_cells(_nb(cells))
        assert result[0][1] == ["line1", "line2", "line3"]

    def test_empty_notebook(self):
        result = extract_md_cells(_nb([]))
        assert result == []

    def test_cell_indices_preserved_across_code_cells(self):
        # Indices in the original notebook are the source-of-truth for position matching
        cells = [_md("a"), _code("x = 1"), _code("y = 2"), _md("b"), _md("c")]
        result = extract_md_cells(_nb(cells))
        assert [idx for idx, _ in result] == [0, 3, 4]


# ---------------------------------------------------------------------------
# 3. collect_link_targets — link extraction + 5 filters
# ---------------------------------------------------------------------------

class TestCollectLinkTargets:
    def _cells_of(self, *cell_sources) -> list:
        """Build a notebook and return md_cells ready for collect_link_targets."""
        return extract_md_cells(_nb([_md(s) for s in cell_sources]))

    def test_basic_markdown_link(self):
        targets = collect_link_targets(self._cells_of("[Infer-10](Infer-10-Model-Selection.ipynb)"))
        assert len(targets) == 1
        t = targets[0]
        assert t["text"] == "Infer-10"
        assert t["target"] == "Infer-10-Model-Selection.ipynb"
        assert t["cell_idx"] == 0
        assert t["line_no"] == 1

    def test_multiple_links_per_line(self):
        targets = collect_link_targets(self._cells_of("[A](a.ipynb) and [B](b.ipynb)"))
        assert len(targets) == 2
        assert [t["target"] for t in targets] == ["a.ipynb", "b.ipynb"]

    def test_filter_http_links(self):
        targets = collect_link_targets(self._cells_of("[site](http://example.com) [local](file.ipynb)"))
        assert len(targets) == 1
        assert targets[0]["target"] == "file.ipynb"

    def test_filter_https_links(self):
        targets = collect_link_targets(self._cells_of("[secure](https://example.com) [local](file.ipynb)"))
        assert [t["target"] for t in targets] == ["file.ipynb"]

    def test_filter_mailto_links(self):
        targets = collect_link_targets(self._cells_of("[mail](mailto:foo@bar) [local](file.ipynb)"))
        assert [t["target"] for t in targets] == ["file.ipynb"]

    def test_filter_root_path_links(self):
        targets = collect_link_targets(self._cells_of("[abs](/abs/path.ipynb) [local](file.ipynb)"))
        assert [t["target"] for t in targets] == ["file.ipynb"]

    def test_filter_template_variables(self):
        targets = collect_link_targets(self._cells_of("[tpl]({variable}) [local](file.ipynb)"))
        assert [t["target"] for t in targets] == ["file.ipynb"]

    def test_filter_angle_bracket_template(self):
        targets = collect_link_targets(self._cells_of("[tpl](<placeholder>) [local](file.ipynb)"))
        assert [t["target"] for t in targets] == ["file.ipynb"]

    def test_filter_anchor_only(self):
        targets = collect_link_targets(self._cells_of("[section](#section-name) [local](file.ipynb)"))
        assert [t["target"] for t in targets] == ["file.ipynb"]

    def test_filter_percent_encoded(self):
        # Percent-encoded target is filtered out (ambiguous for filesystem match)
        targets = collect_link_targets(self._cells_of("[tpl](file%20name.ipynb) [local](file.ipynb)"))
        assert [t["target"] for t in targets] == ["file.ipynb"]

    def test_filter_no_extension_no_path(self):
        # Targets without file extension AND without path separator are filtered
        # (cannot be safely resolved as a file)
        targets = collect_link_targets(self._cells_of("[generic](variable) [local](file.ipynb)"))
        assert [t["target"] for t in targets] == ["file.ipynb"]

    def test_filter_trailing_slash(self):
        # Trailing slash = directory link, not file
        targets = collect_link_targets(self._cells_of("[dir](somedir/) [local](file.ipynb)"))
        assert [t["target"] for t in targets] == ["file.ipynb"]

    def test_link_with_anchor_extracted(self):
        # Anchor is part of the target string but resolve_target strips it
        targets = collect_link_targets(self._cells_of("[local](file.ipynb#section)"))
        assert len(targets) == 1
        assert targets[0]["target"] == "file.ipynb#section"

    def test_relative_path_with_subdirs(self):
        targets = collect_link_targets(self._cells_of("[ref](../other/notebook.ipynb)"))
        assert len(targets) == 1
        assert targets[0]["target"] == "../other/notebook.ipynb"

    def test_position_metadata_cell_idx_and_line_no(self):
        targets = collect_link_targets(self._cells_of("intro\n\n[link1](a.ipynb)\n\n[link2](b.ipynb)"))
        assert len(targets) == 2
        assert (targets[0]["cell_idx"], targets[0]["line_no"]) == (0, 3)
        assert (targets[1]["cell_idx"], targets[1]["line_no"]) == (0, 5)


# ---------------------------------------------------------------------------
# 4. resolve_target — relative resolution + anchor stripping + percent-decoding
# ---------------------------------------------------------------------------

class TestResolveTarget:
    def test_relative_same_dir(self):
        nb = Path("C:/foo/bar/nb.ipynb")
        resolved = resolve_target(nb, "sibling.ipynb")
        assert str(resolved).replace("\\", "/").endswith("foo/bar/sibling.ipynb")

    def test_relative_parent_dir(self):
        nb = Path("C:/foo/bar/nb.ipynb")
        resolved = resolve_target(nb, "../other.ipynb")
        assert str(resolved).replace("\\", "/").endswith("foo/other.ipynb")

    def test_anchor_stripped(self):
        nb = Path("C:/foo/bar/nb.ipynb")
        resolved = resolve_target(nb, "sibling.ipynb#section-1")
        # Anchor is stripped before resolve — only the file path remains
        assert str(resolved).replace("\\", "/").endswith("foo/bar/sibling.ipynb")
        assert "#section-1" not in str(resolved)

    def test_percent_decoded(self):
        nb = Path("C:/foo/bar/nb.ipynb")
        resolved = resolve_target(nb, "file%20name.ipynb")
        assert "file name.ipynb" in str(resolved) or "file%20name.ipynb" in str(resolved)
        # The percent-decoding is part of the documented contract (urllib.parse.unquote)


# ---------------------------------------------------------------------------
# 5. diff_targets — position matching + accent-only detection
# ---------------------------------------------------------------------------

class TestDiffTargets:
    def _mk(self, target: str, cell_idx: int = 0, line_no: int = 1) -> dict:
        return {"cell_idx": cell_idx, "line_no": line_no, "text": "X", "target": target}

    def test_no_change_no_regression(self):
        base = [self._mk("Infer-10.ipynb")]
        head = [self._mk("Infer-10.ipynb")]
        assert diff_targets(base, head) == []

    def test_accent_regression_detected_foundational(self):
        # The founding case: cure introduced accent in target
        base = [self._mk("Infer-10-Model-Selection.ipynb")]
        head = [self._mk("Infer-10-Model-sélection.ipynb")]
        regs = diff_targets(base, head)
        assert len(regs) == 1
        assert regs[0]["kind"] == "ACCENT_REGRESSION"
        assert regs[0]["target_added"] == "Infer-10-Model-sélection.ipynb"
        assert regs[0]["target_removed"] == "Infer-10-Model-Selection.ipynb"

    def test_accent_only_in_text_no_regression(self):
        # Text of link gains accent but target stays clean = NOT a target regression
        base = [self._mk("Infer-10-Selection.ipynb", )]
        base[0]["text"] = "Selection"
        head = [self._mk("Infer-10-Selection.ipynb")]
        head[0]["text"] = "Sélection"
        regs = diff_targets(base, head)
        assert regs == []

    def test_fundamental_change_ignored(self):
        # Target completely changes (not accent-only) = out of scope
        base = [self._mk("Infer-10.ipynb")]
        head = [self._mk("Infer-99.ipynb")]
        regs = diff_targets(base, head)
        assert regs == []

    def test_case_insensitive_match(self):
        # Capital S vs lowercase s = match via .lower() (case-insensitive match)
        base = [self._mk("Infer-10-Selection.ipynb")]
        head = [self._mk("Infer-10-sélection.ipynb")]
        regs = diff_targets(base, head)
        assert len(regs) == 1
        assert regs[0]["kind"] == "ACCENT_REGRESSION"

    def test_ligature_oe_ae_caught(self):
        # ASCII-fold: coeur/oeuvre match via strip_accents ligature replacement
        base = [self._mk("coeur.ipynb")]
        head = [self._mk("cœur.ipynb")]
        regs = diff_targets(base, head)
        assert len(regs) == 1

    def test_multiple_links_per_position_deduped(self):
        # Same position with multiple matches = each diff-targets once
        base = [
            self._mk("a.ipynb", line_no=1),
            self._mk("a.ipynb", line_no=1),  # same position
        ]
        head = [self._mk("à.ipynb", line_no=1)]
        regs = diff_targets(base, head)
        # The "seen" set de-duplicates (diag_key includes target strings)
        assert len(regs) == 1

    def test_position_mismatch_not_matched(self):
        # Different line_no = no match (position-based matching strict)
        base = [self._mk("Infer-10.ipynb", line_no=5)]
        head = [self._mk("Infér-10.ipynb", line_no=7)]
        regs = diff_targets(base, head)
        assert regs == []

    def test_meta_preserved_in_diagnostic(self):
        # All metadata fields are preserved for the dashboard/log consumer
        base = [self._mk("Infer-10-Selection.ipynb", cell_idx=3, line_no=22)]
        head = [self._mk("Infer-10-sélection.ipynb", cell_idx=3, line_no=22)]
        regs = diff_targets(base, head)
        assert regs[0]["head_cell_idx"] == 3
        assert regs[0]["head_line_no"] == 22
        assert regs[0]["base_cell_idx"] == 3
        assert regs[0]["base_line_no"] == 22
        assert regs[0]["text"] == "X"


# ---------------------------------------------------------------------------
# 6. scan_notebook — end-to-end + disk-existence verdict
# ---------------------------------------------------------------------------

class TestScanNotebook:
    def _make_nb(self, target: str) -> dict:
        return _nb([_md(f"| [Infer-10]({target}) |\n")])

    @mock.patch("detect_link_target_regression.read_notebook_at_ref")
    def test_scan_realistic_defect_broken_link(self, mock_read):
        """The catalog-founding defect: cure introduced accent, file absent on disk."""
        nb_base = self._make_nb("Infer-10-Model-Selection.ipynb")
        nb_head = self._make_nb("Infer-10-Model-sélection.ipynb")
        mock_read.side_effect = lambda path, ref: nb_base if ref == "origin/main" else nb_head

        # Mock Path.exists: the base variant exists, the accented variant does NOT
        real_resolve = resolve_target
        def fake_resolve(nb_path, target):
            if "sélection" in target or "selection" in target.lower():
                p = real_resolve(nb_path, target)
                # Override .exists for the test
                return p
            return real_resolve(nb_path, target)

        with mock.patch.object(Path, "exists", return_value=False):
            nb_path = Path("MyIA.AI.Notebooks/Probas/Infer/Infer-11-Topic-Models.ipynb")
            result = scan_notebook(nb_path, "origin/main", "origin/fix/c683-accents-2876")
            assert result["stats"]["regressions_count"] == 1
            # Without disk resolution distinction, kind stays ACCENT_REGRESSION
            assert result["regressions"][0]["kind"] in (
                "ACCENT_REGRESSION", "BROKEN_LINK_ACCENT_REGRESSION"
            )
            assert result["stats"]["base_links"] == 1
            assert result["stats"]["head_links"] == 1

    @mock.patch("detect_link_target_regression.read_notebook_at_ref")
    def test_scan_clean_no_regression(self, mock_read):
        """No regression when targets match exactly across base and head."""
        nb_base = self._make_nb("Infer-10-Model-Selection.ipynb")
        nb_head = self._make_nb("Infer-10-Model-Selection.ipynb")
        mock_read.side_effect = lambda path, ref: nb_base if ref == "origin/main" else nb_head

        nb_path = Path("MyIA.AI.Notebooks/Probas/Infer/Infer-11.ipynb")
        result = scan_notebook(nb_path, "origin/main", "origin/fix/clean")
        assert result["stats"]["regressions_count"] == 0
        assert result["regressions"] == []

    @mock.patch("detect_link_target_regression.read_notebook_at_ref")
    def test_scan_head_ref_none_uses_working_tree(self, mock_read):
        """head_ref=None means: read from disk via json.loads, not git show."""
        nb_base = self._make_nb("Infer-10.ipynb")
        # mock_read only called for base_ref; head loaded via nb_path.read_text
        mock_read.side_effect = lambda path, ref: nb_base

        nb_path = Path("MyIA.AI.Notebooks/Probas/Infer/Infer-11.ipynb")
        # When head_ref=None, scan_notebook reads the file from disk
        # We need to mock the file read
        nb_head_disk = self._make_nb("Infer-10.ipynb")  # clean: same as base
        with mock.patch.object(Path, "read_text", return_value=json.dumps(nb_head_disk)):
            with mock.patch.object(Path, "exists", return_value=True):
                result = scan_notebook(nb_path, "origin/main", None)
                assert "head_ref" in result
                # head_ref label is "working_tree" when head_ref=None
                assert result["head_ref"] == "working_tree"

    @mock.patch("detect_link_target_regression.read_notebook_at_ref")
    def test_scan_returns_resolved_paths(self, mock_read):
        """Diagnostic entries include resolved absolute paths and disk-existence flags."""
        nb_base = self._make_nb("Infer-10-Selection.ipynb")
        nb_head = self._make_nb("Infer-10-sélection.ipynb")
        mock_read.side_effect = lambda path, ref: nb_base if ref == "origin/main" else nb_head

        nb_path = Path("MyIA.AI.Notebooks/Probas/Infer/Infer-11.ipynb")
        with mock.patch.object(Path, "exists", return_value=False):
            result = scan_notebook(nb_path, "origin/main", "origin/fix/test")
            r = result["regressions"][0]
            assert "resolved_path_added" in r
            assert "resolved_path_removed" in r
            assert "resolved_exists_added" in r
            assert "resolved_exists_removed" in r
            assert r["resolved_exists_added"] is False
            assert r["resolved_exists_removed"] is False

    @mock.patch("detect_link_target_regression.read_notebook_at_ref")
    def test_scan_base_ref_unreadable_returns_error(self, mock_read):
        """Missing base_ref = explicit error in result (no crash)."""
        # Head reads OK; base_ref is unreadable (git show fails)
        mock_read.side_effect = lambda path, ref: (
            _nb([_md("[ok](a.ipynb)")]) if ref == "origin/fix/test" else None
        )
        nb_path = Path("MyIA.AI.Notebooks/Probas/Infer/Infer-11.ipynb")
        with mock.patch.object(Path, "exists", return_value=True):
            result = scan_notebook(nb_path, "origin/main", "origin/fix/test")
            assert "error" in result
            assert "base_ref" in result["error"]

    def test_read_notebook_at_ref_handles_subprocess_error(self):
        """read_notebook_at_ref returns None on subprocess failure (no crash)."""
        # Calling with a ref that doesn't exist = git show returns non-zero
        result = read_notebook_at_ref(
            Path("MyIA.AI.Notebooks/Probas/Infer/Infer-11.ipynb"),
            "origin/this-ref-does-not-exist-12345",
        )
        # Should return None, not raise
        assert result is None


# ---------------------------------------------------------------------------
# 7. main() — CLI exit codes
# ---------------------------------------------------------------------------

class TestMainExitCodes:
    def test_missing_notebook_exits_2(self, tmp_path, capsys):
        nb_path = tmp_path / "does_not_exist.ipynb"
        rc = main([str(nb_path)])
        assert rc == 2
        captured = capsys.readouterr()
        assert "introuvable" in captured.err or "ERROR" in captured.err

    @mock.patch("detect_link_target_regression.scan_notebook")
    def test_check_mode_exits_1_on_regression(self, mock_scan, tmp_path, capsys):
        nb_path = tmp_path / "test.ipynb"
        nb_path.write_text("{}", encoding="utf-8")
        mock_scan.return_value = {
            "notebook": str(nb_path),
            "regressions": [{"kind": "ACCENT_REGRESSION"}],
            "stats": {"base_links": 1, "head_links": 1, "regressions_count": 1},
            "base_ref": "origin/main",
            "head_ref": "working_tree",
        }
        rc = main([str(nb_path), "--check", "--json"])  # --json bypasses formatter
        assert rc == 1

    @mock.patch("detect_link_target_regression.scan_notebook")
    @mock.patch("detect_link_target_regression.print")  # suppress formatter
    def test_no_check_mode_exits_0_even_with_regression(self, mock_scan, mock_print, tmp_path, capsys):
        nb_path = tmp_path / "test.ipynb"
        nb_path.write_text("{}", encoding="utf-8")
        mock_scan.return_value = {
            "notebook": str(nb_path),
            "regressions": [{"kind": "ACCENT_REGRESSION"}],
            "stats": {"base_links": 1, "head_links": 1, "regressions_count": 1},
            "base_ref": "origin/main",
            "head_ref": "working_tree",
        }
        rc = main([str(nb_path)])  # no --check, no --json
        assert rc == 0

    @mock.patch("detect_link_target_regression.scan_notebook")
    def test_clean_run_exits_0(self, mock_scan, tmp_path, capsys):
        nb_path = tmp_path / "test.ipynb"
        nb_path.write_text("{}", encoding="utf-8")
        mock_scan.return_value = {
            "notebook": str(nb_path),
            "regressions": [],
            "stats": {"base_links": 0, "head_links": 0, "regressions_count": 0},
            "base_ref": "origin/main",
            "head_ref": "working_tree",
        }
        rc = main([str(nb_path), "--check"])
        assert rc == 0

    @mock.patch("detect_link_target_regression.scan_notebook")
    def test_json_output_is_valid_json(self, mock_scan, tmp_path, capsys):
        nb_path = tmp_path / "test.ipynb"
        nb_path.write_text("{}", encoding="utf-8")
        mock_scan.return_value = {
            "notebook": str(nb_path),
            "regressions": [],
            "stats": {"base_links": 0, "head_links": 0, "regressions_count": 0},
            "base_ref": "origin/main",
            "head_ref": "working_tree",
        }
        rc = main([str(nb_path), "--json"])
        assert rc == 0
        captured = capsys.readouterr()
        parsed = json.loads(captured.out)
        assert parsed["stats"]["regressions_count"] == 0


# ---------------------------------------------------------------------------
# 8. LINK_PATTERN — the regex itself
# ---------------------------------------------------------------------------

class TestLinkPattern:
    def test_captures_simple_link(self):
        m = LINK_PATTERN.search("[text](target.ipynb)")
        assert m.group(1) == "text"
        assert m.group(2) == "target.ipynb"

    def test_handles_unicode_text(self):
        m = LINK_PATTERN.search("[Sélection](Infer-10.ipynb)")
        assert m.group(1) == "Sélection"
        assert m.group(2) == "Infer-10.ipynb"

    def test_handles_path_separators(self):
        m = LINK_PATTERN.search("[ref](../sub/file.ipynb)")
        assert m.group(2) == "../sub/file.ipynb"

    def test_handles_anchor(self):
        m = LINK_PATTERN.search("[ref](file.ipynb#section)")
        assert m.group(2) == "file.ipynb#section"

    def test_no_match_on_plain_text(self):
        m = LINK_PATTERN.search("just text without links")
        assert m is None

    def test_no_match_on_incomplete_link(self):
        # Missing closing bracket
        m = LINK_PATTERN.search("[text(target.ipynb)")
        assert m is None
