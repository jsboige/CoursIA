"""Tests for scripts/notebook_tools/detect_ascii_workaround.py — Prong-A ASCII detector.

Validates the artifact filter (c.598, fix to c.597 forensic finding #6843):
- _output papermill artifacts (filename suffix *_output.ipynb in this repo) are EXCLUDED
- canonical source is still scanned
- the documented SC-17 stale-artifact case firsthand: source has no bar, _output does
"""

import sys
from pathlib import Path

import pytest

# Convention siblings (test_notebook_tools_pure.py, test_execute_qcpy_docker.py) :
# inserer scripts/notebook_tools/ et importer le module directement. Importer
# `notebook_tools.detect_ascii_workaround` (package-style) enregistrerait le
# REPERTOIRE comme namespace package `notebook_tools` dans sys.modules, masquant
# le module notebook_tools.py pour les autres tests de la session pytest
# (ImportError "unknown location" en CI Scripts Tests).
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "notebook_tools"))

from detect_ascii_workaround import SKIP_DIRS, _should_skip, _iter_notebooks, detect_cell


class TestSkipDirs:
    """The artifact filter — prevents stale _output false positives."""

    def test_should_skip_output_filename_suffix(self):
        """A *_output.ipynb filename (papermill artifact) is flagged for skip.

        In this repo, _output artifacts are filename SUFFIXES, not directories
        (158 *_output.ipynb files, 0 _output/ dirs). This is the actual SC-17
        stale-artifact case from c.597.
        """
        rel = Path("SymbolicAI/SmartContracts/04-Privacy-Cryptography/SC-17-E2E-Verifiable-Voting_output.ipynb")
        assert _should_skip(rel) is True

    def test_should_not_skip_canonical_source(self):
        """The canonical source (no _output suffix) is NOT skipped."""
        rel = Path("SymbolicAI/SmartContracts/04-Privacy-Cryptography/SC-17-E2E-Verifiable-Voting.ipynb")
        assert _should_skip(rel) is False

    def test_should_skip_dir_segments(self):
        """A path under a SKIP_DIR (e.g. .lake) is also skipped."""
        rel = Path("SomeFam/.lake/build/nb.ipynb")
        assert _should_skip(rel) is True

    def test_skip_dirs_align_with_navlink_convention(self):
        """SKIP_DIRS mirrors check_notebook_navlinks.py:SKIP_DIRS (repo convention)."""
        expected = {
            ".lake", ".git", "__pycache__", "_archives", "archive", "_archive",
            ".ipynb_checkpoints", ".pytest_cache", "worktrees", "foundry-lib",
        }
        assert expected.issubset(SKIP_DIRS), f"missing: {expected - SKIP_DIRS}"

    @pytest.mark.parametrize("skip_dir", sorted(SKIP_DIRS))
    def test_each_skip_dir_caught_in_path(self, skip_dir):
        """Any SKIP_DIR appearing as a path segment triggers skip."""
        rel = Path(f"some/prefix/{skip_dir}/nb.ipynb")
        assert _should_skip(rel) is True, f"{skip_dir} not caught"


class TestIterNotebooksExcludesOutput:
    """The walk does not yield *_output.ipynb artifacts."""

    def test_no_output_artifacts_in_walk(self, tmp_path):
        """A tree with canonical + _output twin yields ONLY canonical."""
        nb_root = tmp_path / "MyIA.AI.Notebooks" / "Fam"
        nb_root.mkdir(parents=True)
        canonical = nb_root / "Nb.ipynb"
        artifact = nb_root / "Nb_output.ipynb"
        canonical.write_text('{"cells":[],"metadata":{},"nbformat":4,"nbformat_minor":5}', encoding="utf-8")
        artifact.write_text('{"cells":[],"metadata":{},"nbformat":4,"nbformat_minor":5}', encoding="utf-8")

        walked = [p.name for p in _iter_notebooks(tmp_path, family="Fam")]
        assert walked == ["Nb.ipynb"], f"_output artifact leaked into walk: {walked}"


class TestCSharpBarDetection:
    """C# (.NET Interactive) data-bar idiom `new string('#', barLen)` — closes the
    documented C# blind spot. Same discriminator as the Python forms: FILL char
    (not separator) repeated by a DATA-derived length (not a bare int literal).

    Calibrated against the current corpus (329 `new string`/`Enumerable.Repeat`/
    `PadLeft` occurrences, all separator chars -> 0 live hits): a capability
    extension + anti-regression guard for a future `new string('#', barLen)`.
    """

    def test_new_string_fill_char_data_length_is_defect(self):
        """`new string('#', barLen)` — fill char + data-derived length -> DEFECT."""
        assert detect_cell("var bar = new string('#', barLen);") is not None

    def test_new_string_fill_char_computed_expr_is_defect(self):
        """`new string('#', (int)(score*W))` — computed length -> DEFECT."""
        assert detect_cell("var b = new string('#', (int)(score*W));") is not None

    def test_enumerable_repeat_fill_char_is_defect(self):
        """`Enumerable.Repeat('|', score)` — .NET fill-repeat -> DEFECT."""
        assert detect_cell("var b = new string(Enumerable.Repeat('|', score).ToArray());") is not None

    def test_new_string_separator_dash_is_not_defect(self):
        """`new string('-', 60)` — separator char -> table border, NOT a data bar."""
        assert detect_cell("Console.WriteLine(new string('-', 60));") is None

    def test_new_string_separator_width_is_not_defect(self):
        """`new string('=', width)` — separator char (even with a variable) -> NOT a bar."""
        assert detect_cell("var line = new string('=', width);") is None

    def test_new_string_fill_char_constant_width_is_not_defect(self):
        """`new string('#', 40)` — fill char but FIXED literal width -> decorative border, NOT data."""
        assert detect_cell("var x = new string('#', 40);") is None
        assert detect_cell("var x = new string('#', 40 );") is None

    def test_padleft_separator_is_not_defect(self):
        """`.PadLeft(10, '=')` — padding, not a repeated data bar."""
        assert detect_cell("s.PadLeft(10, '=')") is None

    def test_signature_label_reported(self):
        """A C# data-bar hit carries the `csharp_new_string_bar` signature."""
        finding = detect_cell("var bar = new string('#', barLen);")
        assert finding is not None
        assert "csharp_new_string_bar" in finding["signatures"]

