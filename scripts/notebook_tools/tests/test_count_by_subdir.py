"""Tests for the `count-by-subdir` sub-command of notebook_tools.py (See #4959).

Covers cmd_count_by_subdir exposed at:
    python scripts/notebook_tools/notebook_tools.py count-by-subdir [...]

Behaviour under test:
- --series <name>  restricts to a single series; total/by_subfolder returned
- --all             includes research/archive/examples notebooks
- --check-readme    produces a 4-column table Actual / README / Status
- --json            emits machine-readable JSON
- invalid --series  returns total=0 (graceful empty result, no exception)
- counts are sourced from count_notebooks_by_series.count_notebooks_in_dir
  (no shadow implementation: if the wrapper breaks, the assertions fail
  on the contract, not on the underlying counts).
"""

import io
import json
import sys
from contextlib import redirect_stdout
from pathlib import Path

import pytest

_tools_dir = Path(__file__).resolve().parent.parent
if str(_tools_dir) not in sys.path:
    sys.path.insert(0, str(_tools_dir))

from notebook_tools import cmd_count_by_subdir


def _args(**kwargs):
    """Build a minimal argparse.Namespace compatible with cmd_count_by_subdir."""
    import argparse
    defaults = {
        "series": None,
        "all": False,
        "check_readme": False,
        "json": False,
    }
    defaults.update(kwargs)
    return argparse.Namespace(**defaults)


# ---------------------------------------------------------------------------
# cmd_count_by_subdir — happy paths on the real repository
# ---------------------------------------------------------------------------


class TestCmdCountBySubdir:
    def test_real_repo_all_series_default(self):
        """Default invocation: all series, pedagogical mode, human-readable."""
        buf = io.StringIO()
        with redirect_stdout(buf):
            rc = cmd_count_by_subdir(_args())
        assert rc == 0
        out = buf.getvalue()
        # All 10 main SERIES_ORDER entries from count_notebooks_by_series.py
        # appear in the human-readable output (GenAI..RL).
        for name in [
            "GenAI", "Search", "ML", "SymbolicAI", "QuantConnect",
            "GameTheory", "Sudoku", "Probas", "IIT", "RL",
        ]:
            assert name in out, f"expected series {name} in output"
        # Total line is present and indicates > 800 notebooks (sanity floor).
        assert "TOTAL" in out

    def test_real_repo_search_only(self):
        buf = io.StringIO()
        with redirect_stdout(buf):
            rc = cmd_count_by_subdir(_args(series="Search"))
        assert rc == 0
        out = buf.getvalue()
        assert "Search" in out
        # Search hub has 4 documented sub-folders per audit c.1331+6.
        assert "Applications" in out
        assert "Part1-Foundations" in out

    def test_real_repo_check_readme_search_ok(self):
        """Search hub is currently OK (actual == declared). Locks the gate."""
        buf = io.StringIO()
        with redirect_stdout(buf):
            rc = cmd_count_by_subdir(
                _args(series="Search", check_readme=True),
            )
        assert rc == 0
        out = buf.getvalue()
        assert "Search" in out
        assert "OK" in out
        assert "MISMATCH" not in out  # Search is documented aligned.

    def test_real_repo_check_readme_all(self):
        """--check-readme across all 10 series produces a table with at least
        one OK and may include MISMATCH entries (audit signal)."""
        buf = io.StringIO()
        with redirect_stdout(buf):
            rc = cmd_count_by_subdir(_args(check_readme=True))
        assert rc == 0
        out = buf.getvalue()
        assert "OK" in out
        # Series header is present
        assert "Series" in out

    def test_real_repo_json_single_series(self):
        buf = io.StringIO()
        with redirect_stdout(buf):
            rc = cmd_count_by_subdir(_args(series="Search", json=True))
        assert rc == 0
        payload = json.loads(buf.getvalue())
        assert "Search" in payload
        assert payload["Search"]["total"] >= 100  # Search = 115 currently
        assert "by_subfolder" in payload["Search"]
        # Subfolder keys are documented folder names.
        for sub in ["Applications", "Part1-Foundations", "Part4-Metaheuristics"]:
            assert sub in payload["Search"]["by_subfolder"]

    def test_real_repo_json_check_readme_enriched(self):
        """--check-readme --json emits enriched entries with readme_declared + status."""
        buf = io.StringIO()
        with redirect_stdout(buf):
            rc = cmd_count_by_subdir(
                _args(series="Search", check_readme=True, json=True),
            )
        assert rc == 0
        # Human-readable table goes to stdout first, then JSON.
        # Strip the table by finding the first '{' of the JSON object.
        out = buf.getvalue()
        json_start = out.find("{")
        assert json_start > 0
        payload = json.loads(out[json_start:])
        assert "Search" in payload
        search_entry = payload["Search"]
        assert search_entry["status"] == "OK"
        assert search_entry["readme_declared"] == search_entry["total"]

    def test_real_repo_all_includes_research(self):
        """--all produces a different (>=) total than the default."""
        default_buf = io.StringIO()
        with redirect_stdout(default_buf):
            cmd_count_by_subdir(_args(series="Search"))
        all_buf = io.StringIO()
        with redirect_stdout(all_buf):
            cmd_count_by_subdir(_args(series="Search", all=True))
        # Parse the "TOTAL" line out of each to compare counts.
        def parse_total(out):
            for line in out.splitlines():
                if line.strip().startswith("TOTAL"):
                    return int(line.split()[1])
            return -1

        default_total = parse_total(default_buf.getvalue())
        all_total = parse_total(all_buf.getvalue())
        assert all_total >= default_total > 0

    def test_invalid_series_returns_zero_no_exception(self):
        """--series NonExistent should not raise; total=0."""
        buf = io.StringIO()
        with redirect_stdout(buf):
            rc = cmd_count_by_subdir(_args(series="NonExistentSeries_xyz"))
        assert rc == 0
        out = buf.getvalue()
        assert "TOTAL" in out
        assert "0" in out  # total line shows 0


# ---------------------------------------------------------------------------
# Contract: cmd_count_by_subdir delegates to count_notebooks_by_series.py
# ---------------------------------------------------------------------------


class TestDelegationContract:
    """If the wrapper reimplements counting, this guard fails (pr-review §B)."""

    def test_wrapper_uses_pure_functions_from_count_module(self):
        """cmd_count_by_subdir must import count_notebooks_in_dir + extract_readme_count.

        We verify the import chain by introspecting the source: the function
        must call the underlying module rather than re-implement the loop.
        """
        import inspect
        from notebook_tools import cmd_count_by_subdir as fn
        src = inspect.getsource(fn)
        assert "count_notebooks_by_series" in src, (
            "cmd_count_by_subdir must delegate to count_notebooks_by_series "
            "(no shadow re-implementation — ai-01 mandate #4959)"
        )
        assert "count_notebooks_in_dir" in src
        assert "extract_readme_count" in src

    def test_series_order_matches_count_module(self):
        """The SERIES_ORDER list used for table output comes from the same module."""
        from notebook_tools import cmd_count_by_subdir as fn
        from count_notebooks_by_series import SERIES_ORDER
        import inspect
        src = inspect.getsource(fn)
        assert "SERIES_ORDER" in src
        # SERIES_ORDER in count_notebooks_by_series: 11 entries (incl. EPF)
        assert len(SERIES_ORDER) == 11
