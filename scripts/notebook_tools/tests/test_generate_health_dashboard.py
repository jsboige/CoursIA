"""Tests for scripts/notebook_tools/generate_health_dashboard.py.

The module is a procedural one-shot generator (acceptance #4 of #4210): it reads
``COURSE_CATALOG.generated.json`` from the CWD and writes
``docs/reference/HEALTH_DASHBOARD.md`` to the CWD. It has no ``__main__`` guard
and no functions -- the whole body runs at import/exec time. The AST-import
isolation pattern therefore does not apply (no FunctionDef to extract).

The clean hermetic approach for a procedural one-shot is END-TO-END via
subprocess: run the script with ``cwd`` set to a ``tmp_path`` containing a
SYNTHETIC catalog, then assert on the generated Markdown. This pins the
generator's contract (aggregations, section structure, badge counts, per-serie
breakdown, BROKEN detail, snapshot date derivation, error path) without
touching the real catalog.

No real notebook data, no real ``COURSE_CATALOG.generated.json`` is read --
every fixture builds a minimal synthetic catalog.
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

# Absolute path to the module under test (resolved from this test file's
# location, independent of the pytest rootdir / CWD).
SCRIPT = Path(__file__).resolve().parents[1] / "generate_health_dashboard.py"

CATALOG = "COURSE_CATALOG.generated.json"
OUT = Path("docs") / "reference" / "HEALTH_DASHBOARD.md"


def _run(tree: Path) -> subprocess.CompletedProcess:
    """Run the generator with cwd=tree; return the CompletedProcess."""
    return subprocess.run(
        [sys.executable, str(SCRIPT)],
        cwd=str(tree),
        capture_output=True,
        text=True,
        encoding="utf-8",
    )


def _run_and_expect_file(tree: Path) -> str:
    """Run the generator and return the generated Markdown text.

    Fails with a rich diagnostic if the file was not written (rc, stdout,
    stderr shown) -- surfaces subprocess-env issues under pytest.
    """
    r = _run(tree)
    out = tree / OUT
    if not out.exists():
        raise AssertionError(
            f"generator did not write {out} (rc={r.returncode})\n"
            f"--- stdout ---\n{r.stdout}\n--- stderr ---\n{r.stderr}")
    return out.read_text(encoding="utf-8")


def _nb(**over) -> dict:
    """Build one synthetic catalog entry with sane defaults."""
    base = {
        "title": "nb",
        "serie": "ML",
        "status": "READY",
        "maturity": "prod",
        "kernel": "python3",
        "last_validation": "2026-01-01",
        "requires_gpu": False,
        "requires_cloud": False,
        "requires_wsl": False,
        "requires_api": False,
        "executable_locally": True,
    }
    base.update(over)
    return base


def _write_catalog(tree: Path, entries: list) -> Path:
    """Write a synthetic catalog at tree/COURSE_CATALOG.generated.json."""
    p = tree / CATALOG
    p.write_text(json.dumps(entries), encoding="utf-8")
    return p


# --------------------------------------------------------------------------- #
# Happy path: structure + global aggregation
# --------------------------------------------------------------------------- #
class TestStructureAndGlobals:
    def test_writes_output_file(self, tmp_path):
        _write_catalog(tmp_path, [_nb()])
        r = _run(tmp_path)
        assert r.returncode == 0, r.stderr
        assert (tmp_path / OUT).exists()

    def test_creates_nested_output_dir(self, tmp_path):
        # OUT = docs/reference/... -- parent dirs must be auto-created.
        _write_catalog(tmp_path, [_nb()])
        _run(tmp_path)
        assert (tmp_path / OUT).parent.is_dir()

    def test_header_title_present(self, tmp_path):
        _write_catalog(tmp_path, [_nb()])
        t = _run_and_expect_file(tmp_path)
        assert t.startswith("# Tableau de santé du dépôt")

    def test_total_count_in_prose(self, tmp_path):
        _write_catalog(tmp_path, [_nb(title=f"n{i}") for i in range(5)])
        assert "**5** notebooks référencés" in _run_and_expect_file(tmp_path)

    def test_global_status_table_percent(self, tmp_path):
        # 2 READY + 2 BROKEN of 4 -> 50.0% each.
        _write_catalog(tmp_path, [
            _nb(title="r1", status="READY"),
            _nb(title="r2", status="READY"),
            _nb(title="b1", status="BROKEN"),
            _nb(title="b2", status="BROKEN"),
        ])
        t = _run_and_expect_file(tmp_path)
        assert "| READY | 2 | 50.0% |" in t
        assert "| BROKEN | 2 | 50.0% |" in t

    def test_status_omitted_counts_as_unknown(self, tmp_path):
        # An entry with no status -> status_global Counter key "?", not crash.
        entries = [{"title": "x", "serie": "ML", "kernel": "python3"}]
        _write_catalog(tmp_path, entries)
        r = _run(tmp_path)
        assert r.returncode == 0
        # READY/DEMO/BROKEN rows show 0; no KeyError.
        assert "| READY | 0 | 0.0% |" in _run_and_expect_file(tmp_path)


# --------------------------------------------------------------------------- #
# Environment requirement badges
# --------------------------------------------------------------------------- #
class TestEnvBadges:
    def test_requirement_counts(self, tmp_path):
        # The 4 requirement-bearing notebooks are NOT local-executable; the
        # 5th is. (_nb() defaults executable_locally=True, so override to
        # False on the 4 that need gpu/cloud/wsl/api.)
        _write_catalog(tmp_path, [
            _nb(title="a", requires_gpu=True, executable_locally=False),
            _nb(title="b", requires_cloud=True, executable_locally=False),
            _nb(title="c", requires_wsl=True, executable_locally=False),
            _nb(title="d", requires_api=True, executable_locally=False),
            _nb(title="e", executable_locally=True),
        ])
        t = _run_and_expect_file(tmp_path)
        assert "| **local** (exécutable sans GPU/cloud/WSL) | 1 |" in t
        assert "| WSL requis | 1 |" in t
        assert "| GPU requis | 1 |" in t
        assert "| Cloud requis (QC / GenAI Docker) | 1 |" in t
        assert "| API key requise | 1 |" in t


# --------------------------------------------------------------------------- #
# Per-serie breakdown
# --------------------------------------------------------------------------- #
class TestPerSerieBreakdown:
    def test_serie_row_aggregation(self, tmp_path):
        _write_catalog(tmp_path, [
            _nb(title="r1", serie="ML", status="READY"),
            _nb(title="b1", serie="ML", status="BROKEN"),
            _nb(title="d1", serie="ML", status="DEMO"),
            _nb(title="r2", serie="Search", status="READY"),
        ])
        t = _run_and_expect_file(tmp_path)
        # ML: 1 READY, 1 DEMO, 1 BROKEN, 3 total, 33% READY
        assert "| ML | 1 | 1 | 1 | 3 | 33% |" in t
        # Search: 1 READY, 0 DEMO, 0 BROKEN, 1 total, 100% READY
        assert "| Search | 1 | 0 | 0 | 1 | 100% |" in t

    def test_series_sorted_alphabetically(self, tmp_path):
        _write_catalog(tmp_path, [
            _nb(title="a", serie="Zeta"),
            _nb(title="b", serie="Alpha"),
            _nb(title="c", serie="Mid"),
        ])
        t = _run_and_expect_file(tmp_path)
        assert t.index("| Alpha |") < t.index("| Mid |") < t.index("| Zeta |")


# --------------------------------------------------------------------------- #
# Kernels section
# --------------------------------------------------------------------------- #
class TestKernelsSection:
    def test_kernel_counts_most_common(self, tmp_path):
        _write_catalog(tmp_path, [
            _nb(title=f"p{i}", kernel="python3") for i in range(3)
        ] + [_nb(title="c0", kernel="csharp")] )
        t = _run_and_expect_file(tmp_path)
        assert "| python3 | 3 |" in t
        assert "| csharp | 1 |" in t
        # most_common -> python3 (3) before csharp (1).
        assert t.index("| python3 |") < t.index("| csharp |")


# --------------------------------------------------------------------------- #
# BROKEN detail section
# --------------------------------------------------------------------------- #
class TestBrokenSection:
    def test_broken_section_present_with_entries(self, tmp_path):
        _write_catalog(tmp_path, [
            _nb(title="broken1", status="BROKEN", serie="ML",
                maturity="beta", last_validation="2026-03-01"),
        ])
        t = _run_and_expect_file(tmp_path)
        assert "## BROKEN" in t
        assert "broken1" in t

    def test_no_broken_section_when_all_ready(self, tmp_path):
        _write_catalog(tmp_path, [_nb(title="r1", status="READY")])
        assert "## BROKEN" not in _run_and_expect_file(tmp_path)

    def test_broken_header_includes_count(self, tmp_path):
        _write_catalog(tmp_path, [
            _nb(title=f"b{i}", status="BROKEN") for i in range(2)
        ])
        assert "## BROKEN (2" in _run_and_expect_file(tmp_path)


# --------------------------------------------------------------------------- #
# Snapshot date derivation (catalog-derived, NOT Date.now)
# --------------------------------------------------------------------------- #
class TestSnapshotDate:
    def test_snapshot_date_is_max_last_validation(self, tmp_path):
        _write_catalog(tmp_path, [
            _nb(title="a", last_validation="2026-01-01"),
            _nb(title="b", last_validation="2026-07-15"),
            _nb(title="c", last_validation="2026-03-10"),
        ])
        t = _run_and_expect_file(tmp_path)
        assert "date catalogue : **2026-07-15**" in t

    def test_snapshot_date_na_when_no_validations(self, tmp_path):
        entries = [{"title": "x", "serie": "ML", "status": "READY"}]
        _write_catalog(tmp_path, entries)
        assert "date catalogue : **n/a**" in _run_and_expect_file(tmp_path)


# --------------------------------------------------------------------------- #
# Error path: non-list / empty catalog (assertion failure -> rc 1)
# --------------------------------------------------------------------------- #
class TestErrorPaths:
    def test_empty_list_aborts(self, tmp_path):
        _write_catalog(tmp_path, [])
        r = _run(tmp_path)
        assert r.returncode != 0
        # The script asserts "catalog must be a non-empty list".
        assert "non-empty list" in r.stderr

    def test_non_list_json_aborts(self, tmp_path):
        (tmp_path / CATALOG).write_text('{"not": "a list"}', encoding="utf-8")
        r = _run(tmp_path)
        assert r.returncode != 0

    def test_missing_catalog_aborts(self, tmp_path):
        # No catalog written -> FileNotFoundError (uncaught) -> rc != 0.
        r = _run(tmp_path)
        assert r.returncode != 0


# --------------------------------------------------------------------------- #
# stdout summary line
# --------------------------------------------------------------------------- #
class TestStdoutSummary:
    def test_summary_line_reports_counts(self, tmp_path):
        _write_catalog(tmp_path, [
            _nb(title="r", status="READY"),
            _nb(title="d", status="DEMO"),
            _nb(title="b", status="BROKEN"),
        ])
        r = _run(tmp_path)
        assert r.returncode == 0
        assert "total notebooks: 3" in r.stdout
        assert "READY 1" in r.stdout
        assert "DEMO 1" in r.stdout
        assert "BROKEN 1" in r.stdout

    def test_summary_reports_bytes_written(self, tmp_path):
        _write_catalog(tmp_path, [_nb()])
        r = _run(tmp_path)
        assert "wrote" in r.stdout
        assert "bytes" in r.stdout
