"""Tests for ``scripts/notebook_tools/generate_health_dashboard.py`` — health-dashboard
generator (issue #4210 acceptance #4).

Why this test file exists
-------------------------
``generate_health_dashboard.py`` derives a public health snapshot from
``COURSE_CATALOG.generated.json`` and writes ``docs/reference/HEALTH_DASHBOARD.md``.
It is the *consumption* counterpart of the catalog generator (cron-driven,
``catalog-cron.yml``): where ``generate_catalog.py`` *writes* the catalogue,
``generate_health_dashboard.py`` *reads* it and produces a curated prose view.

Because the script is module-level (top-level imperative body, no functions
importable from the outside), the test strategy is **end-to-end subprocess**
with ``tmp_path`` + ``monkeypatch.chdir``:

  * write a synthesised catalogue to ``tmp_path/COURSE_CATALOG.generated.json``
  * run ``python scripts/notebook_tools/generate_health_dashboard.py`` in tmp_path
  * assert stdout, exit code, and ``tmp_path/docs/reference/HEALTH_DASHBOARD.md``

This matches the SOTA-not-workaround verdict of c.632: SOTA-OK = the tested code
is the canonical module, not a re-implementation toy. The module is pure-stdlib
(``json``/``pathlib``/``collections``/``datetime``); no external dependency.

Eight clusters mirroring the module's documented decision logic:

  1. TestCatalogParsing    — catalogue shape: empty / non-list / no last_validation
  2. TestStatusAggregation — Counter over status (READY/DEMO/BROKEN/UNKNOWN)
  3. TestMaturityKernel    — Counter over maturity/kernel
  4. TestRequirementBadges — requires_gpu/cloud/wsl/api + executable_locally
  5. TestSeriesBreakdown   — per-serie Counter, alphabetical sort, pct READY
  6. TestBrokenSection     — BROKEN list rendering, skipped when empty
  7. TestOutputStructure   — header / footer / See #4210 anchors
  8. TestRunScript         — subprocess end-to-end + exit code + filesystem

Test data design: every catalogue below is built with ``_nb(...)`` (a one-line
helper producing a minimal valid notebook entry). All filesystem ops use
``tmp_path`` (isolation-first). The full anti-regression sweep
(``python -m pytest scripts/notebook_tools/tests/``) is NOT exercised here —
that's the suite-level concern, not the unit-level one.
"""
import json
import subprocess
import sys
from pathlib import Path

import pytest

SCRIPT_DIR = Path(__file__).resolve().parent.parent  # scripts/notebook_tools/
REPO_ROOT = SCRIPT_DIR.parent.parent  # repo root
GENERATOR = str((SCRIPT_DIR / "generate_health_dashboard.py").resolve())  # absolute path for subprocess

# Add scripts/notebook_tools to sys.path so the test can `import generate_health_dashboard`
# if/when the module exposes functions. The current module is script-style; the
# import is harmless (top-level execution guarded by `if __name__ == "__main__"`
# is intentionally absent — every import side-effects). We therefore avoid
# importing the module and run it as a subprocess instead.

# ---------------------------------------------------------------------------
# Helpers — catalogue entry factory
# ---------------------------------------------------------------------------

def _nb(
    serie: str = "Probas",
    title: str = "n01-demo",
    status: str = "READY",
    maturity: str = "DEMO",
    kernel: str = "python3",
    *,
    requires_gpu: bool = False,
    requires_cloud: bool = False,
    requires_wsl: bool = False,
    requires_api: bool = False,
    executable_locally: bool = True,
    last_validation: str = "2026-07-19T12:00:00Z",
) -> dict:
    """Build a minimal catalogue entry matching the schema documented in
    ``generate_catalog.py``."""
    return {
        "serie": serie,
        "title": title,
        "status": status,
        "maturity": maturity,
        "kernel": kernel,
        "requires_gpu": requires_gpu,
        "requires_cloud": requires_cloud,
        "requires_wsl": requires_wsl,
        "requires_api": requires_api,
        "executable_locally": executable_locally,
        "last_validation": last_validation,
    }


def _write_catalogue(tmp_path: Path, entries: list[dict]) -> Path:
    cat = tmp_path / "COURSE_CATALOG.generated.json"
    cat.write_text(json.dumps(entries), encoding="utf-8")
    return cat


def _run_generator(tmp_path: Path, entries: list[dict]) -> subprocess.CompletedProcess:
    """Run the generator as a subprocess, chdir=tmp_path so relative paths
    (``COURSE_CATALOG.generated.json`` in / ``docs/reference/HEALTH_DASHBOARD.md``
    out) resolve there."""
    _write_catalogue(tmp_path, entries)
    return subprocess.run(
        [sys.executable, GENERATOR],
        cwd=str(tmp_path),
        capture_output=True,
        text=True,
        timeout=30,
    )


# ---------------------------------------------------------------------------
# 1. Catalogue parsing — shape guards + edge cases
# ---------------------------------------------------------------------------
class TestCatalogParsing:
    def test_empty_list_assertion_fires(self, tmp_path):
        """An empty catalogue triggers the `assert isinstance(d, list) and d` guard."""
        _write_catalogue(tmp_path, [])
        result = subprocess.run(
            [sys.executable, GENERATOR],
            cwd=str(tmp_path),
            capture_output=True,
            text=True,
            timeout=30,
        )
        assert result.returncode != 0
        assert "catalog must be a non-empty list" in result.stderr or "AssertionError" in result.stderr

    def test_missing_last_validation_uses_n_a(self, tmp_path):
        """When no entry has last_validation, snapshot_date falls back to ``"n/a"``."""
        # Build entries with all-empty last_validation: max("") == ""
        entries = [_nb(title=f"n{i:02d}", last_validation="") for i in range(3)]
        result = _run_generator(tmp_path, entries)
        assert result.returncode == 0
        out = (tmp_path / "docs/reference/HEALTH_DASHBOARD.md").read_text(encoding="utf-8")
        assert "n/a" in out  # snapshot_date fallback rendered

    def test_mixed_dates_picks_max(self, tmp_path):
        """The script takes the lexicographic max of last_validation strings
        (ISO-8601 sorts chronologically as strings — a documented shortcut)."""
        entries = [
            _nb(title="old", last_validation="2025-01-01T00:00:00Z"),
            _nb(title="newer", last_validation="2026-07-19T12:00:00Z"),
            _nb(title="middle", last_validation="2025-12-31T23:59:59Z"),
        ]
        result = _run_generator(tmp_path, entries)
        assert result.returncode == 0
        out = (tmp_path / "docs/reference/HEALTH_DASHBOARD.md").read_text(encoding="utf-8")
        assert "2026-07-19T12:00:00Z" in out

    def test_status_counter_unknown_fallback(self, tmp_path):
        """An entry whose status is missing or unknown still increments
        status_global via the ``.get('status', '?')`` fallback."""
        entries = [
            _nb(title="n01", status="READY"),
            {"serie": "Test", "title": "n02"},  # no status key at all
            _nb(title="n03", status="WEIRD"),  # unknown status
        ]
        result = _run_generator(tmp_path, entries)
        assert result.returncode == 0
        out = (tmp_path / "docs/reference/HEALTH_DASHBOARD.md").read_text(encoding="utf-8")
        # Status table renders READY but WEIRD is NOT in the explicit loop;
        # only the 3 documented statuses get rows (READY/DEMO/BROKEN).
        assert "| READY |" in out
        # Markdown bold around count: ``**3** notebooks référencés au catalogue.``
        assert "**3** notebooks référencés au catalogue" in out


# ---------------------------------------------------------------------------
# 2. Status aggregation — Counter table
# ---------------------------------------------------------------------------
class TestStatusAggregation:
    @pytest.mark.parametrize("status,n", [
        ("READY", 7),
        ("DEMO", 3),
        ("BROKEN", 1),
    ])
    def test_status_count_in_table(self, tmp_path, status, n):
        entries = [_nb(title=f"n{i:02d}", status=status) for i in range(n)]
        result = _run_generator(tmp_path, entries)
        assert result.returncode == 0
        out = (tmp_path / "docs/reference/HEALTH_DASHBOARD.md").read_text(encoding="utf-8")
        # The status table renders ``| {status} | {n} | {pct:.1f}% |``
        assert f"| {status} | {n} |" in out

    def test_status_pct_renders_one_decimal(self, tmp_path):
        """Percentage is rendered with ``:.1f`` — 1 decimal place."""
        # 1 BROKEN out of 3 = 33.3%
        entries = (
            [_nb(title=f"ready{i}", status="READY") for i in range(2)]
            + [_nb(title="broken", status="BROKEN")]
        )
        result = _run_generator(tmp_path, entries)
        out = (tmp_path / "docs/reference/HEALTH_DASHBOARD.md").read_text(encoding="utf-8")
        assert "| BROKEN | 1 | 33.3% |" in out
        assert "| READY | 2 | 66.7% |" in out

    def test_statuses_not_in_table_are_ignored(self, tmp_path):
        """Unknown statuses (not in [READY, DEMO, BROKEN]) are counted in
        status_global but do NOT appear in the rendered table."""
        entries = [
            _nb(title="weird", status="ARCHIVED"),
            _nb(title="r", status="READY"),
        ]
        result = _run_generator(tmp_path, entries)
        out = (tmp_path / "docs/reference/HEALTH_DASHBOARD.md").read_text(encoding="utf-8")
        # ARCHIVED never rendered as a table row
        assert "| ARCHIVED |" not in out
        assert "| READY | 1 |" in out


# ---------------------------------------------------------------------------
# 3. Maturity + Kernel — Counter tables
# ---------------------------------------------------------------------------
class TestMaturityKernel:
    def test_maturity_counter_appears_in_summary(self, tmp_path):
        """Maturity is computed but NOT rendered in a dedicated table in the
        current module — we only assert it doesn't crash the script. The Counter
        is alive in stdout though (printed totals)."""
        entries = [_nb(title=f"n{i}", maturity="DEMO") for i in range(3)]
        result = _run_generator(tmp_path, entries)
        assert result.returncode == 0

    def test_kernel_counter_most_common_sorting(self, tmp_path):
        """Kernels table renders in Counter.most_common() order (descending count)."""
        entries = [
            _nb(title=f"py{i}", kernel="python3") for i in range(5)
        ] + [
            _nb(title=f"cs{i}", kernel="dotnet-interactive") for i in range(2)
        ] + [
            _nb(title="lean1", kernel="lean4"),
        ]
        result = _run_generator(tmp_path, entries)
        out = (tmp_path / "docs/reference/HEALTH_DASHBOARD.md").read_text(encoding="utf-8")
        # python3 first (5), then dotnet-interactive (2), then lean4 (1)
        py_idx = out.find("| python3 |")
        cs_idx = out.find("| dotnet-interactive |")
        lean_idx = out.find("| lean4 |")
        assert py_idx != -1 and cs_idx != -1 and lean_idx != -1
        assert py_idx < cs_idx < lean_idx  # descending frequency


# ---------------------------------------------------------------------------
# 4. Requirement badges — local / GPU / cloud / WSL / API
# ---------------------------------------------------------------------------
class TestRequirementBadges:
    def test_local_count_excludes_other_requirements(self, tmp_path):
        """``executable_locally`` is independent from GPU/cloud/wsl/api."""
        entries = [
            _nb(title="local1", executable_locally=True),
            _nb(title="local2", executable_locally=True),
            _nb(title="gpu1", executable_locally=False, requires_gpu=True),
            _nb(title="cloud1", executable_locally=False, requires_cloud=True),
        ]
        result = _run_generator(tmp_path, entries)
        out = (tmp_path / "docs/reference/HEALTH_DASHBOARD.md").read_text(encoding="utf-8")
        assert "| **local** (exécutable sans GPU/cloud/WSL) | 2 |" in out
        assert "| GPU requis | 1 |" in out
        assert "| Cloud requis (QC / GenAI Docker) | 1 |" in out

    def test_requirement_counts_aggregate_across_overlap(self, tmp_path):
        """A notebook can be GPU+WSL simultaneously; each requirement counter
        increments independently (sum can exceed total)."""
        entries = [
            _nb(title="both", requires_gpu=True, requires_wsl=True),
            _nb(title="gpu-only", requires_gpu=True),
            _nb(title="wsl-only", requires_wsl=True),
        ]
        result = _run_generator(tmp_path, entries)
        out = (tmp_path / "docs/reference/HEALTH_DASHBOARD.md").read_text(encoding="utf-8")
        assert "| GPU requis | 2 |" in out
        assert "| WSL requis | 2 |" in out

    def test_all_zero_requirements_renders_clean(self, tmp_path):
        entries = [_nb(title=f"n{i}", executable_locally=True) for i in range(4)]
        result = _run_generator(tmp_path, entries)
        out = (tmp_path / "docs/reference/HEALTH_DASHBOARD.md").read_text(encoding="utf-8")
        assert "| **local** (exécutable sans GPU/cloud/WSL) | 4 |" in out
        assert "| GPU requis | 0 |" in out


# ---------------------------------------------------------------------------
# 5. Series breakdown — per-serie Counter + alphabetical sort
# ---------------------------------------------------------------------------
class TestSeriesBreakdown:
    def test_series_alphabetical_sort(self, tmp_path):
        """Series are rendered in sorted() order, NOT insertion order."""
        entries = [
            _nb(serie="Search", title="s1", status="READY"),
            _nb(serie="Audio", title="a1", status="BROKEN"),
            _nb(serie="ML", title="m1", status="DEMO"),
        ]
        result = _run_generator(tmp_path, entries)
        out = (tmp_path / "docs/reference/HEALTH_DASHBOARD.md").read_text(encoding="utf-8")
        audio_idx = out.find("| Audio |")
        ml_idx = out.find("| ML |")
        search_idx = out.find("| Search |")
        assert audio_idx != -1 and ml_idx != -1 and search_idx != -1
        assert audio_idx < ml_idx < search_idx

    def test_series_pct_renders_zero_decimals(self, tmp_path):
        """Series pct uses ``:.0f`` (integer rounding) — distinct from status
        table which uses ``:.1f``."""
        # 2 READY + 1 BROKEN = 67% READY (rounded to int), 3 total
        entries = [
            _nb(serie="Probas", title="r1", status="READY"),
            _nb(serie="Probas", title="r2", status="READY"),
            _nb(serie="Probas", title="b1", status="BROKEN"),
        ]
        result = _run_generator(tmp_path, entries)
        out = (tmp_path / "docs/reference/HEALTH_DASHBOARD.md").read_text(encoding="utf-8")
        assert "| Probas | 2 | 0 | 1 | 3 | 67% |" in out

    def test_series_total_zero_pct_no_crash(self, tmp_path):
        """A series with all-zero counts shouldn't divide by zero — current
        module guards via ``pct = 100*rdy/total if total else 0``. We can't
        construct an empty series because each entry adds at least one Counter
        bucket, but we can assert total >= 1 in every rendered row."""
        entries = [_nb(serie="Empty", title="x", status="DEMO")]
        result = _run_generator(tmp_path, entries)
        out = (tmp_path / "docs/reference/HEALTH_DASHBOARD.md").read_text(encoding="utf-8")
        assert "| Empty | 0 | 1 | 0 | 1 | 0% |" in out


# ---------------------------------------------------------------------------
# 6. BROKEN detail section
# ---------------------------------------------------------------------------
class TestBrokenSection:
    def test_broken_section_omitted_when_empty(self, tmp_path):
        """When no BROKEN entry exists, the entire BROKEN section is skipped
        (no table, no header)."""
        entries = [_nb(title=f"n{i}", status="READY") for i in range(3)]
        result = _run_generator(tmp_path, entries)
        out = (tmp_path / "docs/reference/HEALTH_DASHBOARD.md").read_text(encoding="utf-8")
        assert "## BROKEN" not in out

    def test_broken_section_lists_each_entry(self, tmp_path):
        """When BROKEN entries exist, each one gets a row with serie/title/maturity/last_validation."""
        entries = [
            _nb(serie="Probas", title="n01-broken", status="BROKEN", maturity="POC", last_validation="2026-01-15T08:00:00Z"),
            _nb(serie="Search", title="n02-stuck", status="BROKEN", maturity="LEGACY", last_validation="2025-11-03T19:42:00Z"),
        ]
        result = _run_generator(tmp_path, entries)
        out = (tmp_path / "docs/reference/HEALTH_DASHBOARD.md").read_text(encoding="utf-8")
        assert "## BROKEN (2 — à traiter en priorité)" in out
        assert "| Probas | n01-broken | POC | 2026-01-15T08:00:00Z |" in out
        assert "| Search | n02-stuck | LEGACY | 2025-11-03T19:42:00Z |" in out

    def test_broken_count_in_section_header(self, tmp_path):
        """The section header includes the live count between parens."""
        entries = [_nb(title=f"b{i}", status="BROKEN") for i in range(4)]
        result = _run_generator(tmp_path, entries)
        out = (tmp_path / "docs/reference/HEALTH_DASHBOARD.md").read_text(encoding="utf-8")
        assert "## BROKEN (4 — à traiter en priorité)" in out


# ---------------------------------------------------------------------------
# 7. Output structure — header / footer / anchors
# ---------------------------------------------------------------------------
class TestOutputStructure:
    def test_header_anchors_issue(self, tmp_path):
        """The doc anchors #4210 and #4208 explicitly — See #4210 (acceptance #4),
        See #4208 (CoursIA → référence publique)."""
        entries = [_nb(title="n1")]
        result = _run_generator(tmp_path, entries)
        out = (tmp_path / "docs/reference/HEALTH_DASHBOARD.md").read_text(encoding="utf-8")
        assert "acceptance #4 de #4210" in out
        assert "See #4208" in out
        assert "See #4210" in out

    def test_header_disclaimer_about_generation(self, tmp_path):
        """The 'snapshot statique' disclaimer is mandatory — it's the rationale
        for the doc being non-hand-maintained."""
        entries = [_nb(title="n1")]
        result = _run_generator(tmp_path, entries)
        out = (tmp_path / "docs/reference/HEALTH_DASHBOARD.md").read_text(encoding="utf-8")
        # The disclaimer wraps "n'est pas maintenu à la main" in ``**...**`` bold.
        assert "**n'est pas maintenu à la main**" in out
        assert "python scripts/notebook_tools/generate_health_dashboard.py" in out

    def test_total_notebooks_count_in_intro(self, tmp_path):
        entries = [_nb(title=f"n{i:02d}") for i in range(7)]
        result = _run_generator(tmp_path, entries)
        out = (tmp_path / "docs/reference/HEALTH_DASHBOARD.md").read_text(encoding="utf-8")
        assert "**7** notebooks référencés au catalogue." in out

    def test_voir_aussi_block_includes_catalogue_source(self, tmp_path):
        """The footer anchors the catalogue source."""
        entries = [_nb(title="n1")]
        result = _run_generator(tmp_path, entries)
        out = (tmp_path / "docs/reference/HEALTH_DASHBOARD.md").read_text(encoding="utf-8")
        assert "## Voir aussi" in out
        assert "COURSE_CATALOG.generated.md" in out
        assert "catalog-cron.yml" in out


# ---------------------------------------------------------------------------
# 8. End-to-end subprocess — exit code + filesystem + stdout
# ---------------------------------------------------------------------------
class TestRunScript:
    def test_run_exits_zero_on_valid_catalogue(self, tmp_path):
        entries = [_nb(title=f"n{i}") for i in range(3)]
        result = _run_generator(tmp_path, entries)
        assert result.returncode == 0

    def test_run_creates_output_file(self, tmp_path):
        entries = [_nb(title="n1")]
        _run_generator(tmp_path, entries)
        out_path = tmp_path / "docs/reference/HEALTH_DASHBOARD.md"
        assert out_path.exists()
        assert out_path.stat().st_size > 0

    def test_run_creates_parent_directories(self, tmp_path):
        """``OUT.parent.mkdir(parents=True, exist_ok=True)`` must create nested
        docs/reference/ even when tmp_path is empty."""
        entries = [_nb(title="n1")]
        result = _run_generator(tmp_path, entries)
        assert result.returncode == 0
        assert (tmp_path / "docs/reference").is_dir()

    def test_stdout_includes_wrote_line_and_totals(self, tmp_path):
        """The script prints two summary lines on stdout:
          - ``=== wrote {OUT} ({N} bytes, {M} lines) ===``
          - ``total notebooks: N | READY X DEMO Y BROKEN Z``
        """
        entries = (
            [_nb(title=f"r{i}", status="READY") for i in range(2)]
            + [_nb(title=f"d{i}", status="DEMO") for i in range(3)]
            + [_nb(title="b", status="BROKEN")]
        )
        result = _run_generator(tmp_path, entries)
        assert "wrote" in result.stdout
        assert "total notebooks: 6" in result.stdout
        assert "READY 2 DEMO 3 BROKEN 1" in result.stdout

    def test_stderr_empty_on_success(self, tmp_path):
        entries = [_nb(title="n1")]
        result = _run_generator(tmp_path, entries)
        assert result.stderr == ""

    def test_run_idempotent_overwrite(self, tmp_path):
        """Running the script twice on the same tmp_path produces the same
        output (deterministic — no timestamp, no random)."""
        entries = [_nb(title=f"n{i}") for i in range(3)]
        _run_generator(tmp_path, entries)
        first = (tmp_path / "docs/reference/HEALTH_DASHBOARD.md").read_text(encoding="utf-8")
        _run_generator(tmp_path, entries)
        second = (tmp_path / "docs/reference/HEALTH_DASHBOARD.md").read_text(encoding="utf-8")
        assert first == second

    def test_run_missing_catalogue_crashes_with_read_error(self, tmp_path):
        """No catalogue file at all → ``CAT.read_text()`` raises FileNotFoundError
        → subprocess exits non-zero with a Python traceback on stderr."""
        result = subprocess.run(
            [sys.executable, GENERATOR],
            cwd=str(tmp_path),
            capture_output=True,
            text=True,
            timeout=30,
        )
        assert result.returncode != 0
        assert "FileNotFoundError" in result.stderr or "No such file" in result.stderr
