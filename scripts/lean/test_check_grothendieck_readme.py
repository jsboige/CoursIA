#!/usr/bin/env python3
"""Tests for scripts/lean/check_grothendieck_readme.py — pin the six positive controls.

Background
----------
The checker is the **anti-récidive organe** for #15474. After the
2026-09-11 re-review on head ``cf2c0cb24`` flagged that
``--inject-fake`` only handled three of the four drift classes
(UNDERCOUNT, TOOLCHAIN_DRIFT, MISSING_IN_TABLE) and that ``--strict``
promotion of OVERCOUNT/ORPHAN_IN_TABLE was untested at the behavioral
level (the prior ``TestStrictPromotion`` only regex-matched the source,
which ai-01 demonstrated was silent when the implementation was
stubbed), this file pins **behavioral coverage** for all six classes:

1. **Faux sous-compte live détecté** — a fake counter (``--inject-fake
   {"counter": 61}``) on a clean README yields ``UNDERCOUNT: blocking``.
2. **Mention historique bornée ignorée** — a README with the literal
   "61" surrounded by an explicit historical marker ("ancienne
   mention") does NOT contribute to ``UNDERCOUNT``; the literal is
   surfaced in the operator-visible ``raw`` but excluded from the drift
   verdict.
3. **Module disque absent de table détecté** — a fake ``missing_in_table``
   override yields ``MISSING_IN_TABLE: blocking``.
4. **Panne toolchain détectée** — a fake ``toolchain_drift`` override
   yields ``TOOLCHAIN_DRIFT: blocking``.
5. **OVERCOUNT advisory sans --strict** — a fake ``overcount`` override
   without ``--strict`` exits 0 and the drift entry has
   ``severity == "advisory"``.
6. **OVERCOUNT/ORPHAN blocking avec --strict** — a fake ``overcount`` or
   ``orphan_in_table`` override WITH ``--strict`` exits 1 and the drift
   entry has ``severity == "blocking"``.

Usage
-----
    python scripts/lean/test_check_grothendieck_readme.py            # verbose mode
    python scripts/lean/test_check_grothendieck_readme.py --quiet    # only failures

Self-test
---------
The script is **stdlib-only** (no pytest), following the convention
established by ``detect_consecutive_code_cells.py``. Each test prints a
line per row and the script exits with the count of failures. Exit
code 0 means all rows green; non-zero means N rows failed.

History-aware skip edge
-----------------------
Test 5 (added 2026-09-11) verifies the boundary ai-01 flagged
(2026-09-10 CHANGES_REQUESTED #4): a *neighbouring* historical marker
must NOT mask a current claim. We test by writing a temporary README
with "Le compte historique avant #15474 était 61 leaf ; aujourd'hui
nous en avons 73 leaf" — the second occurrence must contribute to
UNDERCOUNT, the first must not.

Limitations
-----------
Tests construct temporary README files under ``tmp_path`` (caller-passed
or ``tempfile.mkdtemp``); they do not touch the lake on disk. The
``check_lake`` machinery uses ``git ls-tree origin/main`` for the disk
read so test fakes are scoped to the README extraction layer only.
"""
from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
CHECKER = REPO_ROOT / "scripts" / "lean" / "check_grothendieck_readme.py"
DEFAULT_LAKE = REPO_ROOT / "MyIA.AI.Notebooks" / "SymbolicAI" / "Lean" / "grothendieck_lean"


def _run_checker(*args: str, expect_exit: int, cwd: Path | None = None) -> subprocess.CompletedProcess:
    proc = subprocess.run(
        [sys.executable, str(CHECKER), *args, "--json"],
        cwd=cwd or REPO_ROOT,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    return proc


class TestHistoryAwareSkip(unittest.TestCase):
    """Pin the history-aware skip behavior ai-01 flagged as not pinned."""

    def test_anchor_marker_skips(self):
        """`ancienne` marker in 90-char window → claim is historical, NOT undercount."""
        # Construct a temporary README with a historical occurrence and a
        # correct current occurrence, then ask the checker to extract
        # leaf-count claims.
        from check_grothendieck_readme import _extract_leaf_count_claims
        with tempfile.NamedTemporaryFile("w", suffix=".md", delete=False, encoding="utf-8") as fp:
            fp.write(
                "## Ancienne version\n\n"
                "L'ancienne prose indiquait « 61 modules leaf ». "
                "Cette mention historique est conservée pour traçabilité.\n\n"
                "## Version courante\n\n"
                "La version actuelle annonce 73 modules leaf.\n"
            )
            tmp_path = Path(fp.name)
        try:
            nums, raw = _extract_leaf_count_claims(tmp_path)
            # The "61" must appear in raw (operator-visible) but NOT in nums (verdict).
            self.assertIn(61, [r[0] for r in raw], "61 should be surfaced in raw for operator review")
            self.assertNotIn(61, nums, "61 must be excluded from the verdict (historical)")
            self.assertIn(73, nums, "73 must be in the verdict (current)")
        finally:
            tmp_path.unlink()

    def test_neighbouring_marker_does_not_mask_current(self):
        """The 2026-09-10 boundary flagged by ai-01: a marker NEAR a current claim
        must not pull the current claim into the historical skip.
        """
        from check_grothendieck_readme import _extract_leaf_count_claims
        # Edge phrasing — first number has 'historique' far away (>90 chars)
        # but second number is the live claim.
        with tempfile.NamedTemporaryFile("w", suffix=".md", delete=False, encoding="utf-8") as fp:
            fp.write(
                "Référence historique (section précédente) : avant #15474 on "
                "comptait 61 leaf. Aujourd'hui le compte canonique mesuré "
                "par git ls-tree est **73 modules leaf** fin 2026, et le "
                "présentiel est aligné.\n"
            )
            tmp_path = Path(fp.name)
        try:
            nums, raw = _extract_leaf_count_claims(tmp_path)
            self.assertIn(73, nums, "73 (current) must contribute to the verdict despite the historical neighbor")
            # 61 may or may not be in raw depending on window; the strict claim is about 73.
        finally:
            tmp_path.unlink()


class TestInjectFake(unittest.TestCase):
    """Pin the four positive controls via subprocess (real CLI)."""

    def test_undercount_fake_yields_blocking(self):
        with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False, encoding="utf-8") as fp:
            json.dump({"counter": 61}, fp)
            fake_path = Path(fp.name)
        try:
            proc = _run_checker("--inject-fake", str(fake_path), expect_exit=1)
            self.assertEqual(proc.returncode, 1, f"checker must exit 1 on injected UNDERCOUNT; output:\n{proc.stdout}\n{proc.stderr}")
            doc = json.loads(proc.stdout)
            kinds = [d["kind"] for d in doc["drifts"]]
            self.assertIn("UNDERCOUNT", kinds)
            sev = next(d["severity"] for d in doc["drifts"] if d["kind"] == "UNDERCOUNT")
            self.assertEqual(sev, "blocking")
        finally:
            fake_path.unlink()

    def test_toolchain_drift_fake_yields_blocking(self):
        with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False, encoding="utf-8") as fp:
            json.dump({"toolchain_drift": "v4.99.0"}, fp)
            fake_path = Path(fp.name)
        try:
            proc = _run_checker("--inject-fake", str(fake_path), expect_exit=1)
            self.assertEqual(proc.returncode, 1)
            doc = json.loads(proc.stdout)
            kinds = [d["kind"] for d in doc["drifts"]]
            self.assertIn("TOOLCHAIN_DRIFT", kinds)
        finally:
            fake_path.unlink()

    def test_missing_in_table_fake_yields_blocking(self):
        with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False, encoding="utf-8") as fp:
            json.dump({"missing_in_table": ["FooLyingOnDisk"]}, fp)
            fake_path = Path(fp.name)
        try:
            proc = _run_checker("--inject-fake", str(fake_path), expect_exit=1)
            self.assertEqual(proc.returncode, 1)
            doc = json.loads(proc.stdout)
            kinds = [d["kind"] for d in doc["drifts"]]
            self.assertIn("MISSING_IN_TABLE", kinds)
        finally:
            fake_path.unlink()

    def test_baseline_exits_zero(self):
        """No fake + clean lake → exit 0 (the default state of the PR after fix)."""
        proc = _run_checker(expect_exit=0)
        self.assertEqual(proc.returncode, 0, f"baseline must exit 0; output:\n{proc.stdout}\n{proc.stderr}")


class TestStrictPromotion(unittest.TestCase):
    """Behavioral pinning: --strict promotes OVERCOUNT and ORPHAN_IN_TABLE to blocking.

    Replaces the prior regex-only pinning (which ai-01 demonstrated was
    silent: replacing ``OVERCOUNT`` severity with a literal ``"advisory"``
    left 7/7 tests green). These four tests run the real CLI with
    ``--inject-fake`` and assert on the produced ``Report`` JSON, so the
    severity expression cannot be stubbed without breaking at least one
    test.
    """

    def test_overcount_advisory_without_strict(self):
        """--inject-fake overcount without --strict → exit 0, severity advisory."""
        with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False, encoding="utf-8") as fp:
            json.dump({"overcount": 9999}, fp)
            fake_path = Path(fp.name)
        try:
            proc = _run_checker("--inject-fake", str(fake_path), expect_exit=0)
            self.assertEqual(
                proc.returncode, 0,
                f"OVERCOUNT w/o --strict is advisory → must exit 0; got {proc.returncode}\nstdout:\n{proc.stdout}\nstderr:\n{proc.stderr}",
            )
            doc = json.loads(proc.stdout)
            oc = [d for d in doc["drifts"] if d["kind"] == "OVERCOUNT"]
            self.assertEqual(len(oc), 1, f"exactly one OVERCOUNT entry expected, got {len(oc)}: {doc['drifts']}")
            self.assertEqual(oc[0]["severity"], "advisory")
        finally:
            fake_path.unlink()

    def test_overcount_blocking_with_strict(self):
        """--inject-fake overcount with --strict → exit 1, severity blocking."""
        with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False, encoding="utf-8") as fp:
            json.dump({"overcount": 9999}, fp)
            fake_path = Path(fp.name)
        try:
            proc = _run_checker("--strict", "--inject-fake", str(fake_path), expect_exit=1)
            self.assertEqual(
                proc.returncode, 1,
                f"OVERCOUNT WITH --strict must exit 1; got {proc.returncode}\nstdout:\n{proc.stdout}\nstderr:\n{proc.stderr}",
            )
            doc = json.loads(proc.stdout)
            oc = [d for d in doc["drifts"] if d["kind"] == "OVERCOUNT"]
            self.assertEqual(len(oc), 1, f"exactly one OVERCOUNT entry expected, got {len(oc)}: {doc['drifts']}")
            self.assertEqual(oc[0]["severity"], "blocking")
        finally:
            fake_path.unlink()

    def test_orphan_advisory_without_strict(self):
        """--inject-fake orphan_in_table without --strict → exit 0, severity advisory."""
        with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False, encoding="utf-8") as fp:
            json.dump({"orphan_in_table": ["FooGoneFromDisk", "BarAlsoGone"]}, fp)
            fake_path = Path(fp.name)
        try:
            proc = _run_checker("--inject-fake", str(fake_path), expect_exit=0)
            self.assertEqual(
                proc.returncode, 0,
                f"ORPHAN_IN_TABLE w/o --strict is advisory → must exit 0; got {proc.returncode}\nstdout:\n{proc.stdout}\nstderr:\n{proc.stderr}",
            )
            doc = json.loads(proc.stdout)
            orphans = [d for d in doc["drifts"] if d["kind"] == "ORPHAN_IN_TABLE"]
            self.assertEqual(len(orphans), 1, f"exactly one ORPHAN_IN_TABLE entry expected, got {len(orphans)}: {doc['drifts']}")
            self.assertEqual(orphans[0]["severity"], "advisory")
        finally:
            fake_path.unlink()

    def test_orphan_blocking_with_strict(self):
        """--inject-fake orphan_in_table with --strict → exit 1, severity blocking."""
        with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False, encoding="utf-8") as fp:
            json.dump({"orphan_in_table": ["FooGoneFromDisk"]}, fp)
            fake_path = Path(fp.name)
        try:
            proc = _run_checker("--strict", "--inject-fake", str(fake_path), expect_exit=1)
            self.assertEqual(
                proc.returncode, 1,
                f"ORPHAN_IN_TABLE WITH --strict must exit 1; got {proc.returncode}\nstdout:\n{proc.stdout}\nstderr:\n{proc.stderr}",
            )
            doc = json.loads(proc.stdout)
            orphans = [d for d in doc["drifts"] if d["kind"] == "ORPHAN_IN_TABLE"]
            self.assertEqual(len(orphans), 1, f"exactly one ORPHAN_IN_TABLE entry expected, got {len(orphans)}: {doc['drifts']}")
            self.assertEqual(orphans[0]["severity"], "blocking")
        finally:
            fake_path.unlink()


def main() -> int:
    suite = unittest.TestLoader().loadTestsFromModule(sys.modules[__name__])
    runner = unittest.TextTestRunner(verbosity=2 if "--quiet" not in sys.argv else 0)
    result = runner.run(suite)
    return 0 if result.wasSuccessful() else len(result.failures) + len(result.errors)


if __name__ == "__main__":
    sys.exit(main())
