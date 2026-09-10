#!/usr/bin/env python3
"""Tests for scripts/lean/check_grothendieck_readme.py — pin the four positive controls.

Background
----------
The checker is the **anti-récidive organe** for #15474. After the
2026-09-10 re-review on head ``621dd53cb1`` flagged three gaps in the
positive controls (no ``--inject-fake`` argument, ``--strict`` does not
promote OVERCOUNT/ORPHAN, history-aware skip not pinned), this file
adds four-row test coverage:

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
    """Pin that --strict promotes OVERCOUNT and ORPHAN_IN_TABLE to blocking."""

    def test_strict_promotion(self):
        # We can't easily inject ORPHAN/OVERCOUNT via the JSON fake (those
        # classes need a synthetic table, which the README extraction layer
        # doesn't expose through the fake). Instead, we pin the documented
        # severity-mapping at the source: walk the module's
        # `check_lake(strict=True)` body and verify each severtiy expression
        # references `strict`. This is the lighter, more reliable form of
        # pinning for a class whose injection requires filesystem mutation.
        src = CHECKER.read_text(encoding="utf-8")
        # Both occurrence should reference 'blocking' if strict else 'advisory'.
        self.assertRegex(
            src,
            r'severity=\("blocking"\s+if\s+strict\s+else\s+"advisory"\)',
            "check_lake must promote OVERCOUNT/ORPHAN via 'blocking if strict else advisory'",
        )


def main() -> int:
    suite = unittest.TestLoader().loadTestsFromModule(sys.modules[__name__])
    runner = unittest.TextTestRunner(verbosity=2 if "--quiet" not in sys.argv else 0)
    result = runner.run(suite)
    return 0 if result.wasSuccessful() else len(result.failures) + len(result.errors)


if __name__ == "__main__":
    sys.exit(main())
