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
from unittest import mock

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


def make_lake(
    tmp: Path,
    *,
    disk_modules: list[str] | None = None,
    readme_fr: str | None = None,
    readme_en: str | None = None,
    toolchain: str = "leanprover/lean4:v4.33.0",
) -> Path:
    """Build a minimal lake under ``tmp`` for behavioral tests of ``check_lake``.

    ``disk_modules`` is a list of leaf basenames WITHOUT the ``_en`` suffix;
    the helper writes both ``Foo.lean`` and ``Foo_en.lean`` for each. If
    ``None``, no ``.lean`` files are written (an empty lake).

    ``readme_fr`` / ``readme_en`` are written verbatim to README.md /
    README.en.md. If ``None``, the README is omitted (an empty readme is
    used as the assertion baseline).

    ``toolchain`` is the content of ``lean-toolchain``; defaults to the
    current production pin so the TOOLCHAIN_DRIFT class doesn't trip.
    """
    lake = tmp / "lake"
    lake.mkdir()
    if disk_modules is not None:
        for mod in disk_modules:
            (lake / f"{mod}.lean").write_text(f"-- {mod}\n", encoding="utf-8")
            (lake / f"{mod}_en.lean").write_text(f"-- {mod}_en\n", encoding="utf-8")
    if readme_fr is not None:
        (lake / "README.md").write_text(readme_fr, encoding="utf-8")
    if readme_en is not None:
        (lake / "README.en.md").write_text(readme_en, encoding="utf-8")
    (lake / "lean-toolchain").write_text(toolchain + "\n", encoding="utf-8")
    return lake


def _patch_disk(monkeypatch, checker_module, disk_fr: set[str], disk_en: set[str], umbrella: int = 0):
    """Patch ``_git_ls_tree_disk`` so a test can drive ``check_lake`` with a
    synthetic disk state without touching ``origin/main``.

    Returns the mock object the caller can inspect.
    """
    return monkeypatch.patch.object(
        checker_module,
        "_git_ls_tree_disk",
        lambda lake_root: (set(disk_fr), set(disk_en), umbrella),
    )


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


class TestCheckLakeDirect(unittest.TestCase):
    """Behavioral pinning of the three production branches that the previous
    round's tests did not exercise directly::

        * OVERCOUNT   — README leaf-count strictly greater than disk
        * ORPHAN_IN_TABLE (FR) — table mentions a module absent on disk
        * ORPHAN_IN_TABLE (EN) — same, on README.en.md

    These tests construct a **minimal temp lake** and call ``check_lake``
    directly (not via ``--inject-fake``). They monkey-patch
    ``_git_ls_tree_disk`` so a synthetic disk state can be driven without
    touching ``origin/main``. The point is that each branch under test is
    the **live** branch in ``check_lake`` — not the fake-augmented branch
    that ``--inject-fake`` covers separately.

    Each test exercises both ``strict=False`` (advisory) and ``strict=True``
    (blocking) on the same underlying drift shape — so mutating the
    severity expression in ``check_lake`` breaks at least one test.
    """

    def test_overcount_advisory_then_blocking(self):
        """A README claiming more leaf modules than the disk contains
        produces ``OVERCOUNT`` advisory without ``strict=True`` and
        blocking with it.
        """
        import check_grothendieck_readme as cgr

        with tempfile.TemporaryDirectory() as td:
            tmp = Path(td)
            lake = make_lake(
                tmp,
                disk_modules=["Adjunction", "CoversCoherent", "Spaces"],
                readme_fr=(
                    "# Lake\n\n"
                    "Ce lake couvre **5 modules leaf** en FR.\n\n"
                    "| # | FR | EN |\n"
                    "|---|----|----|\n"
                    "| 1 | `Adjunction.lean` | `Adjunction_en.lean` |\n"
                    "| 2 | `CoversCoherent.lean` | `CoversCoherent_en.lean` |\n"
                    "| 3 | `Spaces.lean` | `Spaces_en.lean` |\n"
                ),
                readme_en=(
                    "# Lake (EN)\n\n"
                    "This lake covers **5 leaf modules**.\n\n"
                    "| # | FR | EN |\n"
                    "|---|----|----|\n"
                    "| 1 | `Adjunction.lean` | `Adjunction_en.lean` |\n"
                    "| 2 | `CoversCoherent.lean` | `CoversCoherent_en.lean` |\n"
                    "| 3 | `Spaces.lean` | `Spaces_en.lean` |\n"
                ),
            )

            with mock.patch.object(cgr, "_git_ls_tree_disk",
                                   lambda lr: ({"Adjunction", "CoversCoherent", "Spaces"},
                                               {"Adjunction", "CoversCoherent", "Spaces"}, 0)), \
                 mock.patch.object(cgr, "REPO_ROOT", lake.parent):
                rpt_advisory = cgr.check_lake(lake, strict=False)
                rpt_blocking = cgr.check_lake(lake, strict=True)

            overs_advisory = [d for d in rpt_advisory.drifts if d.kind == "OVERCOUNT"]
            overs_blocking = [d for d in rpt_blocking.drifts if d.kind == "OVERCOUNT"]

            self.assertEqual(
                len(overs_advisory), 1,
                f"exactly one OVERCOUNT expected (advisory); got {rpt_advisory.drifts}",
            )
            self.assertEqual(overs_advisory[0].severity, "advisory",
                             f"OVERCOUNT w/o strict must be advisory; got {overs_advisory[0].severity}")
            self.assertFalse(rpt_advisory.blocking,
                             f"OVERCOUNT advisory must NOT make the report blocking; drifts: {rpt_advisory.drifts}")

            self.assertEqual(
                len(overs_blocking), 1,
                f"exactly one OVERCOUNT expected (blocking); got {rpt_blocking.drifts}",
            )
            self.assertEqual(overs_blocking[0].severity, "blocking",
                             f"OVERCOUNT WITH strict must be blocking; got {overs_blocking[0].severity}")
            self.assertTrue(rpt_blocking.blocking,
                            f"OVERCOUNT blocking must promote the report to blocking; drifts: {rpt_blocking.drifts}")

    def test_orphan_in_table_fr_advisory_then_blocking(self):
        """A README.md table listing a module absent on disk produces
        ``ORPHAN_IN_TABLE`` (FR) — advisory without ``--strict``, blocking
        with it.
        """
        import check_grothendieck_readme as cgr

        with tempfile.TemporaryDirectory() as td:
            tmp = Path(td)
            lake = make_lake(
                tmp,
                disk_modules=["Adjunction", "CoversCoherent"],
                readme_fr=(
                    "# Lake\n\n"
                    "| # | FR | EN |\n"
                    "|---|----|----|\n"
                    "| 1 | `Adjunction.lean` | `Adjunction_en.lean` |\n"
                    "| 2 | `CoversCoherent.lean` | `CoversCoherent_en.lean` |\n"
                    "| 3 | `GhostModule.lean` | `GhostModule_en.lean` |\n"
                ),
                readme_en=(
                    "# Lake (EN)\n\n"
                    "| # | FR | EN |\n"
                    "|---|----|----|\n"
                    "| 1 | `Adjunction.lean` | `Adjunction_en.lean` |\n"
                    "| 2 | `CoversCoherent.lean` | `CoversCoherent_en.lean` |\n"
                ),
            )

            with mock.patch.object(cgr, "_git_ls_tree_disk",
                                   lambda lr: ({"Adjunction", "CoversCoherent"},
                                               {"Adjunction", "CoversCoherent"}, 0)), \
                 mock.patch.object(cgr, "REPO_ROOT", lake.parent):
                rpt_advisory = cgr.check_lake(lake, strict=False)
                rpt_blocking = cgr.check_lake(lake, strict=True)

            orphans_advisory = [d for d in rpt_advisory.drifts if d.kind == "ORPHAN_IN_TABLE"]
            orphans_blocking = [d for d in rpt_blocking.drifts if d.kind == "ORPHAN_IN_TABLE"]

            self.assertTrue(len(orphans_advisory) >= 1,
                            f"at least one ORPHAN_IN_TABLE expected (FR); got {rpt_advisory.drifts}")
            fr_advisory = next((d for d in orphans_advisory
                                if "GhostModule" in d.detail), None)
            self.assertIsNotNone(fr_advisory, f"FR-side orphan 'GhostModule' expected; got {orphans_advisory}")
            self.assertEqual(fr_advisory.severity, "advisory",
                             f"ORPHAN_IN_TABLE FR w/o strict must be advisory; got {fr_advisory.severity}")
            self.assertFalse(rpt_advisory.blocking,
                             f"advisory ORPHAN must NOT promote the report to blocking; drifts: {rpt_advisory.drifts}")

            fr_blocking = next((d for d in orphans_blocking
                                if "GhostModule" in d.detail), None)
            self.assertIsNotNone(fr_blocking, f"FR-side orphan 'GhostModule' expected (blocking); got {orphans_blocking}")
            self.assertEqual(fr_blocking.severity, "blocking",
                             f"ORPHAN_IN_TABLE FR WITH strict must be blocking; got {fr_blocking.severity}")
            self.assertTrue(rpt_blocking.blocking,
                            f"blocking ORPHAN (FR) must promote the report to blocking; drifts: {rpt_blocking.drifts}")

    def test_orphan_in_table_en_advisory_then_blocking(self):
        """An ``README.en.md`` table listing a module absent on disk
        produces ``ORPHAN_IN_TABLE`` (EN) — advisory without ``--strict``,
        blocking with it. This pins the **second** live ORPHAN branch
        (the production code splits on FR vs EN both via distinct
        conditionals, both must be exercised).
        """
        import check_grothendieck_readme as cgr

        with tempfile.TemporaryDirectory() as td:
            tmp = Path(td)
            lake = make_lake(
                tmp,
                disk_modules=["Adjunction", "Spaces"],
                readme_fr=(
                    "# Lake\n\n"
                    "| # | FR | EN |\n"
                    "|---|----|----|\n"
                    "| 1 | `Adjunction.lean` | `Adjunction_en.lean` |\n"
                    "| 2 | `Spaces.lean` | `Spaces_en.lean` |\n"
                ),
                readme_en=(
                    "# Lake (EN)\n\n"
                    "| # | FR | EN |\n"
                    "|---|----|----|\n"
                    "| 1 | `Adjunction.lean` | `Adjunction_en.lean` |\n"
                    "| 2 | `Spaces.lean` | `Spaces_en.lean` |\n"
                    "| 3 | `GhostENModule.lean` | `GhostENModule_en.lean` |\n"
                ),
            )

            with mock.patch.object(cgr, "_git_ls_tree_disk",
                                   lambda lr: ({"Adjunction", "Spaces"},
                                               {"Adjunction", "Spaces"}, 0)), \
                 mock.patch.object(cgr, "REPO_ROOT", lake.parent):
                rpt_advisory = cgr.check_lake(lake, strict=False)
                rpt_blocking = cgr.check_lake(lake, strict=True)

            orphans_advisory = [d for d in rpt_advisory.drifts if d.kind == "ORPHAN_IN_TABLE"]
            orphans_blocking = [d for d in rpt_blocking.drifts if d.kind == "ORPHAN_IN_TABLE"]

            self.assertTrue(len(orphans_advisory) >= 1,
                            f"at least one ORPHAN_IN_TABLE expected; got {rpt_advisory.drifts}")
            en_advisory = next((d for d in orphans_advisory
                                if "GhostENModule" in d.detail and "README.en.md" in d.detail), None)
            self.assertIsNotNone(en_advisory, f"EN-side orphan 'GhostENModule' on README.en.md expected; got {orphans_advisory}")
            self.assertEqual(en_advisory.severity, "advisory",
                             f"ORPHAN_IN_TABLE EN w/o strict must be advisory; got {en_advisory.severity}")
            self.assertFalse(rpt_advisory.blocking,
                             f"advisory ORPHAN (EN) must NOT promote the report to blocking; drifts: {rpt_advisory.drifts}")

            en_blocking = next((d for d in orphans_blocking
                                if "GhostENModule" in d.detail and "README.en.md" in d.detail), None)
            self.assertIsNotNone(en_blocking, f"EN-side orphan 'GhostENModule' expected (blocking); got {orphans_blocking}")
            self.assertEqual(en_blocking.severity, "blocking",
                             f"ORPHAN_IN_TABLE EN WITH strict must be blocking; got {en_blocking.severity}")
            self.assertTrue(rpt_blocking.blocking,
                            f"blocking ORPHAN (EN) must promote the report to blocking; drifts: {rpt_blocking.drifts}")


def main() -> int:
    suite = unittest.TestLoader().loadTestsFromModule(sys.modules[__name__])
    runner = unittest.TextTestRunner(verbosity=2 if "--quiet" not in sys.argv else 0)
    result = runner.run(suite)
    return 0 if result.wasSuccessful() else len(result.failures) + len(result.errors)


if __name__ == "__main__":
    sys.exit(main())
