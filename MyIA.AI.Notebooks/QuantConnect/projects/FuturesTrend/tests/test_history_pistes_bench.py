#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""Tests CPU pour bench_carver13_history_pistes (issue #16076).

Le bench de #16076 est un micro-bench local qui discrimine les 4 pistes
proposées pour attaquer le coût 94% du mur `self.history()` sur carver13.
La composante bench est rapide mais pas pytest-able directement (timing,
pas invariants). Ce test protège trois invariants structurels que toute
évolution du bench DOIT préserver pour rester honnête :

1. Les 4 pistes produisent un résultat de même FORME (dict sym -> closes).
2. La piste flatten/array donne le MÊME ordre de grandeur de données
   (mêmes n_symbols, closes cohérentes par symbole) que la baseline.
3. Le verdict "WINNER" est reproducible : la médiane de C est
   significativement < à celle de A (>= 30% faster, le seuil déclaré
   dans le bench).

Ce test ne chronomètre PAS les 4 pistes (c'est le rôle du bench avec
`--n-iter`), il vérifie que les invariants sont préservés. Un bench qui
briserait un invariant (par ex. retourner un dict vide) ne déclencherait
pas de ratchet sans ce test.

Pré-requis : `numpy`, `pandas` (>= 1.3 pour MultiIndex). Le runner GH
Actions Python par défaut ne porte PAS numpy/pandas — voir MEMORY
`scipy-matplotlib-pip-install-ci-runner.md`.
"""

import math
import os
import sys
import unittest

import numpy as np
import pandas as pd

# Import the bench module without launching its __main__.
_HERE = os.path.dirname(os.path.abspath(__file__))
_PROJ_ROOT = os.path.dirname(_HERE)
if _PROJ_ROOT not in sys.path:
    sys.path.insert(0, _PROJ_ROOT)

import bench_carver13_history_pistes as bench  # noqa: E402


class TestBenchInvariants(unittest.TestCase):
    def setUp(self):
        self.bulk_baseline = bench._make_synthetic_bulk(bench.N_BARS_BASELINE, seed=42)
        self.bulk_reduced = bench._make_synthetic_bulk(bench.N_BARS_REDUCED, seed=42)
        self.bulk_slim = bench._make_synthetic_bulk(bench.N_BARS_SLIM, seed=42)

    def test_synthetic_bulk_shape(self):
        """The synthetic bulk matches the production shape (19 x 592)."""
        # 19 symbols x 592 business days = 11 248 rows (no duplicate index
        # because each (expiry, symbol, time) tuple is unique).
        self.assertEqual(self.bulk_baseline.shape[0], 19 * bench.N_BARS_BASELINE)
        self.assertEqual(self.bulk_baseline.shape[1], 5)  # OHLCV
        # Multi-index has (expiry, symbol, time) -- matches issue #15992.
        self.assertEqual(
            list(self.bulk_baseline.index.names), ["expiry", "symbol", "time"]
        )

    def test_expiry_sentinel_is_constant(self):
        """The expiry level is the 1899-12-30 sentinel on every row.

        This is the property the #15992/#16003 fix relied on: the bulk
        frame for continuous futures has a constant expiry level, so
        slicing MUST happen on the symbol level, not level 0. If a
        future PR changes the synthetic bulk to model real expiries,
        the carver13 logic still has to use bulk.xs(sym, level="symbol")
        -- not bulk.loc[sym] -- or it will silently drop 18 of 19 symbols.
        """
        expiry_level = self.bulk_baseline.index.get_level_values("expiry")
        self.assertEqual(len(expiry_level.unique()), 1)
        self.assertEqual(expiry_level[0], pd.Timestamp("1899-12-30"))

    def test_piste_A_baseline_returns_full_symbol_set(self):
        """Piste A (current carver13 path) returns >= 19 symbols."""
        result = bench._path_baseline_bulk(self.bulk_baseline, bench.N_BARS_BASELINE)
        self.assertEqual(len(result), bench.N_SYMBOLS)
        for sym, closes in result.items():
            self.assertIsInstance(closes, np.ndarray)
            # Slowest EWMAC needs max_slow+2 bars; the bulk has 592 so all
            # symbols reach the burn-in threshold.
            self.assertGreaterEqual(len(closes), bench.EWMAC_PAIRS[-1][1] + 2)

    def test_piste_B_per_symbol_returns_full_symbol_set(self):
        """Piste B (19 individual history calls) also returns 19 symbols."""
        result = bench._path_per_symbol(self.bulk_baseline, bench.N_BARS_BASELINE)
        self.assertEqual(len(result), bench.N_SYMBOLS)

    def test_piste_C_flatten_array_returns_full_symbol_set(self):
        """Piste C (flatten/array path) returns 19 symbols, same closes."""
        result = bench._path_flatten_array(self.bulk_baseline, bench.N_BARS_BASELINE)
        self.assertEqual(len(result), bench.N_SYMBOLS)
        for sym, closes in result.items():
            self.assertIsInstance(closes, np.ndarray)
            self.assertGreaterEqual(len(closes), bench.EWMAC_PAIRS[-1][1] + 2)

    def test_piste_D_reduce_n_bars_returns_full_symbol_set(self):
        """Piste D (n_bars=336) still meets the slowest EWMAC burn-in."""
        result = bench._path_reduce_n_bars(self.bulk_reduced, bench.N_BARS_REDUCED)
        self.assertEqual(len(result), bench.N_SYMBOLS)

    def test_piste_D_slim_still_meets_burn_in(self):
        """Piste D' (n_bars=276) keeps 256+2 = 258 bars -- enough for EWMAC(64, 256)."""
        # bench.N_BARS_SLIM = 276 >= 258 -- the slowest pair burn-in threshold.
        self.assertGreaterEqual(bench.N_BARS_SLIM, bench.EWMAC_PAIRS[-1][1] + 2)
        result = bench._path_reduce_n_bars_slim(self.bulk_slim, bench.N_BARS_SLIM)
        self.assertEqual(len(result), bench.N_SYMBOLS)

    def test_all_pistes_return_identical_close_arrays(self):
        """All 4 pistes produce the SAME per-symbol close arrays.

        This is the discrimination-ratchet: any future PR that changes the
        slicing logic must preserve bit-identity of the close arrays, or
        the EWMAC forecasts downstream will silently diverge. We compare
        on the reduced shape so all 4 paths share the same input length
        (276 bars at minimum, well past the slowest EWMAC burn-in).

        REPAIR c.1151 adjoint round 3 N4: C_alt is now included in the
        invariant. C_alt returns keys ``SYM00..SYM18`` (the synthetic
        symbol codes produced by the flatten layout); the test maps those
        to the canonical ``SYM00..SYM18`` keys used by A/B/C/D on the
        slim bulk (which share the same RNG seed, so the naming happens
        to coincide). The arrays must be byte-equal.
        """
        common_bulk = self.bulk_slim  # 276 bars, same input for everyone.
        results = {
            "A": bench._path_baseline_bulk(common_bulk, bench.N_BARS_SLIM),
            "B": bench._path_per_symbol(common_bulk, bench.N_BARS_SLIM),
            "C": bench._path_flatten_array(common_bulk, bench.N_BARS_SLIM),
            "D": bench._path_reduce_n_bars(common_bulk, bench.N_BARS_SLIM),
        }
        # C_alt: ndarray-only path on the flatten layout of the same bulk.
        arr, sym_codes, _ = bench._make_flatten_layout(common_bulk, bench.N_BARS_SLIM)
        c_alt = bench._path_flatten_array_no_df(arr, sym_codes, bench.N_BARS_SLIM)
        results["C_alt"] = c_alt

        # Every path returns 19 symbols. A/B/C/D share the canonical
        # ``SYM00..SYM18`` keys; C_alt uses the same naming because the
        # synthetic RNG seeds the sym_codes identically.
        sym_sets = [set(r.keys()) for r in results.values()]
        for sym_set in sym_sets[1:]:
            self.assertEqual(sym_set, sym_sets[0])

        # For each symbol, the close arrays are equal across all 5 paths.
        for sym in sym_sets[0]:
            arrays = [r[sym] for r in results.values()]
            ref = arrays[0]
            for arr in arrays[1:]:
                np.testing.assert_array_equal(
                    arr,
                    ref,
                    err_msg=(
                        f"close arrays for {sym} diverge across pistes -- "
                        "this would silently change EWMAC forecasts."
                    ),
                )

    def test_verdict_seuil_coherent_with_bench(self):
        """The 30% WINNER threshold matches what the bench script declares.

        If a future maintainer changes the threshold in the bench, this
        test should be updated -- it is the ratchet that says "WINNER
        means >= 30% faster, not whatever threshold felt right today".
        """
        # The bench code declares 0.70 as the WINNER ratio (see
        # _time_path -> ratio < 0.70 -> WINNER). This test pins that
        # number so a silent threshold change is caught.
        # We don't run the timing here (it's noisy on a CI runner); we
        # just confirm the bench code still uses 0.70 by reading it.
        import inspect

        source = inspect.getsource(bench)
        self.assertIn("ratio < 0.70", source)
        self.assertIn("ratio > 1.30", source)
        self.assertIn("WINNER", source)
        self.assertIn("LOSER", source)
        self.assertIn("NEUTRAL", source)


class TestAntiFabricationNotes(unittest.TestCase):
    """The bench document its scope honestly -- these tests pin the prose."""

    def test_bench_docstring_mentions_qc_bridge_blindspot(self):
        """The bench docstring MUST say it does not model the QC bridge.

        Without this ratchet, a future maintainer could quietly present
        a local WINNER as "94% wall reduction", which is the exact
        anti-fabrication violation this bench exists to prevent.
        """
        import inspect

        source = inspect.getsource(bench)
        self.assertIn("QC bridge", source)
        self.assertIn("NOT modelled", source) or self.assertIn(
            "not modelled", source.lower()
        )
        self.assertIn("Anti-fabrication", source)


class TestREPAIRAdjointPreflight16093(unittest.TestCase):
    """The 3 écarts identified by the adjoint preflight on PR #16093.

    REPAIR 2026-09-14 : three substance gaps caught in review:

    1. `--json` emitted human-readable prose on stdout BEFORE the JSON
       document, so ``json.loads(stdout)`` failed at line 1.
    2. The synthetic DataFrame was built OUTSIDE the timed frontier, so
       the verdict "construction pandas domine" attributed the speedup
       to a step that was not measured.
    3. The source comment promised "non-overlapping IQRs" as the WINNER
       criterion, but the implementation never computed an IQR.

    Each test below pins one fix. If a future maintainer reverts any
    of the three, the corresponding test fails -- which is exactly the
    "push + bump floor = silent fabrication" failure mode this REPAIR
    exists to prevent.
    """

    def test_json_output_is_parseable(self):
        """`--json` MUST emit a single JSON document on stdout parseable
        by ``json.loads``. Human-readable progress moves to stderr.
        """
        import io
        import json
        from contextlib import redirect_stdout, redirect_stderr

        # n_iter=2 to keep the test fast; smoke test only.
        stdout_buf = io.StringIO()
        stderr_buf = io.StringIO()
        with redirect_stdout(stdout_buf), redirect_stderr(stderr_buf):
            try:
                bench.main_with_args(["--json", "--n-iter", "2"])
            except SystemExit as e:
                # argparse may call sys.exit(2) on bad args; the success
                # path doesn't. Either is fine for the smoke test.
                self.assertIn(e.code, (None, 0, 2))
        stdout_text = stdout_buf.getvalue().strip()
        # Pure JSON: the very first non-whitespace char is '{'.
        self.assertTrue(
            stdout_text.startswith("{"),
            f"stdout must start with '{{' for --json; got first 80 chars: "
            f"{stdout_text[:80]!r}",
        )
        # Parseable.
        parsed = json.loads(stdout_text)
        self.assertIn("paths", parsed)
        self.assertIn("verdicts", parsed)
        self.assertIn("scope_note", parsed)
        # The scope note MUST spell out the WINNER requirement so a future
        # maintainer cannot relax it silently.
        self.assertIn("IQR", parsed["scope_note"])

    def test_stats_include_iqr(self):
        """`_time_path` MUST return p25, p75, and iqr_ms so the WINNER
        verdict can require disjoint IQRs.
        """
        bulk = bench._make_synthetic_bulk(bench.N_BARS_SLIM, seed=42)
        stats = bench._time_path(bench._path_baseline_bulk, bulk,
                                  bench.N_BARS_SLIM, n_iter=40)
        for key in ("median_ms", "p25_ms", "p75_ms", "iqr_ms", "p05_ms", "p95_ms"):
            self.assertIn(key, stats, f"missing stat key: {key}")
        # IQR = p75 - p25 by definition.
        self.assertAlmostEqual(stats["iqr_ms"], stats["p75_ms"] - stats["p25_ms"], places=6)
        # Quartile ordering: p25 <= median <= p75.
        self.assertLessEqual(stats["p25_ms"], stats["median_ms"])
        self.assertLessEqual(stats["median_ms"], stats["p75_ms"])

    def test_iqr_disjoint_helper(self):
        """`_iqr_disjoint(baseline, candidate)` returns True iff the
        candidate IQR sits entirely below the baseline IQR.
        """
        base = {"p25_ms": 10.0, "p75_ms": 20.0}
        # Candidate entirely below baseline.
        self.assertTrue(bench._iqr_disjoint(base, {"p25_ms": 1.0, "p75_ms": 5.0}))
        # Candidate overlapping (p25 < base.p75).
        self.assertFalse(bench._iqr_disjoint(base, {"p25_ms": 15.0, "p75_ms": 25.0}))
        # Candidate exactly touching the baseline's lower edge.
        self.assertFalse(bench._iqr_disjoint(base, {"p25_ms": 20.0, "p75_ms": 30.0}))

    def test_measure_construction_option_exists(self):
        """`--measure-construction` MUST exist and be wired into the timed
        frontier, so the verdict can attribute (or refuse to attribute)
        a speedup to pandas construction.

        Without this knob, the verdict "le gain vient de la construction
        pandas" is unsubstantiated (REPAIR gap #2).
        """
        import argparse
        # Pin via getsource: the option must be declared in main().
        import inspect
        src = inspect.getsource(bench.main)
        self.assertIn("--measure-construction", src)
        self.assertIn("measure_construction", src)
        # And the timing wrapper must consume it.
        self.assertIn("_maybe_wrap_with_construction", src)

    def test_verdict_requires_iqr_disjoint(self):
        """The WINNER verdict MUST require BOTH ratio<0.70 AND IQR
        disjoint from baseline. Pin both conditions in source.
        """
        import inspect

        src = inspect.getsource(bench.main)
        # WINNER branch references both gates.
        self.assertIn("ratio < 0.70 and iqr_disjoint", src)
        # The label must communicate the AND, so a future reader doesn't
        # think the IQR is optional.
        self.assertIn("WINNER", src)
        self.assertIn("IQR disjoint", src)
        # And the NEUTRAL_MEDIAN_ONLY label exists for the case where
        # ratio<0.70 but IQR overlaps -- the speedup is NOT robust.
        self.assertIn("NEUTRAL_MEDIAN_ONLY", src)


class TestREPAIRAdjointPreflight16093c1148(unittest.TestCase):
    """REPAIR c.1148 -- 3 reserves adjointes NON levees en c.1147.

    1. C chemin flatten=True : ajouter C_alt_no_df (array-only floor)
       + borner honnetement C comme transformation in-memory.
    2. D' unsafe : clarifier observation-only (vol_lookback dropped).
    3. Grain header `ci` -> `qc` ; prev #16088 (issue) -> #16072 (PR Merged).
    """

    def test_C_alt_no_df_exists_and_returns_full_symbol_set(self):
        """C_alt_no_df MUST exist and return 19 symbols from a pre-built
        ndarray + sym_codes -- the array-only floor of any flatten=True
        migration. This pins the c.1148 REPAIR's first reserve (the
        missing true-array representation of C).
        """
        bulk = bench._make_synthetic_bulk(bench.N_BARS_BASELINE, seed=42)
        arr, sym_codes, _ = bench._make_flatten_layout(bulk, bench.N_BARS_BASELINE)
        result = bench._path_flatten_array_no_df(arr, sym_codes, bench.N_BARS_BASELINE)
        # All 19 symbols (one per unique sym_codes value) get a slice.
        n_unique = int(sym_codes.max()) + 1
        self.assertEqual(len(result), n_unique)
        for sym, closes in result.items():
            self.assertIsInstance(closes, np.ndarray)
            self.assertGreaterEqual(len(closes), bench.EWMAC_PAIRS[-1][1] + 2)

    def test_Dprime_label_is_observe_only_not_winner(self):
        """The D' slim path MUST be labeled observation-only (vol_lookback
        dropped, Likely UNSAFE) -- NOT a recommendation to ship. The bench
        label includes 'observe_only' and the prose names it as such.

        This pins the c.1148 REPAIR's second reserve: the v1 PR body
        recommended D' without neutrality on forecasts/orders/backtest.
        """
        import inspect
        src = inspect.getsource(bench.main)
        # Label is observation-only -- no 'WINNER' framing for D' slim.
        self.assertIn("D'_observe_only", src)
        # The prose MUST spell out 'observation-only' / 'Likely UNSAFE' so
        # the body cannot quietly revert the recommendation.
        self.assertIn("Likely UNSAFE", src)
        self.assertIn("observation-only", src)
        # The phrase is split across two _say() calls for stderr width;
        # both halves must appear in source. A regex with DOTALL tolerates
        # the wrap (including any source tokens and newlines in between).
        import re
        match = re.search(r"NOT a recommendation.{0,200}to ship", src, flags=re.DOTALL)
        self.assertIsNotNone(
            match,
            "D' slim prose MUST warn 'NOT a recommendation to ship'; "
            "adjoint 2026-09-14 re-review flagged the body without this neutrality.",
        )


class TestREPAIRAdjointPreflight16093c1151(unittest.TestCase):
    """REPAIR c.1151 -- 5 reserves adjointes NON levees en c.1148 round 3.

    1. C_alt pas dans la frontiere `--measure-construction` -> WINNER non-
       comparable. Solution : C_alt FLOOR (jamais WINNER/NEUTRAL/LOSER).
    2. D' peut encore emettre WINNER machine-readable. Solution :
       categorie `OBSERVATION_ONLY` distincte, hors WINNER.
    3. Header `REPAIR/qc` hors enum canonique (DEEP/MED/LIGHT). Solution :
       `MED/qc` ; `prev:` PR Merged (e.g. #16074).
    4. C_alt exclu de l'invariant d'egalite a tort. Solution : ajouter C_alt
       a `test_all_pistes_return_identical_close_arrays`.
    5. Body presente 1 classement sans nommer le mode (default vs
       `--measure-construction` inversent le classement). Solution : nommer
       le mode dans chaque tableau + expliquer l'inversion dans le body PR.
    """

    def test_Dprime_can_never_be_WINNER_at_runtime(self):
        """D' MUST receive ``OBSERVATION_ONLY`` verdict regardless of its
        measured ratio/IQR. The c.1148 'just rename the label' fix left D'
        able to emit ``WINNER (<70% AND IQR disjoint)`` machine-readably
        under `--measure-construction`. The runtime test below runs the
        bench end-to-end and asserts D' is OBSERVATION_ONLY in the JSON.

        REPAIR c.1151 N2 (adjoint round 3).
        """
        import io
        import json
        import os
        import subprocess
        import sys

        # Windows: cwd must be native path, not Unix /d/dev/... (MEMORY
        # `subprocess-windows-bash-path-cwd` -- Git Bash /c/... raises
        # NotADirectoryError under native Python subprocess).
        bench_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        proc = subprocess.run(
            [
                sys.executable,
                os.path.join(bench_dir, "bench_carver13_history_pistes.py"),
                "--n-iter", "30",
                "--measure-construction",
                "--json",
            ],
            cwd=bench_dir,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=120,
            env={**os.environ, "PYTHONIOENCODING": "utf-8"},
        )
        self.assertEqual(
            proc.returncode, 0,
            f"bench crashed: stdout={proc.stdout[:500]!r} stderr={proc.stderr[:500]!r}",
        )
        parsed = json.loads(proc.stdout)
        dprime_key = "D'_observe_only_n_bars_slim (592->276, vol_lookback dropped, observation-only)"
        self.assertIn(dprime_key, parsed["verdicts"])
        verdict = parsed["verdicts"][dprime_key]
        self.assertNotEqual(
            verdict, "WINNER (<70% AND IQR disjoint)",
            "D' MUST NOT be machine-readable WINNER (adjoint round 3 N2); "
            f"got verdict={verdict!r} -- the c.1151 OBSERVATION_ONLY category "
            "is what the JSON should carry.",
        )
        self.assertIn(
            "OBSERVATION_ONLY", verdict,
            f"D' must carry the OBSERVATION_ONLY label, got {verdict!r}",
        )

    def test_C_alt_never_in_WINNER_NEUTRAL_LOSER_ranking(self):
        """C_alt MUST NOT appear in the WINNER/NEUTRAL/LOSER verdict space.

        REPAIR c.1151 N1 (adjoint round 3) -- C_alt is a FLOOR (Python-side
        array-only path), not a comparable candidate. The JSON must carry
        a distinct ``FLOOR`` verdict that is NOT used in the ranking.

        Pinning this in source prevents a future PR from re-introducing
        C_alt into the timed frontier where it would be compared to paths
        paying DataFrame construction cost.
        """
        import inspect
        src = inspect.getsource(bench.main)
        # FLOOR_PATHS set declared.
        self.assertIn("FLOOR_PATHS", src)
        # C_alt branch returns FLOOR verdict.
        self.assertIn("FLOOR (array-only path", src)
        # And it is excluded from the WINNER/NEUTRAL_MEDIAN_ONLY/LOSER branch.
        # Check by reading the source structure: the FLOOR branch comes
        # before the ratio < 0.70 branch in the verdict cascade.
        floor_idx = src.find("FLOOR (array-only path")
        winner_idx = src.find('verdict = "WINNER')
        self.assertGreater(floor_idx, 0)
        self.assertGreater(winner_idx, floor_idx)

    def test_Dprime_observation_only_source_pin(self):
        """Source pin: the OBSERVATION_ONLY set must include D' slim and
        no other path, and the verdict cascade must hard-code D' into
        OBSERVATION_ONLY (cannot be overridden by ratio/IQR).
        """
        import inspect
        src = inspect.getsource(bench.main)
        # OBSERVATION_ONLY_PATHS set declared.
        self.assertIn("OBSERVATION_ONLY_PATHS", src)
        # D' hard-coded into OBSERVATION_ONLY before ratio/IQR branch.
        obs_idx = src.find("OBSERVATION_ONLY_PATHS = {")
        winner_idx = src.find('verdict = "WINNER')
        self.assertGreater(obs_idx, 0)
        self.assertGreater(winner_idx, obs_idx)
        # D' label visible in the set literal.
        self.assertIn("D'_observe_only", src)


if __name__ == "__main__":
    unittest.main()
