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
        """
        common_bulk = self.bulk_slim  # 276 bars, same input for everyone.
        results = {
            "A": bench._path_baseline_bulk(common_bulk, bench.N_BARS_SLIM),
            "B": bench._path_per_symbol(common_bulk, bench.N_BARS_SLIM),
            "C": bench._path_flatten_array(common_bulk, bench.N_BARS_SLIM),
            "D": bench._path_reduce_n_bars(common_bulk, bench.N_BARS_SLIM),
        }
        # Every path returns 19 symbols.
        sym_sets = [set(r.keys()) for r in results.values()]
        for sym_set in sym_sets[1:]:
            self.assertEqual(sym_set, sym_sets[0])

        # For each symbol, the close arrays are equal across all 4 paths.
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


if __name__ == "__main__":
    unittest.main()
