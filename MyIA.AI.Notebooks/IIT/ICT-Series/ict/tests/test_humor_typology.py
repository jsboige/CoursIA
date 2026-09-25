# -*- coding: utf-8 -*-
"""Tests du module ict/humor_typology.py (issue #14035, tranche finale)."""

from __future__ import annotations

import importlib.util
import unittest
from pathlib import Path

import numpy as np


def _load_pairs_module():
    """Charge humor_pairs sans executer la reproduction corpus (reseau/env)."""
    base = Path(__file__).resolve().parent.parent
    spec = importlib.util.spec_from_file_location(
        "hp_standalone", base / "humor_pairs.py"
    )
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _pairs_stub(hp):
    """Paires factices couvrant les 30 ids reels de _PAIR_EDITS."""
    return [
        {"id": jid, "setup": "s", "humour": "s h", "unfun": "s u", "ctrl_edit": "s c"}
        for jid in hp._PAIR_EDITS
    ]


class TestAnnotation(unittest.TestCase):
    def test_couverture_exacte(self):
        from ict.humor_typology import PAIR_TYPES, TYPES, validate_typology

        hp = _load_pairs_module()
        pairs = _pairs_stub(hp)
        self.assertEqual(set(PAIR_TYPES), set(hp._PAIR_EDITS))
        validate_typology(pairs)  # couverture + plancher par type, sans lever

    def test_plancher_par_type(self):
        from ict.humor_typology import MIN_PER_TYPE, PAIR_TYPES, TYPES

        counts = {t: 0 for t in TYPES}
        for t in PAIR_TYPES.values():
            counts[t] += 1
        for t, n in counts.items():
            self.assertGreaterEqual(n, MIN_PER_TYPE, f"type {t} sous le plancher")

    def test_validate_typology_refuse_manquant(self):
        from ict.humor_typology import validate_typology

        hp = _load_pairs_module()
        pairs = _pairs_stub(hp)[:-1]  # un id non annote
        with self.assertRaises(ValueError):
            validate_typology(pairs)

    def test_split_by_type_partition_exacte(self):
        from ict.humor_typology import split_by_type

        hp = _load_pairs_module()
        pairs = _pairs_stub(hp)
        parts = split_by_type(pairs)
        total = sum(len(v) for v in parts.values())
        self.assertEqual(total, len(pairs))
        ids = sorted(p["id"] for v in parts.values() for p in v)
        self.assertEqual(ids, sorted(p["id"] for p in pairs))


class TestInference(unittest.TestCase):
    def test_bootstrap_ic_et_d(self):
        from ict.humor_typology import bootstrap_mean_ic

        rng = np.random.default_rng(0)
        x = rng.normal(loc=2.0, scale=1.0, size=200)
        r1 = bootstrap_mean_ic(x, n_boot=2000, seed=42)
        r2 = bootstrap_mean_ic(x, n_boot=2000, seed=42)
        self.assertAlmostEqual(r1["mean"], r2["mean"])
        self.assertEqual(r1["ic_lo"], r2["ic_lo"])  # reproductibilite au seed
        self.assertLess(r1["ic_lo"], r1["mean"])
        self.assertGreater(r1["ic_hi"], r1["mean"])
        self.assertAlmostEqual(r1["cohens_d"], 2.0, delta=0.35)

    def test_feature_z_null_pur(self):
        """Sous H0 (aucun effet), le max |z| observe reste sous le null p95."""
        from ict.humor_typology import feature_z

        rng = np.random.default_rng(1)
        n, d = 30, 500
        H = rng.normal(size=(n, d))
        U = rng.normal(size=(n, d))
        C = rng.normal(size=(n, d))
        r = feature_z({"humour": H, "unfun": U, "ctrl_edit": C},
                      n_draws=500, seed=7)
        self.assertLessEqual(r["observed_max_abs_z"], r["null_max_p95"] + 0.5)
        self.assertGreaterEqual(r["familywise_p"], 0.0)
        self.assertLessEqual(r["familywise_p"], 1.0)

    def test_feature_z_detecte_effet_fort(self):
        from ict.humor_typology import feature_z

        rng = np.random.default_rng(2)
        n, d = 30, 500
        base = rng.normal(size=(n, d))
        shift = np.zeros(d)
        shift[17] = 8.0  # une feature massivement deplacee
        r = feature_z(
            {"humour": base, "unfun": base + shift,
             "ctrl_edit": base + rng.normal(scale=0.01, size=(n, d))},
            n_draws=500, seed=7,
        )
        self.assertGreater(r["observed_max_abs_z"], r["null_max_p95"])
        self.assertGreater(r["n_over3"], 0)

    def test_final_verdict_sans_candidate(self):
        from ict.humor_typology import final_verdict

        legs = [{"leg": "L12/pun/trained", "verdict": "INCONCLUSIVE"},
                {"leg": "L12/topical/trained", "verdict": "SURFACE_SEULE"}]
        r = final_verdict(legs)
        self.assertEqual(r["verdict"], "AUCUNE_FEATURE_STABLE")
        self.assertEqual(r["n_candidate_legs"], 0)

    def test_final_verdict_avec_candidate(self):
        from ict.humor_typology import final_verdict

        legs = [{"leg": "L12/pun/trained", "verdict": "FEATURE_CANDIDATE"}]
        r = final_verdict(legs)
        self.assertEqual(r["verdict"], "CANDIDATS_PAR_TYPE")
        self.assertEqual(r["candidate_legs"], ["L12/pun/trained"])

    def test_per_pair_deltas_forme(self):
        from ict.humor_typology import per_pair_deltas

        rng = np.random.default_rng(3)
        zones = {k: np.abs(rng.normal(size=(5, 10))) for k in ("humour", "unfun", "ctrl_edit")}
        d = per_pair_deltas(zones)
        self.assertEqual(d["delta_pair"].shape, (5,))
        self.assertTrue((d["delta_pair"] > 0).all())


if __name__ == "__main__":
    unittest.main()
