"""Tests du module :mod:`ict.lens_endpoints` (Epic #15475, #15479 acceptance 3).

Couvre l'acceptance 3 de #15479 — « Un meme run produit des endpoints
SAE/J-Lens/F-Lens et comportementaux **sans ecrasement de semantique** » — sur
des panneaux synthetiques deterministes (CPU, numpy-only) :

  1. (Gate un-run) une intervention clamp du moteur (tranche 1) alimente QUATRE
     familles d'endpoints dans UN bundle : sae, jlens, flens + comportemental.
  2. (Gate anti-ecrasement inter) un mesureur HOMONYME dans deux lentilles
     coexiste — chaque valeur sous son espace de noms, aucune ne meurt.
  3. (Gate anti-ecrasement intra) re-enregistrer un mesureur dans le meme
     couple (lentille, canal) echoue en nommant les trois coordonnees.
  4. (Gate contrat) canal inconnu, cles before/after/delta exactes, JSON
     deterministe et round-trippable, alignement de run nomme le champ fautif.

Pattern herite de ``test_causal_engine.py`` (bootstrap ``sys.path``
module-level, fixtures synthetiques placees a la main, tolerances commentees).
"""

from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from ict.causal_engine import InterventionSpec, apply_intervention  # noqa: E402
from ict.lens_endpoints import (  # noqa: E402
    CHANNELS,
    MultiLensRun,
    assert_run_alignment,
)


def _panel(seed: int = 7, T: int = 6, d: int = 10) -> np.ndarray:
    """Panneau synthetique deterministe, valeurs placees (pas de structure cachee)."""
    rng = np.random.default_rng(seed)
    return rng.normal(size=(T, d)).astype(np.float64)


def _clamp_spec() -> InterventionSpec:
    return InterventionSpec(
        operation="clamp",
        instrument="sae",
        layer=3,
        positions=(1, 2),
        features=(4, 5),
        dose=2.0,
        direction=(1.0, 0.0),
        run="synthetic-run-a",
        seed=11,
    )


def _run_apres_clamp() -> tuple[np.ndarray, np.ndarray]:
    """Le couple avant/apres d'un clamp selectif — le MEME run pour tout le monde."""
    before = _panel()
    after = apply_intervention(before, _clamp_spec())
    return before, after


class TestUnRunQuatreFamilles(unittest.TestCase):
    """Acceptance 3 : un meme run, quatre familles d'endpoints, aucune ecrasee."""

    def test_un_run_quatre_familles_sans_ecrasement(self) -> None:
        before, after = _run_apres_clamp()
        run = MultiLensRun(
            _clamp_spec().alignment(tensor_space="residual")
        )
        run.record("sae", "state", {
            "recon_mse": lambda p: float(np.mean(p * p)),
            "latent_mass": lambda p: float(np.sum(np.abs(p))),
        }, before, after)
        run.record("jlens", "readout", {
            "topk_overlap": lambda p: float(np.count_nonzero(p > 1.0)),
        }, before, after)
        run.record("flens", "readout", {
            "topk_overlap": lambda p: float(np.count_nonzero(p < -1.0)),
            "attribution_shift": lambda p: float(np.linalg.norm(p[:, :3])),
        }, before, after)
        run.record("task", "behavior", {
            "accuracy_proxy": lambda p: float(np.mean(p[:, 0] > 0)),
        }, before, after)

        self.assertEqual(run.lens_ids(), ("sae", "jlens", "flens", "task"))
        payload = run.to_dict()["lenses"]
        self.assertEqual(set(payload), {"sae", "jlens", "flens", "task"})
        # Chaque famille a bien son canal rempli — aucune n'a ete ecrasee.
        self.assertIn("recon_mse_before", payload["sae"]["state"])
        self.assertIn("topk_overlap_before", payload["jlens"]["readout"])
        self.assertIn("topk_overlap_before", payload["flens"]["readout"])
        self.assertIn("accuracy_proxy_before", payload["task"]["behavior"])

    def test_mesureur_homonyme_deux_lentilles_coexiste(self) -> None:
        """LE cas de l'acceptance : deux « topk_overlap », deux semantiques,
        deux valeurs — sous le meme nom de mesureur, dans deux lentilles."""
        before, after = _run_apres_clamp()
        run = MultiLensRun({"run": "synthetic-run-a"})
        run.record("jlens", "readout", {
            "topk_overlap": lambda p: float(np.count_nonzero(p > 1.0)),
        }, before, after)
        run.record("flens", "readout", {
            "topk_overlap": lambda p: float(np.count_nonzero(p < -1.0)),
        }, before, after)

        view = run.channel_view("readout")
        self.assertEqual(set(view), {"jlens", "flens"})
        jl, fl = view["jlens"], view["flens"]
        self.assertIn("topk_overlap_delta", jl)
        self.assertIn("topk_overlap_delta", fl)
        # Les DEUX valeurs existent et mesurent des choses differentes :
        # aucune n'a ecrase l'autre (valeurs placees a la main sur le couple
        # avant/apres du clamp : le clamp ecrit (2,0) sur 2 positions x
        # 2 features, donc +2 cells > 1.0 cote jlens, 0 cote flens).
        self.assertNotEqual(jl["topk_overlap_delta"], fl["topk_overlap_delta"])
        self.assertEqual(jl["topk_overlap_after"] - jl["topk_overlap_before"],
                         jl["topk_overlap_delta"])


class TestAntiEcrasementIntraLentille(unittest.TestCase):
    """Re-enregistrer un mesureur dans le MEME couple (lentille, canal) echoue."""

    def test_reenregistrement_echoue_avec_diagnostic(self) -> None:
        before, after = _run_apres_clamp()
        run = MultiLensRun({"run": "synthetic-run-a"})
        run.record("sae", "state", {
            "recon_mse": lambda p: float(np.mean(p * p)),
        }, before, after)
        with self.assertRaises(ValueError) as ctx:
            run.record("sae", "state", {
                "recon_mse": lambda p: float(np.mean(p * p)),
            }, before, after)
        msg = str(ctx.exception)
        # Les trois coordonnees de l'ecrasement sont nommees.
        for token in ("sae", "state", "recon_mse"):
            self.assertIn(token, msg)

    def test_meme_nom_canal_different_coexiste(self) -> None:
        """Le meme mesureur sur DEUX canaux d'une meme lentille est legitime :
        ce sont deux endpoints differents, pas un ecrasement."""
        before, after = _run_apres_clamp()
        run = MultiLensRun({"run": "synthetic-run-a"})
        run.record("sae", "state", {
            "mass": lambda p: float(np.sum(np.abs(p))),
        }, before, after)
        run.record("sae", "readout", {
            "mass": lambda p: float(np.sum(np.abs(p))),
        }, before, after)
        view_state = run.channel_view("state")["sae"]
        view_readout = run.channel_view("readout")["sae"]
        self.assertIn("mass_before", view_state)
        self.assertIn("mass_before", view_readout)


class TestContratEtSerialisation(unittest.TestCase):
    """Canaux, forme des cles, JSON deterministe, alignement de run."""

    def test_canal_inconnu_echoue(self) -> None:
        run = MultiLensRun({"run": "synthetic-run-a"})
        with self.assertRaises(ValueError):
            run.record("sae", "vibes", {"m": lambda p: 0.0}, _panel(), _panel())
        with self.assertRaises(ValueError):
            run.channel_view("vibes")

    def test_forme_cles_before_after_delta_exacte(self) -> None:
        before, after = _run_apres_clamp()
        run = MultiLensRun({"run": "synthetic-run-a"})
        run.record("sae", "state", {
            "energy": lambda p: float(np.sum(p * p)),
        }, before, after)
        keys = set(run.channel_view("state")["sae"])
        self.assertEqual(keys, {"energy_before", "energy_after", "energy_delta"})
        energy_b = float(np.sum(before * before))
        energy_a = float(np.sum(after * after))
        got = run.channel_view("state")["sae"]
        self.assertAlmostEqual(got["energy_before"], energy_b, places=12)
        self.assertAlmostEqual(got["energy_after"], energy_a, places=12)
        self.assertAlmostEqual(
            got["energy_delta"], energy_a - energy_b, places=12
        )

    def test_json_deterministe_et_round_trippable(self) -> None:
        before, after = _run_apres_clamp()
        run = MultiLensRun(_clamp_spec().alignment())
        run.record("sae", "state", {
            "recon_mse": lambda p: float(np.mean(p * p)),
        }, before, after)
        run.record("task", "behavior", {
            "accuracy_proxy": lambda p: float(np.mean(p[:, 0] > 0)),
        }, before, after)
        self.assertEqual(run.to_json(), run.to_json())
        self.assertEqual(json.loads(run.to_json()), run.to_dict())

    def test_channel_view_isole_et_ignore_les_canaux_vides(self) -> None:
        before, after = _run_apres_clamp()
        run = MultiLensRun({"run": "synthetic-run-a"})
        run.record("sae", "state", {"m": lambda p: 1.0}, before, after)
        run.record("task", "behavior", {"m": lambda p: 1.0}, before, after)
        # La vue d'un canal ne montre QUE les lentilles qui l'ont rempli.
        self.assertEqual(set(run.channel_view("state")), {"sae"})
        self.assertEqual(set(run.channel_view("behavior")), {"task"})
        self.assertEqual(run.channel_view("readout"), {})


class TestAlignementDeRun(unittest.TestCase):
    """Le bundle REFERE le run : deux bundles comparent selon ALIGNMENT_KEYS."""

    def test_assert_run_alignment_nomme_le_champ_fautif(self) -> None:
        a = MultiLensRun({"run": "synthetic-run-a", "seed": 11})
        b = MultiLensRun({"run": "synthetic-run-b", "seed": 11})
        with self.assertRaises(ValueError) as ctx:
            assert_run_alignment(a, b)
        # Le champ fautif ET les deux valeurs observes sont nommes.
        msg = str(ctx.exception)
        self.assertIn("run", msg)
        self.assertIn("synthetic-run-a", msg)
        self.assertIn("synthetic-run-b", msg)

    def test_cle_absente_d_un_cote_ne_bloque_pas(self) -> None:
        a = MultiLensRun({"run": "synthetic-run-a"})
        b = MultiLensRun({"run": "synthetic-run-a", "layer": 3})
        assert_run_alignment(a, b)  # champ optionnel absent d'un cote : OK

    def test_bundle_aligne_avec_le_record_sidecar(self) -> None:
        """Integration tranche 1 + tranche 4 : le bundle et l'enregistrement
        sidecar de la MEME intervention partagent le meme run — l'alignement
        passe ; changer le seed le casse nommement."""
        spec = _clamp_spec()
        bundle = MultiLensRun(spec.alignment())
        other_seed = MultiLensRun(
            dict(spec.alignment(), seed=spec.seed + 1)
        )
        assert_run_alignment(bundle, bundle)
        with self.assertRaises(ValueError) as ctx:
            assert_run_alignment(bundle, other_seed)
        self.assertIn("seed", str(ctx.exception))


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
