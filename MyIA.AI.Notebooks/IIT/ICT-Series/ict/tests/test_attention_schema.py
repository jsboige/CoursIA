"""Tests du banc case 5 — schéma attentionnel (#8182, Graziano AST).

Les seuils viennent du pré-enregistrement scellé dans
``docs/ict/dissociations-matrix.md`` (case 5, PR c.435) : bande
[0.50, 2.00], tueuses [0.85, 1.15] et > 2.50, calibration ε_attn =
0.5 × σ_attn × propa(objet)_médian exécutée AVANT le test principal.

Les tests ne mesurent pas de conscience : ils pincent la formule propa,
l'appariement des contre-factuels, la formule de calibration et CHAQUE
branche de la table de verdict multi-niveau.
"""

from __future__ import annotations

import json

import numpy as np
import pytest

from ict.attention_schema import (
    CALIBRATION_TARGETS,
    CONTEXTS_BY_SEED,
    SEEDS,
    TASK_OBJECT,
    TASK_OTHER,
    TASK_SELF,
    Calibration,
    apply_verdict,
    build_calibration_sets,
    build_prompt_sets,
    calibrate_epsilon,
    propa,
    run_analysis,
    score_main_arms,
)


def _mk_trace(sets: dict[str, list[tuple[np.ndarray, np.ndarray]]], d_sae: int = 8) -> dict:
    """Assemble un dict de trace au schema .npz de sae_traces.load_traces."""
    prompts = {}
    for name, prompts_raw in sets.items():
        for i, (ids, vals) in enumerate(prompts_raw):
            assert ids.shape == vals.shape and ids.ndim == 2
            prompts[(name, i)] = {"ids": ids.astype(np.int32),
                                  "vals": vals.astype(np.float32),
                                  "tokens": np.array(["x"] * ids.shape[0])}
    return {"meta": {"d_sae": d_sae, "k": ids.shape[1]}, "prompts": prompts}


def _synth_prompt(T: int, k: int, *, hot_feature: int, ignition_at: int,
                  consumer_top1: list[int], rng_seed: int = 0) -> tuple[np.ndarray, np.ndarray]:
    """Un prompt synthétique : ignition ``ignition_at`` (somme top-k maximale),
    consommateurs ``ignition_at+1..+5`` portant ``consumer_top1`` en argmax."""
    rng = np.random.default_rng(rng_seed)
    ids = rng.integers(0, 8, size=(T, k))
    vals = rng.uniform(0.1, 1.0, size=(T, k))
    vals = np.sort(vals, axis=1)[:, ::-1]          # topk trié desc
    order = np.argsort(ids[ignition_at])           # features distinctes à l'ignition
    ids[ignition_at] = ids[ignition_at][order]
    vals[ignition_at] = np.array([5.0, 4.0, 3.0][:k])   # somme = max du prompt
    ids[ignition_at, 0] = hot_feature
    for j, feat in enumerate(consumer_top1):
        pos = ignition_at + 1 + j
        if pos < T:
            ids[pos, 0] = feat
            vals[pos, 0] = 2.5                     # argmax net du consommateur
    vals = np.sort(vals, axis=1)[:, ::-1]          # re-trier les valeurs
    return ids, vals


def _pair_prompt(hots: int, *, rng_seed: int = 0, hot: int = 6, distractor: int = 7,
                 k: int = 3) -> tuple[np.ndarray, np.ndarray]:
    """Prompt à ``propa`` exacte : 2 ignitions (10, 25), 10 consommateurs.

    Les ``hots`` premiers consommateurs portent ``hot`` (val 2.5 — masse
    dominante du bras avec les ignitions à 18), les autres ``distractor``
    (val 1.05 > baseline 0.34 → argmax net, mais masse moyenne loin sous la
    baseline → hors signature top-2). Baseline : features 0-1 uniquement,
    vals [0.30, 0.34] → moyenne ~0.48 par feature, bruit << marges.
    ``propa(bras) = hots/10`` par prompt, exactement.
    """
    T = 40
    rng = np.random.default_rng(rng_seed)
    ids = rng.integers(0, 2, size=(T, k))
    vals = np.sort(rng.uniform(0.30, 0.34, size=(T, k)), axis=1)[:, ::-1]
    hots = max(0, min(10, int(hots)))
    pattern = [1] * hots + [0] * (10 - hots)
    j = 0
    for ign in (10, 25):
        ids[ign] = (hot, hot, hot)
        vals[ign] = (8.0, 6.0, 4.0)
        for pos in range(ign + 1, ign + 6):
            if pattern[j]:
                ids[pos, 0], vals[pos, 0] = hot, 2.5
            else:
                ids[pos, 0], vals[pos, 0] = distractor, 1.05
            j += 1
    return ids, vals


def _arm_traces(arm_hots: dict[str, int]) -> dict:
    """Trace 3 prompts/bras au schema .npz ; chaque prompt à ``hots`` hot."""
    prompts = {}
    for name, hots in arm_hots.items():
        for i in range(3):
            ids, vals = _pair_prompt(hots, rng_seed=i)
            prompts[(name, i)] = {"ids": ids.astype(np.int32),
                                  "vals": vals.astype(np.float32),
                                  "tokens": np.array(["x"] * ids.shape[0])}
    return {"meta": {"d_sae": 8, "k": 3}, "prompts": prompts}


class TestPromptsApparies:
    def test_9_prompts_par_graine_trois_bras(self):
        for seed in SEEDS:
            sets = build_prompt_sets(seed)
            assert set(sets) == {"attn_self", "attn_other", "obj_chaise"}
            assert all(len(v) == 3 for v in sets.values())

    def test_contexte_partage_identique_dans_chaque_triplet(self):
        """Contre-factuels exacts : même contexte amont, seule la cible diffère."""
        for seed in SEEDS:
            sets = build_prompt_sets(seed)
            for s, o, ob in zip(sets["attn_self"], sets["attn_other"], sets["obj_chaise"]):
                ctx_s = s[: -len(TASK_SELF)]
                ctx_o = o[: -len(TASK_OTHER)]
                ctx_ob = ob[: -len(TASK_OBJECT)]
                assert ctx_s == ctx_o == ctx_ob

    def test_calibration_deux_objets_publics_non_agentiques(self):
        for seed in SEEDS:
            calib = build_calibration_sets(seed)
            assert set(calib) == {"calib_obj1", "calib_obj2"}
            joined = " ".join(calib["calib_obj1"] + calib["calib_obj2"])
            assert "attention" not in joined.lower()
            assert "agent" not in joined.lower()

    def test_banque_contextes_3_par_seed_et_5_seeds_prealables(self):
        assert len(SEEDS) == 5
        for seed in SEEDS:
            assert len(CONTEXTS_BY_SEED[seed]) == 3
        assert len(CALIBRATION_TARGETS) == 2


class TestPropa:
    def test_formule_sur_trace_synthetique(self):
        # signature dominée par la feature 1 (chaude partout + ignitions).
        ids, vals = _synth_prompt(T=30, k=3, hot_feature=1, ignition_at=10,
                                  consumer_top1=[1, 1, 1, 5, 5], rng_seed=0)
        ids2, vals2 = _synth_prompt(T=30, k=3, hot_feature=1, ignition_at=12,
                                    consumer_top1=[1, 5, 1, 5, 1], rng_seed=1)
        traces = _mk_trace({"bras": [(ids, vals), (ids2, vals2)]})
        # consommateurs : 3/5 puis 3/5 dans la signature (feature 1 en tête de
        # moyenne), feature 5 jamais dominante en moyenne -> hors signature.
        assert propa(traces, "bras", k_features=2) == pytest.approx(0.6)

    def test_bras_absent_refuse(self):
        traces = _mk_trace({"bras": [_synth_prompt(20, 3, hot_feature=1, ignition_at=10,
                                                  consumer_top1=[1, 1, 1, 1, 1])]})
        with pytest.raises(ValueError, match="absent"):
            propa(traces, "autre_bras", k_features=2)

    def test_trace_trop_courte_refusee(self):
        ids = np.zeros((4, 3), dtype=np.int32)
        vals = np.ones((4, 3), dtype=np.float32)
        with pytest.raises(ValueError, match="trop courte"):
            propa(_mk_trace({"bras": [(ids, vals)]}), "bras")


class TestCalibration:
    RATIOS = {0: 1.0, 1: 1.2, 7: 0.75, 42: 1.0, 99: 6 / 7}

    @staticmethod
    def _seed_traces(r: float) -> dict:
        # propa(obj1) = 6/10 ; propa(obj2) = 0.6/r réalisé exactement sur la
        # grille des dixièmes (hots = round(10 x 0.6 / r)).
        return _arm_traces({"calib_obj1": 6, "calib_obj2": round(10 * 0.6 / r)})

    def test_sigma_et_rapports_neutres(self):
        traces = {s: self._seed_traces(r) for s, r in self.RATIOS.items()}
        calib = calibrate_epsilon(traces, k_features=2)
        expected_sigma = float(np.std(list(self.RATIOS.values()), ddof=1))
        assert calib.sigma_attn == pytest.approx(expected_sigma, rel=1e-6)
        for s, r in self.RATIOS.items():
            assert calib.r_neutre_by_seed[s] == pytest.approx(r, rel=0.05)

    def test_epsilon_assemble_apres_scale_uniquement(self):
        calib = Calibration(r_neutre_by_seed={0: 1.0, 1: 1.1, 7: 0.9, 42: 1.05, 99: 0.95},
                            sigma_attn=0.1)
        with pytest.raises(ValueError, match="anti-HARKing"):
            score_main_arms({}, calib)


class TestVerdict:
    def test_confirmed(self):
        r = {s: 1.4 for s in SEEDS}
        disc = {s: 0.10 for s in SEEDS}
        verdict, kills = apply_verdict(r, disc, epsilon_attn=0.02)
        assert verdict == "CONFIRMED" and not kills

    def test_falsified_repression(self):
        r = {0: 0.3, 1: 0.2, 7: 0.4, 42: 0.35, 99: 1.4}
        verdict, kills = apply_verdict(r, {s: 0.1 for s in SEEDS}, 0.02)
        assert verdict == "FALSIFIED" and any("réprime" in k.lower() for k in kills)

    def test_falsified_artefact_blocage(self):
        r = {0: 3.1, 1: 2.9, 7: 3.3, 42: 1.4, 99: 1.5}
        verdict, kills = apply_verdict(r, {s: 0.1 for s in SEEDS}, 0.02)
        assert verdict == "FALSIFIED" and any("blocage" in k for k in kills)

    def test_inconclusif_bande_tueuse_une_graine(self):
        r = {0: 1.4, 1: 1.45, 7: 1.5, 42: 1.4, 99: 1.0}
        verdict, kills = apply_verdict(r, {s: 0.1 for s in SEEDS}, 0.02)
        assert verdict == "INCONCLUSIF" and any("0.85, 1.15" in k for k in kills)

    def test_inconclusif_discrimination_sous_epsilon(self):
        r = {s: 1.4 for s in SEEDS}
        verdict, kills = apply_verdict(r, {s: 0.001 for s in SEEDS}, 0.02)
        assert verdict == "INCONCLUSIF" and any("ε_attn" in k for k in kills)

    def test_hors_bande_sans_majorite_falsifie(self):
        r = {0: 0.6, 1: 0.65, 7: 0.55, 42: 2.3, 99: 0.62}   # médiane 0.62, dans bande
        verdict, _ = apply_verdict(r, {s: 0.1 for s in SEEDS}, 0.02)
        assert verdict == "CONFIRMED"      # aucun critère tueur touché


class TestRunAnalysis:
    def test_ordre_calibration_puis_score_serialisable(self):
        ratios = {0: 1.0, 1: 1.2, 7: 0.75, 42: 1.0, 99: 6 / 7}
        calib = calibrate_epsilon(
            {s: _arm_traces({"calib_obj1": 6, "calib_obj2": round(6 / r)})
             for s, r in ratios.items()}, k_features=2)
        # propa(attn_self) = 0.8, propa(obj_chaise) = 0.5 → R_attn = 1.6/seed.
        main = {s: _arm_traces({"attn_self": 8, "obj_chaise": 5}) for s in SEEDS}
        result = run_analysis(calib, main, k_features=2)
        assert set(result) >= {"case", "calibration", "main", "verdict"}
        assert result["calibration"]["epsilon_attn"] == pytest.approx(
            0.5 * calib.sigma_attn * result["calibration"]["propa_obj_median_scale"])
        assert result["verdict"] in {"CONFIRMED", "FALSIFIED", "INCONCLUSIF"}
        json.dumps(result)                  # sérialisable pour results/
