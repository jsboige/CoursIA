"""Tests du banc case 4 — self-model minimal (#8182, Metzinger).

Les seuils viennent du pré-enregistrement scellé dans
``docs/ict/dissociations-matrix.md`` (case 4, PR c.1245) : bande
[0.50, 2.00], tueuses [0.85, 1.15] et > 2.50, calibration ε_self =
0.5 × σ_self × propa(autrui)_médian exécutée AVANT le test principal.

Les tests ne mesurent pas de conscience : ils pincent la réutilisation de
l'opérateur canonique ``propa`` (importé de case 5, non modifié),
l'appariement des contre-factuels self/autrui/neutre, la formule de
calibration et CHAQUE branche de la table de verdict multi-niveau.
"""

from __future__ import annotations

import json
import re

import numpy as np
import pytest

from ict.attention_schema import CONTEXTS_BY_SEED
from ict.self_model_minimal import (
    ARM_SETS,
    CALIBRATION_TARGETS,
    SEEDS,
    TASK_NEUTRAL,
    TASK_OTHER,
    TASK_SELF,
    Calibration,
    apply_verdict_self,
    build_calibration_sets,
    build_prompt_sets,
    calibrate_epsilon_self,
    run_analysis,
    score_main_arms,
)
from ict.attention_schema import propa


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

    Même construction que test_attention_schema (la formule propa est
    inchangée — c'est ce que la case 4 doit garantir) :
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
            assert set(sets) == set(ARM_SETS)
            assert all(len(v) == 3 for v in sets.values())

    def test_contexte_partage_identique_dans_chaque_triplet(self):
        """Contre-factuels exacts : même contexte amont, seule la cible diffère."""
        for seed in SEEDS:
            sets = build_prompt_sets(seed)
            for s, o, n in zip(sets["self_state"], sets["other_agent"],
                               sets["neutral_statue"]):
                ctx_s = s[: -len(TASK_SELF)]
                ctx_o = o[: -len(TASK_OTHER)]
                ctx_n = n[: -len(TASK_NEUTRAL)]
                assert ctx_s == ctx_o == ctx_n

    def test_meme_banque_de_contextes_que_case_5(self):
        """Comparabilité cross-case : la banque importée est inchangée."""
        assert len(CONTEXTS_BY_SEED) == 5
        assert all(len(v) == 3 for v in CONTEXTS_BY_SEED.values())

    def test_calibration_deux_objets_publics_non_identitaires(self):
        for seed in SEEDS:
            calib = build_calibration_sets(seed)
            assert set(calib) == {"calib_obj1", "calib_obj2"}
            joined = " ".join(calib["calib_obj1"] + calib["calib_obj2"])
            assert "état interne" not in joined.lower()
            # mots identitaires aux frontières de mots ("toi" matcherait
            # "laboratoire" en substring naïf).
            for mot in ("agent", "toi", "tu", "tes"):
                assert not re.search(rf"\b{mot}\b", joined.lower())

    def test_bras_neutre_distinct_des_entites_de_calibration(self):
        """L'objet public Z du bras neutre ne recycle pas calib_obj1/obj2."""
        entites = {clause.split("Décris ")[1].split(" après")[0]
                   for _, clause in CALIBRATION_TARGETS}
        neutre = TASK_NEUTRAL.split("Décris ")[1].split(" après")[0]
        assert neutre not in entites


class TestOperateurCanonique:
    def test_propa_est_celui_de_case_5(self):
        """L'instrument n'est PAS retouché : même formule, mêmes exceptions."""
        from ict.self_model_minimal import propa as propa_case4
        assert propa_case4 is propa

    def test_formule_sur_trace_synthetique(self):
        ids, vals = _synth_prompt(T=30, k=3, hot_feature=1, ignition_at=10,
                                  consumer_top1=[1, 1, 1, 5, 5], rng_seed=0)
        ids2, vals2 = _synth_prompt(T=30, k=3, hot_feature=1, ignition_at=12,
                                    consumer_top1=[1, 5, 1, 5, 1], rng_seed=1)
        traces = _mk_trace({"bras": [(ids, vals), (ids2, vals2)]})
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
        return _arm_traces({"calib_obj1": 6, "calib_obj2": round(10 * 0.6 / r)})

    def test_sigma_et_rapports_neutres(self):
        traces = {s: self._seed_traces(r) for s, r in self.RATIOS.items()}
        calib = calibrate_epsilon_self(traces, k_features=2)
        expected_sigma = float(np.std(list(self.RATIOS.values()), ddof=1))
        assert calib.sigma_self == pytest.approx(expected_sigma, rel=1e-6)
        for s, r in self.RATIOS.items():
            assert calib.r_neutre_by_seed[s] == pytest.approx(r, rel=0.05)

    def test_moins_de_3_graines_exploitables_refuse(self):
        with pytest.raises(ValueError, match="<3"):
            calibrate_epsilon_self({0: self._seed_traces(1.0)}, k_features=2)

    def test_epsilon_assemble_apres_scale_uniquement(self):
        calib = Calibration(r_neutre_by_seed={0: 1.0, 1: 1.1, 7: 0.9, 42: 1.05, 99: 0.95},
                            sigma_self=0.1)
        with pytest.raises(ValueError, match="anti-HARKing"):
            score_main_arms({}, calib)


class TestVerdict:
    def test_confirmed(self):
        r = {s: 1.4 for s in SEEDS}
        disc = {s: 0.10 for s in SEEDS}
        verdict, kills = apply_verdict_self(r, disc, epsilon_self=0.02)
        assert verdict == "CONFIRMED" and not kills

    def test_falsified_repression(self):
        r = {0: 0.3, 1: 0.2, 7: 0.4, 42: 0.35, 99: 1.4}
        verdict, kills = apply_verdict_self(r, {s: 0.1 for s in SEEDS}, 0.02)
        assert verdict == "FALSIFIED" and any("réprime" in k.lower() for k in kills)

    def test_falsified_artefact_persona_figee(self):
        r = {0: 3.1, 1: 2.9, 7: 3.3, 42: 1.4, 99: 1.5}
        verdict, kills = apply_verdict_self(r, {s: 0.1 for s in SEEDS}, 0.02)
        assert verdict == "FALSIFIED" and any("persona figée" in k for k in kills)

    def test_inconclusif_bande_tueuse_une_graine(self):
        r = {0: 1.4, 1: 1.45, 7: 1.5, 42: 1.4, 99: 1.0}
        verdict, kills = apply_verdict_self(r, {s: 0.1 for s in SEEDS}, 0.02)
        assert verdict == "INCONCLUSIF" and any("0.85, 1.15" in k for k in kills)

    def test_inconclusif_discrimination_sous_epsilon(self):
        r = {s: 1.4 for s in SEEDS}
        verdict, kills = apply_verdict_self(r, {s: 0.001 for s in SEEDS}, 0.02)
        assert verdict == "INCONCLUSIF" and any("ε_self" in k for k in kills)

    def test_hors_bande_sans_majorite_falsifie(self):
        r = {0: 0.6, 1: 0.65, 7: 0.55, 42: 2.3, 99: 0.62}   # médiane 0.62, dans bande
        verdict, _ = apply_verdict_self(r, {s: 0.1 for s in SEEDS}, 0.02)
        assert verdict == "CONFIRMED"


class TestRunAnalysis:
    def test_ordre_calibration_puis_score_serialisable(self):
        ratios = {0: 1.0, 1: 1.2, 7: 0.75, 42: 1.0, 99: 6 / 7}
        calib = calibrate_epsilon_self(
            {s: _arm_traces({"calib_obj1": 6, "calib_obj2": round(6 / r)})
             for s, r in ratios.items()}, k_features=2)
        # propa(self_state) = 0.8, propa(other_agent) = 0.5 → R_self = 1.6/seed.
        main = {s: _arm_traces({"self_state": 8, "other_agent": 5}) for s in SEEDS}
        result = run_analysis(calib, main, k_features=2)
        assert set(result) >= {"case", "substrate", "calibration", "main", "verdict"}
        assert result["case"] == "case4_self_model_minimal"
        assert result["calibration"]["epsilon_self"] == pytest.approx(
            0.5 * calib.sigma_self * result["calibration"]["propa_other_median_scale"])
        assert result["main"]["r_self_by_seed"][0] == pytest.approx(1.6, rel=0.05)
        assert result["verdict"] in {"CONFIRMED", "FALSIFIED", "INCONCLUSIF"}
        json.dumps(result)                  # sérialisable pour results/

    def test_rapport_exact_sur_grille_dixiemes(self):
        """R_self réalisé exactement : self 8/10, autrui 5/10 → 1.6 partout."""
        main = {s: _arm_traces({"self_state": 8, "other_agent": 5}) for s in SEEDS}
        calib = Calibration(
            r_neutre_by_seed={s: 1.0 for s in SEEDS}, sigma_self=0.05)
        result = run_analysis(calib, main, k_features=2)
        for r in result["main"]["r_self_by_seed"].values():
            assert r == pytest.approx(1.6, rel=0.05)
