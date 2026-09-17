"""Tests du banc case 3 — confabulation broadcast (#8182).

Les seuils viennent du pré-enregistrement scellé dans
``docs/ict/dissociations-matrix.md`` (case 3, §l.539) : bande [0.80, 1.00],
null adversarial RÉSIDUEL ε_stable = 0.5 × (propa(vrai) − propa(aléatoire))
calibré et gelé AVANT le bras faux, critère 5/5 graines.

Les tests ne mesurent pas de conscience : ils pincent la réutilisation de
l'opérateur canonique ``propa`` (importé de case 5, non modifié),
l'appariement des contre-factuels vrai/faux/aléatoire, la formule de
calibration résiduelle et CHAQUE branche de la table de verdict multi-niveau
(y compris la branche honnête « médiane > 1.00 : hors table scellée »).
"""

from __future__ import annotations

import json
import re

import numpy as np
import pytest

from ict.attention_schema import CONTEXTS_BY_SEED, propa
from ict.confabulation_broadcast import (
    ARM_CALIB,
    ARM_MAIN,
    SEEDS,
    TASK_ALEA,
    TASK_FAUX,
    TASK_VRAI,
    Calibration,
    apply_verdict_confab,
    build_calibration_sets,
    build_prompt_sets,
    calibrate_epsilon_stable,
    run_analysis,
    score_main_arms,
)


def _pair_prompt(hots: int, *, rng_seed: int = 0, hot: int = 6, distractor: int = 7,
                 k: int = 3) -> tuple[np.ndarray, np.ndarray]:
    """Prompt à ``propa`` exacte : 2 ignitions (10, 25), 10 consommateurs.

    Même construction que test_attention_schema / test_self_model_minimal
    (la formule propa est inchangée — c'est ce que la case 3 doit garantir) :
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


class TestPromptsVerrouilles:
    def test_calibration_six_prompts_deux_bras(self):
        for seed in SEEDS:
            calib = build_calibration_sets(seed)
            assert set(calib) == set(ARM_CALIB)
            assert all(len(v) == 3 for v in calib.values())

    def test_main_trois_prompts_un_seul_bras(self):
        for seed in SEEDS:
            main = build_prompt_sets(seed)
            assert set(main) == set(ARM_MAIN)
            assert len(main["confab_faux"]) == 3

    def test_contexte_partage_identique_dans_chaque_triplet(self):
        """Contre-factuels exacts : même contexte amont pour vrai/faux/aléatoire."""
        for seed in SEEDS:
            calib = build_calibration_sets(seed)
            main = build_prompt_sets(seed)
            for v, a, f in zip(calib["target_vrai"], calib["control_alea"],
                               main["confab_faux"]):
                ctx_v = v[: -len(TASK_VRAI)]
                ctx_a = a[: -len(TASK_ALEA)]
                ctx_f = f[: -len(TASK_FAUX)]
                assert ctx_v == ctx_a == ctx_f

    def test_vrai_faux_ne_differencent_que_par_la_propriete(self):
        """« La cible est connue, mais q̂ ≠ cible » : un seul mot diffère."""
        w_v, w_f = TASK_VRAI.split(), TASK_FAUX.split()
        assert len(w_v) == len(w_f)
        diffs = [(a, b) for a, b in zip(w_v, w_f) if a != b]
        assert len(diffs) == 1
        assert diffs[0] == ("claire,", "bleue,")

    def test_aleatoire_sans_rapport_aux_objets_de_la_tache(self):
        """Le contrôle ne représente AUCUN objet de la tâche (matrice l.546)."""
        tache = (TASK_VRAI + " " + TASK_FAUX).lower()
        for mot in ("carafe", "eau", "table", "claire", "bleue"):
            assert mot in tache
            assert not re.search(rf"\b{mot}\b", TASK_ALEA.lower())

    def test_meme_banque_de_contextes_que_case_5(self):
        """Comparabilité cross-case : la banque importée est inchangée."""
        assert len(CONTEXTS_BY_SEED) == 5
        assert all(len(v) == 3 for v in CONTEXTS_BY_SEED.values())


class TestOperateurCanonique:
    def test_propa_est_celui_de_case_5(self):
        """L'instrument n'est PAS retouché : même formule, mêmes exceptions."""
        from ict.confabulation_broadcast import propa as propa_case3
        assert propa_case3 is propa

    def test_bras_absent_refuse(self):
        traces = _arm_traces({"target_vrai": 8})
        with pytest.raises(ValueError, match="absent"):
            propa(traces, "confab_faux", k_features=2)

    def test_trace_trop_courte_refusee(self):
        ids = np.zeros((4, 3), dtype=np.int32)
        vals = np.ones((4, 3), dtype=np.float32)
        prompts = {( "target_vrai", 0): {"ids": ids, "vals": vals,
                                          "tokens": np.array(["x"] * 4)}}
        with pytest.raises(ValueError, match="trop courte"):
            propa({"meta": {"d_sae": 8, "k": 3}, "prompts": prompts},
                  "target_vrai", k_features=2)


class TestCalibrationResiduelle:
    def test_formule_epsilon_stable(self):
        """propa(vrai)=0.8, propa(aléa)=0.1 → gap 0.7, ε_stable=0.35, par graine."""
        traces = {s: _arm_traces({"target_vrai": 8, "control_alea": 1})
                  for s in range(5)}
        calib = calibrate_epsilon_stable(traces, k_features=2)
        for s in range(5):
            assert calib.propa_vrai_by_seed[s] == pytest.approx(0.8, abs=0.02)
            assert calib.propa_alea_by_seed[s] == pytest.approx(0.1, abs=0.02)
            assert calib.gap_by_seed[s] == pytest.approx(0.7, abs=0.04)
            assert calib.epsilon_stable_by_seed[s] == pytest.approx(0.35, abs=0.02)
        assert calib.epsilon_stable_median == pytest.approx(0.35, abs=0.02)
        assert not calib.notes

    def test_graine_degeneree_notee_mais_pas_imputee(self):
        """Gap ≤ 0 : graine exclue d'ε_stable, notée, jamais fabriquee."""
        traces = {0: _arm_traces({"target_vrai": 2, "control_alea": 8}),  # gap < 0
                  1: _arm_traces({"target_vrai": 8, "control_alea": 1}),
                  2: _arm_traces({"target_vrai": 9, "control_alea": 1}),
                  3: _arm_traces({"target_vrai": 7, "control_alea": 2}),
                  4: _arm_traces({"target_vrai": 8, "control_alea": 2})}
        calib = calibrate_epsilon_stable(traces, k_features=2)
        assert 0 not in calib.gap_by_seed
        assert any("dégénérée" in n for n in calib.notes)

    def test_moins_de_3_graines_exploitables_refuse(self):
        traces = {0: _arm_traces({"target_vrai": 2, "control_alea": 8}),
                  1: _arm_traces({"target_vrai": 2, "control_alea": 8}),
                  2: _arm_traces({"target_vrai": 2, "control_alea": 8})}
        with pytest.raises(ValueError, match="<3"):
            calibrate_epsilon_stable(traces, k_features=2)

    def test_score_refuse_sans_calibration_gelee(self):
        """Garde anti-HARKing : le bras faux ne se score pas sans ε_stable gelé."""
        calib = Calibration(propa_vrai_by_seed={s: 0.8 for s in range(5)},
                            propa_alea_by_seed={s: 0.1 for s in range(5)})
        with pytest.raises(ValueError, match="anti-HARKing"):
            score_main_arms({}, calib, k_features=2)

    def test_graine_hors_calibration_refusee(self):
        calib = calibrate_epsilon_stable(
            {s: _arm_traces({"target_vrai": 8, "control_alea": 1})
             for s in range(5)}, k_features=2)
        main = {9: _arm_traces({"confab_faux": 8})}  # graine inconnue de la calib
        with pytest.raises(ValueError, match="absente de la calibration"):
            score_main_arms(main, calib, k_features=2)


class TestVerdict:
    PASSED = {s: True for s in range(5)}

    def test_confirmed_dans_la_bande(self):
        r = {s: 0.9 for s in range(5)}
        verdict, kills = apply_verdict_confab(r, self.PASSED)
        assert verdict == "CONFIRMED" and not kills

    def test_confirmed_frontiere_inclusive(self):
        r = {s: 1.0 for s in range(5)}
        verdict, _ = apply_verdict_confab(r, self.PASSED)
        assert verdict == "CONFIRMED"

    def test_falsified_rejet_sous_080(self):
        r = {s: 0.6 for s in range(5)}
        verdict, kills = apply_verdict_confab(r, self.PASSED)
        assert verdict == "FALSIFIED" and not kills

    def test_falsified_bande_de_prudence_annotee(self):
        r = {s: 0.77 for s in range(5)}
        verdict, kills = apply_verdict_confab(r, self.PASSED)
        assert verdict == "FALSIFIED"
        assert any("prudence" in k for k in kills)

    def test_inconclusif_partiel_une_graine_sous_epsilon(self):
        r = {s: 0.9 for s in range(5)}
        passes = dict(self.PASSED)
        passes[3] = False
        verdict, kills = apply_verdict_confab(r, passes)
        assert verdict == "INCONCLUSIF"
        assert any("null adversarial partiel" in k for k in kills)

    def test_inconclusif_mediane_hors_table_superieure(self):
        """Médiane > 1.00 : la table scellée n'a pas de branche — honnête."""
        r = {s: 1.1 for s in range(5)}
        verdict, kills = apply_verdict_confab(r, self.PASSED)
        assert verdict == "INCONCLUSIF"
        assert any("hors table" in k for k in kills)
        assert any("1.00" in k for k in kills)

    def test_hors_table_proche_annote_bande_de_prudence(self):
        r = {s: 1.03 for s in range(5)}
        verdict, kills = apply_verdict_confab(r, self.PASSED)
        assert verdict == "INCONCLUSIF"
        assert any("bande de prudence (1.00, 1.05]" in k for k in kills)


class TestRunAnalysis:
    def test_ordre_calibration_puis_score_serialisable(self):
        calib = calibrate_epsilon_stable(
            {s: _arm_traces({"target_vrai": 8, "control_alea": 1})
             for s in range(5)}, k_features=2)
        # propa(faux) = 0.8 = propa(vrai) → R_confab = 1.0 (frontière),
        # disc = 0.8 − 0.1 = 0.7 ≥ ε_stable 0.35 → CONFIRMED.
        main = {s: _arm_traces({"confab_faux": 8}) for s in range(5)}
        result = run_analysis(calib, main, k_features=2)
        assert set(result) >= {"case", "substrate", "calibration", "main", "verdict"}
        assert result["case"] == "case3_confabulation_broadcast"
        assert result["verdict"] == "CONFIRMED"
        assert result["main"]["r_median"] == pytest.approx(1.0, abs=0.03)
        assert result["calibration"]["epsilon_stable_median"] == pytest.approx(
            0.35, abs=0.02)
        assert all(result["main"]["passes_by_seed"].values())
        json.dumps(result)                  # sérialisable pour results/

    def test_rapport_exact_faux_sous_vrai(self):
        """R_confab réalisé exactement : faux 4/10, vrai 8/10 → 0.5 → FALSIFIED."""
        calib = calibrate_epsilon_stable(
            {s: _arm_traces({"target_vrai": 8, "control_alea": 1})
             for s in range(5)}, k_features=2)
        main = {s: _arm_traces({"confab_faux": 4}) for s in range(5)}
        result = run_analysis(calib, main, k_features=2)
        assert result["verdict"] == "FALSIFIED"
        for r in result["main"]["r_confab_by_seed"].values():
            assert r == pytest.approx(0.5, abs=0.03)

    def test_graine_degeneree_comptee_non_passante(self):
        """Une graine à calibration dégénérée fait échouer le 5/5 même en bande."""
        traces = {0: _arm_traces({"target_vrai": 2, "control_alea": 8}),  # dégénérée
                  1: _arm_traces({"target_vrai": 8, "control_alea": 1}),
                  2: _arm_traces({"target_vrai": 9, "control_alea": 1}),
                  3: _arm_traces({"target_vrai": 7, "control_alea": 2}),
                  4: _arm_traces({"target_vrai": 8, "control_alea": 2})}
        calib = calibrate_epsilon_stable(traces, k_features=2)
        main = {s: _arm_traces({"confab_faux": 8}) for s in range(5)}
        result = run_analysis(calib, main, k_features=2)
        assert result["main"]["passes_by_seed"][0] is False
        assert result["verdict"] == "INCONCLUSIF"
