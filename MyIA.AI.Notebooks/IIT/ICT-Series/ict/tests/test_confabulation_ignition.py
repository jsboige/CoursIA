"""Tests unitaires pour ``ict.confabulation_ignition`` (case 15, #8182 —
confabulation, « W diffuse un q erroné », SECONDE opérationnalisation après
case 3 #15915 SAE INCONCLUSIF PAR CONSTRUCTION — re-scope c.5709770262).

Pins des prédictions pré-enregistrées (commentaire #8182 c.5709692119,
2026-09-17T06:00:27Z ; amendement v1→v2 c.5709716652 AVANT re-run — P1
stricte insatisfiable par construction au plafond, P5 bras vrai saturé ;
mesures v2 du 2026-09-17, 5 graines 0/1/7/42/99) :

  1. (P1) propa(b) non-croissante sur la grille b ∈ {0,2,4,6,8,16} ET
     chute totale ≥ 0.80 — 5/5 graines (dose-réponse).
  2. (P2, consécration — la prédiction de la ligne matrice) CF =
     propa(b=2)/propa(b=0) ≥ 0.80 — 5/5 graines (mesuré 0.917-1.000,
     médiane 0.938).
  3. (P3, dissociation vs null — le tueur de la ligne matrice) Δ =
     propa(b=2) − médiane propa(aléatoire) ≥ 0.15 — 5/5 graines
     (mesuré +0.500 à +0.542).
  4. (P4, contrôle de rejet) propa(b=16) = 0 ≤ null − 0.10 — 5/5 graines :
     l'inversion globale est rejetée, la porte contenu fonctionne dans les
     deux sens.
  5. (P5 v2, gain d'ignition) propa(aléatoire, β=0) ≈ 0.19-0.23 ≤
     médiane null − 0.15 ≈ 0.42 — 5/5 graines. Le bras vrai sature
     (adoption locale seule 0.917-1.000) : redondance des canaux à ce SNR,
     rapportée comme donnée.
  6. (Sanity) déterminisme par seed ; sous-ensembles sans remise ;
     null borné loin de 0 et de 1 (aucune dégénérescence de ratio) ;
     garde REJET_PROTOCOLE (monde sourd σ=50 → propa(vrai) < 0.70).
"""

import numpy as np
import pytest

from ict.confabulation_ignition import (
    BETA_IGNITION,
    CF_CONFIRM,
    DELTA_MIN,
    DOSE_FLIPS,
    M_NULL,
    MIN_TRUE_PROPA,
    N_CONSUMERS,
    N_LATENTS,
    P4_MARGIN,
    P5_LIFT,
    SEEDS,
    SUBSET_SIZE,
    THETA_ADOPT,
    TOTAL_DROP_MIN,
    build_world,
    false_content,
    propagation_rate,
    random_contents,
    random_null_median,
    run_case15,
    run_case15_protocol,
)


class TestRuleAdoption:
    def test_score_et_seuil_sur_monde_artisanal(self):
        # 2 consommateurs x 1 latent (via subsets dupliqués) : aligné adopte,
        # anti-aligné refuse — l'adoption est la règle score > theta.
        w = build_world(0)
        z = np.ones(N_LATENTS)
        aligned = np.ones(N_LATENTS)
        anti = -np.ones(N_LATENTS)
        p_up = propagation_rate(w, aligned)
        p_down = propagation_rate(w, anti)
        assert p_up > p_down

    def test_beta_zero_baisse_toujours_ladoption(self):
        w = build_world(3)
        c = false_content(w.z, 2)
        assert propagation_rate(w, c, beta=0.0) <= propagation_rate(w, c)


class TestConstruction:
    def test_false_content_inverse_exactement_b_bits(self):
        z = np.array([1.0, -1.0] * 8)
        for b in DOSE_FLIPS:
            c = false_content(z, b)
            assert (c[:b] == -z[:b]).all()
            assert (c[b:] == z[b:]).all()

    def test_subsets_taille_sans_remise(self):
        w = build_world(5)
        assert w.subsets.shape == (N_CONSUMERS, SUBSET_SIZE)
        for row in w.subsets:
            assert len(set(row.tolist())) == SUBSET_SIZE

    def test_lectures_centrees_sur_le_vrai(self):
        # E[read] = z : le biais du canal local est nul par construction
        w = build_world(11)
        assert np.allclose(w.reads.mean(axis=0), w.z[w.subsets].mean(axis=0),
                           atol=0.2)


class TestPredictions:
    def test_p1_non_croissante_et_chute_totale(self):
        for s in SEEDS:
            dose = run_case15(s)["dose_curve"]
            seq = [dose[b] for b in DOSE_FLIPS]
            assert all(seq[i] >= seq[i + 1] for i in range(len(seq) - 1)), (s, seq)
            assert seq[0] - seq[-1] >= TOTAL_DROP_MIN, (s, seq)

    def test_p2_consecration_cf(self):
        for s in SEEDS:
            case = run_case15(s)
            assert case["cf"] is not None, f"REJET_PROTOCOLE inattendu : {s}"
            assert case["cf"] >= CF_CONFIRM, (s, case["cf"])

    def test_p3_dissociation_vs_null(self):
        for s in SEEDS:
            case = run_case15(s)
            assert case["delta"] is not None, f"REJET_PROTOCOLE inattendu : {s}"
            assert case["delta"] >= DELTA_MIN, (s, case["delta"])

    def test_p4_inversion_globale_rejetee(self):
        for s in SEEDS:
            case = run_case15(s)
            assert case["dose_curve"][16] <= case["null_median"] - P4_MARGIN, s

    def test_p5_ignition_eleve_le_contenu_sans_evidence(self):
        for s in SEEDS:
            case = run_case15(s)
            assert case["no_ignition_random"] <= case["null_median"] - P5_LIFT, s

    def test_amendement_v1_motivation_plafond_seed7(self):
        # pin de la motivation de l'amendement c.5709716652 : sur la graine 7,
        # le pas b0 -> b2 est EXACTEMENT plat (0.979 = 0.979) — événement de
        # résolution à N=48, pas une non-réponse de dose. Si ce test casse,
        # le flux RNG a changé : relire l'amendement avant tout re-seuillage.
        dose = run_case15(7)["dose_curve"]
        assert dose[0] == dose[2] == 47.0 / N_CONSUMERS  # 0.97917


class TestSanity:
    def test_determinisme_par_seed(self):
        assert run_case15(7) == run_case15(7)

    def test_null_borne_loin_de_0_et_de_1(self):
        # garde anti-dégénérescence : le null aléatoire est dans (0.2, 0.8)
        # sur toutes les graines — aucun ratio P2/P3 n'a de dénominateur mort
        for s in SEEDS:
            w = build_world(s)
            null = random_null_median(w, s)
            assert 0.2 < null < 0.8, (s, null)

    def test_garde_rejet_protocole_monde_sourd(self):
        # contrôle positif de la garde : un monde sourd (sigma=50) ne propage
        # même pas le contenu vrai -> serait REJET_PROTOCOLE, jamais compté
        w_deaf = build_world(0, sigma_read=50.0)
        assert propagation_rate(w_deaf, w_deaf.z) < MIN_TRUE_PROPA

    def test_random_contents_uniformes(self):
        rng = np.random.default_rng(0)
        cs = random_contents(rng, 500)
        assert cs.shape == (500, N_LATENTS)
        assert abs(cs.mean()) < 0.05  # iid uniforme ±1, centré

    def test_protocole_complet_verdict(self):
        out = run_case15_protocol()
        assert out["verdict"].startswith("CONFIRMED_CONSECRATION"), out["verdict"]
        assert out["rejected_seeds"] == []
        assert out["seeds"] == list(SEEDS)
        assert out["constants"]["beta_ignition"] == BETA_IGNITION
        assert out["constants"]["theta_adopt"] == THETA_ADOPT
        assert out["constants"]["m_null"] == M_NULL
        assert out["constants"]["dose_flips"] == list(DOSE_FLIPS)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
