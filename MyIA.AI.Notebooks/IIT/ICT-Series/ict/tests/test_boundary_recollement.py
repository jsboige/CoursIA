"""Tests unitaires pour ``ict.boundary_recollement`` (case 14, #8182 iceberg L3 — Emilsson, seconde opérationnalisation).

Pins des prédictions pré-enregistrées (commentaire #8182 c.5709451880,
re-verrouillées v2 le 2026-09-17T06:55Z c.5709502555 — l'instrument v1
ρ*=0.6 s'effondrait en une composante sur 2/5 seeds S2, ratios `inf`
de garde = PAS une preuve ; v2 : ρ*=0.75 + REJET_PROTOCOLE sur
effondrement, jamais compté comme pass. Mesurées le 2026-09-17 —
5 seeds 0/1/7/42/99, T=400, M_null=200) :

  1. (P1, mécanique) D({tout}) = 0 EXACT pour tout substrat, tout seed —
     une partition à une partie n'a pas de couture.
  2. (P2, S1) ratio_topo ∈ [0.75, 1.30] sur 5/5 seeds — frontière
     topologique coupant un broadcast pur : INVISIBLE au recollement.
  3. (P3, S2) ratio_func ≥ 1.50 sur 5/5 seeds — frontière dispersée
     alignée sur la cause locale : VISIBLE (le recollement suit la
     cause commune, pas la connectivité de champ).
  4. (P4, S3 CTRL) ratio_topo ≥ 1.50 sur 5/5 seeds — frontière alignée
     (cause + topologie d'accord) : détectée.
  5. (S2 punchline) B_topo(S2) = {tout} — la topologie de champ ne trace
     AUCUNE frontière là où le recollement en punit une fonctionnelle.
  6. (Sanity) déterminisme par seed ; tailles des partitions nulles
     appariées ; corrélations empiriques dans les bandes théoriques
     (within-H > rho* > cross pour S2/S3).
"""

import numpy as np
import pytest

from ict.boundary_recollement import (
    BAND_INVISIBLE,
    MIN_VISIBLE,
    M_NULL,
    RHO_STAR,
    SEEDS,
    T_STEPS,
    boundary_case,
    build_substrate,
    connected_components,
    field_topology_boundary,
    functional_boundary,
    matched_random_null,
    partition_reading_divergence,
    run_case14_protocol,
    simulate,
)


class TestP1Mecanique:
    def test_partition_une_partie_divergence_nulle_exacte(self):
        for kind in ("s1_topo_split_broadcast", "s2_scattered_cause",
                     "s3_ctrl_aligned"):
            X = simulate(build_substrate(kind), seed=0)
            d = partition_reading_divergence(X, [[i for i in range(X.shape[1])]])
            assert d == 0.0, f"{kind}: D({{tout}}) = {d} != 0 exact"


class TestConstruction:
    def test_s1_topologie_deux_composantes_broadcast_pur(self):
        sub = build_substrate("s1_topo_split_broadcast")
        parts = field_topology_boundary(sub)
        assert [len(p) for p in parts] == [4, 8]
        assert (sub.L[:, 1] == 0).all()  # f1 éteint : broadcast pur

    def test_s2_topologie_une_composante_cause_dispersee(self):
        sub = build_substrate("s2_scattered_cause")
        parts = field_topology_boundary(sub)
        assert len(parts) == 1  # le champ est uniformément connexe
        assert sorted(sub.local_set) == list(range(0, 12, 2))

    def test_s3_topologie_et_cause_alignees(self):
        sub = build_substrate("s3_ctrl_aligned")
        parts = field_topology_boundary(sub)
        assert [len(p) for p in parts] == [6, 6]
        assert sorted(sub.local_set) == parts[0]  # f1 charge exactement R


class TestPredictions:
    def test_p2_s1_frontiere_topo_invisible(self):
        ratios = [boundary_case("s1_topo_split_broadcast", s)["ratio_topo"]
                  for s in SEEDS]
        lo, hi = BAND_INVISIBLE
        assert all(lo <= r <= hi for r in ratios), ratios

    def test_p3_s2_frontiere_fonctionnelle_visible(self):
        ratios = [boundary_case("s2_scattered_cause", s)["ratio_func"]
                  for s in SEEDS]
        # v2 : un effondrement de règle (ratio None) invalide la prédiction
        assert all(r is not None for r in ratios), \
            f"REJET_PROTOCOLE : {ratios}"
        assert all(r >= MIN_VISIBLE for r in ratios), ratios

    def test_p4_s3_controle_positif_visible(self):
        ratios = [boundary_case("s3_ctrl_aligned", s)["ratio_topo"]
                  for s in SEEDS]
        assert all(r is not None for r in ratios), \
            f"REJET_PROTOCOLE : {ratios}"
        assert all(r >= MIN_VISIBLE for r in ratios), ratios

    def test_v2_regle_effondree_rend_none_pas_inf(self):
        # garde anti-self-gaming : ratio indéfini = None, jamais inf
        case = boundary_case("s2_scattered_cause", seed=0)
        for key in ("ratio_topo", "ratio_func"):
            r = case[key]
            assert r is None or np.isfinite(r), (key, r)

    def test_s2_punchline_topo_ne_trace_rien(self):
        case = boundary_case("s2_scattered_cause", seed=0)
        assert len(case["parts_topo"]) == 1
        assert case["d_topo"] == 0.0


class TestSanity:
    def test_determinisme_par_seed(self):
        a = boundary_case("s2_scattered_cause", seed=7)
        b = boundary_case("s2_scattered_cause", seed=7)
        assert a == b

    def test_null_apparie_en_tailles(self):
        sub = build_substrate("s1_topo_split_broadcast")
        X = simulate(sub, seed=1)
        rng = np.random.default_rng(1)
        # le null du null : mêmes tailles -> mêmes tailles (par construction)
        d = matched_random_null(X, [4, 8], m_null=20, seed=2)
        assert d > 0.0  # un split aléatoire 4+8 a une divergence non nulle

    def test_correlations_empiriques_dans_les_bandes(self):
        # within-H > rho* > cross (S2) : la règle fonctionnelle sépare H
        sub = build_substrate("s2_scattered_cause")
        X = simulate(sub, seed=0, t_steps=4000)  # T long : corr stable
        corr = np.corrcoef(X, rowvar=False)
        H = list(range(0, 12, 2))
        Hc = [i for i in range(12) if i not in H]
        within = np.mean([corr[i, j] for i in H for j in H if i < j])
        cross = np.mean([corr[i, j] for i in H for j in Hc])
        assert within > RHO_STAR > cross, (within, cross)

    def test_composantes_connexes_bfs_canonique(self):
        adj = np.array([[0.0, 0.9, 0.1], [0.9, 0.0, 0.1], [0.1, 0.1, 0.0]])
        assert connected_components(adj, 0.5) == [[0, 1], [2]]

    def test_protocole_complet_verdicts(self):
        out = run_case14_protocol()
        assert out["cases"]["s1"]["verdict"].startswith("INVISIBLE")
        assert out["cases"]["s2"]["verdict"].startswith("VISIBLE")
        assert out["cases"]["s3"]["verdict"].startswith("VISIBLE")
        assert out["seeds"] == list(SEEDS) and T_STEPS == 400 and M_NULL == 200


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
