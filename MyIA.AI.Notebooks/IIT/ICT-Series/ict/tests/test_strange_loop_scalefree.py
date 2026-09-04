"""Tests unitaires pour ``ict.strange_loop_scalefree`` (case 8c, #8182).

Pins du pre-enregistrement (commit ``a0dc764023``, ANTERIEUR au jouet)
et du resultat mesure le 2026-09-02. Trois choses y sont epinglees, et
la premiere est un echec :

  1. **P1 seconde a echoue par sa face NEGATIVE**, et le verdict scelle
     ``INSTRUMENT_INVALIDE`` est conserve tel quel. La face positive
     tient (``T`` exactement invariant sous ``err -> c.err``, 25/25
     bras) ; la face negative predisait que l'ANCIENNE metrique, elle,
     bougerait. Elle ne bouge pas -- et la demonstration tient en une
     ligne : son test est ``mean(errs[t-win:t]) < 1.2 . pre``, dont les
     DEUX membres sont multiplies par ``c``. Le controle etait
     **insatisfaisable par construction**. Ce n'est pas l'implementation
     qui trahit la definition, contrairement a ce que le
     pre-enregistrement affirmait : c'est la specification du controle
     qui etait fausse.

  2. Le controle CORRIGE est **additif**, et il est ecrit comme
     POST-HOC partout. Sous ``errs -> errs + k . pre`` l'ancien horizon
     retrecit de 33 a 48 % (5/5 graines, monotone) tandis que le temps
     de relaxation est **exactement** constant et le pic d'exces
     identique a l'arrondi flottant pres (1 ULP : l'identite
     ``(errs + k.pre) - (pre + k.pre) = errs - pre`` est exacte sur les
     reels, pas sur les doubles). Le defaut est la normalisation par la
     LIGNE DE BASE, pas par la PERTURBATION.

  3. La decouverte de substance : les surrogates de la case 8b ne sont
     **pas perturbes** par le shift. Leur erreur BAISSE (ratio post/pre
     de 0.49 a 0.72 sur 5/5 graines), avec un pic d'exces NEGATIF sur
     3/5. Mecanisme : le shift fait passer ``|beta|`` de 0.8 a 0.5, or
     ``beta . m_t`` -- le motif autonome, invisible au surrogate -- est
     precisement son erreur irreductible. Le shift retrecit son angle
     mort.

**Ce que ces tests n'affirment pas.** Aucun n'assert que P2 seconde est
confirmee. ``rho_beta_sf`` median vaut 12.5, ce qui ressemble a une
confirmation massive ; c'est un artefact de PLAFOND, exactement
symetrique de l'artefact de PLANCHER (0.07) de la case 8b sur les
memes traces. La nouvelle metrique a retourne le SIGNE de l'artefact
sans produire de mesure. Seule une troisieme quantite -- le ratio
post/pre, qui a un signe -- tranche.
"""

from __future__ import annotations

import numpy as np
import pytest

from ict.strange_loop_scalefree import (
    CATCHUP_FACTOR,
    WIN,
    baseline_offset_control,
    collect_trace,
    horizon_from_errs,
    relaxation,
    run_case8c,
    scale_invariance,
)
from ict.strange_loop_selfmodel import (
    CompositeSurrogate,
    LoopPolicy,
    SelfLoopModel,
    adaptation_horizon,
)
from ict.strange_loop_irreducible import (
    AutonomousPolicy,
    adaptation_horizon_irr,
)

ARMS_8B = ("c8b_loop", "c8b_surrogate", "c8b_noise")
ARMS_ALL = ARMS_8B + ("c8_loop", "c8_surrogate")


@pytest.fixture(scope="module")
def case8c() -> dict:
    return run_case8c()


class TestControleScellePremiereFace:
    """P1 seconde, face POSITIVE : elle tient, exactement."""

    def test_relaxation_exactement_invariante_tous_bras(self, case8c):
        assert case8c["summary"]["relaxation_invariant_all"] is True

    def test_invariance_est_exacte_pas_approchee(self):
        errs = collect_trace(SelfLoopModel(n_feat=8, seed=0),
                             LoopPolicy(n_feat=8, seed=1000), seed=0)
        base = relaxation(errs)["relaxation_time"]
        for c in (0.1, 10.0, 1e-3, 1e3):
            assert relaxation(errs * c)["relaxation_time"] == base

    def test_disruption_aussi_sans_echelle(self):
        errs = collect_trace(SelfLoopModel(n_feat=8, seed=2),
                             LoopPolicy(n_feat=8, seed=1002), seed=2)
        base = relaxation(errs)["disruption"]
        for c in (0.1, 10.0):
            assert relaxation(errs * c)["disruption"] == pytest.approx(base)


class TestControleScelleSecondeFaceEchouee:
    """P1 seconde, face NEGATIVE : elle echoue, et le verdict reste."""

    def test_ancienne_metrique_na_pas_bouge(self, case8c):
        assert case8c["summary"]["old_metric_moved_any"] is False

    def test_verdict_scelle_conserve(self, case8c):
        # Le verdict est celui que la regle pre-enregistree calcule.
        # Il n'est PAS reecrit apres coup, meme si la cause en est une
        # erreur de specification et non un defaut d'instrument.
        assert case8c["summary"]["instrument_valid"] is False
        assert case8c["summary"]["verdict"] == "INSTRUMENT_INVALIDE"

    def test_pourquoi_ancienne_metrique_est_invariante(self):
        # La demonstration, sur une trace reelle : les deux membres de
        # `mean(...) < 1.2 * pre` sont homogenes de degre 1 en errs.
        errs = collect_trace(SelfLoopModel(n_feat=8, seed=3),
                             LoopPolicy(n_feat=8, seed=1003), seed=3)
        base = horizon_from_errs(errs)
        for c in (0.1, 2.0, 10.0, 1e4):
            assert horizon_from_errs(errs * c) == base

    def test_le_controle_etait_insatisfaisable_par_construction(self):
        # Aucune trace, sur aucun bras, ne peut faire bouger l'ancienne
        # metrique multiplicativement. Le controle ne pouvait pas passer.
        rng = np.random.default_rng(0)
        for _ in range(5):
            errs = np.abs(rng.normal(1.0, 0.3, size=4000))
            assert scale_invariance(errs)["old_metric_moved"] is False


class TestControleAdditifPostHoc:
    """Le controle que P1 seconde aurait du specifier. POST-HOC."""

    def test_relaxation_stable_sur_tous_les_bras(self, case8c):
        assert case8c["summary"]["posthoc_offset_relaxation_stable"] == "25/25"

    def test_ancienne_metrique_bouge_sur_quinze_bras(self, case8c):
        assert case8c["summary"]["posthoc_offset_old_moved"] == "15/25"

    def test_les_dix_immobiles_sont_exactement_les_planchers(self, case8c):
        # Recoupement interne : les seuls bras que le decalage additif ne
        # fait pas bouger sont ceux DEJA poses sur la plus petite valeur
        # exprimable. L'ancienne metrique bouge donc 15/15 des bras qui
        # PEUVENT bouger -- les 10 exceptions sont l'artefact lui-meme.
        immobiles = [row[a] for row in case8c["rows"] for a in ARMS_ALL
                     if not row[a]["offset"]["old_metric_moved"]]
        assert len(immobiles) == 10
        assert all(arm["old_horizon"] == WIN for arm in immobiles)
        assert all(set(arm["offset"]["old_horizon"]) == {WIN}
                   for arm in immobiles)

    def test_horizon_retrecit_monotonement_relaxation_constante(self, case8c):
        # 5/5 graines sur le self-modele 8b : l'ancien horizon fond,
        # la relaxation ne bouge pas d'un pas, le pic est inchange (1 ULP).
        for row in case8c["rows"]:
            off = row["c8b_loop"]["offset"]
            old = off["old_horizon"]
            assert old[0] > old[1] > old[2], "graine %d" % row["seed"]
            assert len(set(off["relaxation_time"])) == 1
            pics = off["peak_excess"]
            assert pics[1] == pytest.approx(pics[0], rel=1e-12)
            assert pics[2] == pytest.approx(pics[0], rel=1e-12)

    def test_ampleur_du_retrecissement(self, case8c):
        # Entre 33 % et 48 % de perte, mesures le 2026-09-02.
        pertes = [1.0 - row["c8b_loop"]["offset"]["old_horizon"][2]
                  / row["c8b_loop"]["offset"]["old_horizon"][0]
                  for row in case8c["rows"]]
        assert min(pertes) == pytest.approx(0.333, abs=0.02)
        assert max(pertes) == pytest.approx(0.482, abs=0.02)

    def test_le_decalage_se_soustrait_de_lexces(self):
        # La raison analytique : excess = s(t) - pre, et le decalage
        # entre dans les deux termes.
        errs = collect_trace(SelfLoopModel(n_feat=8, seed=0),
                             AutonomousPolicy(n_feat=8, seed=1000,
                                              motive_std=0.6), seed=0)
        out = baseline_offset_control(errs)
        assert out["relaxation_stable"] is True
        # Exact sur les reels, a 1 ULP pres sur les doubles.
        for pic in out["peak_excess"][1:]:
            assert pic == pytest.approx(out["peak_excess"][0], rel=1e-12)

    def test_controle_posthoc_ne_peut_produire_aucun_verdict(self):
        # Garde structurel (Tell c.850-L4) : la fonction ne rend que des
        # nombres, aucune cle de verdict.
        errs = collect_trace(SelfLoopModel(n_feat=8, seed=1),
                             LoopPolicy(n_feat=8, seed=1001), seed=1)
        out = baseline_offset_control(errs)
        assert "verdict" not in out
        assert not any("confirm" in k.lower() for k in out)


class TestPerturbationAbsente:
    """La decouverte de substance : le shift n'ABIME PAS les surrogates."""

    def test_surrogates_8b_non_perturbes_sur_trois_graines(self, case8c):
        counts = case8c["summary"]["posthoc_unperturbed_counts"]
        assert counts["c8b_surrogate"] == 3
        assert counts["c8b_noise"] == 3

    def test_self_modele_8b_toujours_perturbe(self, case8c):
        assert case8c["summary"]["posthoc_unperturbed_counts"]["c8b_loop"] == 0

    def test_erreur_des_surrogates_8b_baisse_apres_le_shift(self, case8c):
        # 5/5 graines : ratio post/pre entre 0.49 et 0.72. L'erreur est
        # DIVISEE, pas augmentee -- il n'y a rien a rattraper.
        for row in case8c["rows"]:
            r = row["c8b_surrogate"]["post_shift_ratio"]
            assert 0.45 < r < 0.75, "graine %d : %r" % (row["seed"], r)

    def test_case8_ne_montre_pas_cette_baisse(self, case8c):
        # Contraste : sous politique DETERMINISTE, pas de motif autonome,
        # donc pas d'angle mort a retrecir. Ratio ~1.
        med = case8c["summary"]["posthoc_post_shift_ratio_median"]
        assert med["c8_loop"] == pytest.approx(1.05, abs=0.06)
        assert med["c8_surrogate"] == pytest.approx(1.03, abs=0.06)
        assert med["c8b_surrogate"] == pytest.approx(0.53, abs=0.06)

    def test_pic_negatif_implique_non_perturbe(self, case8c):
        for row in case8c["rows"]:
            for a in ARMS_ALL:
                arm = row[a]
                if arm["peak_excess"] <= 0.0:
                    assert arm["perturbed"] is False
                    assert arm["disruption"] == 0.0

    def test_les_deux_graines_perturbees_le_sont_trivialement(self, case8c):
        # Meme la ou peak > 0, il vaut ~0.017 contre ~0.4 pour le lacet :
        # un ordre de grandeur et demi d'ecart.
        pics_surr = [row["c8b_surrogate"]["peak_excess"]
                     for row in case8c["rows"]
                     if row["c8b_surrogate"]["perturbed"]]
        pics_loop = [row["c8b_loop"]["peak_excess"] for row in case8c["rows"]]
        assert max(pics_surr) < 0.03
        assert min(pics_loop) > 0.29


class TestArtefactRetourneNonInterprete:
    """L'ancienne metrique disait 0.07, la nouvelle dit 12.5. Ni l'une
    ni l'autre n'est une vitesse."""

    def test_rho_pinne_mais_non_lu_comme_confirmation(self, case8c):
        s = case8c["summary"]
        assert s["rho_beta_sf_median"] == pytest.approx(12.5, abs=0.5)
        # P2 seconde exigeait >= 4/5. Meme sans les deux gardes, le
        # compte ne l'atteint pas.
        assert s["rho_beta_sf_ge3_count"] == 3
        assert s["verdict"] != "CONFIRMED"

    def test_le_rho_est_porte_par_le_plafond(self, case8c):
        # 2000 = toute la queue de trajectoire : la valeur rendue quand
        # un bras n'est pas perturbe. Ce n'est pas une lenteur.
        med = case8c["summary"]["relaxation_median"]
        assert med["c8b_surrogate"] == 2000.0
        assert med["c8b_noise"] == 2000.0
        assert case8c["summary"]["ceiling_counts"]["c8b_surrogate"] == 3

    def test_degenerescence_se_declenche_independamment(self, case8c):
        # Deuxieme garde, distinct du controle d'instrument : meme si
        # P1 seconde avait tenu, le verdict serait INCONCLUSIF.
        assert case8c["summary"]["all_perturbed"] is False
        assert case8c["summary"]["instrument_degenerate"] is True


class TestTemoinCase8:
    """Le null (e) du pre-enregistrement : il ne se declenche PAS."""

    def test_case8_garde_son_verdict_publie(self, case8c):
        # rho_old publie (PR #12942) = 1.0 ; rho_sf mesure ici = 1.0.
        # La falsification de la case 8 survit au changement de metrique.
        assert case8c["summary"]["rho_beta_sf_case8_median"] == pytest.approx(
            1.0, abs=0.35)

    def test_case8_reste_a_egalite_sur_les_deux_axes(self, case8c):
        d = case8c["summary"]["disruption_median"]
        assert d["c8_loop"] == pytest.approx(d["c8_surrogate"], rel=0.15)


class TestFideliteDeLaTrace:
    """La comparaison porte sur les MEMES nombres, pas sur deux runs."""

    def test_reproduit_lancienne_metrique_case8(self):
        for seed in range(3):
            ref = adaptation_horizon(SelfLoopModel(n_feat=8, seed=seed),
                                     LoopPolicy(n_feat=8, seed=seed + 1000),
                                     seed=seed)["adaptation_horizon"]
            errs = collect_trace(SelfLoopModel(n_feat=8, seed=seed),
                                 LoopPolicy(n_feat=8, seed=seed + 1000),
                                 seed=seed)
            assert horizon_from_errs(errs) == ref

    def test_reproduit_lancienne_metrique_case8b(self):
        for seed in range(3):
            ref = adaptation_horizon_irr(
                CompositeSurrogate(n_feat=8, seed=seed),
                AutonomousPolicy(n_feat=8, seed=seed + 1000, motive_std=0.6),
                seed=seed)["adaptation_horizon"]
            errs = collect_trace(
                CompositeSurrogate(n_feat=8, seed=seed),
                AutonomousPolicy(n_feat=8, seed=seed + 1000, motive_std=0.6),
                seed=seed)
            assert horizon_from_errs(errs) == ref


class TestLimiteDeLaNouvelleMetrique:
    """Retirer la confusion d'echelle n'a pas retire toute limite."""

    def test_case8_est_sous_resolue_par_la_fenetre(self, case8c):
        # Les bras de la case 8 relaxent en 8-10 pas, sous la fenetre de
        # lissage (50) : la nouvelle metrique a SON propre plancher.
        med = case8c["summary"]["relaxation_median"]
        assert med["c8_loop"] <= WIN
        assert med["c8_surrogate"] <= WIN
        assert case8c["summary"]["floor_counts"]["c8_loop"] == 5

    def test_le_plancher_est_annonce_pas_masque(self, case8c):
        # Il est porte par la meme cle que celle de la case 8b, pour
        # etre lu de la meme facon.
        for row in case8c["rows"]:
            arm = row["c8_loop"]
            assert arm["at_floor"] == (arm["relaxation_time"] <= WIN)


class TestSanity:
    def test_determinisme_par_graine(self):
        a = run_case8c(n_seeds=2)["summary"]
        b = run_case8c(n_seeds=2)["summary"]
        assert a == b

    def test_recherche_demarre_au_pic_pas_au_shift(self):
        errs = collect_trace(SelfLoopModel(n_feat=8, seed=0),
                             AutonomousPolicy(n_feat=8, seed=1000,
                                              motive_std=0.6), seed=0)
        out = relaxation(errs)
        assert out["T"] >= out["t_peak"]

    def test_constantes_reprises_de_lancienne_metrique(self):
        assert WIN == 50
        assert CATCHUP_FACTOR == 1.2
