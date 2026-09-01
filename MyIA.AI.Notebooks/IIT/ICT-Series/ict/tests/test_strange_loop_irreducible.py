"""Tests unitaires pour ``ict.strange_loop_irreducible`` (case 8b, #8182).

Pins des prédictions pré-enregistrées (commit ``85dbca6364``, antérieur
au jouet) et du résultat mesuré le 2026-09-02 :

  0. (Contrôle) la manipulation a pris : ``residual_share`` médian
     **0.35 > 0.30**. La même sonde appliquée à la politique
     *déterministe* de la case 8 rend **0.0000** — le contrôle a donc
     un négatif, il ne se contente pas d'un positif.
  1. (P1') fermeture : médiane ``d*`` <= 12, >= 4/5 graines
     (mesuré : médiane 8.0, 4/5).
  2. (P2'/P3') **NON MESURABLES**. Les deux surrogates se posent sur le
     PLANCHER de l'échelle d'horizon (50 = plus petite valeur
     exprimable, la recherche démarrant à ``shift_step + 50``) sur
     **5/5** graines, le self-modèle sur **0/5**. ``rho_beta`` et
     ``kappa`` ne comparent alors pas des vitesses, mais des largeurs
     de seuil : la métrique normalise chaque modèle sur SA PROPRE
     asymptote pré-shift, et la manipulation fait diverger ces
     asymptotes d'un facteur ~2.9.
  3. (Contraste) la case 8, re-mesurée dans le même run, a des
     asymptotes **à égalité** (ratio ~1.00) et **aucun** bras au
     plancher. Sa falsification était donc une vraie mesure ; c'est la
     case 8b qui casse l'instrument — et elle le casse *parce que* la
     manipulation a réussi.

**Ce que ces tests n'affirment pas.** Aucun n'assert que P2' est
falsifiée. ``rho_beta`` médian vaut 0.07, ce qui *ressemble* à une
falsification massive en sens inverse ; c'est un artefact de plancher,
et le pinner comme un résultat serait la faute même que la case 8b
devait corriger. Ils pinnent la valeur **et** la dégénérescence qui
interdit de la lire.
"""

from __future__ import annotations

import numpy as np
import pytest

from ict.strange_loop_irreducible import (
    AutonomousPolicy,
    NoiseChannelSurrogate,
    adaptation_horizon_irr,
    irreducibility_share,
    run_case8b,
)
from ict.strange_loop_selfmodel import LoopPolicy, SelfLoopModel, run_case8


@pytest.fixture(scope="module")
def case8b() -> dict:
    """Protocole complet 5 graines — déterministe, partagé entre gates."""
    return run_case8b()


class TestControleManipulation:
    """La variable sous test a-t-elle bougé ? Mesurée, jamais supposée."""

    def test_residual_share_au_dessus_du_seuil(self, case8b):
        med = case8b["summary"]["residual_share_median"]
        assert med > 0.30, (
            f"manipulation non établie : residual_share médian = {med:.3f}"
        )

    def test_manipulation_took_coherent(self, case8b):
        assert case8b["summary"]["manipulation_took"]

    def test_negatif_du_controle_politique_deterministe(self):
        """La sonde rend 0 quand l'action EST une fonction de l'état.

        Sans ce négatif, ``residual_share > 0.30`` ne prouverait rien :
        une sonde qui rendrait toujours du résiduel passerait le gate
        sur n'importe quelle politique.
        """
        for s in range(3):
            d = irreducibility_share(LoopPolicy(seed=s + 1000), seed=s)
            assert d["residual_share"] < 1e-3, (
                f"seed {s} : la politique case 8 est déterministe en x, "
                f"résiduel attendu ~0, mesuré {d['residual_share']:.4f}"
            )

    def test_positif_du_controle_politique_autonome(self):
        for s in range(3):
            d = irreducibility_share(AutonomousPolicy(seed=s + 1000), seed=s)
            assert d["residual_share"] > 0.05, (
                f"seed {s} : motif autonome non détecté "
                f"({d['residual_share']:.4f})"
            )


class TestP1Fermeture:
    """Seule prédiction pré-enregistrée que l'instrument sait trancher."""

    def test_d_star_mediane_basse(self, case8b):
        med = case8b["summary"]["d_star_median"]
        assert med <= 12.0, f"P1' rompu : médiane d* = {med}"

    def test_d_star_4_sur_5(self, case8b):
        n = case8b["summary"]["d_star_le12_count"]
        assert n >= 4, f"P1' rompu : {n}/5 graines seulement sous 12"

    def test_kink_saturation(self, case8b):
        n = case8b["summary"]["kink_saturation_count"]
        assert n >= 4, f"kink rompu : {n}/5 graines seulement saturées"


class TestInstrumentDegenere:
    """Le cœur du résultat : pourquoi P2'/P3' ne sont pas mesurables."""

    def test_verdict_est_inconclusif_instrument(self, case8b):
        v = case8b["summary"]["verdict"]
        assert v == "INCONCLUSIF_INSTRUMENT", (
            f"verdict enregistré (INCONCLUSIF_INSTRUMENT) != mesure ({v}) "
            f"— le jouet a dérivé, ré-enregistrer"
        )

    def test_surrogates_au_plancher_5_sur_5(self, case8b):
        s = case8b["summary"]
        assert s["floor_surrogate_count"] == 5, s["floor_surrogate_count"]
        assert s["floor_noise_count"] == 5, s["floor_noise_count"]

    def test_self_modele_jamais_au_plancher(self, case8b):
        """L'asymétrie est le fait décisif : ce n'est pas un bruit global."""
        assert case8b["summary"]["floor_loop_count"] == 0

    def test_horizon_surrogate_est_bien_la_valeur_minimale(self, case8b):
        """50 n'est pas « rapide », c'est le plus petit chiffre exprimable."""
        for r in case8b["rows"]:
            assert r["surrogate_beta"]["adaptation_horizon"] == 50
            assert r["noise_beta"]["adaptation_horizon"] == 50
            assert r["loop_beta"]["adaptation_horizon"] > 100

    def test_asymptotes_divergentes(self, case8b):
        ratio = case8b["summary"]["pre_err_ratio_median"]
        assert ratio > 2.0, (
            f"les asymptotes ne divergent plus (ratio {ratio:.2f}) : "
            f"le diagnostic de dégénérescence ne tient plus"
        )

    def test_ratios_pinnes_mais_non_interpretes(self, case8b):
        """PIN de la valeur mesurée — SANS en faire une falsification.

        ``rho_beta`` médian ~0.07 et ``kappa`` == 1.0 exactement : deux
        signatures de plancher, pas deux résultats.
        """
        s = case8b["summary"]
        assert s["rho_beta_ge3_count"] == 0
        assert s["rho_beta_median"] < 0.2
        assert s["kappa_median"] == 1.0, (
            "kappa exactement 1.0 = les deux surrogates au même plancher ; "
            "toute autre valeur voudrait dire que le plancher a bougé"
        )


class TestContrasteAvecCase8:
    """L'instrument casse *parce que* la manipulation a réussi."""

    def test_case8_sans_plancher_ni_divergence(self):
        base = run_case8()
        ratio = [x["surrogate_beta"]["pre_median_err"]
                 / max(x["loop_beta"]["pre_median_err"], 1e-12)
                 for x in base["rows"]]
        assert 0.8 < float(np.median(ratio)) < 1.25, (
            "case 8 : asymptotes attendues à égalité (~1.00)"
        )
        for x in base["rows"]:
            assert x["surrogate_beta"]["adaptation_horizon"] > 50, (
                "case 8 : aucun bras ne devrait toucher le plancher — "
                "sa falsification était une vraie mesure"
            )


class TestSanity:
    def test_politique_est_stateful(self):
        pol = AutonomousPolicy(seed=7)
        assert pol.act(0.4) != pol.act(0.4), (
            "le motif interne doit avancer à chaque act"
        )

    def test_vue_gelee_est_une_carte(self):
        """``closure_depth`` itère une CARTE : elle doit être sans état."""
        frozen = AutonomousPolicy(seed=7).frozen(0.0)
        assert frozen.act(0.4) == frozen.act(0.4)

    def test_vue_gelee_ignore_le_motif_courant(self):
        pol = AutonomousPolicy(seed=7)
        pol.m = 12.0
        assert np.isclose(pol.frozen(0.0).act(0.3), pol.state_part(0.3))

    def test_determinisme_par_graine(self):
        a = run_case8b(n_seeds=2)["summary"]
        b = run_case8b(n_seeds=2)["summary"]
        assert a == b

    def test_noise_surrogate_aveugle_a_l_action(self):
        s = NoiseChannelSurrogate(seed=0)
        s.u[:] = 1.0
        assert s.predict(0.3, 0.0) == s.predict(0.3, 5.0)

    def test_noise_surrogate_a_bien_un_canal_exogene(self):
        s = NoiseChannelSurrogate(seed=0)
        s.u[:] = 1.0
        s.new_step()
        first = s.predict(0.3, 0.0)
        s.new_step()
        assert s.predict(0.3, 0.0) != first, (
            "le canal z doit être re-tiré à chaque new_step"
        )

    def test_horizon_self_modele_non_censure(self, case8b):
        """Le bras qui EST mesuré ne doit pas être censuré au cap."""
        for r in case8b["rows"]:
            assert r["loop_beta"]["caught_up"], (
                f"graine {r['seed']} : horizon self au cap — censure"
            )

    def test_hook_new_step_optionnel(self):
        """``adaptation_horizon_irr`` accepte un modèle sans canal exogène."""
        r = adaptation_horizon_irr(SelfLoopModel(seed=1),
                                   AutonomousPolicy(seed=1001), seed=1)
        assert r["adaptation_horizon"] > 0
