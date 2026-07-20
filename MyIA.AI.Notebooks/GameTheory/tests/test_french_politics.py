"""Tests pour ``cooperative_games.french_politics`` (module application NFP 2024).

Couvre les contrats du module consommes par les notebooks GameTheory-15c
(Cooperative Games applique) et PIN specifiquement la correction de bug #7364
(signe inverse sur la "perte" RN dans ``analyze_barrage_effect``) afin qu'une
re-introduction de la regression soit detectee.

Le module est un module APPLICATIF (donnees reelles Ministere de l'Interieur
2024 + couches cooperative_games). Toute la logique testee est DETERMINISTE :
les fonctions de valeur (``seats_coalition_value`` etc.) ne font que composer
les constantes du module (``PARTIES_2024``, facteurs de synergie calibres) -> les
assertions sont des valeurs exactes calculees a la main, verifiees par execution
premiere (G.9), pas des invariants vagues.

Run with: pytest tests/test_french_politics.py -v
"""

import sys
from pathlib import Path

import numpy as np
import pytest

# Ajoute GameTheory/ au path pour importer le package cooperative_games
sys.path.insert(0, str(Path(__file__).parent.parent))

from cooperative_games.coalition_games import CoalitionGame, WeightedVotingGame  # noqa: E402
from cooperative_games.french_politics import (  # noqa: E402
    ABSOLUTE_MAJORITY,
    BARRAGE_EFFECT,
    NFP_TOTAL_SEATS,
    PARTIES_2024,
    SECOND_ROUND_RESULTS,
    TOTAL_SEATS,
    FrenchLeftCoalition2024,
    analyze_barrage_effect,
    analyze_coalition_dynamics,
    create_voting_game_assembly,
    get_2024_legislative_data,
    negotiation_value,
    seats_coalition_value,
    voting_power_value,
)


# Ordre canonique des partis (cf. FrenchLeftCoalition2024.PARTIES)
PARTIES = ['LFI', 'PS', 'EELV', 'PCF']
IDX = {p: i for i, p in enumerate(PARTIES)}  # LFI=0, PS=1, EELV=2, PCF=3


# --------------------------------------------------------------------------- #
#  Constantes + accessoires de donnees                                        #
# --------------------------------------------------------------------------- #

class TestConstants:
    """Les constantes politiques de 2024 (sources off. Ministere Interieur)."""

    def test_party_count(self):
        assert len(PARTIES_2024) == 4
        assert set(PARTIES_2024) == set(PARTIES)

    def test_majority_and_total_seats(self):
        # Assemblee nationale francaise : 577 sieges, majorite absolue = 289.
        assert TOTAL_SEATS == 577
        assert ABSOLUTE_MAJORITY == 289

    def test_estimated_alone_seats(self):
        # Estimations "seul" (sans front republicain) : LFI 40, PS 35, EELV 15, PCF 5.
        alone = {p: PARTIES_2024[p].estimated_alone_seats for p in PARTIES}
        assert alone == {'LFI': 40, 'PS': 35, 'EELV': 15, 'PCF': 5}

    def test_barrage_effect_rn_perte_is_negative(self):
        # RN_perte < 0 : le barrage coute des sieges au RN (convention de signe).
        assert BARRAGE_EFFECT['RN_perte'] < 0
        assert BARRAGE_EFFECT['NFP_benefice'] > 0

    def test_get_2024_legislative_data(self):
        data = get_2024_legislative_data()
        assert set(data) == set(PARTIES)
        # Chaque entree a les champs attendus.
        for p in PARTIES:
            assert data[p].short_name == p
            assert data[p].seats_won > 0
            assert 0 < data[p].first_round_pct < 30


# --------------------------------------------------------------------------- #
#  seats_coalition_value                                                       #
# --------------------------------------------------------------------------- #

class TestSeatsCoalitionValue:
    """seats_coalition_value : logique de synergie calibree deterministe."""

    def test_empty_coalition_zero(self):
        assert seats_coalition_value(set(), PARTIES) == 0.0

    def test_single_party_base_only(self):
        # n=1 : pas de synergie, return base (estimated_alone_seats).
        assert seats_coalition_value({IDX['LFI']}, PARTIES) == 40.0
        assert seats_coalition_value({IDX['PS']}, PARTIES) == 35.0
        assert seats_coalition_value({IDX['EELV']}, PARTIES) == 15.0
        assert seats_coalition_value({IDX['PCF']}, PARTIES) == 5.0

    def test_grand_coalition_nfp_total(self):
        # n=4 : coalition totale = resultat calibre NFP_TOTAL_SEATS (180).
        grand = set(IDX.values())
        assert seats_coalition_value(grand, PARTIES) == float(NFP_TOTAL_SEATS)
        assert seats_coalition_value(grand, PARTIES) == 180.0

    @pytest.mark.parametrize("pair,base,synergy,expected", [
        # expected = round(base * synergy, 1) — Python round (banker's) sur .1 decimal.
        ({'LFI', 'PCF'}, 40 + 5, 1.25, 56.2),
        ({'PS', 'EELV'}, 35 + 15, 1.30, 65.0),
        ({'LFI', 'PS'}, 40 + 35, 1.20, 90.0),
        ({'PS', 'PCF'}, 35 + 5, 1.22, 48.8),
        ({'LFI', 'EELV'}, 40 + 15, 1.18, 64.9),
        ({'EELV', 'PCF'}, 15 + 5, 1.15, 23.0),
    ])
    def test_two_party_synergy(self, pair, base, synergy, expected):
        coalition = {IDX[p] for p in pair}
        assert seats_coalition_value(coalition, PARTIES) == pytest.approx(expected)

    @pytest.mark.parametrize("missing,base,synergy,expected", [
        ('LFI', 35 + 15 + 5, 1.55, 85.2),    # PS+EELV+PCF, round(85.25,1)=85.2
        ('PS', 40 + 15 + 5, 1.42, 85.2),     # LFI+EELV+PCF
        ('EELV', 40 + 35 + 5, 1.60, 128.0),  # LFI+PS+PCF
        ('PCF', 40 + 35 + 15, 1.80, 162.0),  # LFI+PS+EELV (presque plein)
    ])
    def test_three_party_synergy(self, missing, base, synergy, expected):
        coalition = {IDX[p] for p in PARTIES if p != missing}
        assert len(coalition) == 3
        assert seats_coalition_value(coalition, PARTIES) == pytest.approx(expected)

    def test_grand_coalition_greater_than_any_subcoalition(self):
        # Monotonicite pedagogique : la grande coalition > toute sous-coalition.
        grand = set(IDX.values())
        full_value = seats_coalition_value(grand, PARTIES)
        from itertools import combinations
        for size in (1, 2, 3):
            for combo in combinations(IDX.values(), size):
                assert seats_coalition_value(set(combo), PARTIES) <= full_value


# --------------------------------------------------------------------------- #
#  voting_power_value + negotiation_value                                      #
# --------------------------------------------------------------------------- #

class TestVotingPowerValue:
    """voting_power_value : proportionnel, plafonne a 1.0."""

    def test_empty_zero(self):
        assert voting_power_value(set(), PARTIES) == 0.0

    def test_below_majority_proportional(self):
        # NFP (180 sieges) < 289 -> 180/289.
        grand = set(IDX.values())
        assert voting_power_value(grand, PARTIES) == pytest.approx(180 / 289)

    def test_single_party_small(self):
        assert voting_power_value({IDX['LFI']}, PARTIES) == pytest.approx(40 / 289)

    def test_capped_at_one(self):
        # Aucune sous-coalition du NFP n'atteint 289 -> toutes < 1.0 ; mais le
        # plafond 1.0 est verifie par construction (seats >= 289 -> 1.0).
        # On verifie que toutes les valeurs sont dans [0, 1].
        from itertools import combinations
        for size in (1, 2, 3, 4):
            for combo in combinations(IDX.values(), size):
                v = voting_power_value(set(combo), PARTIES)
                assert 0.0 <= v <= 1.0


class TestNegotiationValue:
    """negotiation_value : scaled 0-100, avec facteur d'unite decroissant."""

    def test_empty_zero(self):
        assert negotiation_value(set(), PARTIES) == 0.0

    def test_single_party_no_unity_penalty(self):
        # n=1 : unity=1.0, value = seats/TOTAL_SEATS * 100.
        v = negotiation_value({IDX['LFI']}, PARTIES)
        assert v == pytest.approx(40 / 577 * 1.0 * 100)

    def test_grand_coalition_has_internal_tension_penalty(self):
        # n=4 : unity=0.75 (tensions internes) -> penalite.
        grand = set(IDX.values())
        v = negotiation_value(grand, PARTIES)
        assert v == pytest.approx(180 / 577 * 0.75 * 100)

    def test_scales_with_seats(self):
        # Plus de sieges (parti seul > petit parti) -> plus de levier.
        lfi = negotiation_value({IDX['LFI']}, PARTIES)
        pcf = negotiation_value({IDX['PCF']}, PARTIES)
        assert lfi > pcf


# --------------------------------------------------------------------------- #
#  FrenchLeftCoalition2024                                                     #
# --------------------------------------------------------------------------- #

class TestFrenchLeftCoalition2024:
    """FrenchLeftCoalition2024 : sous-classe CoalitionGame deleguant aux fns de valeur."""

    @pytest.mark.parametrize("value_type", ['seats', 'voting_power', 'negotiation'])
    def test_construct_valid_value_types(self, value_type):
        game = FrenchLeftCoalition2024(value_type=value_type)
        assert isinstance(game, CoalitionGame)
        assert game.n_players == 4
        assert len(game.player_names) == 4

    def test_unknown_value_type_raises(self):
        with pytest.raises(ValueError, match="Unknown value type"):
            FrenchLeftCoalition2024(value_type='bogus')

    def test_characteristic_function_delegates_to_seats(self):
        # value_type='seats' -> game.value(S) == seats_coalition_value(S, PARTIES).
        game = FrenchLeftCoalition2024(value_type='seats')
        grand = set(IDX.values())
        assert game.value(grand) == seats_coalition_value(grand, PARTIES)
        assert game.value(set()) == 0.0
        assert game.value({IDX['LFI']}) == 40.0

    def test_player_names_are_full_names(self):
        game = FrenchLeftCoalition2024()
        # player_names = noms longs (pas les short codes).
        assert 'La France Insoumise' in game.player_names
        assert 'LFI' not in game.player_names

    def test_shapley_efficiency_on_seats_game(self):
        # Axiome d'efficacite de Shapley : sum(phi) == v(grand coalition).
        # Test d'integration leger (deja couvert pour shapley lui-meme ; ici on
        # verifie que le jeu NFP compose correctement avec shapley_value_exact).
        from cooperative_games.shapley import shapley_value_exact
        game = FrenchLeftCoalition2024(value_type='seats')
        shapley = shapley_value_exact(game)
        grand = set(IDX.values())
        assert len(shapley) == 4
        assert shapley.sum() == pytest.approx(game.value(grand))
        # Non-negativite (toutes les parties contribuent positivement dans ce jeu).
        assert (shapley >= 0).all()


# --------------------------------------------------------------------------- #
#  create_voting_game_assembly                                                 #
# --------------------------------------------------------------------------- #

class TestCreateVotingGameAssembly:
    """create_voting_game_assembly : WeightedVotingGame 5 blocs, quota 289."""

    def test_returns_game_and_banzhaf(self):
        game, banzhaf = create_voting_game_assembly()
        assert isinstance(game, WeightedVotingGame)
        assert isinstance(banzhaf, np.ndarray)

    def test_five_blocs_and_quota(self):
        game, _ = create_voting_game_assembly()
        assert game.n_players == 5
        # Quota = majorite absolue (289).
        assert game.quota == ABSOLUTE_MAJORITY

    def test_weights_match_assembly_composition(self):
        game, _ = create_voting_game_assembly()
        # NFP 182, Ensemble 168, LR 45, RN 143, Autres 39.
        assert sorted(game.weights) == sorted([182, 168, 45, 143, 39])

    def test_banzhaf_nonnegative(self):
        _, banzhaf = create_voting_game_assembly()
        assert len(banzhaf) == 5
        assert (banzhaf >= 0).all()


# --------------------------------------------------------------------------- #
#  analyze_barrage_effect — ★ REGRESSION PIN #7364                            #
# --------------------------------------------------------------------------- #

class TestAnalyzeBarrageEffect:
    """analyze_barrage_effect : ★ PIN de la correction #7364 (signe RN perte).

    Bug #7364 : le signe de la "perte" RN etait inverse, montrant le RN
    gagnant des sieges grace au barrage (contre-sens politique). La correction
    rend la perte POSITIVE (le barrage coute des sieges au RN). Ces tests
    echoueront si la regression est re-introduite.
    """

    def test_returns_string(self):
        out = analyze_barrage_effect()
        assert isinstance(out, str)
        assert len(out) > 0

    def test_rn_perte_is_positive_pin_7364(self):
        """★ Le RN PERD des sieges a cause du barrage (perte > 0).

        rn_without_barrage = 143 - int(143 * -0.15) = 143 - (-21) = 164
        perte = 164 - 143 = 21  (positive = sieges perdus).

        Ligne IMPACT exacte : '  RN:       143 sieges (~164 sans barrage, perte: 21)'.
        On filtre les lignes "sieges" (la section IMPACT), pas la 1re ligne RN
        (section DESISTEMENTS)."""
        out = analyze_barrage_effect()
        rn_line = next(l for l in out.splitlines() if "RN" in l and "sieges" in l)
        assert "perte:" in rn_line
        # Extraire la valeur de perte (la ligne finit par "...perte: 21)").
        import re
        m = re.search(r"perte:\s*\(?(-?\d+)\)?", rn_line)
        assert m, f"could not parse perte in: {rn_line!r}"
        perte_val = int(m.group(1))
        assert perte_val > 0, f"#7364 regression: RN perte must be positive, got {perte_val}"
        assert perte_val == 21  # valeur exacte: int(143*0.15)=21

    def test_nfp_and_ensemble_gain_from_barrage(self):
        """NFP et Ensemble GAGNENT des sieges grace au barrage (gain > 0).

        NFP: 182 - int(182*0.12)=161 -> gain +21
        Ensemble: 168 - int(168*0.08)=155 -> gain +13"""
        out = analyze_barrage_effect()
        nfp_line = next(l for l in out.splitlines() if "NFP" in l and "sieges" in l)
        ens_line = next(l for l in out.splitlines() if "Ensemble" in l and "sieges" in l)
        assert "gain: +21" in nfp_line
        assert "gain: +13" in ens_line

    def test_desistement_counts_present(self):
        out = analyze_barrage_effect()
        # Les desistements officiels par bloc doivent apparaitre.
        assert str(SECOND_ROUND_RESULTS['NFP']['withdrawals']) in out
        assert str(SECOND_ROUND_RESULTS['RN']['withdrawals']) in out


class TestAnalyzeCoalitionDynamics:
    """Couverture de ``analyze_coalition_dynamics`` (orchestrateur haut-niveau
    qui assemble Shapley + Core + convexite + tables pour les 3 fonctions de
    valeur). Non couvert avant ce test (0 ref dans le fichier). Les assertions
    portent sur le contrat structurel + l'invariant d'efficiency de Shapley
    (sum des valeurs == valeur de la grande coalition) — un invariant de game
    theory fondamental, pas un pin de valeur : si l'orchestration passait le
    mauvais game a ``shapley_value_exact`` ou melait les value_type,
    l'efficiency casserait. Valeurs confirmees par execution firsthand (G.9).
    """

    EXPECTED_KEYS = {
        "game", "shapley_values", "shapley_dict", "grand_coalition_value",
        "core_exists", "core_point", "is_convex", "analysis_text",
        "marginal_table",
    }

    @pytest.mark.parametrize("value_type", ["seats", "voting_power", "negotiation"])
    def test_returns_all_documented_keys(self, value_type):
        results = analyze_coalition_dynamics(value_type=value_type)
        assert set(results.keys()) == self.EXPECTED_KEYS

    @pytest.mark.parametrize("value_type", ["seats", "voting_power", "negotiation"])
    def test_shapley_efficiency_holds(self, value_type):
        """Invariant d'efficiency : sum(shapley_values) == grand_coalition_value.
        Propriete definissoire de la valeur de Shapley (efficiency = 1)."""
        results = analyze_coalition_dynamics(value_type=value_type)
        total = float(np.sum(results["shapley_values"]))
        gv = float(results["grand_coalition_value"])
        assert abs(total - gv) < 1e-6, (
            f"Shapley efficiency broken for value_type={value_type}: "
            f"sum={total}, grand_coalition_value={gv}"
        )

    @pytest.mark.parametrize("value_type", ["seats", "voting_power", "negotiation"])
    def test_shapley_dict_keys_are_the_four_parties(self, value_type):
        results = analyze_coalition_dynamics(value_type=value_type)
        assert set(results["shapley_dict"].keys()) == set(FrenchLeftCoalition2024.PARTIES)

    @pytest.mark.parametrize("value_type", ["seats", "voting_power", "negotiation"])
    def test_shapley_dict_values_match_shapley_values(self, value_type):
        """shapley_dict[PARTIES[i]] doit egaler shapley_values[i] (coherence
        entre les deux representations du meme calcul)."""
        results = analyze_coalition_dynamics(value_type=value_type)
        parties = FrenchLeftCoalition2024.PARTIES
        shapley = results["shapley_values"]
        for i, party in enumerate(parties):
            assert abs(results["shapley_dict"][party] - shapley[i]) < 1e-9

    @pytest.mark.parametrize("value_type", ["seats", "voting_power", "negotiation"])
    def test_core_and_convexity_are_bool(self, value_type):
        results = analyze_coalition_dynamics(value_type=value_type)
        assert isinstance(results["core_exists"], bool)
        assert isinstance(results["is_convex"], bool)

    @pytest.mark.parametrize("value_type", ["seats", "voting_power", "negotiation"])
    def test_narrative_tables_are_nonempty_strings(self, value_type):
        """analysis_text et marginal_table sont des rapports formates (str) ;
        vides = l'orchestration a saute la generation."""
        results = analyze_coalition_dynamics(value_type=value_type)
        assert isinstance(results["analysis_text"], str) and len(results["analysis_text"]) > 0
        assert isinstance(results["marginal_table"], str) and len(results["marginal_table"]) > 0


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
