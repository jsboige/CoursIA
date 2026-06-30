# -*- coding: utf-8 -*-
"""
Tests pour le module examples/kuhn_poker_cfr.py (Counterfactual Regret
Minimization sur Kuhn Poker). Module companion du notebook
GameTheory-13-ImperfectInfo-CFR.ipynb.

Kuhn Poker (Kuhn 1950) est le jeu de poker a information incomplete le plus
simple : 3 cartes (J < Q < K), ante de 1, P1 agit (Check/Bet) puis P2 repond.
C'est le cas d'ecole de la theorie des jeux a information incomplete, et CFR
(Zinkevich et al. 2007) est l'algorithme de reference pour y approcher un
equilibre de Nash en forme extensive.

Les tests assertent des INVARIANTS (le contrat du module + des resultats
theoriques connus), pas seulement l'absence de crash :

  - **Utilites terminales** : chaque feuille de l'arbre de jeu a une utilite
    deterministe verifiable a la main (showdown +/-1 ou +/-2, fold +1).
  - **Regret matching** : get_strategy est une distribution de probabilite ;
    regrets negatifs -> uniforme ; regrets positifs -> proportionnels.
  - **Reproductibilite** : train() seeded est deterministe (meme graine ->
    meme utilite moyenne).
  - **Valeur du jeu** : Kuhn Poker est defavorable a P1 (value theorique
    -1/18 ~ -0.056) -> l'utilite moyenne convergee est negative.
  - **Structure d'equilibre** : la strategie moyenne convergee respecte les
    invariants qualitatifs de l'equilibre de Nash de Kuhn Poker (le King bet
    plus que le Jack ne bluffe ; P2 fold le Jack face a un bet, call le King).

Run with: pytest tests/test_kuhn_poker_cfr.py -v
"""

import random
import sys
from pathlib import Path

import numpy as np
import pytest

# Ajoute GameTheory/ au path : examples/ est un package (examples/__init__.py).
sys.path.insert(0, str(Path(__file__).parent.parent))

from examples.kuhn_poker_cfr import (  # noqa: E402
    KuhnPoker,
    JACK,
    QUEEN,
    KING,
    CHECK,
    BET,
    FOLD,
    CALL,
    CARD_NAMES,
)


# ----------------------------------------------------------------------------
# Fixtures.
# ----------------------------------------------------------------------------

@pytest.fixture
def fresh_game():
    """Instance vierge (regret_sum / strategy_sum vides)."""
    return KuhnPoker()


@pytest.fixture(scope="module")
def trained_game():
    """Instance entraînée (seeded) reutilisee pour les tests d'equilibre.

    50000 iterations de chance-sampling CFR suffisent a converger vers une
    strategie proche de l'equilibre de Nash de Kuhn Poker. Le seed rend la
    suite deterministe.
    """
    random.seed(42)
    g = KuhnPoker()
    g.train(50000)
    return g


# ----------------------------------------------------------------------------
# Utilites terminales (deterministes) : on appelle cfr() directement sur des
# histories terminales avec des cartes connues -> utilite exacte.
# ----------------------------------------------------------------------------

class TestTerminalUtilities:
    """Chaque feuille de l'arbre de Kuhn Poker a une utilite connue."""

    def test_check_check_higher_card_wins(self, fresh_game):
        """cc (showdown) : P0 gagne +1 si sa carte > celle de P1."""
        assert fresh_game.cfr([KING, QUEEN], "cc", 1.0, 1.0) == 1
        assert fresh_game.cfr([QUEEN, KING], "cc", 1.0, 1.0) == -1

    def test_check_bet_fold(self, fresh_game):
        """cbf : P2 mise apres le check de P1, P1 se couche -> P0 gagne +1.

        (cfr est ecrit du point de vue de P0 = joueur courant au debut du
        sous-arbre ; ici P0 designe le joueur qui a checke et beneficie du
        fold adverse.)
        """
        assert fresh_game.cfr([QUEEN, KING], "cbf", 1.0, 1.0) == 1
        assert fresh_game.cfr([JACK, KING], "cbf", 1.0, 1.0) == 1

    def test_check_bet_call_showdown(self, fresh_game):
        """cbc : les deux misent, pot de 2 -> showdown +/-2."""
        assert fresh_game.cfr([KING, QUEEN], "cbc", 1.0, 1.0) == 2
        assert fresh_game.cfr([QUEEN, KING], "cbc", 1.0, 1.0) == -2

    def test_bet_fold(self, fresh_game):
        """bf : P0 mise, P2 se couche -> P0 gagne +1."""
        assert fresh_game.cfr([QUEEN, KING], "bf", 1.0, 1.0) == 1

    def test_bet_call_showdown(self, fresh_game):
        """bc : P0 mise, P2 suit, pot de 2 -> showdown +/-2."""
        assert fresh_game.cfr([KING, QUEEN], "bc", 1.0, 1.0) == 2
        assert fresh_game.cfr([JACK, KING], "bc", 1.0, 1.0) == -2

    def test_terminal_does_not_touch_regrets(self, fresh_game):
        """Un appel sur feuille terminale n'initialise aucun information set."""
        fresh_game.cfr([KING, QUEEN], "cc", 1.0, 1.0)
        fresh_game.cfr([KING, QUEEN], "bf", 1.0, 1.0)
        assert fresh_game.regret_sum == {}
        assert fresh_game.strategy_sum == {}


# ----------------------------------------------------------------------------
# Information sets et regret matching.
# ----------------------------------------------------------------------------

class TestInfoSet:
    """get_info_set encode carte + history sous une forme lisible."""

    def test_root_info_set(self, fresh_game):
        assert fresh_game.get_info_set(KING, "") == "K"
        assert fresh_game.get_info_set(JACK, "") == "J"

    def test_info_set_with_history(self, fresh_game):
        assert fresh_game.get_info_set(QUEEN, "c") == "Qc"
        assert fresh_game.get_info_set(JACK, "cb") == "Jcb"


class TestRegretMatching:
    """get_strategy : la regle de regret matching (Hart & Mas-Colell)."""

    def test_new_info_set_is_uniform(self, fresh_game):
        """Un information set jamais vu -> strategie uniforme (2 actions)."""
        strat = fresh_game.get_strategy("K")
        np.testing.assert_allclose(strat, [0.5, 0.5])

    def test_all_negative_regrets_is_uniform(self, fresh_game):
        """Si tous les regrets sont negatifs ou nuls -> uniforme."""
        fresh_game.regret_sum["Q"] = np.array([-3.0, -1.0])
        fresh_game.strategy_sum["Q"] = np.zeros(2)
        strat = fresh_game.get_strategy("Q")
        np.testing.assert_allclose(strat, [0.5, 0.5])

    def test_positive_regrets_are_proportional(self, fresh_game):
        """Regrets positifs -> proba proportionnelle au regret positif."""
        fresh_game.regret_sum["K"] = np.array([3.0, 1.0])
        fresh_game.strategy_sum["K"] = np.zeros(2)
        strat = fresh_game.get_strategy("K")
        np.testing.assert_allclose(strat, [0.75, 0.25])

    def test_zeroed_positive_regret(self, fresh_game):
        """Un regret positif nul, l'autre positif -> toute la masse dessus."""
        fresh_game.regret_sum["J"] = np.array([0.0, 5.0])
        fresh_game.strategy_sum["J"] = np.zeros(2)
        strat = fresh_game.get_strategy("J")
        np.testing.assert_allclose(strat, [0.0, 1.0])

    def test_strategy_is_a_distribution(self, fresh_game):
        """get_strategy renvoie toujours une distribution de probabilite."""
        for regrets in ([3.0, 1.0], [-1.0, -2.0], [0.0, 0.0], [5.0, 0.0]):
            fresh_game.regret_sum["X"] = np.array(regrets)
            fresh_game.strategy_sum["X"] = np.zeros(2)
            strat = fresh_game.get_strategy("X")
            assert np.isclose(strat.sum(), 1.0)
            assert np.all(strat >= 0.0)
            assert np.all(strat <= 1.0)


# ----------------------------------------------------------------------------
# Entrainement : reproductibilite et valeur du jeu.
# ----------------------------------------------------------------------------

class TestTrainReproducibility:
    """train() est stochastique mais deterministe sous graine fixee."""

    def test_seeded_train_is_deterministic(self):
        """Deux runs avec meme graine -> meme utilite moyenne (bit pour bit)."""
        random.seed(123)
        u1 = KuhnPoker().train(3000)
        random.seed(123)
        u2 = KuhnPoker().train(3000)
        assert u1 == u2

    def test_different_seeds_same_ballpark(self):
        """Deux graines differentes convergent vers la meme valeur (a bruit pres)."""
        random.seed(1)
        u1 = KuhnPoker().train(20000)
        random.seed(999)
        u2 = KuhnPoker().train(20000)
        # Les deux estimations tournent autour de la valeur du jeu (-1/18).
        assert abs(u1 - u2) < 0.15

    def test_train_returns_float(self, fresh_game):
        random.seed(0)
        u = fresh_game.train(100)
        assert isinstance(u, float)

    def test_train_populates_strategy_sum(self, fresh_game):
        """Apres train, au moins un information set a ete visite."""
        random.seed(0)
        fresh_game.train(1000)
        assert len(fresh_game.strategy_sum) > 0
        assert len(fresh_game.regret_sum) > 0


class TestGameValue:
    """Kuhn Poker est defavorable au joueur 1 (value theorique -1/18)."""

    def test_game_value_is_negative_for_p1(self, trained_game):
        """La valeur du jeu est ~ -0.056 (P1 est desavantage).

        On verifie l'invariant de signe (robuste a la stochasticite) plutot
        qu'une valeur exacte : P1 ne peut pas esperer un gain positif a
        l'equilibre de Nash de Kuhn Poker.
        """
        random.seed(42)
        u = KuhnPoker().train(50000)
        assert u < 0.0
        assert u > -0.5  # borne superieure lache (un ante = 1)


# ----------------------------------------------------------------------------
# Structure d'equilibre : invariants qualitatifs de la strategie convergee.
# ----------------------------------------------------------------------------

class TestEquilibriumStructure:
    """La strategie moyenne convergee respecte la theorie de Kuhn Poker.

    L'equilibre de Nash de Kuhn Poker (Kuhn 1950) est parametre par
    alpha dans [0, 1/3] : P1 bet le King avec prob 3*alpha (value bet),
    bet le Jack avec prob alpha (bluff), et check la Queen. Les probas
    exactes dependent d'alpha, mais les INVARIANTS QUALITATIFS ci-dessous
    tiennent pour toute valeur d'alpha dans la famille d'equilibre.
    """

    def test_average_strategy_is_distribution(self, trained_game):
        """Chaque information set de la strategie moyenne somme a 1."""
        avg = trained_game.get_average_strategy()
        for info_set, strat in avg.items():
            assert np.isclose(strat.sum(), 1.0), f"{info_set} ne somme pas a 1"
            assert np.all(strat >= 0.0)

    def test_p1_king_bets_more_than_jack(self, trained_game):
        """P1 value-bet le King davantage qu'il ne bluffe le Jack.

        Invariant central : le King (main gagnante) est mise plus souvent que
        le Jack (bluff) a l'equilibre.
        """
        avg = trained_game.get_average_strategy()
        if "K" in avg and "J" in avg:
            p_king_bet = avg["K"][1]   # index 1 = bet
            p_jack_bet = avg["J"][1]
            assert p_king_bet >= p_jack_bet

    def test_p2_folds_jack_to_bet(self, trained_game):
        """P2 se couche le Jack face a une mise (sa pire main)."""
        avg = trained_game.get_average_strategy()
        if "Jb" in avg:
            # "Jb" = P2 tient le Jack face a un bet de P1. index 0 = fold.
            assert avg["Jb"][0] >= 0.5  # fold majoritairement

    def test_p2_calls_king_to_bet(self, trained_game):
        """P2 suit le King face a une mise (sa meilleure main)."""
        avg = trained_game.get_average_strategy()
        if "Kb" in avg:
            # "Kb" = P2 tient le King face a un bet. index 1 = call.
            assert avg["Kb"][1] >= 0.5  # call majoritairement

    def test_root_info_sets_visited(self, trained_game):
        """Apres un entraînement suffisant, les 3 infosets racine de P1 sont visits.

        Kuhn Poker a 9 information sets (J/Q/K pour P1, puis Jc/Qc/Kc et
        Jb/Qb/Kb pour P2). On verifie le sanity minimal : les 3 infosets ou
        P1 decide a la racine (J, Q, K) sont bien presents dans la strategie
        moyenne apres 50000 iterations.
        """
        avg = trained_game.get_average_strategy()
        for card in ("J", "Q", "K"):
            assert card in avg, f"infoset racine {card} absent apres training"


# ----------------------------------------------------------------------------
# Constantes du module.
# ----------------------------------------------------------------------------

class TestConstants:
    """Les constantes de cartes/actions sont coherentes avec le module."""

    def test_card_ordering(self):
        """Jack < Queen < King (indices croissants)."""
        assert JACK < QUEEN < KING

    def test_card_names_mapping(self):
        assert CARD_NAMES[JACK] == "J"
        assert CARD_NAMES[QUEEN] == "Q"
        assert CARD_NAMES[KING] == "K"

    def test_action_constants_distinct(self):
        """Check != Bet et Fold != Call."""
        assert CHECK != BET
        assert FOLD != CALL


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
