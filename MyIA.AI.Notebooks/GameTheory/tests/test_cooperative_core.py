"""
Tests pour le module cooperative_games/core.py (Le Core des jeux cooperatifs).

Le Core d'un jeu cooperatif est l'ensemble des allocations qu'aucune coalition
ne peut ameliorer :

    Core(v) = {x dans R^n : sum(x_i) = v(N)  et  sum_{i in S} x_i >= v(S)
                                pour toute coalition S subset N}

Ces tests assertent des INVARIANTS theoriques (les contrats du module), pas
seulement l'absence de crash :

  - **Efficacite** : toute allocation du Core somme a v(N).
  - **Rationalite de coalition** : toute allocation du Core donne a chaque
    coalition au moins sa valeur v(S) ; une allocation insuffisante est
    bloquee par la coalition lese (rendue par is_in_core).
  - **Core vide pour les jeux majority 3 joueurs** (contre-exemple canonique) :
    aucun point ne satisfait toutes les contraintes de paires.
  - **Core non-vide pour les jeux convexes** : v(S)=|S|^2 est convexe
    (marginales croissantes), le Core est non-vide, la valeur de Shapley
    (symetrique -> partage egal) est dans le Core.
  - **Dualite Bondareva-Shapley** : la condition equilibre (LP dual) coincide
    avec compute_core sur la (non-)vacuite du Core, sur plusieurs jeux.
  - **Geometrie 2D** : pour 2 joueurs, le Core est un intervalle
    [v({0}), v(N)-v({1})] sur la droite d'efficacite, non-vide ssi
    v({0})+v({1}) <= v(N).
  - **Coherence des objectifs LP** ('any'/'center'/'equal') : ils rendent
    tous un point faisable du Core (non-vide) ou None (vide), de maniere
    deterministe et compatible avec is_in_core.

Run with: pytest tests/test_cooperative_core.py -v
"""

import sys
from pathlib import Path

import numpy as np
import pytest

# Ajoute GameTheory/ au path pour importer cooperative_games comme package.
sys.path.insert(0, str(Path(__file__).parent.parent))

from cooperative_games.coalition_games import (  # noqa: E402
    CoalitionGame,
    VotingGame,
    majority_game,
    unanimity_game,
)
from cooperative_games.core import (  # noqa: E402
    core_constraints,
    is_in_core,
    compute_core,
    core_vertices_2d,
    core_vertices_3d,
    bondareva_shapley_condition,
)


# ----------------------------------------------------------------------------
# Jeux de reference (toutes les valeurs sont calculees a la main dans les
# docstrings des fixtures ci-dessous ; les tests s'appuient dessus).
# ----------------------------------------------------------------------------

def _convex_square(n=3):
    """Jeu convexe v(S) = |S|^2. Marginales croissantes => convexe (supermodulaire).
    Pour n=3 : v(singleton)=1, v(paire)=4, v(N)=9."""
    return CoalitionGame(n, lambda S: float(len(S) ** 2))


def _two_player_nonempty():
    """Jeu 2 joueurs non-vide : v({0})=1, v({1})=2, v({0,1})=4.
    Core = intervalle x0 dans [1, 2] (car 1+2=3 <= 4)."""
    values = {frozenset(): 0.0, frozenset({0}): 1.0,
              frozenset({1}): 2.0, frozenset({0, 1}): 4.0}
    return CoalitionGame(2, lambda S: values[frozenset(S)])


def _two_player_empty():
    """Jeu 2 joueurs vide : v({0})=3, v({1})=3, v({0,1})=4.
    3+3=6 > 4 => Core vide."""
    values = {frozenset(): 0.0, frozenset({0}): 3.0,
              frozenset({1}): 3.0, frozenset({0, 1}): 4.0}
    return CoalitionGame(2, lambda S: values[frozenset(S)])


def _dictator_unanimity():
    """Unanimite sur {0} (joueur 0 veto/dictateur) en 3 joueurs.
    v(S)=1 ssi 0 in S. Core = point unique [1, 0, 0]."""
    return unanimity_game(3, {0})


# ----------------------------------------------------------------------------
# core_constraints : generation des contraintes LP du Core.
# ----------------------------------------------------------------------------

class TestCoreConstraints:
    """core_constraints : forme standard (A_ub, b_ub, A_eq, b_eq) pour linprog."""

    def test_equality_constraint_is_efficiency(self):
        """A_eq @ x == b_eq encode sum(x_i) = v(N) : ligne de 1, rhs = v(N)."""
        game = _convex_square(3)
        A_ub, b_ub, A_eq, b_eq = core_constraints(game)
        assert A_eq.shape == (1, 3)
        assert np.allclose(A_eq, np.ones((1, 3)))
        assert b_eq == pytest.approx(game.grand_coalition_value())  # 9.0

    def test_one_inequality_per_proper_nonempty_coalition(self):
        """Pour n=3 : 2^3 - 2 = 6 sous-ensembles propres non-vides
        (3 singletons + 3 paires) => 6 contraintes d'inegalite."""
        game = _convex_square(3)
        A_ub, b_ub, A_eq, b_eq = core_constraints(game)
        assert A_ub.shape == (6, 3)
        assert b_ub.shape == (6,)

    def test_inequality_encodes_coalition_rationality(self):
        """Chaque ligne -1_{S} @ x <= -v(S) equivaut a sum_{i in S} x_i >= v(S).
        Pour v(S)=|S|^2 : la contrainte du singleton {0} a rhs=-1 ; celle de la
        paire {0,1} a rhs=-4."""
        game = _convex_square(3)
        A_ub, b_ub, A_eq, b_eq = core_constraints(game)
        # Identifier la ligne de la paire {0,1} : coef -1 sur colonnes 0 et 1.
        row01 = A_ub[(A_ub[:, 0] == -1) & (A_ub[:, 1] == -1) & (A_ub[:, 2] == 0)]
        assert row01.shape[0] == 1
        idx01 = np.where((A_ub[:, 0] == -1) & (A_ub[:, 1] == -1) & (A_ub[:, 2] == 0))[0][0]
        assert b_ub[idx01] == pytest.approx(-4.0)
        # Singleton {2} : coef -1 sur colonne 2 uniquement, rhs=-1.
        idx2 = np.where((A_ub[:, 0] == 0) & (A_ub[:, 1] == 0) & (A_ub[:, 2] == -1))[0][0]
        assert b_ub[idx2] == pytest.approx(-1.0)

    def test_constraints_feasible_for_convex_game(self):
        """Le Core d'un jeu convexe etant non-vide, le LP a au moins une solution.
        On verifie en resolvant avec un cout nul (trouver un point faisable)."""
        from scipy.optimize import linprog
        game = _convex_square(3)
        A_ub, b_ub, A_eq, b_eq = core_constraints(game)
        res = linprog(np.zeros(3), A_ub=A_ub, b_ub=b_ub,
                      A_eq=A_eq, b_eq=b_eq, method='highs')
        assert res.success
        # Le point faisable respecte bien l'efficacite.
        assert res.x.sum() == pytest.approx(game.grand_coalition_value())


# ----------------------------------------------------------------------------
# is_in_core : test d'appartenance + coalition bloquante.
# ----------------------------------------------------------------------------

class TestIsInCore:
    """is_in_core : (est_dans_core, coalition_bloquante)."""

    def test_efficient_and_rational_allocation_is_in_core(self):
        """[3,3,3] pour v(S)=|S|^2 : sum=9=v(N), singletons 3>=1, paires 6>=4
        => dans le Core."""
        game = _convex_square(3)
        ok, blocking = is_in_core(game, np.array([3.0, 3.0, 3.0]))
        assert ok is True
        assert blocking is None

    def test_inefficient_allocation_rejected(self):
        """Une allocation dont la somme != v(N) n'est pas dans le Core
        (pas de coalition bloquante signalee : c'est l'efficacite qui echoue)."""
        game = _convex_square(3)
        ok, blocking = is_in_core(game, np.array([3.0, 3.0, 2.0]))  # sum=8 != 9
        assert ok is False
        assert blocking is None

    def test_blocking_coalition_returned(self):
        """[0.5, 0.5, 8] sum=9 mais singleton {0} recoit 0.5 < v({0})=1 :
        rejete, et la coalition bloquante est {0}."""
        game = _convex_square(3)
        ok, blocking = is_in_core(game, np.array([0.5, 0.5, 8.0]))
        assert ok is False
        assert blocking == {0}

    def test_blocking_pair_returned(self):
        """[2, 2, 5] sum=9, singletons ok (2>=1), mais paire {0,1} recoit 4
        == v({0,1})=4 (limite, donc OK) ; paire {0,2}=7>=4 OK. En revanche
        [1.5, 1.5, 6] : paire {0,1}=3 < 4 => bloquee par {0,1}."""
        game = _convex_square(3)
        ok, blocking = is_in_core(game, np.array([1.5, 1.5, 6.0]))
        assert ok is False
        assert blocking == {0, 1}

    def test_boundary_allocation_within_tolerance(self):
        """Une allocation exactement a la limite (paire {0,1}=4=v({0,1})) est
        acceptee ; tolerance numerique."""
        game = _convex_square(3)
        # [2,2,5] : paire {0,1}=4 == v=4 => OK (>= avec tolerance).
        ok, _ = is_in_core(game, np.array([2.0, 2.0, 5.0]))
        assert ok is True

    def test_majority_game_has_no_core_allocation(self):
        """Jeu majority 3 joueurs (quota 2) : le Core est vide, AUCUNE
        allocation n'appartient au Core. Le partage egal [1/3,1/3,1/3] est
        bloque par une paire (qui exige >= 1)."""
        game = majority_game(3)
        ok, blocking = is_in_core(game, np.array([1 / 3, 1 / 3, 1 / 3]))
        assert ok is False
        assert blocking is not None
        assert len(blocking) == 2  # une paire bloque.

    def test_dictator_point_is_in_core(self):
        """unanimity_game(3, {0}) : Core = point unique [1,0,0]."""
        game = _dictator_unanimity()
        ok, blocking = is_in_core(game, np.array([1.0, 0.0, 0.0]))
        assert ok is True
        assert blocking is None


# ----------------------------------------------------------------------------
# compute_core : trouver un point du Core par PL (3 objectifs).
# ----------------------------------------------------------------------------

class TestComputeCore:
    """compute_core : (core_non_vide, allocation) selon l'objectif LP."""

    def test_convex_game_core_nonempty_all_objectives(self):
        """Jeu convexe => Core non-vide ; les 3 objectifs rendent un point."""
        game = _convex_square(3)
        for objective in ('any', 'center', 'equal'):
            nonempty, alloc = compute_core(game, objective=objective)
            assert nonempty is True, f"objective={objective} should be feasible"
            assert alloc is not None

    def test_computed_point_is_in_core(self):
        """Tout point rendu par compute_core doit effectivement etre dans le
        Core (coherence avec is_in_core)."""
        game = _convex_square(3)
        for objective in ('any', 'center', 'equal'):
            _, alloc = compute_core(game, objective=objective)
            ok, blocking = is_in_core(game, alloc)
            assert ok is True, (
                f"objective={objective} returned alloc {alloc} not in core "
                f"(blocked by {blocking})"
            )

    def test_computed_point_is_efficient(self):
        """Tout point du Core est efficient : sum(x) == v(N)."""
        game = _convex_square(3)
        vN = game.grand_coalition_value()
        for objective in ('any', 'center', 'equal'):
            _, alloc = compute_core(game, objective=objective)
            assert alloc.sum() == pytest.approx(vN)

    def test_equal_objective_close_to_equal_division(self):
        """L'objectif 'equal' minimise la distance L1 au partage egal.
        Pour le jeu convexe symetrique v(S)=|S|^2, [3,3,3] est dans le Core
        ET est le partage egal => 'equal' doit le rendre (ou un point tres
        proche)."""
        game = _convex_square(3)
        _, alloc = compute_core(game, objective='equal')
        assert np.allclose(alloc, [3.0, 3.0, 3.0], atol=1e-5)

    def test_majority_game_core_empty_all_objectives(self):
        """Jeu majority 3 joueurs => Core vide pour les 3 objectifs."""
        game = majority_game(3)
        for objective in ('any', 'center', 'equal'):
            nonempty, alloc = compute_core(game, objective=objective)
            assert nonempty is False, f"objective={objective} should be empty"
            assert alloc is None

    def test_dictator_core_single_point(self):
        """unanimity_game(3,{0}) : Core = [1,0,0] unique. 'any' le rend."""
        game = _dictator_unanimity()
        nonempty, alloc = compute_core(game, objective='any')
        assert nonempty is True
        assert np.allclose(alloc, [1.0, 0.0, 0.0])

    def test_objectives_agree_on_emptiness(self):
        """Sur un meme jeu, les 3 objectifs rendent le meme verdict
        (non-vide vs vide). Coherence interne du module."""
        factories = [
            ("convex_square", lambda: _convex_square(3)),
            ("dictator_unanimity", _dictator_unanimity),
            ("majority_3", lambda: majority_game(3)),
        ]
        for name, factory in factories:
            game = factory()
            verdicts = [compute_core(game, objective=obj)[0]
                        for obj in ('any', 'center', 'equal')]
            assert len(set(verdicts)) == 1, (
                f"objectives disagree on {name}: {verdicts}"
            )

    def test_invalid_objective_raises(self):
        game = _convex_square(3)
        with pytest.raises(ValueError):
            compute_core(game, objective='nonsense')

    def test_deterministic_same_result_twice(self):
        """Le PL highs est deterministe : deux appels rendent le meme point."""
        game = _convex_square(3)
        _, a = compute_core(game, objective='center')
        _, b = compute_core(game, objective='center')
        np.testing.assert_array_equal(a, b)


# ----------------------------------------------------------------------------
# core_vertices_2d : geometrie du Core a 2 joueurs (intervalle).
# ----------------------------------------------------------------------------

class TestCoreVertices2D:
    """core_vertices_2d : le Core d'un jeu a 2 joueurs est un intervalle."""

    def test_nonempty_interval_endpoints(self):
        """v({0})=1, v({1})=2, v(N)=4 : intervalle x0 dans [1, 2].
        Somments : [1, 3] et [2, 2]."""
        game = _two_player_nonempty()
        verts = core_vertices_2d(game)
        assert verts is not None
        assert verts.shape == (2, 2)
        # Trier par x0 pour comparer deterministiquement.
        v = verts[np.argsort(verts[:, 0])]
        assert v[0] == pytest.approx([1.0, 3.0])
        assert v[1] == pytest.approx([2.0, 2.0])

    def test_endpoints_are_efficient(self):
        """Chaque sommet somme a v(N)=4 (sur la droite d'efficacite)."""
        game = _two_player_nonempty()
        verts = core_vertices_2d(game)
        for x0, x1 in verts:
            assert x0 + x1 == pytest.approx(4.0)

    def test_empty_core_returns_none(self):
        """v({0})=3, v({1})=3, v(N)=4 : 3+3>4 => Core vide."""
        game = _two_player_empty()
        assert core_vertices_2d(game) is None

    def test_wrong_player_count_raises(self):
        game = _convex_square(3)
        with pytest.raises(ValueError):
            core_vertices_2d(game)


# ----------------------------------------------------------------------------
# core_vertices_3d : echantillonnage du Core sur le 2-simplexe.
# ----------------------------------------------------------------------------

class TestCoreVertices3D:
    """core_vertices_3d : echantillonne la frontiere du Core pour 3 joueurs."""

    def test_convex_game_returns_in_core_points(self):
        """Jeu convexe (Core non-vide) : rend un nuage de points, TOUS dans
        le Core (verifies par is_in_core)."""
        game = _convex_square(3)
        points = core_vertices_3d(game, n_points=20)
        assert points is not None
        assert len(points) >= 1
        for alloc in points:
            ok, _ = is_in_core(game, alloc)
            assert ok, f"sampled point {alloc} not in core"

    def test_empty_core_returns_none(self):
        """Jeu majority 3 joueurs (Core vide) => None."""
        game = majority_game(3)
        assert core_vertices_3d(game, n_points=20) is None

    def test_wrong_player_count_raises(self):
        game = _two_player_nonempty()
        with pytest.raises(ValueError):
            core_vertices_3d(game)


# ----------------------------------------------------------------------------
# bondareva_shapley_condition : caractérisation duale de la non-vacuité.
# ----------------------------------------------------------------------------

class TestBondarevaShapley:
    """bondareva_shapley_condition : (est_equilibre, ecart).
    Theoreme de Bondareva-Shapley : le Core est non-vide ssi le jeu est
    equilibre. La dualite LP doit donc coincider avec compute_core."""

    @pytest.mark.parametrize("factory, expected_nonempty", [
        pytest.param(lambda: _convex_square(3), True, id="convex_square"),
        pytest.param(lambda: _two_player_nonempty(), True, id="two_player_nonempty"),
        pytest.param(lambda: _two_player_empty(), False, id="two_player_empty"),
        pytest.param(lambda: majority_game(3), False, id="majority_3"),
        pytest.param(_dictator_unanimity, True, id="dictator_unanimity"),
    ])
    def test_matches_compute_core(self, factory, expected_nonempty):
        """Le verdict equilibre == verdict compute_core sur 5 jeux."""
        game = factory()
        balanced, gap = bondareva_shapley_condition(game)
        nonempty, _ = compute_core(game, objective='any')
        assert balanced == nonempty == expected_nonempty
        # Coherence du signe de l'ecart : non-vide => gap >= 0, vide => gap < 0.
        if expected_nonempty:
            assert gap >= -1e-8
        else:
            assert gap < -1e-6

    def test_majority_gap_is_negative(self):
        """Le jeu majority 3 joueurs est desequilibre : la collection equilibre
        des 3 paires (poids 0.5 chacune) donne somme ponderee 1.5 > v(N)=1,
        soit un ecart v(N) - max = 1 - 1.5 = -0.5."""
        game = majority_game(3)
        balanced, gap = bondareva_shapley_condition(game)
        assert balanced is False
        assert gap == pytest.approx(-0.5, abs=1e-6)


# ----------------------------------------------------------------------------
# Theoreme : pour un jeu convexe, la valeur de Shapley est dans le Core.
# ----------------------------------------------------------------------------
# Pour le jeu SYMETRIQUE v(S)=|S|^2, la valeur de Shapley est egalitaire
# (tous les joueurs interchangeables) => [v(N)/n, ...] = [3, 3, 3].

class TestConvexShapleyInCore:
    """Theoreme : pour un jeu convexe, Shapley in Core."""

    def test_equal_shapley_in_core_of_convex_game(self):
        """Jeu convexe symetrique v(S)=|S|^2 : Shapley = [3,3,3] (symetrie),
        et ce point est dans le Core."""
        game = _convex_square(3)
        # Verification de convexite (garantit le theoreme).
        assert game.is_convex() is True
        shapley = np.array([3.0, 3.0, 3.0])  # v(N)/n par symetrie.
        ok, blocking = is_in_core(game, shapley)
        assert ok is True, f"Shapley {shapley} should be in core (blocked by {blocking})"

    def test_convex_game_core_nonempty_matches_theory(self):
        """Convexe => Core non-vide (theoreme). Verifie via compute_core ET
        bondareva_shapley (deux methodes independantes)."""
        game = _convex_square(3)
        assert game.is_convex() is True
        nonempty_lp, _ = compute_core(game, objective='any')
        balanced, _ = bondareva_shapley_condition(game)
        assert nonempty_lp is True
        assert balanced is True
