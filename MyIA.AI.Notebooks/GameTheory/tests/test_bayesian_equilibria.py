"""
Tests for bayesian_equilibria (issue #22382, premier jalon : module + tests).

Reproductible + comparaison native sur les memes fixtures : chaque fixture est
un jeu bayesien duc-typed sur le contrat d'organe de GameTheory-11, et un
oracle natif par type (meilleure reponse pure par type, comme l'organe
``is_bayean_nash_equilibrium`` du notebook) est recalculé dans le test
independamment du module.

Run with: pytest tests/test_bayesian_equilibria.py
"""

import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Callable, Dict, List, Tuple

import numpy as np
import pytest

# Reserve Hermes #22615 (n.2) : si nashpy est absent localement, les tests
# SKIPPent proprement au lieu d'echouer a la collecte. En CI, nashpy est
# declare dans gametheory-tests.yml (job "GameTheory pytest").
pytest.importorskip(
    "nashpy", reason="nashpy requis (declare en CI ; localement: pip install nashpy)"
)

# Add parent directory to path (convention des tests GameTheory)
sys.path.insert(0, str(Path(__file__).parent.parent))

import bayesian_equilibria as be


# ---------------------------------------------------------------------------
# Fixtures : jeux duc-typed sur le contrat d'organe (PAS une seconde
# definition de BayesianGame)
# ---------------------------------------------------------------------------


@dataclass
class NativeGame:
    """Fixture : contrat d'organe de GameTheory-11 (5 champs + name)."""

    name: str
    players: List[str]
    types: Dict[str, List[str]]
    prior: Dict[Tuple[str, str], float]
    actions: Dict[str, List[str]]
    payoffs: Callable


def bos_game(p: float = 0.7) -> NativeGame:
    """BoS a type incertain — payoffs EXACTS de GameTheory-11
    (``create_uncertain_bos``) : J1 a un seul type N, J2 a O (prob p) / F."""

    def payoffs(types: Tuple[str, str], actions: Tuple[str, str]):
        _, t2 = types
        a1, a2 = actions
        if a1 == a2:
            if a1 == "O":
                return (2, 1) if t2 == "O" else (2, 0)
            return (1, 2) if t2 == "F" else (1, 0)
        return (0, 0)

    return NativeGame(
        name="BoS bayesien",
        players=["J1", "J2"],
        types={"J1": ["N"], "J2": ["O", "F"]},
        prior={("N", "O"): p, ("N", "F"): 1 - p},
        actions={"J1": ["O", "F"], "J2": ["O", "F"]},
        payoffs=payoffs,
    )


def correlated_game(prior: Dict[Tuple[str, str], float]) -> NativeGame:
    """Instance discriminante (critere 4) : 2 types de chaque cote (H/L),
    2 actions (A/B). J1 (poids W1) veut s'ALIGNER, J2 (poids W2) veut se
    DEPLACER — la correlation du prior rend le produit des marginales
    insuffisant."""
    w1 = {"H": 1.0, "L": 0.5}
    w2 = {"H": 1.0, "L": 1.0 / 3.0}

    def payoffs(types: Tuple[str, str], actions: Tuple[str, str]):
        (t1, t2), (a1, a2) = types, actions
        m = 1 if a1 == a2 else -1
        return (w1[t1] * m, -w2[t2] * m)

    return NativeGame(
        name="Jeu bayesien correle",
        players=["J1", "J2"],
        types={"J1": ["H", "L"], "J2": ["H", "L"]},
        prior=prior,
        actions={"J1": ["A", "B"], "J2": ["A", "B"]},
        payoffs=payoffs,
    )


@pytest.fixture
def corr_game() -> NativeGame:
    """Prior corrélé : P(HH) = P(LL) = 0.4, P(HL) = P(LH) = 0.1."""
    return correlated_game(
        {("H", "H"): 0.4, ("H", "L"): 0.1, ("L", "H"): 0.1, ("L", "L"): 0.4}
    )


@pytest.fixture
def corr_game_product() -> NativeGame:
    """Memes gains, prior produit des marginales (0.25 partout)."""
    return correlated_game({k: 0.25 for k in corr_prior_keys()})


def corr_prior_keys():
    return [("H", "H"), ("H", "L"), ("L", "H"), ("L", "L")]


# ---------------------------------------------------------------------------
# Oracle natif par type (independant du module) — meme sémantique que
# l'organe du notebook : meilleure reponse pure par type
# ---------------------------------------------------------------------------


def native_marginals(game: NativeGame, k: int, plans, sigma) -> Dict[str, np.ndarray]:
    player = game.players[k]
    out: Dict[str, np.ndarray] = {}
    for pos, t in enumerate(game.types[player]):
        dist = np.zeros(len(game.actions[player]))
        for w, pl in zip(sigma, plans):
            dist[game.actions[player].index(pl[pos])] += w
        out[t] = dist
    return out


def native_is_bne(
    game: NativeGame,
    plans1,
    plans2,
    sigma1: np.ndarray,
    sigma2: np.ndarray,
    tol: float = 1e-6,
) -> bool:
    """Oracle natif : pour chaque joueur et chaque type de probabilite
    positive, l'action (marginale) doit etre une meilleure reponse au
    profil conditionnel de l'adversaire — recalcule depuis le prior et les
    gains natifs, sans la forme strategique."""
    all_plans = (plans1, plans2)
    sigmas = (np.asarray(sigma1, float), np.asarray(sigma2, float))
    for k in (0, 1):
        other = 1 - k
        player = game.players[k]
        marg_k = native_marginals(game, k, plans1, sigma1) if k == 0 else \
            native_marginals(game, k, plans2, sigma2)
        marg_o = native_marginals(game, other, plans1, sigma1) if other == 0 else \
            native_marginals(game, other, plans2, sigma2)
        for t_k in game.types[player]:
            p_k = sum(
                p for prof, p in game.prior.items() if prof[k] == t_k
            )
            if p_k <= 0.0:
                continue
            cond = {}
            for a_k in game.actions[player]:
                tot = 0.0
                for t_o in game.types[game.players[other]]:
                    joint = game.prior.get(
                        (t_k, t_o) if k == 0 else (t_o, t_k), 0.0
                    )
                    if joint == 0.0:
                        continue
                    for a_o, w in zip(game.actions[game.players[other]], marg_o[t_o]):
                        profile = (t_k, t_o) if k == 0 else (t_o, t_k)
                        acts = (a_k, a_o) if k == 0 else (a_o, a_k)
                        tot += (joint / p_k) * w * game.payoffs(profile, acts)[k]
                cond[a_k] = tot
            current = float(
                np.dot(marg_k[t_k], [cond[a] for a in game.actions[player]])
            )
            if max(cond.values()) - current > tol:
                return False
    return True


# ---------------------------------------------------------------------------
# 1-3. Matrices ex ante
# ---------------------------------------------------------------------------


class TestStrategicForm:
    def test_bos_matrices_exact(self):
        """BoS (p=0.7) : matrices ex ante derivees a la main."""
        form = be.to_strategic_form(bos_game())
        np.testing.assert_allclose(
            form.matrix1,
            [[2.0, 1.4, 0.6, 0.0], [0.0, 0.3, 0.7, 1.0]],
            atol=1e-9,
        )
        np.testing.assert_allclose(
            form.matrix2,
            [[0.7, 0.7, 0.0, 0.0], [0.0, 0.6, 0.0, 0.6]],
            atol=1e-9,
        )

    def test_correlated_matrices_exact(self, corr_game):
        """Instance discriminante : memes matrices, verifiees a la main."""
        form = be.to_strategic_form(corr_game)
        np.testing.assert_allclose(
            form.matrix1,
            [
                [0.75, 0.15, -0.15, -0.75],
                [0.25, 0.45, -0.45, -0.25],
                [-0.25, -0.45, 0.45, 0.25],
                [-0.75, -0.15, 0.15, 0.75],
            ],
            atol=1e-9,
        )
        np.testing.assert_allclose(
            form.matrix2,
            [
                [-2 / 3, -1 / 3, 1 / 3, 2 / 3],
                [-0.2, -0.4, 0.4, 0.2],
                [0.2, 0.4, -0.4, -0.2],
                [2 / 3, 1 / 3, -1 / 3, -2 / 3],
            ],
            atol=1e-9,
        )

    def test_correlated_vs_product_prior_matrices_differ(self, corr_game, corr_game_product):
        """Coeur du critere 4 : remplacer le joint par le produit des
        marginales CHANGE les gains ex ante."""
        f_corr = be.to_strategic_form(corr_game)
        f_prod = be.to_strategic_form(corr_game_product)
        assert not np.allclose(f_corr.matrix1, f_prod.matrix1)
        assert not np.allclose(f_corr.matrix2, f_prod.matrix2)

    def test_prior_must_sum_to_one(self):
        bad = bos_game()
        bad.prior = {("N", "O"): 0.9, ("N", "F"): 0.9}
        with pytest.raises(ValueError, match="prior"):
            be.to_strategic_form(bad)

    def test_plan_space_cap_before_materialization(self):
        """Critere 6 : 128 plans (2^7) > borne 64 -> PlanSpaceTooLargeError,
        declare AVANT toute materialisation ; 64 plans (2^6) passe exact."""
        seven = [f"t{i}" for i in range(7)]
        six = [f"t{i}" for i in range(6)]
        with pytest.raises(be.PlanSpaceTooLargeError):
            be.build_plan_space(seven, ["A", "B"])
        assert be.plan_count(seven, ["A", "B"]) == 128
        # 64 plans = borne : accepte ; et la borne est franchissable explicitement
        assert len(be.build_plan_space(six, ["A", "B"])) == 64
        assert len(be.build_plan_space(seven, ["A", "B"], max_plans=128)) == 128


# ---------------------------------------------------------------------------
# 4-7. Instance discriminante : BNE purs, solveur, controle analytique
# ---------------------------------------------------------------------------


def _pure_sigma(plans, chosen) -> np.ndarray:
    return np.array([1.0 if pl == chosen else 0.0 for pl in plans])


class TestDiscriminatingInstance:
    def test_no_pure_bne_under_correlated_prior(self, corr_game):
        """AUCUNE des 16 pures n'est un BNE (prior corrélé) — verifie par
        l'oracle natif par type."""
        form = be.to_strategic_form(corr_game)
        for p1 in form.plans[0]:
            for p2 in form.plans[1]:
                s1 = _pure_sigma(form.plans[0], p1)
                s2 = _pure_sigma(form.plans[1], p2)
                assert not native_is_bne(corr_game, form.plans[0], form.plans[1], s1, s2)

    def test_product_prior_has_exactly_four_pure_bne(self, corr_game_product):
        """Sous prior produit : exactement 4/16 pures sont des BNE — les
        profils « split » (chaque joueur joue A et B, un par type)."""
        form = be.to_strategic_form(corr_game_product)
        bne = []
        for p1 in form.plans[0]:
            for p2 in form.plans[1]:
                s1 = _pure_sigma(form.plans[0], p1)
                s2 = _pure_sigma(form.plans[1], p2)
                if native_is_bne(corr_game_product, form.plans[0], form.plans[1], s1, s2):
                    bne.append((p1, p2))
        assert sorted(bne) == [
            (("A", "B"), ("A", "B")),
            (("A", "B"), ("B", "A")),
            (("B", "A"), ("A", "B")),
            (("B", "A"), ("B", "A")),
        ]

    def test_solver_found_and_every_equilibrium_validates(self, corr_game):
        """Critere 2 : Nashpy natif trouve des equilibres mixtes ; chacun
        passe le validateur independant (regret maximal <= tol)."""
        form = be.to_strategic_form(corr_game)
        result = be.solve_strategic_form(form, "support_enumeration")
        assert result.is_found
        assert result.equilibria
        for s1, s2 in result.equilibria:
            report = be.validate_bne(corr_game, form, s1, s2)
            assert report.is_bne, (s1, s2, report.max_regret)
            assert report.max_regret <= 1e-6

    def test_analytic_control_half_half_all_conditional_zero(self, corr_game):
        """Contrôle analytique (critere 4) : a 1/2-1/2 par type, TOUS les
        gains conditionnels sont exactement 0 (E[match] = 0 face a 1/2-1/2),
        donc le regret est exactement 0 — pas une coincidence numerique."""
        form = be.to_strategic_form(corr_game)
        s1 = np.array([0.5, 0.0, 0.0, 0.5])  # H: 1/2, L: 1/2 (corrélé)
        s2 = np.array([0.5, 0.0, 0.0, 0.5])
        report = be.validate_bne(corr_game, form, s1, s2)
        assert report.is_bne
        for tr in report.reports:
            for a, v in tr.conditional_payoffs.items():
                assert abs(v) <= 1e-12, (tr.player, tr.type, a, v)
            assert tr.regret <= 1e-12

    def test_validator_blind_to_counterfactual_correlation(self, corr_game):
        """Le validateur ne voit que les marginales par type : le melange
        corrélé [0.5,0,0,0.5] et le melange independant [0.25]*4 (memes
        marginales 1/2-1/2) produisent des rapports IDENTIQUES — c'est la
        correlation contrefactuelle que l'equilibre ex ante porte en plus,
        et que le jeu statique ne peut pas verifier."""
        form = be.to_strategic_form(corr_game)
        s_corr = np.array([0.5, 0.0, 0.0, 0.5])
        s_indep = np.full(4, 0.25)
        r_corr = be.validate_bne(corr_game, form, s_corr, s_corr)
        r_indep = be.validate_bne(corr_game, form, s_indep, s_indep)
        assert len(r_corr.reports) == len(r_indep.reports)
        for rc, ri in zip(r_corr.reports, r_indep.reports):
            assert (rc.player, rc.type) == (ri.player, ri.type)
            assert rc.current_payoff == pytest.approx(ri.current_payoff)
            assert rc.regret == pytest.approx(ri.regret)
            assert rc.conditional_payoffs == pytest.approx(ri.conditional_payoffs)

    def test_regret_reads_the_same_entry_as_best_response(self, corr_game):
        """Invariant d'ordre (review NanoClaw de #22615) : `regret` et
        `best_response` doivent se lire sur la MEME entree de la table.

        Le regret etait calcule par un `max` separe sur les valeurs, alors que
        `best_response` vient d'un argmax sur les cles : deux derivations de la
        meme grandeur, qui ne divergent qu'en silence si la table change de
        forme. Le test reconstruit l'invariant depuis le rapport public et
        verifie les deux proprietes qui le rendent vrai — coherence exacte, et
        `best_response` est bien un argmax.
        """
        form = be.to_strategic_form(corr_game)
        for s1, s2 in (
            (np.array([0.5, 0.0, 0.0, 0.5]), np.array([0.5, 0.0, 0.0, 0.5])),
            (np.full(4, 0.25), np.full(4, 0.25)),
            (np.array([1.0, 0.0, 0.0, 0.0]), np.array([0.0, 0.0, 0.0, 1.0])),
        ):
            report = be.validate_bne(corr_game, form, s1, s2)
            for tr in report.reports:
                cond = tr.conditional_payoffs
                assert tr.best_response in cond
                # coherence exacte entre les deux champs du rapport
                assert tr.regret == pytest.approx(
                    cond[tr.best_response] - tr.current_payoff
                )
                # et `best_response` est bien un argmax de la table
                assert cond[tr.best_response] == pytest.approx(max(cond.values()))

    def test_validator_is_deterministic_on_ties(self, corr_game):
        """Sur une table a egalite, le choix de `best_response` ne doit pas
        dependre d'un ordre d'insertion non maitrise : deux appels sur la meme
        entree rendent le meme rapport, champ pour champ."""
        form = be.to_strategic_form(corr_game)
        s = np.array([0.5, 0.0, 0.0, 0.5])
        r1 = be.validate_bne(corr_game, form, s, s)
        r2 = be.validate_bne(corr_game, form, s, s)
        assert len(r1.reports) == len(r2.reports)
        for a, b in zip(r1.reports, r2.reports):
            assert (a.player, a.type) == (b.player, b.type)
            assert a.best_response == b.best_response
            assert a.regret == b.regret
            assert a.conditional_payoffs == b.conditional_payoffs


# ---------------------------------------------------------------------------
# 8-9. BoS natif rejoue (critere 5)
# ---------------------------------------------------------------------------


class TestBosReplay:
    def test_three_native_pure_bne_recognized(self):
        """Les 3 BNE purs natifs du carnet sont reconnus par le validateur
        independant."""
        game = bos_game()
        form = be.to_strategic_form(game)
        native_bne = [
            ("O", ("O", "O")),
            ("O", ("O", "F")),
            ("F", ("F", "F")),
        ]
        for j1_action, j2_plan in native_bne:
            s1 = np.array([1.0, 0.0]) if j1_action == "O" else np.array([0.0, 1.0])
            s2 = _pure_sigma(form.plans[1], j2_plan)
            report = be.validate_bne(game, form, s1, s2)
            assert report.is_bne, (j1_action, j2_plan, report.max_regret)

    def test_solver_returns_exactly_the_three_pure(self):
        """Nashpy sur la forme strategique BoS retourne EXACTEMENT les 3
        pures natives — ni plus, ni une mixture degénérée exigée."""
        game = bos_game()
        form = be.to_strategic_form(game)
        result = be.solve_strategic_form(form, "support_enumeration")
        assert result.is_found
        got = set()
        for s1, s2 in result.equilibria:
            i = int(np.argmax(s1))
            j = int(np.argmax(s2))
            assert np.allclose(s1, [1.0 if q == i else 0.0 for q in range(2)])
            assert np.allclose(s2, [1.0 if q == j else 0.0 for q in range(4)])
            got.add((form.plans[0][i], form.plans[1][j]))
        # les plans de J1 (1 type) sont des 1-tuples : ('O',), ('F',)
        assert got == {
            (("O",), ("O", "O")),
            (("O",), ("O", "F")),
            (("F",), ("F", "F")),
        }

    def test_label_invariance(self):
        """Invariance des gains sous permutation des etiquettes de types
        (reordonnancement, pas simple re-etiquetage) : M' = P M P^T."""
        game = bos_game()
        form = be.to_strategic_form(game)
        report = be.check_label_invariance(game, form, (["N"], ["F", "O"]))
        assert report.ok, report.detail
        # controle positif : un reordonnancement trivial est aussi invariant
        report2 = be.check_label_invariance(game, form, (["N"], ["O", "F"]))
        assert report2.ok

    def test_ex_ante_consistency(self):
        """Cohérence ex ante : gain de la forme strategique == somme ponderee
        des gains conditionnels (recalcul natif) pour chaque melange."""
        game = bos_game()
        form = be.to_strategic_form(game)
        for s1, s2 in [
            (np.array([1.0, 0.0]), np.array([1.0, 0.0, 0.0, 0.0])),
            (np.full(2, 0.5), np.full(4, 0.25)),
            (np.array([0.3, 0.7]), np.array([0.1, 0.4, 0.2, 0.3])),
        ]:
            assert be.check_ex_ante_consistency(game, form, s1, s2)

    def test_ex_ante_consistency_correlated(self, corr_game):
        form = be.to_strategic_form(corr_game)
        s1 = np.array([0.5, 0.0, 0.0, 0.5])
        s2 = np.array([0.2, 0.3, 0.1, 0.4])
        assert be.check_ex_ante_consistency(corr_game, form, s1, s2)


# ---------------------------------------------------------------------------
# 12-13. Controles negatifs
# ---------------------------------------------------------------------------


class TestNegativeControls:
    def test_perturbed_mixture_is_explicitly_not_bne(self, corr_game):
        """Mélange perturbé [0.6,0,0,0.4] : les deux plans portent H et L
        ensemble (AA 0.6, BB 0.4), donc P(a1=A) = 0.6 quel que soit le type.
        J2-H (W2=1) : cond A = -(0.6-0.4) = -0.2, cond B = +0.2, courant
        0 -> regret exact 0.2, le pire du profil."""
        form = be.to_strategic_form(corr_game)
        s1 = np.array([0.6, 0.0, 0.0, 0.4])
        s2 = np.array([0.5, 0.0, 0.0, 0.5])
        report = be.validate_bne(corr_game, form, s1, s2)
        assert not report.is_bne
        assert report.max_regret == pytest.approx(0.2, abs=1e-6)
        j2h = [r for r in report.reports if r.player == "J2" and r.type == "H"][0]
        assert j2h.regret == pytest.approx(0.2, abs=1e-6)
        assert j2h.conditional_payoffs["A"] == pytest.approx(-0.2, abs=1e-6)
        assert j2h.conditional_payoffs["B"] == pytest.approx(0.2, abs=1e-6)

    def test_zero_prob_type_is_out_of_support_not_divided(self):
        """Type J2 « X » de probabilite nulle : signale out_of_support,
        jamais « vérifié par division nulle » ; le profil reste BNE."""
        base = bos_game()

        def payoffs_x(types, actions):
            t2 = types[1]
            if t2 == "X":
                return (0, 0)
            return base.payoffs(types, actions)

        game2 = NativeGame(
            name="BoS + type X neutre",
            players=base.players,
            types={"J1": ["N"], "J2": ["O", "F", "X"]},
            prior={("N", "O"): 0.7, ("N", "F"): 0.3, ("N", "X"): 0.0},
            actions={"J1": ["O", "F"], "J2": ["O", "F"]},
            payoffs=payoffs_x,
        )
        form = be.to_strategic_form(game2)
        assert len(form.plans[1]) == 8  # 3 types x 2 actions
        # profil : J1 O ; J2 : O->O, F->F, X->O (X hors support, action neutre)
        s1 = np.array([1.0, 0.0])
        s2 = _pure_sigma(form.plans[1], ("O", "F", "O"))
        report = be.validate_bne(game2, form, s1, s2)
        assert report.is_bne
        assert ("J2", "X") in report.out_of_support
        # et X n'apparait dans AUCUN rapport de regret
        assert not any(r.type == "X" for r in report.reports)

    def test_unknown_algorithm_rejected(self, corr_game):
        form = be.to_strategic_form(corr_game)
        with pytest.raises(ValueError, match="algorithme"):
            be.solve_strategic_form(form, "quantum_divination")


# ---------------------------------------------------------------------------
# 15. Sémantique NOT_FOUND / NUMERICAL (solveur stubbée)
# ---------------------------------------------------------------------------


class TestSolveSemantics:
    def test_not_found_is_not_infeasible(self, corr_game, monkeypatch):
        """NOT_FOUND : le jeu n'est jamais « infeasible » — le solveur a
        seulement echoue a produire un equilibre."""

        class _EmptyGame:
            def __init__(self, A, B):
                pass

            def support_enumeration(self):
                return iter(())

        monkeypatch.setattr(
            be, "nash", type("N", (), {"Game": _EmptyGame})()
        )
        form = be.to_strategic_form(corr_game)
        result = be.solve_strategic_form(form)
        assert result.status == "NOT_FOUND"
        assert not result.is_found
        assert "infeasible" in result.note
        assert "TOUJOURS" in result.note

    def test_numerical_error_is_separate_status(self, corr_game, monkeypatch):
        class _BoomGame:
            def __init__(self, A, B):
                pass

            def support_enumeration(self):
                raise FloatingPointError("divide by zero")

        monkeypatch.setattr(
            be, "nash", type("N", (), {"Game": _BoomGame})()
        )
        form = be.to_strategic_form(corr_game)
        result = be.solve_strategic_form(form)
        assert result.status == "NUMERICAL"
        assert not result.is_found
        assert result.equilibria == ()


# ---------------------------------------------------------------------------
# 16-17. Marginales + concordance oracle natif / validateur
# ---------------------------------------------------------------------------


class TestMarginalsAndConcordance:
    def test_marginals_by_type(self):
        """[0.5,0,0,0.5] sur AA,AB,BA,BB : H et L jouent chacun 1/2-1/2."""
        plans = [("A", "A"), ("A", "B"), ("B", "A"), ("B", "B")]
        out = be.marginals_by_type([0.5, 0.0, 0.0, 0.5], plans, ["H", "L"], ["A", "B"])
        np.testing.assert_allclose(out["H"], [0.5, 0.5])
        np.testing.assert_allclose(out["L"], [0.5, 0.5])

    def test_concordance_bos(self):
        """L'oracle natif et le validateur du module S'ACCORDENT sur les 8
        profils purs du BoS (3 BNE d'un cote, 5 non-BNE de l'autre)."""
        game = bos_game()
        form = be.to_strategic_form(game)
        n_agree = 0
        for p1 in form.plans[0]:
            for p2 in form.plans[1]:
                s1 = _pure_sigma(form.plans[0], p1)
                s2 = _pure_sigma(form.plans[1], p2)
                native = native_is_bne(game, form.plans[0], form.plans[1], s1, s2)
                report = be.validate_bne(game, form, s1, s2)
                assert native == report.is_bne, (p1, p2)
                n_agree += 1
        assert n_agree == 8

    def test_concordance_correlated(self, corr_game):
        """Meme accord sur les 16 profils purs de l'instance discriminante
        (aucun n'est BNE, du cote de l'oracle ET du validateur)."""
        form = be.to_strategic_form(corr_game)
        for p1 in form.plans[0]:
            for p2 in form.plans[1]:
                s1 = _pure_sigma(form.plans[0], p1)
                s2 = _pure_sigma(form.plans[1], p2)
                native = native_is_bne(corr_game, form.plans[0], form.plans[1], s1, s2)
                report = be.validate_bne(corr_game, form, s1, s2)
                assert native == report.is_bne == False, (p1, p2)
