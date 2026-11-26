"""Tests de `amd_synthesis` — synthese globale DSIC-IR (jalon 1 de #22381).

Ce que ces tests mesurent, et non ce qu'ils esperent :

- le temoin booleen et l'impossibilite de paiements strictement positifs de
  `AMD.lean` sont reproduits **au niveau de l'instance** (la preuve generale
  reste celle du noyau Lean, et ces tests ne la certifient pas) ;
- l'optimum CP-SAT est confronte a une enumeration exhaustive independante la
  ou celle-ci reste un temoin, et l'enumeration est refusee — avec son compte
  mesure — la ou elle ne l'est plus ;
- le verificateur rejette les mecanismes alteres en nommant agent, profil et
  deviation ;
- les deux semantiques de DSIC employees par les carnets (report sincere dans
  `16b` et `AMD.lean`, tous les reports dans `16c`) sont mesurees separement,
  avec les comptes publies par ces carnets.
"""

import itertools
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from amd_synthesis import (  # noqa: E402
    Mechanism,
    amd_domain,
    amd_star_mechanism,
    best_by_enumeration,
    count_admissible_at_profile,
    count_candidates,
    enumerate_mechanisms,
    public_project_domain,
    public_project_naive_mechanism,
    revenue,
    synthesize,
    unconstrained_revenue_bound,
    verify,
    verify_dsic_all_reports,
    verify_dsic_sincere_anchored,
    verify_ir_sincere,
    verify_utility,
    welfare,
)

PAY_01 = (0, 1)


# ---------------------------------------------------------------------------
# Témoin booléen d'AMD.lean
# ---------------------------------------------------------------------------


def test_amd_witness_passes_verification():
    """`o_star = r1 ET r2` avec paiements nuls est DSIC et IR sur tout le domaine."""
    domain = amd_domain()
    report = verify(domain, amd_star_mechanism(domain))
    assert report.ok, report.summary()
    assert report.dsic_violations == ()
    assert report.ir_violations == ()


def test_amd_witness_point_welfare_is_two():
    """`amd_star_J : J o_star true true = 2` — bien-être AU PROFIL (1, 1).

    `AMD.lean` n'a pas de prior : `J` est evalue en un profil. Ne pas confondre
    avec `welfare()`, qui somme sur le prior (voir le test suivant).
    """
    domain = amd_domain()
    star = amd_star_mechanism(domain)
    r = domain.profiles.index((1, 1))
    assert sum(domain.values[a][1][star.allocation[r]] for a in range(2)) == 2


def test_prior_weighted_welfare_aggregates_profiles():
    """Le bien-être pondéré n'est pas `J` : il somme sur tous les profils du prior.

    Le temoin ET ne contribue qu'en (1, 1) — donc 2, comme `J` par coincidence —
    mais l'optimum pondéré vaut 4, ce qui montre que les deux grandeurs divergent
    des que l'allocation varie selon le profil.
    """
    domain = amd_domain()
    star = amd_star_mechanism(domain)
    assert welfare(domain, star) == 2
    solved = synthesize(domain, "welfare")
    assert solved.objective_value == 4
    assert solved.objective_value != 2


def test_amd_welfare_optimal_at_true_profile_over_all_allocations():
    """`amd_star_J_optimal` : aucun arbre d'allocation ne depasse 2 au profil (1, 1).

    Enumeration exhaustive des 2^4 allocations a paiements nuls, soit 16
    candidats — la borne est mesuree, pas reprise du theoreme.
    """
    domain = amd_domain()
    r = domain.profiles.index((1, 1))
    best = 0
    for allocation in itertools.product(range(2), repeat=len(domain.profiles)):
        point = sum(domain.values[a][1][allocation[r]] for a in range(2))
        best = max(best, point)
    assert best == 2


# ---------------------------------------------------------------------------
# Impossibilité de paiements strictement positifs partout
# ---------------------------------------------------------------------------


def test_impossibility_strict_payments_infeasible_cpsat():
    """`impossibility_strict_payments` : paiements >= 1 partout rend IR impossible."""
    result = synthesize(amd_domain(payment_bounds=(1, 4)), payments_at_least=1)
    assert result.status == "INFEASIBLE"
    assert result.mechanism is None
    assert result.certified is False


def test_impossibility_strict_payments_no_admissible_by_enumeration():
    """Le meme verdict par enumeration : zero mecanisme IR sur la grille {1, 2}."""
    domain = amd_domain(payment_bounds=(1, 2))
    result = best_by_enumeration(domain, (1, 2))
    assert result.n_candidates == 4096
    assert result.n_admissible == 0
    assert result.mechanism is None and result.value is None


# ---------------------------------------------------------------------------
# Optimum CP-SAT contre énumération exhaustive
# ---------------------------------------------------------------------------


def test_synthesis_matches_exhaustive_revenue():
    """Le revenu optimal de CP-SAT egale l'optimum enumere sur le petit domaine."""
    domain = amd_domain(payment_bounds=(0, 1))
    enumerated = best_by_enumeration(domain, PAY_01, "revenue")
    solved = synthesize(domain, "revenue")
    assert enumerated.n_candidates == 4096
    assert solved.certified, solved.status
    assert solved.objective_value == enumerated.value == 2


def test_synthesis_matches_exhaustive_welfare():
    """Le bien-etre optimal de CP-SAT egale l'optimum enumere sur le petit domaine."""
    domain = amd_domain(payment_bounds=(0, 1))
    enumerated = best_by_enumeration(domain, PAY_01, "welfare")
    solved = synthesize(domain, "welfare")
    assert solved.certified, solved.status
    assert solved.objective_value == enumerated.value == 4


def test_synthesis_result_verified_independently():
    """Le mecanisme rendu par le solveur passe le verificateur independant.

    Les deux objectifs sont relus par le verificateur, qui recalcule la valeur
    annoncee depuis les seules tables du mecanisme.
    """
    domain = amd_domain()
    revenue_result = synthesize(domain, "revenue")
    assert revenue_result.mechanism is not None
    revenue_report = verify(
        domain, revenue_result.mechanism, expected_revenue=revenue_result.objective_value
    )
    assert revenue_report.ok, revenue_report.summary()
    assert revenue_report.revenue == revenue_result.objective_value

    welfare_result = synthesize(domain, "welfare")
    assert welfare_result.mechanism is not None
    welfare_report = verify(
        domain, welfare_result.mechanism, expected_welfare=welfare_result.objective_value
    )
    assert welfare_report.ok, welfare_report.summary()
    assert welfare_report.welfare == welfare_result.objective_value


def test_synthesis_is_certified_and_gap_zero():
    """Statut, borne et ecart : OPTIMAL implique ecart nul, et `certified` le dit."""
    result = synthesize(amd_domain(), "revenue")
    assert result.status == "OPTIMAL"
    assert result.certified is True
    assert result.gap == 0.0
    assert result.objective_bound == result.objective_value
    assert result.n_vars > 0 and result.n_constraints > 0


def test_revenue_strictly_below_unconstrained_bound():
    """L'incitation coute : le revenu DSIC reste sous la borne sans incitation."""
    domain = amd_domain(payment_bounds=(0, 1))
    bound = unconstrained_revenue_bound(domain)
    solved = synthesize(domain, "revenue")
    assert bound == 4
    assert solved.objective_value == 2
    assert solved.objective_value < bound


# ---------------------------------------------------------------------------
# Témoins négatifs
# ---------------------------------------------------------------------------


def test_public_project_naive_rule_violates_dsic():
    """Allouer profil par profil sans incitation viole une incitation, nommement."""
    domain = public_project_domain(cost=4, values_by_type=(1, 3))
    naive = public_project_naive_mechanism(domain, cost=4)
    report = verify(domain, naive)
    assert not report.ok
    assert report.ir_violations == ()
    assert report.dsic_violations, "la regle naive doit violer DSIC"
    violation = report.dsic_violations[0]
    assert violation.agent in (0, 1)
    assert len(violation.profile) == domain.n_agents
    assert violation.deviation is not None
    assert violation.deviating_utility > violation.sincere_utility


def test_public_project_synthesis_is_incentive_compatible():
    """Sur le projet public a cout explicite, le solveur trouve un mecanisme admissible."""
    domain = public_project_domain(cost=4, values_by_type=(1, 3))
    result = synthesize(domain, "welfare")
    assert result.status in ("OPTIMAL", "FEASIBLE"), result.status
    assert result.mechanism is not None
    report = verify(domain, result.mechanism)
    assert report.ok, report.summary()


def test_public_project_revenue_matches_the_pivot_rule():
    """Sur ce projet public, le revenu optimal est celui des paiements pivot (VCG) : 10.

    Le temoin est calcule ici, sans solveur : paiement de `i` = cout moins la somme
    des valeurs des AUTRES agents, borne par sa propre valeur (IR). Le solveur
    retrouve ce revenu sous DSIC + IR, ce qui rend la coincidence falsifiable.
    """
    cost = 4
    domain = public_project_domain(cost=cost, values_by_type=(1, 3))
    pivot_total = 0
    for profile in domain.profiles:
        own = [domain.values[a][profile[a]][1] for a in range(domain.n_agents)]
        if sum(own) < cost:
            continue
        for a in range(domain.n_agents):
            others = sum(own) - own[a]
            pivot_total += max(0, cost - others)

    result = synthesize(domain, "revenue")
    assert result.mechanism is not None and result.certified
    assert pivot_total == 10
    assert result.objective_value == pivot_total
    assert verify(domain, result.mechanism).ok


def test_tampered_payment_is_rejected_naming_agent_and_profile():
    """Un paiement baisse d'un cran casse soit IR soit DSIC, et le rapport le nomme."""
    domain = amd_domain(payment_bounds=(0, 1))
    solved = synthesize(domain, "revenue")
    assert solved.mechanism is not None
    allocation = solved.mechanism.allocation
    tampered_rows = []
    for r, row in enumerate(solved.mechanism.payments):
        tampered_rows.append(tuple(0 if p == 1 else 1 for p in row))
    tampered = Mechanism(allocation=allocation, payments=tuple(tampered_rows))
    report = verify(domain, tampered)
    assert not report.ok
    assert report.dsic_violations or report.ir_violations
    violation = (report.ir_violations or report.dsic_violations)[0]
    assert 0 <= violation.agent < domain.n_agents
    assert violation.profile in domain.profiles


def test_out_of_bounds_payment_is_flagged():
    """Un paiement hors des bornes declarees est signale, sans etre confondu avec DSIC."""
    domain = amd_domain(payment_bounds=(0, 1))
    star = amd_star_mechanism(domain)
    outside = Mechanism(
        allocation=star.allocation,
        payments=tuple((7, 0) for _ in domain.profiles),
    )
    report = verify(domain, outside)
    assert report.domain_ok is True
    assert report.bounds_ok is False
    assert not report.ok


def test_wrong_length_allocation_is_a_domain_violation():
    """Une table d'allocation de mauvaise longueur est un defaut de domaine."""
    domain = amd_domain()
    broken = Mechanism(allocation=(0,), payments=((0, 0),))
    report = verify(domain, broken)
    assert report.domain_ok is False
    assert not report.ok


def test_expected_objective_mismatch_raises():
    """Le verificateur refuse une annonce fausse d'objectif au lieu de l'avaler."""
    domain = amd_domain()
    star = amd_star_mechanism(domain)
    with pytest.raises(AssertionError):
        verify(domain, star, expected_welfare=99)
    with pytest.raises(AssertionError):
        verify(domain, star, expected_revenue=99)


# ---------------------------------------------------------------------------
# Vérificateur indépendant
# ---------------------------------------------------------------------------


def test_verifier_utility_matches_definition():
    """L'utilite du verificateur est bien valeur moins paiement, au profil reporte."""
    domain = public_project_domain(cost=4, values_by_type=(1, 3))
    mechanism = public_project_naive_mechanism(domain, cost=4)
    for agent in range(domain.n_agents):
        for report in domain.profiles:
            r = domain.profiles.index(report)
            expected = (
                domain.values[agent][1][mechanism.allocation[r]]
                - mechanism.payments[r][agent]
            )
            assert verify_utility(domain, mechanism, agent, 1, report) == expected


def test_revenue_and_welfare_recomputed_by_hand():
    """Revenu et bien-etre se recalculent depuis les tables, sans le solveur."""
    domain = amd_domain()
    star = amd_star_mechanism(domain)
    assert revenue(domain, star) == 0
    assert welfare(domain, star) == 2
    charged = Mechanism(allocation=star.allocation, payments=tuple((1, 0) for _ in domain.profiles))
    assert revenue(domain, charged) == len(domain.profiles)


# ---------------------------------------------------------------------------
# Prior nul : un profil ne disparaît pas du domaine
# ---------------------------------------------------------------------------


def test_zero_weight_profile_stays_in_the_domain():
    """Poids nul sur (1, 1) : le profil reste dans le domaine declare."""
    domain = amd_domain(
        weights=(((0, 0), 1), ((0, 1), 1), ((1, 0), 1), ((1, 1), 0))
    )
    assert len(domain.profiles) == 4
    assert domain.prior[(1, 1)] == 0


def test_zero_weight_does_not_remove_dsic_constraint():
    """Un mecanisme fautif SEULEMENT au profil a poids nul est quand meme rejete.

    Paiement de l'agent 0 mis a 1 au seul profil (0, 0), nul partout ailleurs :
    toute la faute tombe sur le profil de poids nul. Un verificateur qui lirait le
    domaine dans le prior ne verrait rien ; celui-ci refuse, et ne nomme que (0, 0).
    """
    domain = amd_domain()
    zeroed = amd_domain(weights=(((0, 0), 0), ((0, 1), 1), ((1, 0), 1), ((1, 1), 1)))
    star = amd_star_mechanism(domain)
    r00 = domain.profiles.index((0, 0))
    payments = list(star.payments)
    payments[r00] = (1, 0)
    mechanism = Mechanism(allocation=star.allocation, payments=tuple(payments))
    report = verify(zeroed, mechanism)
    assert not report.ok
    hit = {v.profile for v in report.dsic_violations} | {v.profile for v in report.ir_violations}
    assert hit == {(0, 0)}


def test_zero_weight_does_not_change_the_admissible_set_size():
    """Le compte d'admissibles ne depend pas des poids : le domaine est declare."""
    full = amd_domain(payment_bounds=(0, 1))
    zeroed = amd_domain(
        weights=(((0, 0), 0), ((0, 1), 1), ((1, 0), 1), ((1, 1), 1)),
        payment_bounds=(0, 1),
    )
    assert count_admissible_at_profile(full, (1, 1), PAY_01, "sincere") == count_admissible_at_profile(
        zeroed, (1, 1), PAY_01, "sincere"
    )


# ---------------------------------------------------------------------------
# Les deux sémantiques, mesurées séparément
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "true_profile, sincere_expected, all_reports_expected",
    [
        ((0, 0), 1024, 16),
        ((0, 1), 1280, 25),
        ((1, 0), 1280, 25),
        ((1, 1), 1856, 47),
    ],
)
def test_semantics_counts_match_the_notebooks(true_profile, sincere_expected, all_reports_expected):
    """Les comptes publies par 16b (report sincere) et 16c (tous reports) sont reproduits.

    Meme espace de 4096 candidats, memes valeurs : la difference mesuree est
    celle des semantiques, pas celle des domaines.
    """
    domain = amd_domain(payment_bounds=(0, 1))
    assert count_admissible_at_profile(domain, true_profile, PAY_01, "sincere") == sincere_expected
    assert (
        count_admissible_at_profile(domain, true_profile, PAY_01, "all_reports")
        == all_reports_expected
    )


def test_all_reports_semantics_is_strictly_stronger():
    """Tout mecanisme admissible sous « tous les reports » l'est sous le report sincere.

    Mesure sur le profil (1, 1), celui ou l'ecart des deux semantiques est le plus
    large (1856 admissibles contre 47) : l'inclusion est stricte, donc les deux
    contrats ne peuvent pas etre confondus.
    """
    domain = amd_domain(payment_bounds=(0, 1))
    true_profile = (1, 1)
    sincerely_ok = []
    for mechanism in enumerate_mechanisms(domain, PAY_01, limit=10_000):
        u0 = verify_utility(domain, mechanism, 0, true_profile[0], true_profile)
        u1 = verify_utility(domain, mechanism, 1, true_profile[1], true_profile)
        deviations_ok = all(
            verify_utility(
                domain,
                mechanism,
                agent,
                true_profile[agent],
                true_profile[:agent] + (d,) + true_profile[agent + 1 :],
            )
            <= verify_utility(domain, mechanism, agent, true_profile[agent], true_profile)
            for agent in range(domain.n_agents)
            for d in range(domain.n_types)
            if d != true_profile[agent]
        )
        if u0 >= 0 and u1 >= 0 and deviations_ok:
            sincerely_ok.append(mechanism)
    strictly_ok = [
        m
        for m in sincerely_ok
        if not verify_dsic_all_reports(domain, m, true_profile)
        and not verify_ir_sincere(domain, m)
    ]
    assert len(strictly_ok) < len(sincerely_ok)
    assert len(strictly_ok) > 0


# ---------------------------------------------------------------------------
# Énumération : témoin sur petit domaine, impasse nommée sur grand
# ---------------------------------------------------------------------------


def test_count_candidates_is_exact_on_the_small_domain():
    """Le compte de candidats est exact : 2^4 allocations fois 2^8 paiements."""
    domain = amd_domain(payment_bounds=(0, 1))
    assert count_candidates(domain, PAY_01) == 4096
    assert sum(1 for _ in enumerate_mechanisms(domain, PAY_01)) == 4096


def _three_by_three_domain():
    """Domaine a 3 agents et 3 types : 27 profils, hors de portee de l'enumeration."""
    values = tuple(
        tuple(tuple(t * o for o in range(2)) for t in range(3)) for _ in range(3)
    )
    weights = tuple((profile, 1) for profile in itertools.product(range(3), repeat=3))
    from amd_synthesis import FiniteDomain

    return FiniteDomain(
        n_agents=3,
        n_types=3,
        n_outcomes=2,
        values=values,
        weights=weights,
        payment_bounds=(0, 1),
    )


def test_enumeration_refused_with_measured_count():
    """Au-dela de la limite, l'enumeration est refusee en nommant son compte mesure."""
    domain = _three_by_three_domain()
    total = count_candidates(domain, PAY_01)
    assert total > 2_000_000
    with pytest.raises(ValueError) as excinfo:
        next(enumerate_mechanisms(domain, PAY_01))
    assert str(total) in str(excinfo.value)


def test_large_domain_solved_by_cpsat_and_verified():
    """La ou l'enumeration est exclue, CP-SAT rend un mecanisme verifie."""
    domain = _three_by_three_domain()
    result = synthesize(domain, "revenue", time_limit_s=60)
    assert result.status in ("OPTIMAL", "FEASIBLE"), result.status
    assert result.mechanism is not None
    report = verify(domain, result.mechanism)
    assert report.ok, report.summary()
    if result.certified:
        assert result.gap == 0.0


# ---------------------------------------------------------------------------
# Validation du domaine
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "kwargs",
    [
        {"n_agents": 0, "n_types": 2, "n_outcomes": 2},
        {"n_agents": 2, "n_types": 0, "n_outcomes": 2},
        {"n_agents": 2, "n_types": 2, "n_outcomes": 1},
    ],
)
def test_domain_rejects_degenerate_sizes(kwargs):
    """Un domaine degenere est refuse a la construction, pas silencieusement accepte."""
    from amd_synthesis import FiniteDomain

    values = tuple(tuple((0, 1) for _ in range(2)) for _ in range(max(kwargs["n_agents"], 1)))
    with pytest.raises(ValueError):
        FiniteDomain(values=values, weights=(((0, 0), 1),), **kwargs)


def test_domain_rejects_negative_weight():
    """Un poids negatif n'est pas un prior : refus."""
    with pytest.raises(ValueError):
        amd_domain(weights=(((0, 0), -1), ((0, 1), 1)))


def test_domain_rejects_duplicate_profile():
    """Un profil present deux fois est ambigu : refus."""
    with pytest.raises(ValueError):
        amd_domain(weights=(((0, 0), 1), ((0, 0), 1)))


def test_domain_rejects_out_of_range_type():
    """Un type hors de [0, n_types) est refuse."""
    with pytest.raises(ValueError):
        amd_domain(weights=(((0, 2), 1),))


def test_domain_rejects_inverted_payment_bounds():
    """Des bornes de paiement inversees sont refusees."""
    with pytest.raises(ValueError):
        amd_domain(payment_bounds=(2, 1))


def test_subsidies_leave_the_revenue_optimum_unchanged_and_degenerate_welfare():
    """Ce que change le droit de subventionner, mesure sur le meme domaine.

    Un maximiseur de revenu ne paie jamais : autoriser les paiements negatifs
    laisse son optimum a 2. Un maximiseur de bien-etre, lui, atteint le meme
    bien-etre (4) en versant le maximum de subvention partout — revenu -32. La
    borne `payment_bounds` par defaut (agents paient) n'est donc pas une
    commodite de modelisation : sans elle, l'objectif de bien-etre est degenere.
    """
    restricted = amd_domain(payment_bounds=(0, 1))
    subsidised = amd_domain(payment_bounds=(-4, 1))
    assert synthesize(restricted, "revenue").objective_value == 2
    assert synthesize(subsidised, "revenue").objective_value == 2

    welfare_result = synthesize(subsidised, "welfare")
    assert welfare_result.objective_value == 4
    assert welfare_result.mechanism is not None
    assert revenue(subsidised, welfare_result.mechanism) == -32


def test_unknown_objective_rejected():
    """Un objectif inconnu est refuse, pas ignore."""
    with pytest.raises(ValueError):
        synthesize(amd_domain(), "revenue+")
