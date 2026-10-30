"""Synthese globale de mecanismes DSIC-IR sur un domaine fini (jalon 1 de #22381).

Ce module repond a une question que les carnets `GameTheory-16b` et
`GameTheory-16c` posent separement : existe-t-il un mecanisme, sur TOUT le
domaine declare a la fois, qui soit a la fois incitatif (DSIC), individuellement
rationnel (IR) et optimal pour un objectif ex ante ? Le generateur de `16b`
choisit une allocation sur un profil vrai puis pose des paiements nuls ; le
carnet `16c` enumere et extrait un revenu, mais avec un verificateur point-prior
quantifie sur les reports. Ici, l'allocation ET les paiements sont les variables
d'un seul probleme d'optimisation, resolu par CP-SAT, puis relus par un
verificateur independant qui ne partage ni utilite ni contraintes avec le
constructeur.

Semantique, enoncee une fois pour toutes
----------------------------------------

- **Paiement paye par l'agent** au mecanisme. L'utilite est quasi-lineaire :
  ``u_i = valeur[i][type][issue] - paiement``. C'est le signe de
  ``AMD.lean:55-56`` (``thetaVal t * issueVal o - p r``) et celui de ``16b``.
- **DSIC au sens ex post, ancre au report sincere**, universellement sur tout le
  domaine declare et sur toute deviation unilaterale : pour tout profil vrai
  ``x`` et tout agent ``i``, ``u_i(x_i, x) >= u_i(x_i, x avec i -> d)``. C'est
  ``AMD.lean:67-70``. Ce n'est **pas** une propriete interimaire (BIC), et ce
  n'est **pas** la variante « tous les reports » que ``16b`` nomme SUR-DURCIE et
  que ``16c`` emploie effectivement : les deux sont fournies separement
  (``verify_dsic_sincere_anchored`` et ``verify_dsic_all_reports``), nommees, et
  mesurees dans les tests — jamais confondues.
- **IR ex post au report sincere** : ``u_i(x_i, x) >= 0`` pour tout profil et
  tout agent (``AMD.lean:74-76``).
- Le **prior** est une table jointe de poids entiers. Un poids **nul** ne retire
  pas le profil du domaine : DSIC et IR restent quantifiees dessus. C'est
  l'erreur que l'acceptance de #22381 interdit explicitement.

Ce que le module ne fait pas
----------------------------

Il ne reimplemente ni l'enumeration de revenu de ``16c`` (cellule 6), ni le
generateur de ``16b`` (cellule 3), ni le WDP/VCG d'OR-Tools de
``Search/Part5-Frontieres/Frontieres-04``. Il ajoute l'objet qui manquait : une
table d'allocation **et** de paiements sous contraintes d'incitation, valable sur
tout le domaine, avec sa borne d'objectif et son ecart prouves par le solveur.

Ce que ce module ne prouve pas
------------------------------

Rien ici ne certifie les theoremes de ``AMD.lean`` : ils restent prouves par le
noyau Lean sur leur propre domaine. Les tests reproduisent le temoin booleen et
l'impossibilite de paiements strictement positifs **au niveau de l'instance**,
ce qui est un controle de coherence, pas une preuve.

Voir #22381 (part of #18706), extension de la phase bayesienne de #2610.
"""

from __future__ import annotations

import itertools
import time
from dataclasses import dataclass
from typing import Iterator, Sequence

from ortools.sat.python import cp_model

Profile = tuple[int, ...]

SEMANTICS_SINCERE = "dsic-sincere-anchored-ex-post"
SEMANTICS_ALL_REPORTS = "dsic-all-reports (sur-durcie, contrat 16c)"


# ---------------------------------------------------------------------------
# Domaine fini
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class FiniteDomain:
    """Domaine fini declare : agents, types, issues, valeurs entieres, prior joint.

    ``values[a][t][o]`` est le paiement entier que l'agent ``a``, de type ``t``,
    recoit de l'issue ``o``. ``weights`` est une suite de couples
    ``(profil, poids)`` ; un profil absent de la table a un poids nul, et un
    poids nul **ne retire pas** le profil du domaine (voir le module).

    ``payment_bounds`` borne les paiements entiers du mecanisme recherche.
    """

    n_agents: int
    n_types: int
    n_outcomes: int
    values: tuple[tuple[tuple[int, ...], ...], ...]
    weights: tuple[tuple[Profile, int], ...]
    payment_bounds: tuple[int, int] = (0, 4)

    def __post_init__(self) -> None:
        if self.n_agents < 1:
            raise ValueError("n_agents doit etre >= 1")
        if self.n_types < 1:
            raise ValueError("n_types doit etre >= 1")
        if self.n_outcomes < 2:
            raise ValueError("n_outcomes doit etre >= 2 (une issue unique ne pose aucun choix)")
        if len(self.values) != self.n_agents:
            raise ValueError(f"values porte {len(self.values)} agents, attendu {self.n_agents}")
        for a, by_type in enumerate(self.values):
            if len(by_type) != self.n_types:
                raise ValueError(f"values[{a}] porte {len(by_type)} types, attendu {self.n_types}")
            for t, row in enumerate(by_type):
                if len(row) != self.n_outcomes:
                    raise ValueError(
                        f"values[{a}][{t}] porte {len(row)} issues, attendu {self.n_outcomes}"
                    )
        lo, hi = self.payment_bounds
        if lo > hi:
            raise ValueError(f"bornes de paiement incoherentes : {self.payment_bounds}")
        seen: set[Profile] = set()
        for profile, w in self.weights:
            if len(profile) != self.n_agents:
                raise ValueError(f"profil {profile} de longueur {len(profile)}, attendu {self.n_agents}")
            for t in profile:
                if not 0 <= t < self.n_types:
                    raise ValueError(f"profil {profile} : type {t} hors de [0, {self.n_types})")
            if w < 0:
                raise ValueError(f"poids negatif pour {profile} : {w}")
            if profile in seen:
                raise ValueError(f"profil {profile} present deux fois dans le prior")
            seen.add(profile)

    @property
    def profiles(self) -> tuple[Profile, ...]:
        """Tout le domaine declare : le produit cartesien des types, trie.

        Le domaine est **declare**, pas derive du prior : c'est ce qui garantit
        qu'un poids nul ne retire pas silencieusement un profil de DSIC et d'IR.
        """
        return tuple(itertools.product(range(self.n_types), repeat=self.n_agents))

    @property
    def prior(self) -> dict[Profile, int]:
        return dict(self.weights)


@dataclass(frozen=True)
class Mechanism:
    """Une table d'allocation et une table de paiements, indexees par profil.

    ``allocation[r]`` est l'issue retenue quand le profil reporte est
    ``domain.profiles[r]`` ; ``payments[r][i]`` est le paiement de l'agent ``i``
    a ce meme profil. Les paiements sont payes **par** l'agent.
    """

    allocation: tuple[int, ...]
    payments: tuple[tuple[int, ...], ...]


# ---------------------------------------------------------------------------
# Verificateur independant
#
# L'arithmetique ci-dessous est ecrite depuis la definition, et le constructeur
# CP-SAT (plus bas) n'appelle aucune de ces fonctions : il construit ses
# expressions lineaires a partir des tables du domaine. C'est cette separation
# qui rend la verification independante, et les tests la mesurent en comparant
# les deux lectures sur des mecanismes tires au hasard.
# ---------------------------------------------------------------------------


def verify_utility(
    domain: FiniteDomain,
    mechanism: Mechanism,
    agent: int,
    true_type: int,
    reported_profile: Profile,
) -> int:
    """Utilite de l'agent `agent`, de type vrai `true_type`, au profil reporte.

    Quasi-lineaire, paiement paye par l'agent : ``valeur - paiement``.
    """
    r = domain.profiles.index(reported_profile)
    outcome = mechanism.allocation[r]
    return domain.values[agent][true_type][outcome] - mechanism.payments[r][agent]


@dataclass(frozen=True)
class Violation:
    """Une violation nommee : le rapport dit qui, ou, et de combien."""

    kind: str
    agent: int
    profile: Profile
    deviation: int | None
    sincere_utility: int
    deviating_utility: int | None

    def __str__(self) -> str:
        if self.kind == "dsic":
            return (
                f"DSIC agent {self.agent} profil {self.profile} deviation {self.deviation} : "
                f"{self.sincere_utility} -> {self.deviating_utility}"
            )
        return f"IR agent {self.agent} profil {self.profile} : utilite {self.sincere_utility} < 0"


@dataclass(frozen=True)
class VerificationReport:
    """Rapport de verification : violations nommees, objectifs recomputes."""

    domain_ok: bool
    bounds_ok: bool
    dsic_violations: tuple[Violation, ...]
    ir_violations: tuple[Violation, ...]
    revenue: int
    welfare: int
    semantics: str

    @property
    def ok(self) -> bool:
        return self.domain_ok and self.bounds_ok and not self.dsic_violations and not self.ir_violations

    def summary(self) -> str:
        return (
            f"{'OK' if self.ok else 'REJET'} [{self.semantics}] "
            f"dsic={len(self.dsic_violations)} ir={len(self.ir_violations)} "
            f"domaine={'ok' if self.domain_ok else 'ko'} bornes={'ok' if self.bounds_ok else 'ko'} "
            f"revenu={self.revenue} bien_etre={self.welfare}"
        )


def _check_shape(domain: FiniteDomain, mechanism: Mechanism) -> bool:
    profiles = domain.profiles
    if len(mechanism.allocation) != len(profiles):
        return False
    if len(mechanism.payments) != len(profiles):
        return False
    for outcome in mechanism.allocation:
        if not 0 <= outcome < domain.n_outcomes:
            return False
    for row in mechanism.payments:
        if len(row) != domain.n_agents:
            return False
    return True


def _check_bounds(domain: FiniteDomain, mechanism: Mechanism) -> bool:
    lo, hi = domain.payment_bounds
    return all(lo <= p <= hi for row in mechanism.payments for p in row)


def verify_dsic_sincere_anchored(
    domain: FiniteDomain, mechanism: Mechanism
) -> tuple[Violation, ...]:
    """DSIC ex post ancre au report sincere, sur tout le domaine declare.

    Pour chaque profil **vrai** `x` et chaque agent : aucun report unilateral
    autre que `x_i` ne donne a `i` une utilite strictement superieure, son type
    vrai restant `x_i`. Semantique de `AMD.lean:67-70`.
    """
    violations: list[Violation] = []
    for profile in domain.profiles:
        for agent in range(domain.n_agents):
            sincere = verify_utility(domain, mechanism, agent, profile[agent], profile)
            for deviation in range(domain.n_types):
                if deviation == profile[agent]:
                    continue
                deviating_profile = (
                    profile[:agent] + (deviation,) + profile[agent + 1 :]
                )
                deviating = verify_utility(
                    domain, mechanism, agent, profile[agent], deviating_profile
                )
                if deviating > sincere:
                    violations.append(
                        Violation(
                            kind="dsic",
                            agent=agent,
                            profile=profile,
                            deviation=deviation,
                            sincere_utility=sincere,
                            deviating_utility=deviating,
                        )
                    )
    return tuple(violations)


def verify_dsic_all_reports(
    domain: FiniteDomain, mechanism: Mechanism, true_profile: Profile
) -> tuple[Violation, ...]:
    """Variante **sur-durcie** : quantification sur les reports, types vrais fixes.

    C'est le contrat effectivement employe par `16c` (`verif_dsic`, point-prior) :
    les types vrais sont injectes, et la condition est verifiee a **chaque profil
    reporte**, pas seulement au report sincere. `16b` nomme cette variante
    SUR-DURCIE et demande de ne pas s'en servir comme critere d'admissibilite
    (reserve #12211) ; `AMD.lean` ne la prouve pas non plus.

    Fournie ici pour que les deux semantiques restent **distinguables** : les
    tests mesurent l'inclusion stricte de celle-ci dans l'autre.
    """
    violations: list[Violation] = []
    for report in domain.profiles:
        for agent in range(domain.n_agents):
            true_type = true_profile[agent]
            sincere = verify_utility(domain, mechanism, agent, true_type, report)
            for deviation in range(domain.n_types):
                if deviation == report[agent]:
                    continue
                deviating_report = (
                    report[:agent] + (deviation,) + report[agent + 1 :]
                )
                deviating = verify_utility(domain, mechanism, agent, true_type, deviating_report)
                if deviating > sincere:
                    violations.append(
                        Violation(
                            kind="dsic",
                            agent=agent,
                            profile=report,
                            deviation=deviation,
                            sincere_utility=sincere,
                            deviating_utility=deviating,
                        )
                    )
    return tuple(violations)


def verify_ir_sincere(domain: FiniteDomain, mechanism: Mechanism) -> tuple[Violation, ...]:
    """IR ex post au report sincere : utilite non negative pour tout agent et profil."""
    violations: list[Violation] = []
    for profile in domain.profiles:
        for agent in range(domain.n_agents):
            u = verify_utility(domain, mechanism, agent, profile[agent], profile)
            if u < 0:
                violations.append(
                    Violation(
                        kind="ir",
                        agent=agent,
                        profile=profile,
                        deviation=None,
                        sincere_utility=u,
                        deviating_utility=None,
                    )
                )
    return tuple(violations)


def revenue(domain: FiniteDomain, mechanism: Mechanism) -> int:
    """Revenu attendu : somme ponderee par le prior des paiements collectes."""
    prior = domain.prior
    total = 0
    for r, profile in enumerate(domain.profiles):
        w = prior.get(profile, 0)
        if w:
            total += w * sum(mechanism.payments[r])
    return total


def welfare(domain: FiniteDomain, mechanism: Mechanism) -> int:
    """Bien-etre attendu : valeurs des agents a l'allocation, hors transferts.

    Les paiements n'y entrent pas : ils s'annulent entre agents dans le surplus
    total (le mecanisme encaisse ce que les agents paient), et les inclure
    compterait deux fois le transfert.
    """
    prior = domain.prior
    total = 0
    for r, profile in enumerate(domain.profiles):
        w = prior.get(profile, 0)
        if w:
            outcome = mechanism.allocation[r]
            total += w * sum(domain.values[a][profile[a]][outcome] for a in range(domain.n_agents))
    return total


def verify(
    domain: FiniteDomain,
    mechanism: Mechanism,
    *,
    expected_revenue: int | None = None,
    expected_welfare: int | None = None,
) -> VerificationReport:
    """Verification complete et independante d'un mecanisme.

    Reconnait la forme du domaine, les bornes de paiement, DSIC (report sincere),
    IR, et recalcule revenu et bien-etre depuis les tables. Ne partage aucune
    contrainte, aucune utilite et aucun etat avec le constructeur CP-SAT.
    """
    domain_ok = _check_shape(domain, mechanism)
    bounds_ok = domain_ok and _check_bounds(domain, mechanism)
    if not domain_ok:
        return VerificationReport(
            domain_ok=False,
            bounds_ok=False,
            dsic_violations=(),
            ir_violations=(),
            revenue=0,
            welfare=0,
            semantics=SEMANTICS_SINCERE,
        )
    dsic = verify_dsic_sincere_anchored(domain, mechanism)
    ir = verify_ir_sincere(domain, mechanism)
    rev = revenue(domain, mechanism)
    welf = welfare(domain, mechanism)
    if expected_revenue is not None and rev != expected_revenue:
        raise AssertionError(f"revenu recalcule {rev} != annonce {expected_revenue}")
    if expected_welfare is not None and welf != expected_welfare:
        raise AssertionError(f"bien-etre recalcule {welf} != annonce {expected_welfare}")
    return VerificationReport(
        domain_ok=True,
        bounds_ok=bounds_ok,
        dsic_violations=dsic,
        ir_violations=ir,
        revenue=rev,
        welfare=welf,
        semantics=SEMANTICS_SINCERE,
    )


def unconstrained_revenue_bound(domain: FiniteDomain) -> int:
    """Borne superieure du revenu quand toute incitation serait ignoree.

    Chaque agent paierait son surplus entier a chaque profil :
    ``sum_r w_r * sum_i max_o values[i][r_i][o]``. Ce n'est pas un revenu
    atteignable sous DSIC et IR — c'est la borne qui rend l'ecart d'incitation
    mesurable plutot qu'affirme.
    """
    prior = domain.prior
    total = 0
    for profile in domain.profiles:
        w = prior.get(profile, 0)
        if w:
            total += w * sum(max(domain.values[a][profile[a]]) for a in range(domain.n_agents))
    return total


# ---------------------------------------------------------------------------
# Constructeur CP-SAT
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class SynthesisResult:
    """Resultat de synthese, avec le statut, la borne et l'ecart du solveur.

    ``certified`` n'est vrai que sur `OPTIMAL` : un statut `FEASIBLE` donne un
    mecanisme admissible mais **pas** un optimum certifie, et l'ecart le dit.
    """

    mechanism: Mechanism | None
    status: str
    objective: str
    objective_value: int | None
    objective_bound: int | None
    gap: float | None
    certified: bool
    n_vars: int
    n_constraints: int
    solve_time_s: float


def synthesize(
    domain: FiniteDomain,
    objective: str = "revenue",
    *,
    time_limit_s: float | None = None,
    payments_at_least: int | None = None,
    workers: int = 1,
    seed: int = 0,
) -> SynthesisResult:
    """Synthetise un mecanisme DSIC + IR sur tout le domaine, par CP-SAT.

    ``objective`` vaut ``"revenue"`` (revenu attendu) ou ``"welfare"``
    (bien-etre attendu). ``payments_at_least`` force un plancher de paiement sur
    tous les profils : c'est l'instance negative qui reproduit
    ``impossibility_strict_payments`` de `AMD.lean:125-127`.
    """
    if objective not in ("revenue", "welfare"):
        raise ValueError(f"objectif inconnu : {objective!r}")
    profiles = domain.profiles
    n_profiles = len(profiles)
    lo, hi = domain.payment_bounds
    if payments_at_least is not None and payments_at_least > hi:
        raise ValueError(
            f"payments_at_least={payments_at_least} hors des bornes {domain.payment_bounds} : "
            "l'instance serait vide par construction, pas par incitation"
        )
    prior = domain.prior

    model = cp_model.CpModel()
    x: dict[tuple[int, int], cp_model.IntVar] = {}
    for r in range(n_profiles):
        row = []
        for o in range(domain.n_outcomes):
            var = model.new_bool_var(f"x_{r}_{o}")
            x[(r, o)] = var
            row.append(var)
        model.add_exactly_one(row)
    pay: dict[tuple[int, int], cp_model.IntVar] = {}
    for r in range(n_profiles):
        for a in range(domain.n_agents):
            floor = lo if payments_at_least is None else max(lo, payments_at_least)
            pay[(r, a)] = model.new_int_var(floor, hi, f"p_{r}_{a}")

    index = {profile: r for r, profile in enumerate(profiles)}

    def outcome_expr(r: int, agent: int, type_: int) -> cp_model.LinearExpr:
        """Expression lineaire de la valeur de `agent` de type `type_` au profil `r`."""
        return sum(
            domain.values[agent][type_][o] * x[(r, o)] for o in range(domain.n_outcomes)
        )

    # DSIC, ancre au report sincere, sur tout le domaine declare.
    for r, profile in enumerate(profiles):
        for agent in range(domain.n_agents):
            sincere = outcome_expr(r, agent, profile[agent]) - pay[(r, agent)]
            for deviation in range(domain.n_types):
                if deviation == profile[agent]:
                    continue
                r_dev = index[profile[:agent] + (deviation,) + profile[agent + 1 :]]
                deviating = outcome_expr(r_dev, agent, profile[agent]) - pay[(r_dev, agent)]
                model.add(sincere >= deviating)

    # IR ex post au report sincere.
    for r, profile in enumerate(profiles):
        for agent in range(domain.n_agents):
            model.add(outcome_expr(r, agent, profile[agent]) - pay[(r, agent)] >= 0)

    if objective == "revenue":
        expr = sum(prior.get(profile, 0) * sum(pay[(r, a)] for a in range(domain.n_agents))
                   for r, profile in enumerate(profiles))
    else:
        expr = sum(
            prior.get(profile, 0) * sum(outcome_expr(r, a, profile[a]) for a in range(domain.n_agents))
            for r, profile in enumerate(profiles)
        )
    model.maximize(expr)

    solver = cp_model.CpSolver()
    solver.parameters.num_search_workers = workers
    solver.parameters.random_seed = seed
    if time_limit_s is not None:
        solver.parameters.max_time_in_seconds = time_limit_s
    started = time.perf_counter()
    status = solver.solve(model)
    elapsed = time.perf_counter() - started

    names = {
        cp_model.OPTIMAL: "OPTIMAL",
        cp_model.FEASIBLE: "FEASIBLE",
        cp_model.INFEASIBLE: "INFEASIBLE",
        cp_model.MODEL_INVALID: "MODEL_INVALID",
        cp_model.UNKNOWN: "UNKNOWN",
    }
    status_name = names.get(status, str(status))
    certified = status == cp_model.OPTIMAL
    mechanism: Mechanism | None = None
    value: int | None = None
    bound: int | None = None
    gap: float | None = None
    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        allocation: list[int] = []
        for r in range(n_profiles):
            chosen = [o for o in range(domain.n_outcomes) if solver.value(x[(r, o)]) == 1]
            if len(chosen) != 1:
                raise RuntimeError(f"allocation non unicite au profil {profiles[r]} : {chosen}")
            allocation.append(chosen[0])
        mechanism = Mechanism(
            allocation=tuple(allocation),
            payments=tuple(
                tuple(int(solver.value(pay[(r, a)])) for a in range(domain.n_agents))
                for r in range(n_profiles)
            ),
        )
        value = int(round(solver.objective_value))
        bound = int(round(solver.best_objective_bound))
        if certified:
            gap = 0.0
        elif value:
            gap = (bound - value) / abs(value)
        else:
            gap = None
    return SynthesisResult(
        mechanism=mechanism,
        status=status_name,
        objective=objective,
        objective_value=value,
        objective_bound=bound,
        gap=gap,
        certified=certified,
        n_vars=len(x) + len(pay),
        n_constraints=len(model.proto.constraints),
        solve_time_s=elapsed,
    )


# ---------------------------------------------------------------------------
# Enumeration exhaustive : le temoin, pas le concurrent
# ---------------------------------------------------------------------------


def count_candidates(domain: FiniteDomain, payment_values: Sequence[int]) -> int:
    """Nombre exact de mecanismes a enumerer sur ce domaine et cette grille.

    C'est le nombre qui decide si l'enumeration est encore un temoin ou deja une
    impasse — mesure, jamais affirme.
    """
    n_profiles = len(domain.profiles)
    return (domain.n_outcomes**n_profiles) * (len(payment_values) ** (n_profiles * domain.n_agents))


def enumerate_mechanisms(
    domain: FiniteDomain,
    payment_values: Sequence[int],
    *,
    limit: int = 2_000_000,
) -> Iterator[Mechanism]:
    """Enumere tous les mecanismes admissibles sur la grille de paiements.

    Leve ``ValueError`` au-dela de ``limit`` candidats, en **nommant le compte
    mesure** : une enumeration refusee doit dire pourquoi, pas echouer en silence
    ni tourner indefiniment.
    """
    n_profiles = len(domain.profiles)
    total = count_candidates(domain, payment_values)
    if total > limit:
        raise ValueError(
            f"enumeration refusee : {total} candidats > limite {limit} "
            f"({n_profiles} profils, {domain.n_outcomes} issues, "
            f"{len(payment_values)} valeurs de paiement)"
        )
    for allocation in itertools.product(range(domain.n_outcomes), repeat=n_profiles):
        for flat in itertools.product(payment_values, repeat=n_profiles * domain.n_agents):
            payments = tuple(
                tuple(flat[r * domain.n_agents + a] for a in range(domain.n_agents))
                for r in range(n_profiles)
            )
            yield Mechanism(allocation=allocation, payments=payments)


@dataclass(frozen=True)
class EnumerationResult:
    """Meilleur mecanisme admissible trouve par enumeration exhaustive."""

    mechanism: Mechanism | None
    value: int | None
    n_candidates: int
    n_admissible: int
    objective: str


def best_by_enumeration(
    domain: FiniteDomain,
    payment_values: Sequence[int],
    objective: str = "revenue",
    *,
    limit: int = 2_000_000,
) -> EnumerationResult:
    """Meilleur mecanisme admissible par force brute, sur un domaine enumerable."""
    if objective not in ("revenue", "welfare"):
        raise ValueError(f"objectif inconnu : {objective!r}")
    best: Mechanism | None = None
    best_value: int | None = None
    admissible = 0
    for mechanism in enumerate_mechanisms(domain, payment_values, limit=limit):
        if verify_dsic_sincere_anchored(domain, mechanism) or verify_ir_sincere(domain, mechanism):
            continue
        admissible += 1
        value = revenue(domain, mechanism) if objective == "revenue" else welfare(domain, mechanism)
        if best_value is None or value > best_value:
            best, best_value = mechanism, value
    return EnumerationResult(
        mechanism=best,
        value=best_value,
        n_candidates=count_candidates(domain, payment_values),
        n_admissible=admissible,
        objective=objective,
    )


def count_admissible_at_profile(
    domain: FiniteDomain,
    true_profile: Profile,
    payment_values: Sequence[int],
    semantics: str,
) -> int:
    """Compte des mecanismes admissibles pour un profil vrai donne.

    ``semantics`` vaut ``"sincere"`` (contrat 16b / `AMD.lean`) ou
    ``"all_reports"`` (contrat effectif de 16c). Le meme espace de candidats est
    parcouru dans les deux cas : la difference mesuree est celle des semantiques,
    pas celle des domaines.
    """
    if semantics not in ("sincere", "all_reports"):
        raise ValueError(f"semantique inconnue : {semantics!r}")
    count = 0
    for mechanism in enumerate_mechanisms(domain, payment_values):
        violated = False
        for agent in range(domain.n_agents):
            true_type = true_profile[agent]
            if semantics == "sincere":
                u = verify_utility(domain, mechanism, agent, true_type, true_profile)
                if u < 0:
                    violated = True
                    break
                for deviation in range(domain.n_types):
                    if deviation == true_profile[agent]:
                        continue
                    report = true_profile[:agent] + (deviation,) + true_profile[agent + 1 :]
                    if verify_utility(domain, mechanism, agent, true_type, report) > u:
                        violated = True
                        break
            else:
                for report in domain.profiles:
                    u = verify_utility(domain, mechanism, agent, true_type, report)
                    if u < 0:
                        violated = True
                        break
                    if any(
                        verify_utility(
                            domain,
                            mechanism,
                            agent,
                            true_type,
                            report[:agent] + (d,) + report[agent + 1 :],
                        )
                        > u
                        for d in range(domain.n_types)
                        if d != report[agent]
                    ):
                        violated = True
                        break
            if violated:
                break
        if not violated:
            count += 1
    return count


# ---------------------------------------------------------------------------
# Instances nommees des carnets
# ---------------------------------------------------------------------------


def amd_domain(
    *,
    weights: tuple[tuple[Profile, int], ...] | None = None,
    payment_bounds: tuple[int, int] = (0, 4),
) -> FiniteDomain:
    """Le domaine booléen d'`AMD.lean` : deux agents, theta dans {0, 1}, issue dans {0, 1}.

    `values[a][t][o] = t * o` (``AMD.lean:49-52`` : ``thetaVal`` et ``issueVal``
    valent 0 ou 1). Sans prior explicite, les quatre profils portent le poids 1.
    """
    values = tuple(
        tuple(tuple(t * o for o in range(2)) for t in range(2)) for _ in range(2)
    )
    if weights is None:
        weights = tuple((profile, 1) for profile in itertools.product(range(2), repeat=2))
    return FiniteDomain(
        n_agents=2,
        n_types=2,
        n_outcomes=2,
        values=values,
        weights=weights,
        payment_bounds=payment_bounds,
    )


def amd_star_mechanism(domain: FiniteDomain) -> Mechanism:
    """Le temoin booleen d'`AMD.lean:89-92` : ``o_star = r1 ET r2``, paiements nuls."""
    allocation = tuple(1 if (profile[0] and profile[1]) else 0 for profile in domain.profiles)
    payments = tuple(tuple(0 for _ in range(domain.n_agents)) for _ in domain.profiles)
    return Mechanism(allocation=allocation, payments=payments)


def public_project_domain(
    cost: int,
    values_by_type: Sequence[int],
    *,
    weights: tuple[tuple[Profile, int], ...] | None = None,
    payment_bounds: tuple[int, int] = (0, 8),
) -> FiniteDomain:
    """Projet public a cout explicite : deux agents, issues {pas de projet, projet}.

    ``values_by_type[t]`` est le gain entier d'un agent de type ``t`` si le projet
    se fait (0 sinon). Le cout ne contraint pas le domaine : il entre dans la
    regle d'allocation « naive », celle qui optimise profil par profil sans
    incitation, et c'est cette regle dont les tests mesurent la defaillance.
    """
    n_types = len(values_by_type)
    values = tuple(
        tuple((0, values_by_type[t]) for t in range(n_types)) for _ in range(2)
    )
    if weights is None:
        weights = tuple((profile, 1) for profile in itertools.product(range(n_types), repeat=2))
    return FiniteDomain(
        n_agents=2,
        n_types=n_types,
        n_outcomes=2,
        values=values,
        weights=weights,
        payment_bounds=payment_bounds,
    )


def public_project_naive_mechanism(domain: FiniteDomain, cost: int) -> Mechanism:
    """Regle « sans incitations » : batir si la somme des valeurs couvre le cout.

    L'allocation est optimale profil par profil, et chaque agent paie **sa propre
    valeur au profil reporte** (utilite nulle, donc IR). Cette regle ignore
    l'incitation : sous-declarer son type ne change pas l'allocation d'un agent
    non pivot mais fait baisser son paiement, ce qui est strictement profitable.
    C'est le temoin negatif que l'acceptance de #22381 demande.
    """
    allocation = tuple(
        1
        if sum(domain.values[a][profile[a]][1] for a in range(domain.n_agents)) >= cost
        else 0
        for profile in domain.profiles
    )
    payments = tuple(
        tuple(
            domain.values[a][profile[a]][allocation[r]] for a in range(domain.n_agents)
        )
        for r, profile in enumerate(domain.profiles)
    )
    return Mechanism(allocation=allocation, payments=payments)


def main() -> None:
    """Trois instances, trois verdicts : statut, borne d'objectif et ecart."""
    domain = amd_domain()
    star = amd_star_mechanism(domain)
    report = verify(domain, star, expected_welfare=2)
    print(f"temoin AMD        : {report.summary()}")

    naive_domain = public_project_domain(cost=4, values_by_type=(1, 3))
    naive = public_project_naive_mechanism(naive_domain, cost=4)
    naive_report = verify(naive_domain, naive)
    first = naive_report.dsic_violations[0] if naive_report.dsic_violations else None
    print(f"projet public     : {naive_report.summary()}")
    print(f"  premiere violation : {first}")

    for objective in ("revenue", "welfare"):
        result = synthesize(domain, objective)
        print(
            f"CP-SAT {objective:8s}: statut={result.status} valeur={result.objective_value} "
            f"borne={result.objective_bound} ecart={result.gap} "
            f"vars={result.n_vars} contraintes={result.n_constraints} "
            f"temps={result.solve_time_s:.3f}s"
        )
        if result.mechanism is not None:
            print(f"  verifie : {verify(domain, result.mechanism).summary()}")
    print(f"borne sans incitation : {unconstrained_revenue_bound(domain)}")
    inforced = synthesize(amd_domain(payment_bounds=(1, 4)), payments_at_least=1)
    print(f"paiements >= 1     : statut={inforced.status} (impossibility_strict_payments)")


if __name__ == "__main__":
    main()
