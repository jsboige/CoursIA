"""Jeux bayesiens a deux joueurs finis : forme strategique + Nashpy + validateur BNE.

Module d'import (issue #22382, premier jalon) pour analyser un jeu bayesien
statique a deux joueurs sans en faire un LP de minimax — un jeu bayesien
general ne se reduit PAS a un LP de minimax : le vrai moteur de jeux
bimatriciels (Nashpy) resout la forme strategique ex ante, et un validateur
independent par type controle le resultat.

Pipeline
--------
1. :func:`to_strategic_form` — chaque strategie pure de la forme strategique
   est un **plan contingent** (type -> action). Les matrices ex ante sont
   construites par le **meme prior joint** et les **memes gains natifs** de
   l'organe ``BayesianGame`` (GameTheory-11) : aucune independance des types
   n'est imposee, le prior corrèle est somme tel quel.
2. :func:`solve_strategic_form` — **Nashpy natif** sur la forme strategique.
   Le resultat distingue statut ``FOUND`` / ``NOT_FOUND`` / ``NUMERICAL`` :
   un jeu fini a deux joueurs a toujours un equilibre de Nash, le jeu n'est
   donc jamais "infeasible" ; l'exhaustivite n'est en revanche pas garantie
   en presence de degenerescence.
3. :func:`marginals_by_type` — convertit un melange de plans en distributions
   d'actions **par type**.
4. :func:`validate_bne` — **validateur independant** : recalcule les gains
   conditionnels depuis les gains natifs (prior + Bayes) et mesure le regret
   maximal de chaque type de probabilite positive sur toutes ses deviations
   pures. Les types de probabilite nulle sont signales ``out_of_support``,
   jamais "verifies par division nulle".

Deux concepts distincts
-----------------------
L'equilibre de Nash de la forme strategique ex ante (melanges sur les plans)
et l'equilibre bayesien de Nash (BNE, par type) ne coincident pas en general.
Un melange de plans fixe egalement la **coordination contrefactuelle** des
actions des types non realises d'un meme joueur (par ex. P(type H joue A ET
type L joue B)) : cette coordination est porteuse de gain ex ante — c'est elle
que le solveur optimise — mais elle n'est **pas observable** dans le jeu
statique a un seul type realise, ou seule l'action du type realise affecte les
gains. Le validateur ne voit que les marginales par type ; un equilibre ex
ante qui ne passe pas le validateur n'est donc PAS un BNE, et les deux notions
doivent etre rapportees, pas moyennées.

Contrat d'entree (duck-typed sur l'organe de GameTheory-11)
-----------------------------------------------------------
``game.name`` · ``game.players`` · ``game.types`` (joueur -> [types]) ·
``game.prior`` (profil de types -> probabilite, somme 1) · ``game.actions``
(joueur -> [actions]) · ``game.payoffs`` ((types, actions) -> (gain1, gain2)).
L'adaptateur est **explicite** : il ne redéfinit pas la classe de l'organe.
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass
from typing import Dict, List, Sequence, Tuple

import numpy as np

try:
    import nashpy as nash
except ImportError as exc:  # pragma: no cover - regle F : installer, ne pas contourner
    raise ImportError("nashpy est requis : pip install nashpy") from exc


#: Borne par defaut de l'espace de plans contingents (croissance exponentielle).
DEFAULT_MAX_PLANS = 64

_NOTE_NOT_FOUND = (
    "Aucun equilibre retourne. Un jeu fini a deux joueurs a TOUJOURS un "
    "equilibre de Nash : le jeu n'est jamais 'infeasible' — le solveur a "
    "seulement echoue a en produire un (degenerescence, algorithme limite)."
)
_NOTE_FOUND = (
    "Equilibres trouves par {algorithm}. Exhaustivite non garantie en presence "
    "de degenerescence : des equilibres peuvent etre omis, la liste n'est pas "
    "certifiee complete."
)
_NOTE_NUMERICAL = (
    "Erreur numerique signalee par le solveur : aucun verdict d'equilibre "
    "n'est porte sur ce resultat."
)


class PlanSpaceTooLargeError(Exception):
    """L'espace de plans contingents depasse la borne declaree.

    Le nombre de plans est ``len(actions) ** len(types)`` — croissance
    exponentielle. La borne est calculee **avant** toute materialisation ;
    il n'y a jamais de troncature silencieuse.
    """


# ---------------------------------------------------------------------------
# Espace de plans contingents
# ---------------------------------------------------------------------------


def plan_count(types: Sequence[str], actions: Sequence[str]) -> int:
    """Nombre de plans contingents : une action par type (croissance exponentielle)."""
    return len(actions) ** len(types)


def build_plan_space(
    types: Sequence[str],
    actions: Sequence[str],
    max_plans: int = DEFAULT_MAX_PLANS,
) -> List[Tuple[str, ...]]:
    """Matérialise l'espace de plans, avec la borne calculee en amont.

    Un plan est un tuple d'actions indexe par la position du type : le plan
    ``("A", "B")`` pour les types ``[H, L]`` signifie "H joue A, L joue B".

    Raises:
        PlanSpaceTooLargeError: si ``plan_count > max_plans`` — avant
            qu'aucun plan ne soit materialise.
    """
    count = plan_count(types, actions)
    if count > max_plans:
        raise PlanSpaceTooLargeError(
            f"{count} plans contingents > borne {max_plans} "
            f"({len(actions)} actions ^ {len(types)} types) ; "
            "croissance exponentielle declaree, aucune troncature silencieuse"
        )
    return [tuple(p) for p in itertools.product(actions, repeat=len(types))]


# ---------------------------------------------------------------------------
# Forme strategique ex ante
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class StrategicForm:
    """Forme strategique ex ante d'un jeu bayesien a deux joueurs.

    Les lignes/colonnes sont les plans contingents ; ``matrix1[i, j]`` est le
    gain ex ante du joueur 1 quand il joue le plan ``plans1[i]`` et l'autre
    le plan ``plans2[j]``.
    """

    players: Tuple[str, str]
    types: Tuple[Tuple[str, ...], Tuple[str, ...]]
    actions: Tuple[Tuple[str, ...], Tuple[str, ...]]
    plans: Tuple[Tuple[Tuple[str, ...], ...], Tuple[Tuple[str, ...], ...]]
    matrix1: np.ndarray
    matrix2: np.ndarray


def _ex_ante_matrix(
    game: object,
    player: int,
    plans1: Sequence[Tuple[str, ...]],
    plans2: Sequence[Tuple[str, ...]],
) -> np.ndarray:
    """Gain ex ante d'un joueur : somme du prior joint (tel quel) x gains natifs."""
    p1, p2 = game.players
    t1_labels, t2_labels = game.types[p1], game.types[p2]
    matrix = np.zeros((len(plans1), len(plans2)))
    for i, pl1 in enumerate(plans1):
        for j, pl2 in enumerate(plans2):
            total = 0.0
            for t1, t2 in itertools.product(t1_labels, t2_labels):
                prob = game.prior.get((t1, t2), 0.0)
                if prob == 0.0:
                    continue
                a1 = pl1[t1_labels.index(t1)]
                a2 = pl2[t2_labels.index(t2)]
                total += prob * game.payoffs((t1, t2), (a1, a2))[player]
            matrix[i, j] = total
    return matrix


def to_strategic_form(game: object, max_plans: int = DEFAULT_MAX_PLANS) -> StrategicForm:
    """Adaptateur explicite vers la forme strategique ex ante.

    Duck-typed sur le contrat d'organe de GameTheory-11 (cf docstring du
    module) — ce n'est PAS une seconde definition de ``BayesianGame``.

    Args:
        game: jeu bayesien a deux joueurs (contrat d'organe).
        max_plans: borne par joueur de l'espace de plans contingents.

    Raises:
        ValueError: plus de deux joueurs, ou prior qui ne somme pas a 1.
        PlanSpaceTooLargeError: espace de plans au-dessus de la borne.
    """
    if len(game.players) != 2:
        raise ValueError(
            f"deux joueurs requis, got {len(game.players)} : {game.players}"
        )
    p1, p2 = game.players
    types1, types2 = game.types[p1], game.types[p2]
    actions1, actions2 = game.actions[p1], game.actions[p2]
    prior_sum = sum(game.prior.values())
    if abs(prior_sum - 1.0) > 1e-9:
        raise ValueError(f"prior doit sommer a 1, got {prior_sum}")
    plans1 = build_plan_space(types1, actions1, max_plans)
    plans2 = build_plan_space(types2, actions2, max_plans)
    return StrategicForm(
        players=(p1, p2),
        types=(tuple(types1), tuple(types2)),
        actions=(tuple(actions1), tuple(actions2)),
        plans=(tuple(plans1), tuple(plans2)),
        matrix1=_ex_ante_matrix(game, 0, plans1, plans2),
        matrix2=_ex_ante_matrix(game, 1, plans1, plans2),
    )


# ---------------------------------------------------------------------------
# Resolution (Nashpy natif)
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class SolveResult:
    """Resultat d'un solveur sur la forme strategique.

    ``status`` : ``"FOUND"`` | ``"NOT_FOUND"`` | ``"NUMERICAL"``.
    """

    status: str
    algorithm: str
    equilibria: Tuple[Tuple[np.ndarray, np.ndarray], ...]
    note: str

    @property
    def is_found(self) -> bool:
        return self.status == "FOUND"


def solve_strategic_form(
    form: StrategicForm,
    algorithm: str = "support_enumeration",
) -> SolveResult:
    """Resout la forme strategique avec le solveur Nashpy natif.

    Distingue les trois regimes (cf docstring du module) : un ``NOT_FOUND``
    ne qualifie jamais le jeu d'infaisable ; un ``FOUND`` ne garantit pas
    l'exhaustivite en presence de degenerescence.
    """
    solver_name = {
        "support_enumeration": "support_enumeration",
        "lemke_howson": "lemke_howson_enumeration",
        "vertex_enumeration": "vertex_enumeration",
    }.get(algorithm)
    if solver_name is None:
        raise ValueError(
            f"algorithme inconnu : {algorithm!r} "
            "(attendu : support_enumeration, lemke_howson, vertex_enumeration)"
        )
    game = nash.Game(form.matrix1, form.matrix2)
    solver = getattr(game, solver_name, None)
    if solver is None:
        raise ValueError(f"methode absente de nashpy : {solver_name!r}")
    try:
        equilibria = tuple(solver())
    except Exception as exc:
        return SolveResult(
            status="NUMERICAL",
            algorithm=algorithm,
            equilibria=(),
            note=f"{_NOTE_NUMERICAL} ({exc.__class__.__name__}: {exc})",
        )
    if not equilibria:
        return SolveResult(
            status="NOT_FOUND",
            algorithm=algorithm,
            equilibria=(),
            note=_NOTE_NOT_FOUND,
        )
    return SolveResult(
        status="FOUND",
        algorithm=algorithm,
        equilibria=equilibria,
        note=_NOTE_FOUND.format(algorithm=algorithm),
    )


# ---------------------------------------------------------------------------
# Marginales par type
# ---------------------------------------------------------------------------


def marginals_by_type(
    sigma: Sequence[float],
    plans: Sequence[Tuple[str, ...]],
    types: Sequence[str],
    actions: Sequence[str],
) -> Dict[str, np.ndarray]:
    """Distributions d'actions par type induites par un melange de plans.

    Note (#22382, critere 3) : un melange de plans fixe aussi la
    **coordination contrefactuelle** des actions des types d'un meme joueur
    (par ex. P(type H joue A ET type L joue B)). Cette coordination est
    porteuse de gain **ex ante** — le solveur l'optimise — mais elle n'est
    pas observable dans le jeu statique : un seul type est realise, et seule
    son action affecte les gains. Les marginales par type sont donc
    l'information COMPLETE que le jeu statique porte ; c'est precisement
    pourquoi l'equilibre ex ante et le BNE sont deux concepts distincts.
    """
    out: Dict[str, np.ndarray] = {}
    for k, t in enumerate(types):
        dist = np.zeros(len(actions))
        for weight, plan in zip(sigma, plans):
            dist[actions.index(plan[k])] += weight
        out[t] = dist
    return out


# ---------------------------------------------------------------------------
# Validateur independant de BNE
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class TypeReport:
    """Controle par type : gains conditionnels, regret sur les deviations pures."""

    player: str
    type: str
    prob: float
    conditional_payoffs: Dict[str, float]
    current_payoff: float
    best_response: str
    regret: float


@dataclass(frozen=True)
class ValidationReport:
    """Verdict du validateur independant.

    ``is_bne`` = normalisation/non-negativite des deux melanges ET regret
    maximal <= ``tol``. Les types de probabilite nulle figurent dans
    ``out_of_support`` : ils sont signales, pas verities par division nulle.
    """

    is_bne: bool
    max_regret: float
    tolerance: float
    reports: Tuple[TypeReport, ...]
    out_of_support: Tuple[Tuple[str, str], ...]
    normalization_ok: bool


def _type_prob(game: object, player: str, t: str) -> float:
    idx = game.players.index(player)
    return sum(p for prof, p in game.prior.items() if prof[idx] == t)


def validate_bne(
    game: object,
    form: StrategicForm,
    sigma1: Sequence[float],
    sigma2: Sequence[float],
    tol: float = 1e-6,
) -> ValidationReport:
    """Validateur independant de BNE (recalcul natif, sans la forme strategique).

    Pour chaque joueur et chaque type de probabilite positive : le regret est
    le surcroit de gain conditionnel de la meilleure deviation pure sur le
    gain du melange courant, les gains conditionnels etant recalculés depuis
    le prior et les gains natifs (regle de Bayes).
    """
    sigmas = (np.asarray(sigma1, dtype=float), np.asarray(sigma2, dtype=float))
    normalization_ok = all(
        abs(float(np.sum(s)) - 1.0) <= tol and float(np.min(s)) >= -tol
        for s in sigmas
    )

    # Garde d'ordre (reserve Hermes #22615, n.3) : l'indexation positionnelle
    # sigmas[k] <-> form.players[k] suppose que form et game partagent le meme
    # ordre de joueurs. Un StrategicForm construit a la main, a l'ordre
    # permuté, produirait des gains conditionnels silencieusement faux.
    if list(form.players) != list(game.players):
        raise ValueError(
            "ordre des joueurs incohérent entre form et game : "
            f"form.players={form.players} vs game.players={game.players}"
        )

    reports: List[TypeReport] = []
    out_of_support: List[Tuple[str, str]] = []
    max_regret = 0.0

    for k in (0, 1):
        player = form.players[k]
        types_k, actions_k, plans_k = form.types[k], form.actions[k], form.plans[k]
        other = 1 - k
        marg_k = marginals_by_type(sigmas[k], plans_k, types_k, actions_k)
        marg_o = marginals_by_type(
            sigmas[other], form.plans[other], form.types[other], form.actions[other]
        )
        for t_k in types_k:
            p_k = _type_prob(game, player, t_k)
            if p_k <= 0.0:
                out_of_support.append((player, t_k))
                continue
            cond: Dict[str, float] = {}
            for a_k in actions_k:
                total = 0.0
                for t_o in form.types[other]:
                    joint = game.prior.get(
                        (t_k, t_o) if k == 0 else (t_o, t_k), 0.0
                    )
                    if joint == 0.0:
                        continue
                    for a_o, w in zip(form.actions[other], marg_o[t_o]):
                        profile = (t_k, t_o) if k == 0 else (t_o, t_k)
                        acts = (a_k, a_o) if k == 0 else (a_o, a_k)
                        total += (joint / p_k) * w * game.payoffs(profile, acts)[k]
                cond[a_k] = total
            dist = marg_k[t_k]
            current = float(np.dot(dist, [cond[a] for a in actions_k]))
            best = max(cond, key=cond.get)
            # `best` et `regret` se lisent sur la MEME entree de la table : le
            # regret est le surcroit de `cond[best]` sur le gain courant.
            # Calculer le regret par un `max` separe sur les valeurs donnait
            # deux derivations qui ne divergent qu'en silence (review NanoClaw
            # de #22615). En cas d'egalite entre actions, `max` rend la premiere
            # dans l'ordre de `actions_k` : le choix est deterministe, et le
            # regret vaut 0 pour cette action comme pour toute autre ex aequo.
            regret = float(cond[best] - current)
            max_regret = max(max_regret, regret)
            reports.append(
                TypeReport(
                    player=player,
                    type=t_k,
                    prob=float(p_k),
                    conditional_payoffs=cond,
                    current_payoff=current,
                    best_response=best,
                    regret=regret,
                )
            )

    return ValidationReport(
        is_bne=normalization_ok and max_regret <= tol,
        max_regret=max_regret,
        tolerance=tol,
        reports=tuple(reports),
        out_of_support=tuple(out_of_support),
        normalization_ok=normalization_ok,
    )


# ---------------------------------------------------------------------------
# Invariants
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class InvarianceReport:
    """Verdict de l'invariance des gains sous permutation des etiquettes."""

    ok: bool
    detail: str


def _reorder_matrix(
    game: object,
    form: StrategicForm,
    player: int,
    new_order1: Sequence[str],
    new_order2: Sequence[str],
) -> np.ndarray:
    """Matrice ex ante d'un joueur quand les listes de types sont reordonnees."""
    p1, p2 = form.players
    new_orders = {0: list(new_order1), 1: list(new_order2)}
    plans1 = build_plan_space(new_orders[0], form.actions[0])
    plans2 = build_plan_space(new_orders[1], form.actions[1])
    return _ex_ante_matrix_with_order(game, player, plans1, plans2, new_orders)


def _ex_ante_matrix_with_order(
    game: object,
    player: int,
    plans1: Sequence[Tuple[str, ...]],
    plans2: Sequence[Tuple[str, ...]],
    orders: Dict[int, List[str]],
) -> np.ndarray:
    p1, p2 = game.players
    matrix = np.zeros((len(plans1), len(plans2)))
    for i, pl1 in enumerate(plans1):
        for j, pl2 in enumerate(plans2):
            total = 0.0
            for t1, t2 in itertools.product(orders[0], orders[1]):
                prob = game.prior.get((t1, t2), 0.0)
                if prob == 0.0:
                    continue
                a1 = pl1[orders[0].index(t1)]
                a2 = pl2[orders[1].index(t2)]
                total += prob * game.payoffs((t1, t2), (a1, a2))[player]
            matrix[i, j] = total
    return matrix


def _plan_reorder_permutation(
    actions: Sequence[str], old: Sequence[str], new: Sequence[str]
) -> np.ndarray:
    """Matrice de permutation P avec ``P[i_new, i_old] = 1`` : le plan
    ``i_new`` (ordre ``new``) assigne a chaque etiquette la meme action que
    le plan ``i_old`` (ordre ``old``)."""
    n = len(old)
    plan_list = list(itertools.product(actions, repeat=n))
    perm = np.zeros((len(plan_list), len(plan_list)))
    for i_new, pl in enumerate(plan_list):
        # pl est indexe par position dans l'ordre ``new`` ; re-projection
        # sur l'ordre ``old`` : la position q de ``old`` porte l'etiquette
        # ``old[q]`` qui, dans ``new``, est a l'indice ``new.index(old[q])``.
        old_pl = tuple(pl[new.index(old[q])] for q in range(n))
        perm[i_new, plan_list.index(old_pl)] = 1.0
    return perm


def check_label_invariance(
    game: object,
    form: StrategicForm,
    type_order: Tuple[Sequence[str], Sequence[str]],
    tol: float = 1e-9,
) -> InvarianceReport:
    """Invariance des gains ex ante sous permutation des etiquettes de types.

    Reordonne les listes de types de chaque joueur (memes etiquettes, ordre
    change) et verifie ``M' = P1 M P2^T`` ou ``P`` est la permutation des
    plans induite : les gains ex ante ne dependent que des etiquettes, pas de
    leur ordre de liste.
    """
    p1, p2 = form.players
    new_orders = [list(type_order[0]), list(type_order[1])]
    for k, player in enumerate((p1, p2)):
        if sorted(new_orders[k]) != sorted(form.types[k]):
            return InvarianceReport(
                ok=False,
                detail=(
                    f"{player} : {new_orders[k]} n'est pas une permutation "
                    f"de {list(form.types[k])}"
                ),
            )
    perm1 = _plan_reorder_permutation(form.actions[0], form.types[0], new_orders[0])
    perm2 = _plan_reorder_permutation(form.actions[1], form.types[1], new_orders[1])
    m1 = _reorder_matrix(game, form, 0, new_orders[0], new_orders[1])
    m2 = _reorder_matrix(game, form, 1, new_orders[0], new_orders[1])
    ok = (
        bool(np.allclose(m1, perm1 @ form.matrix1 @ perm2.T, atol=tol))
        and bool(np.allclose(m2, perm1 @ form.matrix2 @ perm2.T, atol=tol))
    )
    detail = (
        "M' = P M P^T verifie pour les deux joueurs "
        if ok
        else "M' != P M P^T : les gains ex ante dependent de l'ordre des etiquettes"
    )
    return InvarianceReport(ok=ok, detail=detail)


def check_ex_ante_consistency(
    game: object,
    form: StrategicForm,
    sigma1: Sequence[float],
    sigma2: Sequence[float],
    tol: float = 1e-9,
) -> bool:
    """Cohérence ex ante : le gain de la forme strategique est la somme
    ponderee des gains conditionnels par type.

    Pour chaque joueur k : ``sigma_k^T M_k sigma_-k`` (forme strategique) ==
    ``sum_{t_k} P(t_k) E[u_k | t_k]`` (recalcul natif depuis le prior et les
    gains natifs). Les deux voies doivent coïncider — c'est le controle qui
    lie l'adaptateur au jeu natif.
    """
    s1 = np.asarray(sigma1, dtype=float)
    s2 = np.asarray(sigma2, dtype=float)
    for k in (0, 1):
        sigma_k = s1 if k == 0 else s2
        sigma_o = s2 if k == 0 else s1
        if k == 0:
            ex_ante = float(s1 @ form.matrix1 @ s2)
        else:
            # lignes = plans du joueur 1, colonnes = plans du joueur 2 :
            # le gain ex ante du joueur 2 transpose la matrice.
            ex_ante = float(s2 @ form.matrix2.T @ s1)
        player = form.players[k]
        other = 1 - k
        marg_k = marginals_by_type(sigma_k, form.plans[k], form.types[k], form.actions[k])
        marg_o = marginals_by_type(sigma_o, form.plans[other], form.types[other], form.actions[other])
        native = 0.0
        for t_k in form.types[k]:
            p_k = _type_prob(game, player, t_k)
            if p_k <= 0.0:
                continue
            for t_o in form.types[other]:
                joint = game.prior.get((t_k, t_o) if k == 0 else (t_o, t_k), 0.0)
                if joint == 0.0:
                    continue
                for a_k, w_k in zip(form.actions[k], marg_k[t_k]):
                    for a_o, w_o in zip(form.actions[other], marg_o[t_o]):
                        profile = (t_k, t_o) if k == 0 else (t_o, t_k)
                        acts = (a_k, a_o) if k == 0 else (a_o, a_k)
                        native += joint * w_k * w_o * game.payoffs(profile, acts)[k]
        if abs(ex_ante - native) > tol:
            return False
    return True
