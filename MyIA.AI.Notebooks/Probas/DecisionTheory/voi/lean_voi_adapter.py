"""Adaptateur exact contrats JSON du banc `voi` -> instance Lean `NoisyProblem`.

Le banc `voi` decrit chaque probleme en nombres decimaux. La representation Lean
`NoisyProblem` du module `Bayesian/InformationNoisy.lean` porte des poids
**entiers** : l'adaptateur choisit deux denominateurs communs, un pour les poids
joints (``Lp``) et un pour les utilites (``Lu``), puis evalue le contrat dans les
deux echelles.

Conversion documentee (item 5 de l'issue #22374) ::

    joint[etat][signal] = prior[etat] * likelihood[signal][etat]     (exact)
    p_int[etat][signal] = joint[etat][signal] * Lp
    u_int[etat][action] = utilite[action][etat] * Lu
    cout_int            = test_cost * Lp * Lu

Toute valeur rendue par le module Lean est donc ``Lp * Lu`` fois la valeur
reelle : ``evsiRaw`` vaut ``Lp * Lu * EVSI``. Les deux facteurs sont distincts
parce que les erreurs sont de nature differente : mettre les utilites a
l'echelle des probabilites multiplierait la valeur par ``Lp`` au carre, ce qui
rendrait le nombre Lean inutilisable comme controle du banc.

Aucun arrondi n'intervient, ni au chargement (``json.loads(..., parse_float=Fraction)``
lit le litteral decimal exact), ni dans les calculs (``fractions.Fraction``), ni
dans l'emission.

Ordre des indices : ``etat`` suit ``states``, ``action`` suit ``actions``,
``signal`` suit ``signals``, tels qu'ecrits dans le JSON. L'ambiguite d'axes est
evitee par la convention objets imbriques du contrat.

Usage en ligne de commande ::

    python lean_voi_adapter.py problems/forage-petrolier.json          # evaluation
    python lean_voi_adapter.py problems/*.json --emit                   # source Lean
"""

from __future__ import annotations

import json
import sys
from dataclasses import dataclass
from fractions import Fraction
from math import lcm
from pathlib import Path
from typing import Any


class AdapterError(ValueError):
    """Entree refusee par l'adaptateur (item 6 : rejet explicite, jamais blanchi)."""


# Marqueurs du bloc genere dans le module Lean. Le test de parite compare le
# bloc du fichier committe a la sortie courante de l'adaptateur : une instance
# Lean editee a la main diverge et rougit.
BLOCK_BEGIN = "/- BEGIN ADAPTER-GENERATED -- ne pas editer a la main, regenerer"
BLOCK_END = "/- END ADAPTER-GENERATED -/"

# Docstrings du bloc genere, indexees par nom d'instance Lean.
BENCH_DOCSTRINGS: dict[str, str] = {
    "benchForagePetrolier": (
        "Banc `voi/forage-petrolier.json` transcrit exactement : poids joints\n"
        "    `prior x vraisemblance` ramenes a des entiers par `Lp = 100`.\n"
        "    Toute valeur de ce module vaut donc 100 fois la valeur en euros."
    ),
    "benchForageNonInformatif": (
        "Banc `voi/forage-non-informatif.json` : meme probleme, test independant\n"
        "    de l'etat. Sa table est exactement factorisee (`w = (3, 7)`, `q = (1, 1)`),\n"
        "    ce qui permet de certifier le zero par le theoreme et non par evaluation."
    ),
}


@dataclass(frozen=True)
class Instance:
    """Une instance Lean `NoisyProblem` derivee d'un contrat JSON."""

    name: str
    states: tuple[str, ...]
    actions: tuple[str, ...]
    signals: tuple[str, ...]
    p: tuple[tuple[int, ...], ...]      # p[etat][signal], mis a l'echelle par Lp
    u: tuple[tuple[int, ...], ...]      # u[etat][action], mis a l'echelle par Lu
    cost: int                           # test_cost * Lp * Lu
    scale_p: int
    scale_u: int
    factored: tuple[tuple[int, ...], tuple[int, ...]] | None

    @property
    def lean_name(self) -> str:
        return "bench" + "".join(part.capitalize() for part in self.name.split("-"))

    @property
    def value_scale(self) -> int:
        """Facteur entre une valeur du module Lean et la valeur reelle."""
        return self.scale_p * self.scale_u


def load_problem(path: str | Path) -> dict[str, Any]:
    """Charge un contrat JSON en conservant les decimaux exacts."""
    return json.loads(Path(path).read_text(encoding="utf-8"), parse_float=Fraction)


def _require(cond: bool, message: str) -> None:
    if not cond:
        raise AdapterError(message)


def _as_fraction(value: Any, what: str) -> Fraction:
    if isinstance(value, bool) or not isinstance(value, (int, Fraction)):
        raise AdapterError(f"{what} : nombre attendu, recu {value!r}")
    return Fraction(value)


def _names(problem: dict[str, Any], key: str) -> tuple[str, ...]:
    _require(key in problem, f"cle absente du contrat : {key}")
    names = problem[key]
    _require(isinstance(names, list) and bool(names), f"{key} doit etre une liste non vide")
    _require(len(set(names)) == len(names), f"{key} contient des doublons : {names}")
    return tuple(names)


def _gcd(a: int, b: int) -> int:
    a, b = abs(a), abs(b)
    while b:
        a, b = b, a % b
    return a


def build_instance(problem: dict[str, Any]) -> Instance:
    """Traduit un contrat JSON en instance Lean, ou refuse explicitement.

    Refus (item 6 de #22374) : poids negatif, prior qui ne somme pas exactement
    a 1, vraisemblance qui ne somme pas exactement a 1 par etat, masse jointe
    totale nulle, cout negatif, cle manquante.

    Un signal **impossible** (vraisemblance nulle pour tous les etats) n'est pas
    un refus : sa colonne jointe est nulle et sa contribution vaut exactement
    zero, ce qui est le comportement voulu par l'acceptance.
    """
    name = problem.get("problem")
    _require(isinstance(name, str) and bool(name), "cle `problem` absente ou vide")

    states = _names(problem, "states")
    actions = _names(problem, "actions")
    signals = _names(problem, "signals")

    for key in ("priors", "utilities", "likelihood"):
        _require(key in problem, f"cle absente du contrat : {key}")

    priors: dict[str, Fraction] = {}
    for state in states:
        _require(state in problem["priors"], f"prior manquant pour l'etat {state}")
        priors[state] = _as_fraction(problem["priors"][state], f"prior[{state}]")
        _require(priors[state] >= 0, f"prior[{state}] negatif : {priors[state]}")
    _require(
        sum(priors.values()) == 1,
        f"les priors ne somment pas exactement a 1 : {sum(priors.values())}",
    )

    likelihood: dict[str, dict[str, Fraction]] = {}
    for signal in signals:
        _require(signal in problem["likelihood"], f"vraisemblance manquante pour {signal}")
        row = problem["likelihood"][signal]
        likelihood[signal] = {}
        for state in states:
            _require(state in row, f"vraisemblance manquante pour {signal}/{state}")
            value = _as_fraction(row[state], f"likelihood[{signal}][{state}]")
            _require(value >= 0, f"likelihood[{signal}][{state}] negatif : {value}")
            likelihood[signal][state] = value
    for state in states:
        total = sum(likelihood[signal][state] for signal in signals)
        _require(
            total == 1,
            f"la vraisemblance de l'etat {state} ne somme pas exactement a 1 : {total}",
        )

    utilities: dict[str, dict[str, Fraction]] = {}
    for action in actions:
        _require(action in problem["utilities"], f"utilite manquante pour l'action {action}")
        column = problem["utilities"][action]
        utilities[action] = {}
        for state in states:
            _require(state in column, f"utilite manquante pour {action}/{state}")
            utilities[action][state] = _as_fraction(
                column[state], f"utilities[{action}][{state}]"
            )

    cost = _as_fraction(problem.get("test_cost", 0), "test_cost")
    _require(cost >= 0, f"test_cost negatif : {cost}")

    joint = {
        state: {signal: priors[state] * likelihood[signal][state] for signal in signals}
        for state in states
    }
    mass = sum(joint[state][signal] for state in states for signal in signals)
    _require(mass > 0, "masse jointe totale nulle : instance inutilisable")

    scale_p = 1
    for state in states:
        for signal in signals:
            scale_p = lcm(scale_p, joint[state][signal].denominator)
    scale_u = 1
    for action in actions:
        for state in states:
            scale_u = lcm(scale_u, utilities[action][state].denominator)

    p = tuple(
        tuple(int(joint[state][signal] * scale_p) for signal in signals) for state in states
    )
    u = tuple(
        tuple(int(utilities[action][state] * scale_u) for action in actions)
        for state in states
    )
    for row in p:
        _require(all(weight >= 0 for weight in row), "poids joint negatif apres mise a l'echelle")

    return Instance(
        name=name,
        states=states,
        actions=actions,
        signals=signals,
        p=p,
        u=u,
        cost=int(cost * scale_p * scale_u),
        scale_p=scale_p,
        scale_u=scale_u,
        factored=_detect_factored(p, len(states), len(signals)),
    )


def _detect_factored(
    p: tuple[tuple[int, ...], ...], n_states: int, n_signals: int
) -> tuple[tuple[int, ...], tuple[int, ...]] | None:
    """Rend ``(w, q)`` entiers tels que ``p[s][x] == w[s] * q[x]``, sinon ``None``.

    Detection exacte sur les entiers, sans tolerance : ``q[x]`` est le pgcd de la
    colonne ``x``, ``w[s]`` le quotient de la premiere colonne non nulle, et
    l'egalite est reverifiee sur toutes les cellules. Une colonne nulle donne
    ``q[x] = 0``, ce qui est exactement le cas « signal impossible ».
    """
    q: list[int] = []
    for x in range(n_signals):
        g = 0
        for s in range(n_states):
            g = _gcd(g, p[s][x])
        q.append(g)

    w: list[int] | None = None
    for x in range(n_signals):
        if q[x] == 0:
            continue
        column = [p[s][x] // q[x] for s in range(n_states)]
        if w is None:
            w = column
        elif w != column:
            return None
    if w is None:
        return None
    for s in range(n_states):
        for x in range(n_signals):
            if w[s] * q[x] != p[s][x]:
                return None
    return (tuple(w), tuple(q))


def evaluate(instance: Instance) -> dict[str, Any]:
    """Evalue le contrat en valeurs exactes, dans les deux echelles.

    Les valeurs ``lean_*`` sont celles que le module Lean imprime ; les autres
    sont les valeurs reelles (en euros), donc divisibles exactement par
    ``value_scale``.
    """
    n_states, n_actions, n_signals = (
        len(instance.states),
        len(instance.actions),
        len(instance.signals),
    )

    def no_info(state: int, action: int) -> int:
        return sum(instance.p[state]) * instance.u[state][action]

    eu_no_info = max(sum(no_info(s, a) for s in range(n_states)) for a in range(n_actions))
    value_signal = sum(
        max(
            sum(instance.p[s][x] * instance.u[s][a] for s in range(n_states))
            for a in range(n_actions)
        )
        for x in range(n_signals)
    )
    value_perfect = sum(
        sum(instance.p[s]) * max(instance.u[s]) for s in range(n_states)
    )
    evsi_raw = value_signal - eu_no_info
    evpi = value_perfect - eu_no_info
    evsi_net = evsi_raw - instance.cost

    scale = instance.value_scale
    _require(
        all(v % scale == 0 for v in (eu_no_info, value_signal, value_perfect, evsi_raw, evpi, evsi_net)),
        "une valeur Lean n'est pas divisible par le facteur d'echelle : conversion inexacte",
    )
    return {
        "name": instance.name,
        "lean_name": instance.lean_name,
        "scale_p": instance.scale_p,
        "scale_u": instance.scale_u,
        "value_scale": scale,
        "eu_no_info": Fraction(eu_no_info, scale),
        "value_signal": Fraction(value_signal, scale),
        "value_perfect": Fraction(value_perfect, scale),
        "evpi": Fraction(evpi, scale),
        "evsi_raw": Fraction(evsi_raw, scale),
        "evsi_net": Fraction(evsi_net, scale),
        "lean_eu_no_info": eu_no_info,
        "lean_value_signal": value_signal,
        "lean_value_perfect": value_perfect,
        "lean_evsi_raw": evsi_raw,
        "lean_evsi_net": evsi_net,
        "lean_evpi": evpi,
        "lean_cost": instance.cost,
        "factored": instance.factored,
    }


def _nested(values: list[int], var: str) -> str:
    """Rend ``if var.val = 0 then v0 else if var.val = 1 then v1 else v2``."""
    if len(values) == 1:
        return str(values[0])

    def rec(index: int) -> str:
        if index == len(values) - 1:
            return str(values[index])
        return f"if {var}.val = {index} then {values[index]} else {rec(index + 1)}"

    return rec(0)


def _by_state(rows: tuple[tuple[int, ...], ...], var: str, indent: str = "    ") -> str:
    """Rend le corps ``p``/``u`` : une branche par etat, la derniere en ``else``."""
    if len(rows) == 1:
        return _nested(list(rows[0]), var)
    lignes = [
        f"{indent}if s.val = {index} then ({_nested(list(rows[index]), var)})"
        for index in range(len(rows) - 1)
    ]
    lignes.append(f"{indent}else ({_nested(list(rows[-1]), var)})")
    return "\n".join(lignes)


def emit_lean(instance: Instance) -> str:
    """Rend la definition Lean de l'instance (corps du bloc genere)."""
    doc = BENCH_DOCSTRINGS.get(instance.lean_name, f"Instance `{instance.name}`.")
    return (
        f"/-- {doc} -/\n"
        f"def {instance.lean_name} : NoisyProblem where\n"
        f"  nS := {len(instance.states)}\n"
        f"  nA := {len(instance.actions)}\n"
        f"  nX := {len(instance.signals) - 1}\n"
        f"  p := fun s x =>\n{_by_state(instance.p, 'x')}\n"
        f"  u := fun s a =>\n{_by_state(instance.u, 'a')}"
    )


def emit_block(instances: list[Instance]) -> str:
    """Rend le bloc complet, marqueurs compris."""
    corps = "\n\n".join(emit_lean(instance) for instance in instances)
    return f"{BLOCK_BEGIN} -/\n\n{corps}\n\n{BLOCK_END}"


def bench_instances(problems_dir: str | Path | None = None) -> list[Instance]:
    """Charge les deux contrats du banc, dans l'ordre d'emission."""
    base = Path(problems_dir) if problems_dir else Path(__file__).resolve().parent / "problems"
    return [
        build_instance(load_problem(base / name))
        for name in ("forage-petrolier.json", "forage-non-informatif.json")
    ]


def main(argv: list[str]) -> int:
    paths = [arg for arg in argv if not arg.startswith("--")]
    instances = [build_instance(load_problem(path)) for path in paths]
    if "--emit" in argv:
        print(emit_block(instances))
        return 0
    for instance in instances:
        values = evaluate(instance)
        print(
            f"=== {values['name']} (Lp = {values['scale_p']}, Lu = {values['scale_u']}, "
            f"echelle des valeurs = {values['value_scale']}) ==="
        )
        for key in ("eu_no_info", "evsi_raw", "evsi_net", "evpi"):
            print(f"  {key:14s} = {values[key]}   (Lean : {values['lean_' + key]})")
        print(f"  table factorisee : {values['factored']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
