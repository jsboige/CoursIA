"""Composition finie de regards avec propagation avant et arrière.

Ici, une lentille optique ``get``/``put`` modélise un regard entre deux
strates finies. Ce sens est distinct des lentilles d'interprétabilité de
:mod:`ict.lens_agreement` (SAE et J-Lens).

La composition calcule réellement les deux jambes : la lecture ``get`` se
propage en avant, puis la demande ``put`` remonte en réinjectant chaque état
intermédiaire. Les domaines finis rendent les lois, l'associativité et les
témoins d'incompatibilité vérifiables exhaustivement.
"""

from __future__ import annotations

from collections.abc import Callable, Sequence
from dataclasses import dataclass
from typing import Any

W = tuple((signal, charge) for signal in range(3) for charge in range(3))
STRATA: dict[str, tuple[Any, ...]] = {
    "W": W,
    "Z3": tuple(range(3)),
    "Z2": tuple(range(2)),
}


@dataclass(frozen=True)
class Regard:
    """Regard déterministe entre deux strates finies."""

    name: str
    src: str
    tgt: str
    get: Callable[[Any], Any]
    put: Callable[[Any, Any], Any]

    def __post_init__(self) -> None:
        if self.src not in STRATA:
            raise ValueError(f"Strate source inconnue : {self.src}")
        if self.tgt not in STRATA:
            raise ValueError(f"Strate cible inconnue : {self.tgt}")


def elements(stratum: str) -> tuple[Any, ...]:
    """Retourner les éléments d'une strate déclarée."""

    try:
        return STRATA[stratum]
    except KeyError as exc:
        raise ValueError(f"Strate inconnue : {stratum}") from exc


def identity(stratum: str) -> Regard:
    """Construire le regard identité d'une strate."""

    elements(stratum)
    return Regard(
        name=f"id{stratum}",
        src=stratum,
        tgt=stratum,
        get=lambda value: value,
        put=lambda _old, demand: demand,
    )


def compose(outer: Regard, inner: Regard) -> Regard:
    """Composer ``outer`` après ``inner`` avec réinjection arrière."""

    if inner.tgt != outer.src:
        raise ValueError(
            f"Regards non composables : {inner.tgt} != {outer.src}"
        )

    def get(state: Any) -> Any:
        return outer.get(inner.get(state))

    def put(state: Any, demand: Any) -> Any:
        intermediate = inner.get(state)
        inner_demand = outer.put(intermediate, demand)
        return inner.put(state, inner_demand)

    return Regard(
        name=f"{outer.name} o {inner.name}",
        src=inner.src,
        tgt=outer.tgt,
        get=get,
        put=put,
    )


def compose_without_reinjection(outer: Regard, inner: Regard) -> Regard:
    """Contrôle fautif : oublier le ``put`` du regard intérieur."""

    if inner.tgt != outer.src or inner.src != outer.src:
        raise ValueError("Le contrôle fautif requiert des strates compatibles")
    return Regard(
        name=f"{outer.name} x {inner.name}",
        src=inner.src,
        tgt=outer.tgt,
        get=lambda state: outer.get(inner.get(state)),
        put=lambda state, demand: outer.put(inner.get(state), demand),
    )


def law_report(regard: Regard) -> dict:
    """Énumérer les violations des lois get-put et put-get."""

    get_put = []
    put_get = []
    for state in elements(regard.src):
        rebuilt = regard.put(state, regard.get(state))
        if rebuilt != state:
            get_put.append((state, rebuilt))
        for demand in elements(regard.tgt):
            observed = regard.get(regard.put(state, demand))
            if observed != demand:
                put_get.append((state, demand, observed))
    return {
        "name": regard.name,
        "src": regard.src,
        "tgt": regard.tgt,
        "n_get_put": len(elements(regard.src)),
        "get_put_violations": tuple(get_put),
        "n_put_get": len(elements(regard.src)) * len(elements(regard.tgt)),
        "put_get_violations": tuple(put_get),
        "is_lens": not get_put and not put_get,
    }


def agreement(left: Regard, right: Regard, *, on: str) -> dict:
    """Mesurer l'accord extensionnel de deux regards sur ``get`` ou ``put``."""

    if (left.src, left.tgt) != (right.src, right.tgt):
        raise ValueError("Les regards doivent relier les mêmes strates")
    if on not in {"get", "put"}:
        raise ValueError("La jambe doit être 'get' ou 'put'")

    disagreements = []
    if on == "get":
        cases = ((state,) for state in elements(left.src))
        for (state,) in cases:
            left_value = left.get(state)
            right_value = right.get(state)
            if left_value != right_value:
                disagreements.append((state, left_value, right_value))
        total = len(elements(left.src))
    else:
        for state in elements(left.src):
            for demand in elements(left.tgt):
                left_value = left.put(state, demand)
                right_value = right.put(state, demand)
                if left_value != right_value:
                    disagreements.append(
                        (state, demand, left_value, right_value)
                    )
        total = len(elements(left.src)) * len(elements(left.tgt))

    same = total - len(disagreements)
    return {
        "leg": on,
        "same": same,
        "total": total,
        "rate": same / total,
        "disagreements": tuple(disagreements),
    }


def witness_report(
    left: Regard,
    right: Regard,
    observer: Regard,
    demand: Any,
) -> dict:
    """Mesurer un accord avant qui masque un désaccord arrière observable."""

    if (left.src, left.tgt) != (right.src, right.tgt):
        raise ValueError("Les regards témoins doivent avoir les mêmes strates")
    if observer.src != left.src:
        raise ValueError("L'observateur doit lire la strate source produite")
    if demand not in elements(left.tgt):
        raise ValueError("La demande n'appartient pas à la strate cible")

    forward = agreement(left, right, on="get")
    backward = agreement(left, right, on="put")
    detected = []
    for state in elements(left.src):
        left_world = left.put(state, demand)
        right_world = right.put(state, demand)
        if observer.get(left_world) != observer.get(right_world):
            detected.append(state)

    return {
        "a": left.name,
        "b": right.name,
        "forward_rate": forward["rate"],
        "backward_rate": backward["rate"],
        "n_backward_disagreements": len(backward["disagreements"]),
        "n_backward_slots": backward["total"],
        "forward_agreement_is_total": not forward["disagreements"],
        "backward_agreement_is_total": not backward["disagreements"],
        "observer": observer.name,
        "observer_demand": demand,
        "n_detectable": len(detected),
        "detected": tuple(detected),
    }


def associativity_report(family: Sequence[Regard]) -> dict:
    """Vérifier l'associativité extensionnelle de tous les triples composables."""

    triples = 0
    points = 0
    violations = []
    for first in family:
        for second in family:
            if first.tgt != second.src:
                continue
            for third in family:
                if second.tgt != third.src:
                    continue
                triples += 1
                left = compose(compose(third, second), first)
                right = compose(third, compose(second, first))
                for state in elements(first.src):
                    for demand in elements(third.tgt):
                        points += 1
                        left_value = (left.get(state), left.put(state, demand))
                        right_value = (right.get(state), right.put(state, demand))
                        if left_value != right_value:
                            violations.append(
                                (first.name, second.name, third.name,
                                 state, demand, left_value, right_value)
                            )
    return {
        "n_composable_triples": triples,
        "n_points": points,
        "n_violations": len(violations),
        "violations": tuple(violations),
    }


def reference_family() -> tuple[Regard, ...]:
    """Construire la famille finie utilisée par le banc de l'opération 12."""

    id_w = identity("W")
    id_z3 = identity("Z3")
    id_z2 = identity("Z2")
    swap = Regard("SWAP", "W", "W", lambda w: (w[1], w[0]),
                  lambda _w, y: (y[1], y[0]))
    lum = Regard("LUM", "W", "Z3", lambda w: w[0],
                 lambda w, y: (y, w[1]))
    lum_d = Regard("LUM-D", "W", "Z3", lambda w: w[0],
                   lambda w, y: (y, (w[1] + y - w[0]) % 3))
    chg = Regard("CHG", "W", "Z3", lambda w: w[1],
                 lambda w, y: (w[0], y))
    chg_d = Regard("CHG-D", "W", "Z3", lambda w: w[1],
                   lambda w, y: ((w[0] + y - w[1]) % 3, y))
    shift = Regard("SHIFT", "Z3", "Z3", lambda x: (x + 1) % 3,
                   lambda _x, y: (y - 1) % 3)
    memo = Regard("MEMO", "Z3", "Z2", lambda x: x % 2,
                  lambda x, y: x if x % 2 == y else y)
    return (id_w, id_z3, id_z2, swap, lum, lum_d, chg, chg_d,
            shift, memo)


def _by_name(family: Sequence[Regard], name: str) -> Regard:
    return next(regard for regard in family if regard.name == name)


def op12_verdict() -> dict:
    """Calculer le verdict reproductible du banc de composition."""

    family = reference_family()
    lum = _by_name(family, "LUM")
    lum_d = _by_name(family, "LUM-D")
    chg = _by_name(family, "CHG")
    chg_d = _by_name(family, "CHG-D")
    memo = _by_name(family, "MEMO")
    shift = _by_name(family, "SHIFT")
    swap = _by_name(family, "SWAP")
    id_w = _by_name(family, "idW")

    correct = compose(swap, swap)
    wrong = compose_without_reinjection(swap, swap)
    return {
        "laws": tuple(law_report(regard) for regard in family),
        "witness_direct": witness_report(lum, lum_d, chg, 0),
        "witness_mirror": witness_report(chg, chg_d, lum, 0),
        "witness_composed": {
            "memo": witness_report(
                compose(memo, lum), compose(memo, lum_d), chg, 0
            ),
            "shift": witness_report(
                compose(shift, lum), compose(shift, lum_d), chg, 0
            ),
        },
        "associativity": associativity_report(family),
        "control_correct": law_report(correct),
        "control_wrong": law_report(wrong),
        "units": {
            regard.name: {
                "right_get": agreement(
                    compose(regard, identity(regard.src)), regard, on="get"
                )["rate"],
                "right_put": agreement(
                    compose(regard, identity(regard.src)), regard, on="put"
                )["rate"],
                "left_get": agreement(
                    compose(identity(regard.tgt), regard), regard, on="get"
                )["rate"],
                "left_put": agreement(
                    compose(identity(regard.tgt), regard), regard, on="put"
                )["rate"],
            }
            for regard in family
            if regard.name not in {id_w.name, "idZ3", "idZ2"}
        },
    }
