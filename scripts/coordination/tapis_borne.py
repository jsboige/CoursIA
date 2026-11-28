#!/usr/bin/env python3
"""La BORNE de commande : UNE echeance partagee par tous les etages du tirage.

Invariant I6 du contrat du picker (#28114) : le budget d'une commande de
tirage est **un seul**, pris au **vrai point d'entree**. Avant, chaque etage
repartait d'une horloge neuve (garde : 120 s pour un `git fetch`, 60 s par
appel git ; selection : 30 s ; qualification : 60 s ; cap : 60 s par
tranche) -- la commande pouvait depasser son contrat.

Ce module rend les **primitives** de la borne : `echeance()` (le point de
fin, pose au point d'entree), `restant()` / `expire()`, `timeout_borne()`
(timeout d'un appel, borne par le restant), `part()` (budget d'un etage,
plafonne par l'echeance), `sous_echeance()` (lecture **abandonnee** au
passage de l'echeance -- fail-OPEN) et `fetteur_sous_borne()`.

Aucun appel reseau ici : le module est pur, il se teste sans `gh`.
"""
from __future__ import annotations

import subprocess
import threading
import time

from coordination import gh_selection

#: La part de la garde de fraicheur. Mesuree le 26/11 sur ce depot :
#: `git fetch origin main` 20,4 s + `git rev-list` (x2) 2,2 s + `git diff
#: --name-only origin/main` des organes 1,1 s -- soit 23,7 s. La part est
#: 30 s : au-dela, la coupe est **degradable** (`FRAICHEUR_BORNEE`).
FRAICHEUR_S = 30.0

#: La borne de la COMMANDE entiere -- la borne du CLI, prise au point
#: d'entree. C'est le CONTRAT : I6 de #28114 dit qu'un tirage rend en moins
#: de 60 s (55 s ici, marge 5 s). Les parts des etages (30 s la garde, 48 s
#: le tirage) sont volontairement SUPERIEURES a cette enveloppe : elles ne
#: s'additionnent pas, elles se PARTAGENT (chaque etage prend
#: `min(echeance, maintenant + sa part)`). La commande ne peut donc pas
#: depasser l'enveloppe : elle est COUPEE, pas attendue. Le pire cas est
#: assume ainsi : l'etage degradable (la garde) encaisse la coupe, l'etage
#: decisionnel (la selection) garde son budget dans le cas normal (23,7 s
#: mesurees -> 31,3 s pour un tirage qui en demande 48).
BUDGET_S = 55.0


def part(echeance_: float | None, part_s: float) -> float | None:
    """Le budget d'un etage : le sien, jamais au-dela de l'echeance.

    L'etage garde son propre budget (le tirage 30 s, la garde de fraicheur
    30 s) mais il est **plafonne par l'echeance de la commande** : un etage
    ne peut pas depenser la part d'un autre.
    """
    if echeance_ is None:
        return None
    return min(echeance_, time.monotonic() + float(part_s))


def echeance(budget_s: float = BUDGET_S, debut: float | None = None) -> float:
    """Le point de fin de la commande : `debut + budget`.

    `debut` par defaut = maintenant. L'appelant qui KNOWS quand la commande
    a commence (le point d'entree) passe son `debut` : la borne couvre alors
    TOUTE la commande, garde de fraicheur comprise.
    """
    return (time.monotonic() if debut is None else debut) + float(budget_s)


def restant(echeance_: float | None) -> float | None:
    """Le temps restant avant l'echeance ; `None` = aucune borne."""
    if echeance_ is None:
        return None
    return echeance_ - time.monotonic()


def expire(echeance_: float | None) -> bool:
    """La borne est-elle depassee ? Sans borne, jamais."""
    r = restant(echeance_)
    return r is not None and r <= 0


def timeout_borne(cap: float, echeance_: float | None) -> int:
    """Le timeout d'un appel : son propre plafond, borne par le restant.

    Rend **0** quand la borne est deja depassee : l'appelant ne lance alors
    rien (un `subprocess` avec un timeout de 0 serait un faux timeout).
    """
    r = restant(echeance_)
    if r is None:
        return int(cap)
    if r <= 0:
        return 0
    return max(1, int(min(cap, r)))


def sous_echeance(lecture, echeance_: float | None):
    """La lecture sous l'echeance : sa valeur, ou `None` si le delai passe.

    La borne est **structurelle** : elle ne suppose pas que l'appel respecte
    le timeout qu'il recoit. Un appel lent (reseau lent, runner lent) est
    abandonne au passage de l'echeance, et la mesure vaut `None` -- fail-OPEN :
    on ne refuse jamais sur une charge qu'on n'a pas su lire. Le fil de lecture
    est un daemon : il ne retarde pas la fin du processus.
    """
    if echeance_ is None:
        return lecture()
    r = restant(echeance_)
    if r is not None and r <= 0:
        return None
    boite: list = []

    def cible() -> None:
        try:
            boite.append(("ok", lecture()))
        except BaseException as exc:  # noqa: BLE001 - propage au demandeur
            boite.append(("err", exc))

    fil = threading.Thread(target=cible, name="tapis-borne", daemon=True)
    fil.start()
    fil.join(r)
    if not boite:
        return None  # echeance passee : la mesure est perdue
    genre, valeur = boite[0]
    if genre == "err":
        raise valeur
    return valeur


def fetteur_sous_borne(lancer, echeance_: float | None):
    """Un fetteur `(since, until) -> list[dict]` run sous la borne.

    `lancer(since, until, timeout)` fait l'appel. Une tranche qui recoit un
    budget epuise leve `subprocess.TimeoutExpired` : la mesure est perdue,
    le cap n'ecarte rien (fail-OPEN).
    """
    def slice_run(since: str, until: str) -> list[dict]:
        r = restant(echeance_)
        if r is not None and r <= 0:
            raise subprocess.TimeoutExpired(cmd="gh pr list", timeout=r)
        return lancer(since, until, timeout=r)
    return slice_run
