#!/usr/bin/env python3
"""La BORNE de commande : UNE echeance partagee par tous les etages du tirage.

Invariant I6 du contrat du picker (#28114) : le budget d'une commande de
tirage est **un seul**, pris au **vrai point d'entree**. Avant, chaque etage
repartait d'une horloge neuve (la garde de fraicheur : 120 s pour un `git
fetch`, 60 s par appel git ; la selection : 30 s ; la qualification : 60 s ;
le cap : 60 s par tranche) -- la commande pouvait depasser plusieurs fois son
contrat.

Ce module rend les **primitives** de la borne : `echeance()` (le point de
fin, pose au point d'entree), `restant()` / `expire()`, `timeout_borne()`
(le timeout d'un appel, borne par le restant), `part()` (le budget d'un
etage, plafonne par l'echeance de la commande), `sous_echeance()` (une lecture
**abandonnee** au passage de l'echeance -- fail-OPEN : la mesure vaut `None`,
elle n'ecarte rien) et `fetteur_sous_borne()`.

Aucun appel reseau ici : le module est pur, il se teste sans `gh`.
"""
from __future__ import annotations

import subprocess
import threading
import time

from coordination import gh_selection

#: La part de la garde de fraicheur dans le budget de la commande. Mesuree
#: le 25/11 sur ce depot : `git fetch origin main` 12,4 s + `git diff` des
#: organes 20,1 s + `git rev-list` 1,7 s -- soit 35 s. La part est le double
#: : la garde ne doit pas pouvoir affamer le tirage, ni etre coupee sur un
#: reseau lent.
FRAICHEUR_S = 45.0

#: Le budget de la COMMANDE entiere : le mur global du tirage (lu dans
#: `gh_selection`, l'organe qui le porte) PLUS la part de la garde de
#: fraicheur. Chaque etage garde son propre budget, pris DANS celui de la
#: commande : la commande ne peut pas depasser la somme de ses etages, et
#: aucun etage ne peut affamer les autres.
BUDGET_S = float(gh_selection.MUR_GLOBAL_S) + FRAICHEUR_S


def part(echeance_: float | None, part_s: float) -> float | None:
    """Le budget d'un etage : le sien, jamais au-dela de l'echeance.

    L'etage garde son propre budget (le tirage 30 s, la garde de fraicheur
    45 s) mais il est **plafonne par l'echeance de la commande** : un etage
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
