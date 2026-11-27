#!/usr/bin/env python3
"""La remise de main BORNEE : un `[RELEASED]` qui nomme un `paths:` ne rend que lui.

La regle `RELACHEE` (`tapis_attente.relachee`) est ecrite ISSUE par issue : le
dernier marqueur du fil rend le grain, quelle que soit la lane, pendant trois
jours. C'est juste quand une issue EST un grain.

Sur un marathon -- un fil qui porte plusieurs carnets -- elle met en quarantaine
des grains que le marqueur ne nomme pas. Mesure du 27/11 sur CoursIA#27133 : le
`[RELEASED]` du carnet Search-11 (verify-reject) a refuse la fournee suivante,
deux grains en 32 s (`refused-claim-not-qualified:RELACHEE`), dont MGS-25 --
un carnet du MEME fil que le marqueur ne nommait pas et qui n'avait jamais
echoue.

Ce module rend la seule chose que la regle ne peut pas voir seule : le scope
declare par le DEMANDEUR (`--paths`). Un marqueur qui nomme une clause `paths:`
disjointe de ce scope ne rend pas ce grain-la. Sans clause -- ou avec une clause
illisible -- la remise reste EPIC-WIDE : dans le doute on sur-bloque, jamais
l'inverse.

Le consommateur (la qualification du claim) l'applique apres coup, quand la
regle a rendu `RELACHEE` : c'est sur, `RELACHEE` est le DERNIER code de
`CODES_QUALIFICATION` dans la chaine de `tapis_rapide._decider`, donc l'ecarter
vide la qualification (les codes suivants dependent du pool et ne qualifient
pas). Cet ordre est epingle par `scripts/tests/test_tapis_remise_borne.py`.
"""
from __future__ import annotations

from coordination.tapis_marqueurs import evenements
from coordination.tapis_visites import evenements_info


def dernier_marqueur(comments: list[dict]):
    """Le dernier marqueur du fil, lu comme le lit `tapis_rapide._decider`."""
    evts = sorted(evenements(comments) + evenements_info(comments),
                  key=lambda e: e.quand)
    return evts[-1] if evts else None


def _binds(ev, scope: list[str]) -> bool:
    """Ce marqueur engage-t-il le scope de l'appelant ?"""
    clause = getattr(ev, "paths", None)
    if not clause:
        return True                      # epic-wide : la clause est absente
    from coordination import claim_grammar  # import tardif : pas de cycle
    rendues = claim_grammar._extract_paths_clause(f"[RELEASED] paths: {clause}")
    if not rendues:
        return True                      # clause illisible : on sur-bloque
    return claim_grammar._scopes_intersect(list(scope), rendues)


def rendue_ailleurs(comments: list[dict], scope: list[str] | None) -> bool:
    """True quand la remise de main du fil ne vise PAS le scope de l'appelant.

    `False` couvre les cas ou la question ne se pose pas : pas de scope declare,
    dernier marqueur qui n'est pas une remise, remise qui porte une condition
    (c'est une PAUSE, decidee ailleurs) ou remise epic-wide.
    """
    if not scope:
        return False
    ev = dernier_marqueur(comments)
    if ev is None or ev.marque != "RELEASED" or getattr(ev, "attend", None):
        return False
    return not _binds(ev, scope)
