#!/usr/bin/env python3
"""Le MOTIF COURANT d'un rendu : l'echec d'outil d'aujourd'hui, ou le code
cite au passe.

Review du coordinateur (25/11, #28440) : `est_echec_outil()` lisait un code
d'echec **n'importe ou** dans le commentaire : une lane qui rendait un grain
pour une barriere reelle voyait son grain degele pour toutes les autres lanes.

Ce module decide : un code d'echec n'est le motif **courant** que si sa
clause ne porte aucun marqueur d'**historique** ET que sa forme est
**positivement identifiee** (format explicite `motif: <code>`, ou forme
Rust mesuree -- voir `tapis_relache_forme`). Un code cite au passe, ou
cite sans forme, ne degele rien : le gel reste **global** (fail-CLOSED).

Le vocabulaire des cinq motifs d'echec d'OUTIL est **ferme** (les cinq
mesures du dispatch `c0035b`, 24/11) ; le vocabulaire des marqueurs
d'historique est, lui, **ouvert** : un marqueur inconnu ne rend un code
historique que s'il est dans la liste, et une liste qui s'etend ne change
rien au fail-CLOSED.
"""
from __future__ import annotations

import re
import unicodedata

from coordination.tapis_relache_forme import codes_identifies

#: Les motifs d'echec d'OUTIL mesures (dispatch `c0035b`, 24/11) : l'echec est
#: dans la chaine d'outillage de la lane, pas dans le grain. Un grain rendu
#: pour l'un de ces motifs n'est pas gele pour la flotte -- seulement pour la
#: lane qui l'a rendu.
MOTIFS_ECHEC_OUTIL = frozenset({
    "stage2-call-failed",
    "verify-reject",
    "refused-revise-trace-mismatch",
    "built-structure-mismatch",
    "stage2-unparsed",
})

#: Les marqueurs d'un motif **cite** (le passe). La clause qui les porte ne
#: decrit pas le motif courant du rendu : elle se souvient. Les formes sont
#: ecrites sans accent : le texte est normalise (accents retires) avant
#: d'etre lu.
MARQUES_HISTORIQUES = frozenset({
    "precedent", "precedente", "precedents", "precedentes",
    "historique", "historiques",
    "ancien", "ancienne", "anciens", "anciennes",
    "passe", "passees", "autrefois",
    "rappelle", "rappellent", "rappelant",
    "mentionne", "mentionnent", "mentionnant",
    "dernier", "derniere", "derniers", "dernieres",
})

#: Un motif est un CODE : il se reconnait a ses separateurs (`-`, `_`), pas a
#: un sous-motif (`verify-reject` ne se lit pas dans `verify-rejected`).
_TOKEN_RE = re.compile(r"[\w-]+")

#: Une CLAUSE : une phrase ou un fragment separe par `;` ou un saut de ligne.
#: Le marqueur d'historique et le code doivent etre dans la meme clause.
_CLAUSE_RE = re.compile(r"[;\n]+")


def _sans_accents(texte: str) -> str:
    """Le texte normalise : les accents retires, la casse conservee."""
    return "".join(c for c in unicodedata.normalize("NFKD", texte or "")
                   if not unicodedata.combining(c))


def codes(corps: str) -> set[str]:
    """Les codes d'echec d'OUTIL cites dans le commentaire."""
    jetons = {t.lower() for t in _TOKEN_RE.findall(_sans_accents(corps))}
    return jetons & MOTIFS_ECHEC_OUTIL


def codes_historiques(corps: str) -> set[str]:
    """Les codes d'echec cites **au passe** : leur clause porte un marqueur.

    Une clause sans marqueur ne prouve rien : le code y est le motif
    courant -- c'est la forme mesuree des rendus de production (Rust, 22/11),
    ou les codes sont listes avec leur fournee et leur date.
    """
    trouves: set[str] = set()
    for clause in _CLAUSE_RE.split(_sans_accents(corps)):
        jetons = {t.lower() for t in _TOKEN_RE.findall(clause)}
        if jetons & MARQUES_HISTORIQUES:
            trouves |= jetons & MOTIFS_ECHEC_OUTIL
    return trouves


def est_echec_outil(corps: str) -> bool:
    """Le rendu dit-il un echec d'OUTIL **courant** ?

    Fail-CLOSED : un code cite au passe n'est pas le motif courant ; un code
    cite dans une forme non identifiee non plus ; un melange de codes
    reste ambigu -- le grain reste donc gele pour toute la flotte (le
    comportement d'avant), plutot que de degeler sur une lecture
    unilaterale.
    """
    trouves = codes(corps)
    if not trouves:
        return False
    if codes_historiques(corps):
        return False
    return bool(codes_identifies(corps) & trouves)
