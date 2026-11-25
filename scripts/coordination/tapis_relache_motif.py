#!/usr/bin/env python3
"""Le vocabulaire d'echec d'outillage d'une remise de main (#28440).

Un `[RELEASED]` qui rapporte un **echec d'outillage** (le build de laRanges
rust du 22/11) ne gele que la lane qui l'a subi : les autres lanes n'ont pas
le meme outillage. Un rendu qui porte une **barriere reelle** (GPU, siege,
arbitrage, proprietaire nomme) gele toute la flotte : le comportement
d'avant, intact.

Le vocabulaire est **ferme** : cinq codes mesures. Un motif inconnu n'est
jamais traite comme un echec d'outil (fail-CLOSED) -- le grain reste gele
pour tous.

Deux lectures que la forme reelle des rendus impose :

1. le **motif est ecrit plus loin que la ligne du marqueur** (la ligne ne dit
   que « 2 essais contenu consommes ») : c'est le **corps du commentaire** qui
   porte les codes ;
2. un code **cite** (rappel d'un echec ancien) n'est pas un echec de CE
   rendu : le code doit etre un **essai** de la remise de main. Un code cite
   hors essai rend l'echec **ambigu** : le gel reste global.
"""
from __future__ import annotations

import re

#: Les cinq codes d'echec d'outillage, mesures sur les rendus de production Rust.
CODES_OUTIL = frozenset({
    "stage2-call-failed",
    "verify-reject",
    "refused-revise-trace-mismatch",
    "built-structure-mismatch",
    "stage2-unparsed",
})

_CODE_RE = re.compile(r"\b(" + "|".join(sorted(CODES_OUTIL)) + r")\b", re.IGNORECASE)
#: Un essai du rendu : il porte son index (« (1) verify-reject ») ou se dit
#: « essai » / « tentative ». Un code cite sans cela est une citation.
_ESSAI_RE = re.compile(r"\(\s*\d+\s*\)|^\s*\d+\s*[.)]\s|\bessais?\b|\btentatives?\b",
                       re.IGNORECASE | re.MULTILINE)


def codes(corps: str) -> set[str]:
    """Les codes d'echec d'outillage cites dans le corps du rendu."""
    return {m.group(1).lower() for m in _CODE_RE.finditer(corps or "")}


def codes_outil(corps: str) -> set[str]:
    """Les codes d'echec d'outillage **de ce rendu** -- ses essais.

    Vide = le rendu ne porte pas d'echec d'outillage identifie : il porte une
    barriere reelle, une citation historique, ou un melange ambigu. Les trois
    cas reglent le gel pour TOUTE la flotte (fail-CLOSED).
    """
    cites = codes(corps)
    if not cites:
        return set()
    essais: set[str] = set()
    for ligne in (corps or "").splitlines():
        if not _ESSAI_RE.search(ligne):
            continue
        essais.update(m.group(1).lower() for m in _CODE_RE.finditer(ligne))
    if not essais:
        return set()  # des codes cites, aucun essai : une citation
    if cites - essais:
        return set()  # melange : un code cite hors essai rend l'echec ambigu
    return essais


def code_outil(corps: str) -> str | None:
    """Un code d'echec d'outillage de ce rendu, ou None."""
    essais = codes_outil(corps)
    return sorted(essais)[0] if essais else None
