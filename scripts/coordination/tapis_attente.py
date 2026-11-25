#!/usr/bin/env python3
"""Les ecarts d'attente d'un grain : la pause explicite.

La regle **RELACHEE** (la remise de main de moins de trois jours) vit dans
`coordination/tapis_relache.py` : depuis #28440, sa **portee** depend du motif
-- un echec d'outillage ne gele que la lane qui l'a subi, une barriere reelle
gele toute la flotte. Elle en a ete extraite pour que ce module tienne son
plafond.

La regle qui reste ici :

**PAUSE** (#27726) -- un `[RELEASED]` qui porte une condition (`attend: #N`
ou `attend: Q<id>`). L'ecart ne porte **aucun delai** : il tient jusqu'a la
levee de la condition -- l'issue ou la PR citee fermee -- ou jusqu'a un
marqueur posterieur, qui rend le grain de nouveau servable. Une condition
sans numero (une question user) n'est pas mesurable par la lecture : elle
tient jusqu'a un marqueur posterieur.
"""
from __future__ import annotations

import re
from datetime import datetime

#: Fenetre de remise de main, en jours.
RELACHE_J = 3

_CITE_RE = re.compile(r"#(\d+)\b")


def pause(evts: list, ctx: dict) -> str | None:
    """Une pause explicite (#27726) : le dernier marqueur est un [RELEASED]
    qui porte une condition (`attend: #N` ou `attend: Q<id>`)."""
    if not evts or evts[-1].marque != "RELEASED" or not evts[-1].attend:
        return None
    ev = evts[-1]
    cites = [int(x) for x in _CITE_RE.findall(ev.attend)]
    if cites and not any(n in ctx["ouverts"] for n in cites):
        return None  # condition levee : l'issue redevient servable
    age = round((ctx["maintenant"] - ev.quand).total_seconds() / 86400, 1)
    return f"pause de {ev.lane or '?'} il y a {age} j : attend {ev.attend}"
