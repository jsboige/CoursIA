#!/usr/bin/env python3
"""Les ecarts d'attente d'un grain : remise de main et pause explicite.

Deux regles qui mesurent la meme chose -- le fil dit que le grain attend --
et qui se distinguent par la seule presence d'une **condition** :

1. **RELACHEE** -- le dernier marqueur du fil est un `[RELEASED]` de moins de
   `RELACHE_J` jours, quelle que soit la lane : son motif (barriere, siege)
   vaut encore. La fenetre est courte (3 jours) : au-dela, le grain revient
   dans le pool.

2. **PAUSE** (#27726) -- ce meme `[RELEASED]` porte une condition
   (`attend: #N` ou `attend: Q<id>`). L'ecart ne porte **aucun delai** : il
   tient jusqu'a la levee de la condition -- l'issue ou la PR citee fermee --
   ou jusqu'a un marqueur posterieur, qui rend le grain de nouveau servable.
   Une condition sans numero (une question user) n'est pas mesurable par la
   lecture : elle tient jusqu'a un marqueur posterieur.

Les deux regles vivent ensemble parce qu'elles se contredisent sur le meme
marqueur : une remise de main qui porte une condition n'est pas une remise de
main de trois jours, c'est une pause.
"""
from __future__ import annotations

import re
from datetime import datetime

#: Fenetre de remise de main, en jours.
RELACHE_J = 3

_CITE_RE = re.compile(r"#(\d+)\b")


def relachee(evts: list, maintenant: datetime) -> str | None:
    """Le dernier marqueur du fil est un [RELEASED] de moins de RELACHE_J jours,
    quelle que soit la lane : son motif (barriere, siege) vaut encore."""
    if not evts or evts[-1].marque != "RELEASED" or evts[-1].attend:
        return None  # un [RELEASED] qui porte une condition est une PAUSE
    ev = evts[-1]
    age = round((maintenant - ev.quand).total_seconds() / 86400, 1)
    if age >= RELACHE_J:
        return None
    return f"rendue par {ev.lane or '?'} il y a {age} j (< {RELACHE_J} j) : lire son motif"


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
