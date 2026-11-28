#!/usr/bin/env python3
"""Les ecarts d'attente d'un grain : remise de main et pause explicite.

Deux regles qui mesurent la meme chose -- le fil dit que le grain attend --
et qui se distinguent par la seule presence d'une **condition** :

1. **RELACHEE** -- le dernier marqueur du fil QUI CONCERNE les chemins demandes
   est un `[RELEASED]` de moins de `RELACHE_J` jours, quelle que soit la lane :
   son motif (barriere, siege) vaut encore. La fenetre est courte (3 jours) :
   au-dela, le grain revient dans le pool. Un `[RELEASED]` porte sur les seuls
   chemins de sa clause `paths:` -- sur tout le grain s'il n'en a pas -- et un
   marqueur posterieur sur d'AUTRES chemins ne l'efface pas (#28899). Sans
   chemins demandes (le tirage), seul le dernier marqueur du fil compte.

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

from coordination import claim_grammar, tapis_relache

#: Fenetre de remise de main, en jours.
RELACHE_J = 3

_CITE_RE = re.compile(r"#(\d+)\b")


def _vise(ev, chemins: list[str] | None) -> bool:
    """Le marqueur porte-t-il sur l'un des chemins demandes ? Sans chemins
    demandes (le tirage), sans clause `paths:` ou avec une clause illisible
    (conservateur, #10597), il vise tout le grain."""
    # La grammaire lit la clause sur la LIGNE du marqueur, depuis son debut.
    ligne = f"[{ev.marque}]{ev.reste}"
    globes = claim_grammar._extract_paths_clause(ligne) if ev.paths else None
    if not chemins or not globes or claim_grammar._unparseable_scope_in(globes):
        return True
    return claim_grammar._scopes_may_overlap_by_pattern(globes, list(chemins))


def relachee(evts: list, maintenant: datetime, lane: str,
             chemins: list[str] | None = None) -> str | None:
    """Le dernier marqueur du fil QUI CONCERNE `chemins` (tous s'ils ne sont
    pas donnes) est un [RELEASED] de moins de RELACHE_J jours.

    Deux portees, pour deux questions differentes (#28899, puis #28440) :

    - les CHEMINS : un `[RELEASED] paths:A` ne gele pas la qualification
      demandee sur les chemins B, et n'efface pas la remise anterieure qui,
      elle, portait ;
    - la LANE : la portee d'un rendu depend de son motif -- un echec d'OUTIL
      ne gele que la lane qui l'a rendu, une barriere reelle gele la flotte
      (`tapis_relache.motif`, fail-CLOSED sur un motif inconnu).
    """
    for i in range(len(evts) - 1, -1, -1):
        ev = evts[i]
        if not _vise(ev, chemins):
            continue  # sur d'AUTRES chemins : il n'efface rien ici (#28899)
        if ev.marque != "RELEASED" or ev.attend:
            return None  # un [RELEASED] qui porte une condition est une PAUSE
        # `motif` lit la lane du rendu sur les marqueurs qui PRECEDENT celui-ci
        # (`portee` scanne `evts[:-1]`) : il recoit le fil tronque, jamais
        # `evts` entier -- la queue du fil est posterieure a la remise de main.
        return tapis_relache.motif(evts[:i + 1], ev, maintenant, lane, RELACHE_J)
    return None


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
