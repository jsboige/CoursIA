#!/usr/bin/env python3
"""La PORTEE d'un [RELEASED] : la lane qui l'a rendu, ou toute la flotte.

Un grain rendu par une lane qui a bute sur un **echec d'OUTIL** n'est gele
que pour CETTE lane : les autres n'ont pas le meme outillage, et leur servir
ce grain n'ouvre aucun risque. Un rendu pour une **barriere reelle** (GPU,
siege, arbitrage) reste un ecart pour toute la flotte : son motif vaut
partout.

Mesure a l'origine du correctif (dispatch `c0035b` du coordinateur, 24/11) :
la garde « `RELEASED` < 3 j » gelait pour **toute** la flotte un grain qu'une
seule lane avait rendu -- typiquement une production qui a consomme ses
essais (`verify-reject`, `built-structure-mismatch`, `stage2-call-failed`).
Le grain devenait impossible a servir par quiconque, et la flotte le perdait.

Deux lectures que la forme reelle des rendus impose :

- le **motif est ecrit plus loin que le marqueur** (la ligne du marqueur ne
  dit que « N essais consommes ») : c'est le **corps du commentaire** qui
  porte les codes d'echec ;
- le marqueur **ne nomme pas toujours sa lane** : quand il ne la nomme pas,
  la lane du rendu est celle du **dernier claim** qui precede la remise de
  main -- c'est la lane qui produisait.

Le vocabulaire est **ferme** : un motif inconnu n'est jamais traite comme un
echec d'outil (fail-CLOSED -- le grain reste gele pour tous), et un motif
d'echec d'outil que personne ne connait ne gele que la lane qui l'a rendu.
"""
from __future__ import annotations

import re
from datetime import datetime

from coordination.tapis_marqueurs import OUVRE

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

#: Un motif est un CODE : il se reconnait a ses separateurs (`-`, `_`), pas a
#: un sous-motif (`verify-reject` ne se lit pas dans `verify-rejected`).
_TOKEN_RE = re.compile(r"[\w-]+")


def est_echec_outil(corps: str) -> bool:
    """Le rendu dit-il un echec d'OUTIL de la lane ?

    Fail-CLOSED : un motif inconnu n'est **pas** un echec d'outil, donc le
    grain reste gele pour toute la flotte (le comportement d'avant).
    """
    jetons = {t.lower() for t in _TOKEN_RE.findall(corps or "")}
    return any(motif in jetons for motif in MOTIFS_ECHEC_OUTIL)


def portee(evts: list, evt) -> str | None:
    """La lane a qui appartient un [RELEASED].

    Le marqueur nomme souvent sa lane ; quand il ne la nomme pas (les rendus
    de production ecrivent le motif sans la lane), elle est celle du dernier
    claim qui precede la remise de main -- c'est la lane qui produisait.
    """
    if evt.lane:
        return evt.lane
    for ev in reversed(evts[:-1]):
        if ev.marque in OUVRE and ev.lane:
            return ev.lane
    return None


def motif(evts: list, evt, maintenant: datetime, lane: str, relache_j: int) -> str | None:
    """L'ecart de la regle RELACHEE pour un marqueur [RELEASED], ou None.

    L'ecart ne porte que si le rendu est **recent** (< `relache_j` jours).
    Sa **portee** depend du motif : un echec d'outil ne gele que la lane qui
    a rendu le grain, une barriere reelle gele toute la flotte.
    """
    age = round((maintenant - evt.quand).total_seconds() / 86400, 1)
    if age >= relache_j:
        return None
    if est_echec_outil(evt.corps):
        qui = portee(evts, evt)
        if qui and qui != lane:
            # Les autres lanes n'ont pas le meme outil : elles ne sont pas gelees.
            return None
        return (f"rendue par {qui or '?'} il y a {age} j (< {relache_j} j) : "
                f"echec d'outil, reserve a {qui or '?'}")
    return (f"rendue par {evt.lane or '?'} il y a {age} j (< {relache_j} j) : "
            f"lire son motif")
