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

**Le motif courant, pas l'historique cite** (review du coordinateur du
25/11 sur #28440) : un code d'echec lu n'importe ou dans le commentaire
degelait le grain pour toute la flotte, meme quand la lane rendait le grain
pour une barriere reelle et ne **rappellait** qu'un ancien `verify-reject`.
La lecture du motif courant est dans `tapis_relache_motif`.
"""
from __future__ import annotations

from datetime import datetime

from coordination.tapis_marqueurs import OUVRE
from coordination.tapis_relache_motif import (MOTIFS_ECHEC_OUTIL,
                                              codes, codes_historiques,
                                              est_echec_outil)

#: Les motifs d'echec d'OUTIL et la lecture du **motif courant** vivent dans
#: `tapis_relache_motif` (extraction du 25/11, review du coordinateur sur
#: #28440) : un code d'echec cite au passe n'est pas le motif courant du
#: rendu. Les alias gardent les appelants intacts.


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
