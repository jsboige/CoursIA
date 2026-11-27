"""La REPRISE d'un grain dont la livraison n'est pas prouvee (#28114).

Un marqueur de livraison non prouve ne doit pas rendre un grain plus servable
que son absence : la decision d'un grain marque est celle d'un grain nu, plus
la note qui dit la livraison. Le defaut mesure (cycle c767) tenait a l'ordre
des operations -- LIVREE posait un ecart, cet ecart faisait sauter l'exclusion
d'occupation, la preuve par le diff retirait LIVREE, et rien n'etait rejoue :
le grain traversait les regles suivantes et il etait servi.

La reprise rejoue `tapis_rapide._decider` en taisant la seule regle LIVREE
(`ctx["livree_muette"]`, sa signature ne change pas), puis applique
l'occupation. Elle sert les deux voies de la qualification :

- `appliquer` : la fenetre des derniers commentaires (`tapis_qualification`) ;
- `decider`   : le fil complet relu (`tapis_fil_complet.confirmer`).

Une livraison PROUVEE garde LIVREE et n'est pas reprise.
"""
from __future__ import annotations

from datetime import datetime
from pathlib import Path

import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from coordination import tapis_diff, tapis_occupation, tapis_rapide
from coordination.tapis_marqueurs import evenements
from coordination.tapis_visites import evenements_info


def _evts(comments: list[dict]) -> list:
    """Les evenements du fil, comme la premiere passe les lit (#22500)."""
    return sorted(evenements(comments) + evenements_info(comments),
                  key=lambda ev: ev.quand)


def _reprendre(e, it: dict, comments: list[dict], ancetres: list[int], ctx: dict,
               prs_par_issue: dict | None) -> str | None:
    """Rejoue la decision sans LIVREE, puis l'occupation ; l'ecart retenu."""
    tapis_rapide._decider(e, it, _evts(comments), ancetres,
                          {**ctx, "livree_muette": True})
    if e.ecart is None:
        occupation = tapis_occupation.marques_pr(prs_par_issue or {}, ctx["lane"])
        tapis_occupation.exclure([e], occupation, ctx["lane"])
    return e.ecart


def appliquer(etats: list, lec, preuve, lane: str, maintenant: datetime,
              jours: int, prs_par_issue: dict | None = None) -> None:
    """La preuve retire LIVREE : les grains retombes reprennent leur decision."""
    if preuve is None:
        return
    livres = [e for e in etats if e.ecart == "LIVREE"]
    tapis_diff.appliquer(etats, lec, preuve)
    tombes = [e for e in livres if e.ecart is None]
    if not tombes:
        return
    ouvertes, parents, _, ctx = tapis_rapide._contexte(lec, lane, maintenant, jours)
    for e in tombes:
        it = ouvertes[e.numero]
        _reprendre(e, it, it.get("comments") or [],
                   tapis_rapide._ancetres(e.numero, parents)[0], ctx, prs_par_issue)


def decider(e, comments: list[dict], code: str | None, preuve, ouvertes: dict,
            parents: dict, ctx: dict, prs_par_issue: dict | None = None) -> str | None:
    """La meme reprise, sur le fil COMPLET deja lu par `confirmer`."""
    if preuve is None:
        return code
    livre = code == "LIVREE"
    code = tapis_diff.decider(e, comments, code, preuve)
    if not livre or code is not None:
        return code
    it = {**ouvertes[e.numero], "comments": comments,
          "comments_total": len(comments)}
    return _reprendre(e, it, comments, tapis_rapide._ancetres(e.numero, parents)[0],
                      ctx, prs_par_issue)
