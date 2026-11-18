#!/usr/bin/env python3
"""La QUALIFICATION d'un grain servi : son corps, son fil complet, sa decision.

Extraction de `coordination/tapis_leger.py` (18/11) : la qualification et le
tirage sont deux reponsabilites distinctes, et la premiere a son propre
plafond de lignes.

Ce module fait ce que la lecture groupee ne sait pas faire :

- il lit le **corps** des seules issues nommees (une lecture ciblee, une
  requete par lot) ;
- il lit le **fil complet** de l'issue, par l'organe REST `gh_snapshot`
  (pagination complete) -- jamais la fenetre des 12 derniers commentaires de
  la lecture groupee, qui peut cacher le marqueur qui ecarte un grain
  (constat de #27179) ;
- il rejoue les **neuf regles d'ecart** de `tapis_rapide.etats` sur ce grain
  qualifie -- la voie legere ne redecide pas, elle alimente la meme decision ;
- il qualifie par **VAGUES** : les ecarts peuvent vider la premiere vague, et
  servir 0 grain alors que le pool en contient serait un echec de methode
  (mesure du 2026-11-18 : les 9 premiers candidats etaient tous ecartes).
"""
from __future__ import annotations

from datetime import datetime

from coordination import gh_bulk, gh_issues, gh_snapshot, tapis_rapide
from coordination.tapis_marqueurs import _iso

#: Les champs de la lecture du CORPS seul (le fil vient d'un autre organe).
#: L'accolade de fermeture du jeu de selection est ajoutee par l'appelant :
#: ce bloc ne se ferme que lui-meme.
CHAMP_CORPS = """number title body createdAt updatedAt labels(first:20){nodes{name}}"""


def lire_corps(run=gh_bulk.run_defaut, depot: str = gh_bulk.DEPOT_GH,
               numeros: list[int] | None = None) -> dict[int, dict]:
    """Le CORPS des issues nommees, sans leurs commentaires.

    Une lecture groupee, ciblee : elle ne porte que sur les candidats servis.
    Le fil complet est une autre lecture, par l'organe REST `gh_snapshot`.
    """
    return gh_issues.lire_champs(run, depot, numeros, CHAMP_CORPS, "corps")


def lire_fil_complet(numero: int, repo: str = gh_bulk.DEPOT_GH) -> list[dict]:
    """Tous les commentaires de l'issue, dans la forme des marqueurs.

    L'organe `gh_snapshot` pagine en REST : c'est le **fil complet**, pas la
    fenetre des 12 derniers commentaires de la lecture groupee.
    """
    return [{"created_at": c.get("createdAt") or "",
             "author": (c.get("author") or {}).get("login") or "",
             "body": c.get("body") or ""}
            for c in gh_snapshot.fetch_issue_comments(repo, numero)]


def qualifier(numero: int, corps: dict, fil: list[dict]) -> dict:
    """Une issue qualifiee, dans la forme que `tapis_rapide.etats` attend.

    Le corps vient de la lecture ciblee, le fil de la lecture complete : les
    deux sont lus pour ce grain-la, jamais pour le pool.
    """
    return {"number": numero, "title": corps.get("title") or "",
            "body": corps.get("body") or "",
            "created_at": corps.get("created_at") or "",
            "updated_at": corps.get("updated_at") or "",
            "labels": list(corps.get("labels") or []),
            "comments_total": len(fil), "comments": fil}


def qualifier_candidats(candidats: list[int], run=gh_bulk.run_defaut,
                        repo: str = gh_bulk.DEPOT_GH) -> tuple[list[dict], list[int]]:
    """Qualifie les candidats : corps (un appel groupe) puis fil complet.

    Rend `(issues qualifiees, echecs)`. Un fil illisible ne bloque pas le
    tirage : le grain est simply absent de la liste qualifiee (fail-OPEN).
    """
    if not candidats:
        return [], []
    corps = lire_corps(run, repo, candidats)
    issues, echecs = [], []
    for n in candidats:
        if n not in corps:
            echecs.append(n)
            continue
        try:
            fil = lire_fil_complet(n, repo)
        except Exception:  # noqa: BLE001 - un fil illisible ne bloque pas le tirage
            echecs.append(n)
            continue
        issues.append(qualifier(n, corps[n], fil))
    return issues, echecs


def qualifier_par_vagues(candidats: list[int], qual_max: int, grains: int,
                         lane: str, maintenant: datetime, jours: int,
                         prs: list[dict], citations: dict, run,
                         max_vagues: int) -> tuple:
    """Qualifie les candidats par VAGUES, jusqu'a remplir la file.

    Mesure du 2026-11-18 : la rotation propose les 9 premiers candidats, et
    les neuf ecarts les ecartent TOUS (lignes RELACHEE, PLAFOND, LIVREE, --
    lus sur le fil complet). Servir 0 grain alors que le pool en contient
    serait un echec de methode, pas un pool vide : la qualification ouvre
    donc la VAGUE suivante tant que la file n'est pas pleine, dans la limite
    de `max_vagues`.

    Rend `(qualifies, issues, echecs, lec, servables)`.
    """
    issues: list[dict] = []
    echecs: list[int] = []
    qualifies: list = []
    servables: list = []
    lec = None
    for vague in range(max_vagues):
        tranche = candidats[vague * qual_max:(vague + 1) * qual_max]
        if not tranche:
            break
        lus, rates = qualifier_candidats(tranche, run)
        issues += lus
        echecs += rates
        lec = gh_bulk.Lecture(issues=issues, prs=prs, citations=citations,
                               lu_a=_iso(maintenant), secondes=0.0,
                               appels=len(issues) + 2)
        qualifies = tapis_rapide.etats(lec, lane, maintenant, jours)
        servables = [e for e in qualifies if e.ecart is None]
        if len(servables) >= grains:
            break
    return qualifies, issues, echecs, lec, servables
