#!/usr/bin/env python3
"""La CLE DE SERVICE d'un grain : la date de la derniere PR qui le COUVRE.

Mandat du coordinateur (19/11/2026, DM `20261119-picker-date-pr-parent`) :
« Remplacer poids/bonus/seances par une voix par issue, ordre de la derniere PR
dont le diff couvre le grain, departage uniforme a egalite ; sans PR,
vieillissement depuis la creation (pas d'anciennete heritee). Une PR enfant
remet aussi le hub en queue, pas les freres ; pas de nouveau service sur
correction de PR existante. »

Trois regles, et rien d'autre :

1. **Une voix par issue** : la cle est UNE date par grain. Ni bonus d'age, ni
   bonus de consolidation, ni nombre de visites n'ordonnent le tirage.
2. **La cle est la derniere PR candidate sur le grain** : le lien se lit dans
   le **corps** de la PR, en forme **canonique** (`See #N`, `Part of #N`,
   `Closes #N`, `Fix(...#N)`...). Une PR qui **mentionne** l'issue en prose ne
   la candidats pas. Arbitrage du 19/11 17:14Z : « ni une mention libre ni
   See/Part of seuls ne prouvent un service. Utiliser les liens comme
   **candidats** et confirmer le perimetre par le **diff**. » La preuve est
   donc l'organe du depot (`tapis_diff.verdict`), decide a la qualification :
   la cle classe sur le candidat, le verdict decide. Une livraison **confirmee
   par son diff** (`coordination.tapis_releve`) prime sur le candidat.
3. **Le hub suit son enfant** : la PR d'un enfant (E) remonte la cle du **hub**
   (H) -- et **seulement** lui : les **freres** (F) gardent leur propre cle.
   Un pli **neuf** n'herite pas de l'age du hub : sans PR, la cle est la
   **creation** du grain.

La date d'une PR est sa **creation** : une correction poussee dans une PR
existante ne la recree pas -- elle ne remet donc pas le grain en tete.

La DENSITE d'un hub (le nombre d'enfants reels) est une **mesure**, pas un
bonus : elle se lit, elle ne classe pas.

La detection des liens canoniques vit dans `coordination.tapis_canon`
(extrait le 19/11 pour tenir le plafond de lignes) ; la lecture qui date le
releve et la livraison confirmee, dans `coordination.tapis_releve`.
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from coordination.tapis_canon import des_prs_canoniques, est_canonique
from coordination.tapis_marqueurs import _dt, _iso
from coordination.tapis_releve import service_connue


def _note(service: dict[int, tuple[str, str]], numero: int, date: str | None,
          origine: str) -> None:
    """Garde la date de service la plus RECENTE d'un grain."""
    d = _dt(date)
    if d is None:
        return
    courant = service.get(int(numero))
    if courant is None or (_dt(courant[0]) or d) < d:
        service[int(numero)] = (_iso(d), origine)


def _chaine(par: dict[int, int | None], numero: int) -> list[int]:
    """Les ancetres d'un grain, du parent direct au plus haut hub."""
    chaine, vus, cur = [], {numero}, par.get(numero)
    while cur is not None and cur not in vus and len(chaine) < 8:
        chaine.append(cur)
        vus.add(cur)
        cur = par.get(cur)
    return chaine


def appliquer(etats_, cites_ouvertes: dict[int, list[dict]] | None = None,
              cites_merges: dict[int, list[dict]] | None = None) -> None:
    """Pose `cle_service` et `cle_origine` sur chaque etat.

    La cle est d'abord le **candidat** (une citation canonique dans le corps
    d'une PR), puis la **confirmation par le diff** (`tapis_releve`) : une
    livraison dont le diff couvre le perimetre declare prime sur le candidat,
    car c'est elle qui est **pertinente** (arbitrage du 19/11). Sans
    confirmation, le candidat reste : la cle candidate, sinon la creation.

    Les citations retenues sont les **canoniques** seules : une PR qui
    mentionne l'issue en prose ne la couvre pas. La date d'une PR est sa
    **creation** -- une correction d'une PR existante n'est pas un service
    nouveau.

    Le hub **suit** l'enfant : la cle d'un grain remonte a ses ancetres, et
    **seulement** a eux -- les freres, eux, gardent leur propre cle.
    """
    service: dict[int, tuple[str, str]] = {}
    for n, lst in (cites_merges or {}).items():
        for c in lst:
            if c.get("canonique"):
                _note(service, n, c.get("date"), "commit " + str(c.get("sha") or "")[:8])
    for n, lst in (cites_ouvertes or {}).items():
        for c in lst:
            if c.get("canonique"):
                _note(service, n, c.get("date"), "PR #" + str(c.get("pr") or ""))

    par = {e.numero: e.parent for e in etats_}
    numeros = sorted((e.numero for e in etats_),
                      key=lambda n: -len(_chaine(par, n)))

    def _propager(source):
        propage = dict(source)
        for numero in numeros:
            s = propage.get(numero)
            if not s:
                continue
            for ancetre in _chaine(par, numero):
                _note(propage, ancetre, s[0], s[1] + " (enfant)")
        return propage

    candidats = _propager(service)
    confirmes = _propager(service_connue())
    final = dict(candidats)
    final.update(confirmes)
    for e in etats_:
        s = final.get(e.numero)
        e.cle_service = s[0] if s else None
        e.cle_origine = s[1] if s else ""


def densites(etats_) -> dict[int, int]:
    """Le nombre d'enfants REELS d'un grain : une mesure, jamais un bonus.

    Elle se lit au moment de la visite du hub ; elle ne classe rien et ne
    declenche aucune creation de ticket.
    """
    d: dict[int, int] = {}
    for e in etats_:
        if e.parent:
            d[e.parent] = d.get(e.parent, 0) + 1
    return d
