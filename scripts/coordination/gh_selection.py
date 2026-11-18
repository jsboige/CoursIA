#!/usr/bin/env python3
"""Le chemin de SELECTION leger : la rotation de toutes les issues ouvertes.

Le tapis classe des CENTAINES d'issues pour en servir quelques-unes a chaque
lane. Ce classement n'a besoin ni du corps des issues, ni de leurs
commentaires, ni des PRs ouvertes : il lui faut des **metadonnees** (numero,
titre, date de creation, labels) et le signal des **travail reel** (les
commits de `origin/main` qui citent l'issue).

La lecture lourde ne sert plus qu'a la **qualification** d'un grain pris en
charge : c'est `gh_bulk.lire_issues`, qui lit le corps et les commentaires des
seules issues nommees.

Deux garanties :

- la **pagination est complete** : une liste partielle n'est jamais servie ;
- le **budget global** est une borne de duree : son depassement leve
  `LectureIncomplete`, et l'appelant doit le dire (jamais de liste a moitie).

`run` est injecte comme dans `gh_bulk` : aucun test ne touche le reseau.
"""
from __future__ import annotations

import json
import time

from coordination import gh_bulk
from coordination.gh_bulk import TAILLES_PAGE, TIMEOUT_S, LectureIncomplete, Run

MUR_GLOBAL_S = 60  # budget global d'une lecture de selection, en duree
TAILLE_PAGE = 50

QUERY_METADONNEES = """query($owner:String!,$name:String!,$n:Int!,$after:String){
 repository(owner:$owner,name:$name){
  issues(states:OPEN,first:$n,after:$after,orderBy:{field:CREATED_AT,direction:ASC}){
   pageInfo{hasNextPage endCursor}
   nodes{number title createdAt updatedAt labels(first:20){nodes{name}}}}}}"""

QUALIFICATION_CHAMP = """number title body createdAt updatedAt labels(first:20){nodes{name}}
    comments(last:12){totalCount nodes{createdAt author{login} body}}}"""


def metadonnee(node: dict) -> dict:
    """Une issue en metadonnees : ni corps, ni commentaires, ni PRs."""
    return {"number": node["number"], "title": node.get("title") or "",
            "created_at": node.get("createdAt") or "",
            "updated_at": node.get("updatedAt") or "",
            "labels": [lab["name"] for lab in (node.get("labels") or {}).get("nodes") or []]}


def _page(run: Run, depot: str, after: str | None, page: int, budget: float) -> dict:
    """Une page de metadonnees ; rejeu a la taille suivante sur panne transitoire.

    Chaque appel recoit le temps restant : le budget global borne la DUREE de
    toute la lecture, pas celle d'un appel."""
    owner, name = depot.split("/")
    for taille in TAILLES_PAGE:
        if budget <= 1:
            raise LectureIncomplete("metadonnees_issues", page,
                                    "budget global de lecture epuise")
        argv = ["gh", "api", "graphql", "-f", f"query={QUERY_METADONNEES}",
                "-f", f"owner={owner}", "-f", f"name={name}", "-F", f"n={taille}"]
        if after:
            argv += ["-f", f"after={after}"]
        texte = gh_bulk._appel(run, argv, "metadonnees_issues", page,
                               timeout=max(1, int(min(TIMEOUT_S, budget))))
        if texte is None:
            continue
        try:
            return json.loads(texte)["data"]["repository"]["issues"]
        except (ValueError, KeyError, TypeError) as exc:
            raise LectureIncomplete("metadonnees_issues", page,
                                    f"reponse illisible : {exc}") from exc
    raise LectureIncomplete("metadonnees_issues", page,
                            f"502/504 ou timeout aux tailles {TAILLES_PAGE}")


def lire_metadonnees_issues(run: Run = gh_bulk.run_defaut, depot: str = gh_bulk.DEPOT_GH,
                            budget_s: float = MUR_GLOBAL_S) -> tuple[list[dict], float]:
    """Toutes les issues ouvertes, metadonnees seules, pagination complete.

    Rend la liste et la duree de la lecture (secondes) : la mesure froide et
    la mesure chaude se comparent sur ce meme chiffre."""
    issues: list[dict] = []
    apres, page = None, 1
    debut = time.monotonic()
    while True:
        reste = budget_s - (time.monotonic() - debut)
        data = _page(run, depot, apres, page, reste)
        issues.extend(metadonnee(node) for node in data["nodes"])
        if not data["pageInfo"]["hasNextPage"]:
            return issues, round(time.monotonic() - debut, 1)
        apres, page = data["pageInfo"]["endCursor"], page + 1


def qualifier(run: Run = gh_bulk.run_defaut, depot: str = gh_bulk.DEPOT_GH,
              numeros: list[int] | None = None) -> dict[int, dict]:
    """Le lecteur existant, CIBLE : corps et commentaires des issues nommees.

    C'est la qualification d'un grain pris en charge : la lecture lourde ne
    porte plus sur le pool entier, mais sur les seuls grains servis."""
    if not numeros:
        return {}
    owner, name = depot.split("/")
    lues: dict[int, dict] = {}
    for i in range(0, len(numeros), TAILLE_PAGE):
        tranche = numeros[i:i + TAILLE_PAGE]
        alias = " ".join(f"i{k}: issue(number:{n}){{{QUALIFICATION_CHAMP}}}"
                         for k, n in enumerate(tranche))
        query = (f"query($owner:String!,$name:String!){{repository(owner:$owner,"
                 f"name:$name){{{alias}}}}}")
        argv = ["gh", "api", "graphql", "-f", f"query={query}",
                "-f", f"owner={owner}", "-f", f"name={name}"]
        texte = gh_bulk._appel(run, argv, "qualification", tranche[0])
        if texte is None:
            raise LectureIncomplete("qualification", tranche[0], "appel indisponible")
        try:
            data = json.loads(texte)["data"]["repository"]
        except (ValueError, KeyError, TypeError) as exc:
            raise LectureIncomplete("qualification", tranche[0],
                                    f"reponse illisible : {exc}") from exc
        for k, n in enumerate(tranche):
            node = data.get(f"i{k}")
            if node:
                lues[n] = gh_bulk.issue(node)
    return lues
