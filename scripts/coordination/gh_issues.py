#!/usr/bin/env python3
"""La lecture CIBLEE des issues nommees, aux champs demandes (#27225).

Une seule porte pour les lectures GraphQL d'un lot d'issues : la requete
`issue(number:N)` en alias, par lots de 50, sur le depot de `gh_bulk`. Deux
consommateurs, deux contenus demandes :

- `gh_selection.qualifier` : corps + les 12 derniers commentaires (la lecture
  groupee du pool, ciblee) ;
- `coordination.tapis_leger` : le **corps seul**, parce que le fil complet
  vient d'un autre organe (`gh_snapshot`, pagination REST).

Le module ne fait aucun choix : il rend les champs demandes, et leve
`LectureIncomplete` plutot que de rendre une liste a moitie.
"""
from __future__ import annotations

import json

from coordination import gh_bulk
from coordination.gh_bulk import LectureIncomplete, Run

TAILLE_LOT = 50


def lire_champs(run: Run = gh_bulk.run_defaut, depot: str = gh_bulk.DEPOT_GH,
                numeros: list[int] | None = None, champs: str = "",
                lecture: str = "issues") -> dict[int, dict]:
    """Les issues nommees, a plat, aux champs demandes.

    Rend `{numero: issue}`. Une issue absente de la reponse est absente du
    resultat : elle n'est pas devinee.
    """
    if not numeros:
        return {}
    owner, name = depot.split("/")
    lues: dict[int, dict] = {}
    for i in range(0, len(numeros), TAILLE_LOT):
        tranche = numeros[i:i + TAILLE_LOT]
        alias = " ".join(f"i{k}: issue(number:{n}){{{champs}}}" for k, n in enumerate(tranche))
        query = (f"query($owner:String!,$name:String!){{repository(owner:$owner,"
                 f"name:$name){{{alias}}}}}")
        argv = ["gh", "api", "graphql", "-f", f"query={query}",
                "-f", f"owner={owner}", "-f", f"name={name}"]
        texte = gh_bulk._appel(run, argv, lecture, tranche[0])
        if texte is None:
            raise LectureIncomplete(lecture, tranche[0], "appel indisponible")
        try:
            data = json.loads(texte)["data"]["repository"]
        except (ValueError, KeyError, TypeError) as exc:
            raise LectureIncomplete(lecture, tranche[0],
                                    f"reponse illisible : {exc}") from exc
        for k, n in enumerate(tranche):
            node = data.get(f"i{k}")
            if node:
                lues[n] = gh_bulk.issue(node)
    return lues
