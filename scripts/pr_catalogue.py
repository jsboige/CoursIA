#!/usr/bin/env python3
"""La PR du CATALOGUE au long cours n'occupe aucun chemin.

`.github/workflows/catalog-cron.yml` rafraichit chaque jour la branche
`chore/catalog-refresh-pending` et ouvre (ou met a jour) une PR qui porte
les catalogues generes ET les README de **toutes** les series. Ce n'est pas
une intention d'editer d'une lane : c'est une vue materialisee du catalogue,
regeneree par l'automatisation.

Sans exemption, cette PR compte comme occupant sur chaque serie. Mesure du
24/11 sur `MyIA.AI.Notebooks/GenAI/**/README.md` : elle sortait parmi les
collisions du mode `--paths` de `scripts/check_lane_claim.py` -- avec huit
autres PRs de travail reel -- et aucune lane ne pouvait plus reclamer une
serie.

L'exemption porte sur la **BRANCHE**, pas sur le numero de PR : le numero
change a chaque reouverture (la PR est fermee quand le catalogue ne derive
plus, `catalog-pr-close.yml`), la branche non. La branche est mono-ecrivaine
et propriete du workflow : c'est une branche de PR a lane unique au sens de
`git-workflow.md`, donc force-pushable par son seul proprietaire.

Ce que l'exemption ne touche pas : le claim d'issue (`[CLAIMED]`) et la
collision d'une PR de **travail reel** restent entiers. Seule la PR
regeneree cesse d'occuper un chemin.
"""

#: La branche du catalogue, propriete du workflow `catalog-cron.yml`.
BRANCHE_CATALOGUE = "chore/catalog-refresh-pending"


def est_catalogue(pr: dict) -> bool:
    """Cette PR est-elle la PR du catalogue au long cours ?

    Elle n'occupe aucun chemin : c'est une vue regeneree, pas un travail de
    lane.
    """
    return (pr.get("headRefName") or "") == BRANCHE_CATALOGUE
