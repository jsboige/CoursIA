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

L'exemption identifie la branche **du depot amont**, pas seulement son nom
(reserve du 26/11) : une branche `chore/catalog-refresh-pending` dans un
fork est une PR de travail reel, pas la vue du catalogue. Une PR dont la
provenance n'est pas lue n'est pas exemptee non plus (fail-CLOSED) : sans
depot de tete, rien ne prouve qu'elle vienne du workflow.
"""

#: La branche du catalogue, propriete du workflow `catalog-cron.yml`.
BRANCHE_CATALOGUE = "chore/catalog-refresh-pending"

#: Le depot amont, seul proprietaire du workflow `catalog-cron.yml`.
DEPOT_CATALOGUE = "jsboige/CoursIA"


def est_catalogue(pr: dict) -> bool:
    """Cette PR est-elle la PR du catalogue au long cours ?

    Elle n'occupe aucun chemin : c'est une vue regeneree, pas un travail de
    lane.

    Deux conditions, cumulees : la branche du catalogue **ET** un depot de
    tete qui est le depot amont. Une branche homonyme venue d'un fork est
    une PR de travail reel ; une provenance absente n'est pas une preuve
    (fail-CLOSED).
    """
    if (pr.get("headRefName") or "") != BRANCHE_CATALOGUE:
        return False
    depot = (pr.get("headRepository") or "").strip().casefold()
    return bool(depot) and depot == DEPOT_CATALOGUE.casefold()
