#!/usr/bin/env python3
"""L'ANCRE de la rotation : l'etat PERSISTANT du dernier numero qualifie.

Une rotation qui avance par POSITION saute des numeros des que le pool
change (une cloture, une arrivee) -- temoin mesure le 19/11 (peer
ai-01:CoursIA) : #3 ouverte, jamais visitee apres quatre tranches. L'ancre
porte le **numero** du dernier grain qualifie.

**Le curseur n'avance que sur un verdict TERMINAL** (peer, 19/11) : le
tirage PROPOSE (`proposer`), la qualification DECIDE (`avancer`). Un tirage
sans action ne la deplace pas.

**Le curseur ne se fige pas sur un INCONNU** (contre-exemple execute le
19/11) : une lecture impossible (`FIL_ILLISIBLE`, `MUR_EPUISE`, `ECHEANCE`,
`ABSENT`) ne DECIDE pas le grain -- elle ne doit pas non plus RETIRER la
couverture des autres : ces numeros sont PARKES (`inconnus`), ils ne
bloquent pas le curseur et reviennent au tour suivant.

**Un tour qui boucle est un tour de plus, pas une fin** : quand la
selection revient en deca du curseur (le pool a ete couvert), le curseur
recommence au plus petit numero et le compteur `tour` s'incremente.

**La tranche PRIMAIRE et la REPRISE sont deux choses distinctes** (19/11,
DM du coordinateur) : les confondre figeait la rotation. La primaire porte
le curseur (son rebouclage ouvre un tour de plus) ; la reprise -- les
illisibles parkes -- revient au service SANS prendre sa place.

L'arithmetique de la selection vit dans `coordination.tapis_tranche`, la
persistance dans `coordination.tapis_etat`.
"""
from __future__ import annotations

from coordination import tapis_etat, tapis_retry
from coordination.tapis_etat import ancre_de, inconnus_de, lire, tour_de  # noqa: F401
from coordination.tapis_tranche import membres, position, tranche  # noqa: F401

ENV_ETAT = tapis_etat.ENV_ETAT
CLASSES = tapis_etat.CLASSES


def ecrire(lane: str, etat: dict) -> object:
    """Persiste l'etat de l'ancre (une ecriture atomique)."""
    return tapis_etat.ecrire(lane, etat)


def boucle(proposes: list[int], ancre: int | None) -> bool:
    """Le pool a ete couvert : la selection revient en deca du curseur.

    Une tranche entierement composee de numeros inferieurs ou egaux au
    curseur est un NOUVEAU tour, pas un retour en arriere : sans cette
    distinction, le curseur se fige au plus grand numero du pool et la
    rotation ressert la meme tranche (contre-exemple du 19/11 : pool
    1..6, taille 2 -- apres le tour complet, la tranche [1, 2] revenait).
    """
    if ancre is None or not proposes:
        return False
    return all(n <= ancre for n in proposes)


def proposer(lane: str, classe: str, primaires: list[int],
             reprises: list[int] | None = None) -> dict:
    """Enregistre les numeros PROPOSES par le tirage, sans bouger l'ancre.

    `primaires` est la tranche **primaire** (celle que le curseur sert) ;
    `reprises` sont les illisibles parkes qui reviennent au service. Le
    rebouclage est deduit de la primaire SEULE : la mesure du 19/11 a
    montre qu'une primaire entierement illisible etait filtree AVANT le
    rebouclage, si bien que le tour ne s'ouvrait plus et que la meme
    tranche revenait indefiniment (#3, #4, #5, #6 n'etaient plus servis).

    Le tirage **selectionne** ; il ne qualifie pas : un tirage sans action
    laisse le curseur en place.
    """
    etat = lire(lane)
    if boucle(list(primaires), etat[classe]["ancre"]):
        etat[classe]["tour"] = etat[classe].get("tour", 0) + 1
        etat[classe]["ancre"] = 0
        etat[classe]["attente"] = {}
    att = etat[classe]["attente"]
    for n in list(primaires) + list(reprises or []):
        att.setdefault(n, False)
    etat[classe]["primaire"] = sorted(set(primaires))
    ecrire(lane, etat)
    return etat


def avancer(lane: str, terminaux: set[int], inconnus: dict | None = None) -> dict:
    """Fait avancer le curseur sur les verdicts TERMINAUX connus.

    Le curseur ne passe jamais un numero dont le verdict n'est pas connu :
    il s'arrete au premier numero en attente. Un lot PARTIEL (une lecture
    en echec) le laisse donc en place.

    Un numero **inconnu** (lecture impossible) ne fige pas le curseur : il
    est PARKE, il ne sera donc ni acquitte ni perdu -- il revient au tour
    suivant. La couverture des autres numeros n'est jamais retiree par
    l'echec d'une lecture.

    Le balayage ne porte que sur la tranche **courante** (`attente`) : les
    inconnus des tours anterieurs sont dans la file de reprise, ils ne
    doivent pas faire sauter le curseur par-dessus des numeros qui n'ont
    pas ete servis (19/11).
    """
    etat = lire(lane)
    for c in CLASSES:
        att = etat[c]["attente"]
        inc = etat[c]["inconnus"]
        for n in terminaux:
            if n in att:
                att[n] = True
            inc.pop(n, None)
        for n, info in (inconnus or {}).items():
            if n in att:
                tapis_retry.parquer(inc, n, info)
        ancre = etat[c]["ancre"]
        # Le balayage porte sur la tranche **PRIMAIRE** du tour courant : la
        # REPRISE (les illisibles parkes) revient au service SANS prendre la
        # place de la primaire -- balayer les deux ensemble faisait monter le
        # curseur jusqu'au dernier numero repris, et la couverture du pool
        # s'arretait (mesure du 19/11 : #3 et #4 jamais servis).
        primaire = etat[c].get("primaire") or []
        cible = sorted(primaire) or sorted(att)
        for n in cible:
            if ancre is not None and n <= ancre:
                continue
            if n in inc:
                ancre = n
                continue
            if not att.get(n):
                break
            ancre = n
        etat[c]["ancre"] = ancre
        etat[c]["attente"] = {n: b for n, b in att.items()
                              if ancre is None or n > ancre}
    ecrire(lane, etat)
    return etat
