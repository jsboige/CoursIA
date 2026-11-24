#!/usr/bin/env python3
"""L'ANCRE de la rotation : l'etat PERSISTANT du dernier numero qualifie.

Une rotation qui avance par POSITION saute des numeros des que le pool
change (une cloture, une arrivee) -- temoin mesure le 19/11 (peer
ai-01:CoursIA) : #3 ouverte, jamais visitee apres quatre tranches. L'ancre
porte le **numero** du dernier grain qualifie.

**Le curseur n'avance que sur un verdict TERMINAL** (peer, 19/11) : le
tirage PROPOSE, la qualification DECIDE.

**Le curseur ne se fige pas sur un INCONNU** (contre-exemple du 19/11) :
une lecture impossible ne DECIDE pas le grain : ces numeros sont PARKES.

**Un tour qui boucle est un tour de plus, pas une fin** : le curseur
recommence au plus petit numero, et le compteur `tour` s'incremente.

**La tranche PRIMAIRE et la REPRISE sont deux choses distinctes** (19/11, DM
du coordinateur) : les confondre figeait la rotation. La primaire porte le
curseur ; la reprise des illisibles parkes revient au service SANS la place.


L'arithmetique de la selection vit dans `coordination.tapis_tranche`, la
persistance dans `coordination.tapis_etat`.
"""
from __future__ import annotations

from coordination import tapis_avance, tapis_etat, tapis_retry
from coordination.tapis_non_tente import NON_TENTE
from coordination.tapis_etat import (ancre_de, inconnus_de, lire,  # noqa: F401
                                    phase_de, tour_de)
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
             reprises: list[int] | None = None, reboucle: bool = True,
             reinit: bool = False) -> dict:
    """Enregistre les numeros PROPOSES par le tirage, sans bouger l'ancre.

    `primaires` est la tranche **primaire** (celle que le curseur sert) ;
    `reprises` sont les illisibles parkes qui reviennent au service. Le
    rebouclage est deduit de la primaire SEULE : la mesure du 19/11 a
    montre qu'une primaire entierement illisible etait filtree AVANT le
    rebouclage, si bien que le tour ne s'ouvrait plus et que la meme
    tranche revenait indefiniment (#3, #4, #5, #6 n'etaient plus servis).

    Le tirage **selectionne** ; il ne qualifie pas : un tirage sans action
    laisse le curseur en place.

    `reboucle=False` : pas de rebouclage par NUMERO (la selection par age
    ne se sert pas des numeros au-dessus de l'ancre). `reinit=True` : le
    tour est couvert -- la file d'attente est rendue, le tour recommence.
    """
    etat = lire(lane)
    if reinit:
        etat[classe]["attente"] = {}
    if reboucle and boucle(list(primaires), etat[classe]["ancre"]):
        etat[classe]["tour"] = etat[classe].get("tour", 0) + 1
        etat[classe]["ancre"] = 0
        etat[classe]["attente"] = {}
    att = etat[classe]["attente"]
    for n in list(primaires) + list(reprises or []):
        att.setdefault(n, False)
    etat[classe]["primaire"] = sorted(set(primaires))
    etat[classe]["phase"] = etat[classe].get("phase", 0) + 1
    ecrire(lane, etat)
    return etat


def avancer(lane: str, terminaux: set[int], inconnus: dict | None = None,
            lot: set[int] | None = None) -> dict:
    """Fait avancer le curseur sur les verdicts TERMINAUX connus.

    Le curseur ne passe jamais un numero **refuse** sans le parker ; un
    grain PROPOSE mais jamais qualifie (NON TENTE) ne le bloque pas non
    plus : il est parke, et le curseur continue (`tapis_non_tente`).

    `lot` est le lot EFFECTIVEMENT qualifie. Le curseur ne passe que sur
    les numeros que le LOT a pris en charge : une qualification porte sur
    un numero qui n'appartient pas a la tranche ne fait pas avancer l'ancre
    des primaires pendantes (review du 19/11). Sans lot, l'avance n'est pas
    bornee. Le balayage lui-meme vit dans `coordination.tapis_avance`.

    Un numero **inconnu** (lecture impossible) ne fige pas le curseur : il
    est PARKE, il revient au tour suivant, et la couverture des autres
    numeros n'est jamais retiree par l'echec d'une lecture.
    """
    etat = lire(lane)
    couvert = set(lot) if lot is not None else None
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
        # REPRISE revient au service SANS prendre la place de la primaire.
        primaire = etat[c].get("primaire") or []
        cible = sorted(primaire) or sorted(att)
        # L'avance est BORNEE au lot : le curseur ne passe que sur les
        # numeros que le lot a reellement pris en charge (revue du 19/11).
        ancre = tapis_avance.avancer(cible, ancre, couvert, att, inc)
        etat[c]["ancre"] = ancre
        # Une entree EN ATTENTE n'est pas retiree par le curseur : elle attend
        # son verdict, et c'est elle qui exclut la selection par age (mandat du
        # 22/11). Un grain REFUSE est une DECISION : il sort de la file ; un
        # grain PARKE NON_TENTE reste en attente ET dans la file de reprise.
        etat[c]["attente"] = {
            n: b for n, b in att.items()
            if ancre is None or n > ancre
            or (not b and (n not in inc or inc[n].get("code") == NON_TENTE))}
    ecrire(lane, etat)
    return etat
