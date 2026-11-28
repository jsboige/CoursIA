#!/usr/bin/env python3
"""Les CAUSES NOMMEES du repli : pourquoi le tirage a declenche le repli.

Dispatch `c0035b` (24/11) : le repli du 24/11 a rendu `voie: repli` et
`selection_s: 0.0` **sans une seule raison** dans le JSON -- un tirage
degrade qu'on ne peut pas expliquer. Ce module porte les deux causes
possibles, chacune avec son code et son motif lisible.

Les builders sont ici, et non dans l'appelant : le repli (`tapis_repli`)
**publie** la cause, l'appelant (`tapis_leger`) la **declenche** -- un seul
endroit fait le lien entre l'evenement et sa cause, donc une cause
nouvelle ne peut pas en oublier une.
"""
from __future__ import annotations


def lecture_incomplete(exc) -> dict:
    """La cause : la lecture de selection a echoue.

    `exc` est l'exception `gh_bulk.LectureIncomplete` : elle porte la
    lecture fautive, la page, et le motif de l'echec.
    """
    return {"code": "lecture-incomplete", "lecture": exc.lecture,
            "page": exc.page, "motif": exc.cause}


def cap_livraisons(fenetre_j: int) -> dict:
    """La cause : le cap de livraisons a vide la file de grains.

    Le cap de livraisons EPIC (#21067) est fail-OPEN : s'il vide la file,
    le repli chronologique rend la main (I2). Le repli doit alors dire
    que c'est le cap qui a vide la file, et non la lecture.
    """
    return {"code": "cap-livraisons",
            "motif": "le cap de livraisons a vide la file de grains",
            "fenetre_j": fenetre_j}


def qualification_echec(motif: str) -> dict:
    """La cause : la qualification de la fenetre servie a echoue.

    La qualification lit le fil complet de chaque grain ; si elle echoue, le
    repli chronologique rend la main. Le repli doit alors dire que c'est la
    qualification qui a echoue, et non la lecture de selection.
    """
    return {"code": "qualification-echec",
            "motif": "la qualification de la fenetre servie a echoue",
            "detail": motif}


def file_vide(motif: str) -> dict:
    """La cause : la file confirmee est vide -- aucun grain ne passe.

    La qualification a refuse tous les grains servis : le repli rend la main
    sur le cache local, qui porte des candidats non confirmes.
    """
    return {"code": "file-confirmee-vide",
            "motif": "aucun grain confirme par la qualification",
            "detail": motif}
