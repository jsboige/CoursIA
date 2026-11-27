#!/usr/bin/env python3
"""Le RAPPORT du tirage universel : les grains, leur etat, l'action, la mesure.

Ce module est **extrait** de `coordination.tapis_universel` : il tient son
propre fichier, comme `tapis_leger_texte` pour `tapis_leger`, et le module
d'origine reste sous son plafond de lignes. `tapis_universel.rapport` reste
appelable (l'alias y garde les appelants intacts).

La **PROVENANCE** d'un grain dit d'ou vient l'action publique : un chemin, une
provenance, une action (reserve du coordinateur du 25/11 sur #28345).

| Provenance | Chemin | Ce que la lane a lu |
|---|---|---|
| `qualifie` | la voie leger | le FIL COMPLET, qualifie avant service |
| `metadonnees` | l'entree universelle | les metadonnees, les citations, les PRs -- **pas le fil** |
| `cache` | le repli chronologique | le CACHE local -- **jamais** le fil, ni le reseau |

Le mot « cache » ne qualifie que le REPLI : la lecture reseau de l'entree
universelle n'est pas un cache, et l'annoncer comme telle serait un motif
faux.
"""
from __future__ import annotations

from datetime import datetime

from coordination import tapis_equilibre, tapis_marqueurs
from coordination.tapis_rapide import Etat

#: Les trois provenances : une par chemin qui produit un grain servi.
QUALIFIE = "qualifie"
METADONNEES = "metadonnees"
CACHE = "cache"

PROVENANCES = frozenset({QUALIFIE, METADONNEES, CACHE})

_ACTIONS = {
    QUALIFIE: ("deja qualifie sur fil complet : le claimer (paths:) puis le servir "
               "-- requalifier si le fil bouge "
               "(scripts/coordination/tapis_prise_en_charge.py)"),
    METADONNEES: ("metadonnees seules, fil NON lu : lire le fil avant de claimer "
                  "(scripts/coordination/tapis_prise_en_charge.py) puis le servir "
                  "-- ne pas claimer sur les seules metadonnees"),
    CACHE: ("candidat du cache, fil NON lu : lire le fil avant de claimer "
            "(scripts/coordination/tapis_prise_en_charge.py) puis le servir "
            "-- ne pas claimer sur la seule lecture du cache"),
}

_BANDEAUX = {
    QUALIFIE: "\nGrains -- deja qualifies sur leur fil complet, "
              "a claimer puis servir :",
    METADONNEES: "\nGrains -- METADONNEES SEULES (fil NON lu) : "
                 "lire le fil avant de claimer, puis servir :",
    CACHE: "\nGrains -- CANDIDATS DU CACHE (fil NON lu) : "
           "lire le fil avant de claimer, puis servir :",
}


def provenance_de(valeur: str | bool) -> str:
    """La provenance explicite d'un grain servi.

    Un libelle de provenance, ou l'ancien booleen `fil_lu` (`True` = fil lu
    et qualifie, `False` = repli sur le cache). Une provenance inconnue ne
    se dit JAMAIS qualifiee : elle tombe sur « metadonnees seules »
    (fail-CLOSED).
    """
    if isinstance(valeur, bool):
        return QUALIFIE if valeur else CACHE
    return valeur if valeur in PROVENANCES else METADONNEES


def bandeau(provenance: str | bool) -> str:
    """La ligne d'entete de la sortie texte : elle nomme la provenance."""
    return _BANDEAUX[provenance_de(provenance)]


def action_de(e: Etat, lane: str, provenance: str | bool) -> str:
    """Ce que la lane doit faire de ce grain : le claimer, puis le servir.

    La qualification a deja ete jouee : la voie leger qualifie la fenetre
    servie sur son FIL COMPLET **avant** de la servir (dispatch `c0030` du
    coordinateur, 24/11). L'action de la lane est donc le CLAIM et le
    travail, pas une nouvelle qualification -- la re-decision reste possible
    (le fil bouge), l'organe est `scripts/coordination/tapis_prise_en_charge.py`.

    `provenance` dit ce que le chemin a reellement lu : le fil qualifie
    (`qualifie`), les seules metadonnees (`metadonnees`, entree universelle)
    ou le cache local (`cache`, repli chronologique). Un grain dont le fil
    n'a pas ete lu ne se claim pas sur la seule lecture qu'en a fait le
    chemin : son action impose la lecture du fil d'abord (reserve du
    coordinateur du 25/11 sur #28345).
    """
    base = _ACTIONS[provenance_de(provenance)]
    if e.consolidation:
        base += " -- issue de consolidation"
    return base


def bloc_qualification(qualif: dict | None = None) -> dict:
    """Le bloc `qualification` du rapport leger : ou, quand, comment.

    Il est ici, et pas dans `tapis_leger_rapport.py`, parce que ce module est
    a son plafond de lignes : un depassement se paie en extraction, jamais
    en relevant le plafond.
    """
    return {
        "organe": "scripts/coordination/tapis_prise_en_charge.py",
        "vagues": "scripts/coordination/tapis_vagues.py : la file se remplit",
        "quand": "avant le service, sur la fenetre servie",
        "ecarts": "les neuf regles se decident sur le fil complet",
        **(qualif or {}),
    }


def rapport(etats_: list[Etat], file: list[Etat], lane: str, maintenant: datetime,
            lecture: dict, ecartees: list[dict] | None = None,
            *, provenance: str | bool) -> dict:
    """Le rapport du tirage universel : les grains, leur etat, l'action, la mesure.

    Les exclusions en **donnees** sont publiees (`ecartees`), comme dans le
    tirage complet : une exclusion n'est jamais silencieuse. `ecartees` porte
    les issues ecartees (`tapis_labels.ecartees`) -- le `pool` reste le nombre
    d'issues ouvertes, ecartees comprises.

    `provenance` dit ce que le chemin a lu (fil qualifie, metadonnees seules,
    cache) : le rapport la publie, et l'action de chaque grain en decoule.
    `fil_lu` reste dans le rapport (vrai seulement pour la provenance
    `qualifie`) : les lecteurs de la voie leger le lisaient.

    `provenance` est **exige** (mot-cle) : aucun chemin ne sert un grain sans
    dire ce qu'il a reellement lu -- c'est la forme qui empeche le defaut
    du 25/11 (une entree qui lisait des metadonnees annoncait « deja
    qualifie sur fil complet »).
    """
    prov = provenance_de(provenance)
    conso = tapis_equilibre.familles_consolidation(etats_)
    return {
        "lane": lane, "maintenant": tapis_marqueurs._iso(maintenant),
        "lecture": lecture, "pool": len(etats_) + len(ecartees or []),
        "fil_lu": prov == QUALIFIE,
        "provenance": prov,
        "ecartees": {"LABEL": ecartees or []},
        "grains": [{"numero": e.numero, "titre": e.titre,
                    "visites": e.visites, "visites_total": e.visites_total,
                    "consolidation": e.consolidation,
                    "priorite": tapis_equilibre.raisons(e, conso, maintenant),
                    "action": action_de(e, lane, prov)} for e in file],
    }
