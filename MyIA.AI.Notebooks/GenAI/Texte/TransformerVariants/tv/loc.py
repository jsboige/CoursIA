"""tv.loc -- mesure du volume de code d'un carnet voisin, a l'execution.

Les tables comparatives de TV-01 et TV-02 publient le volume de code des
carnets voisins. Ces valeurs etaient **figees dans des cellules de code** :
chaque nombre derivait des que le carnet voisin evoluait, et le carnet ne
pouvait pas se voir deriver lui-meme -- sa propre valeur etait un litteral en
dur, la ou la colonne d'en face etait mesuree a l'execution.

Cet organe supprime la classe de defaut : la valeur est **lue sur le disque au
moment de l'execution**, donc elle decrit le carnet reellement execute (le
fichier d'entree du notebook, dont les cellules de code sont celles que le
kernel a interpreteres).

Convention de comptage -- celle qu'enonce la table elle-meme : lignes de
cellules de code, non vides, ne commencant pas par ``#``.

Origine
-------

Issue **#24421** (campagne d'audit #17073, partition GenAI #19451) : les
constantes LOC des carnets voisins etaient figees en dur et derivaient
(383 -> 388, 194 -> 200, 431 -> 436).

Voit aussi
----------

- TV-01 : ``TV-01-Attention-Variants-SOTA.ipynb`` (table « bloc A vs bloc B »).
- TV-02 : ``TV-02-MoE-SOTA.ipynb`` (table « 3.4c from scratch vs industrie »).
"""
from __future__ import annotations

import json
from pathlib import Path

#: repertoire de la serie (le parent du package ``tv``)
SERIE = Path(__file__).resolve().parent.parent

#: racine du depot (le package ``tv`` vit dans MyIA.AI.Notebooks/GenAI/Texte/...)
DEPOT = SERIE.parents[3]

__all__ = ["SERIE", "DEPOT", "code_loc", "carnet"]


def code_loc(chemin) -> int:
    """Nombre de lignes de code d'un carnet, selon la convention de la serie.

    Lignes de cellules de code, non vides, ne commencant pas par ``#``.
    """
    carnet_json = json.loads(Path(chemin).read_text(encoding="utf-8"))
    total = 0
    for cellule in carnet_json.get("cells", []):
        if cellule.get("cell_type") != "code":
            continue
        for ligne in "".join(cellule.get("source", [])).splitlines():
            s = ligne.strip()
            if s and not s.startswith("#"):
                total += 1
    return total


def carnet(nom, base=None) -> int:
    """Volume de code du carnet ``nom``, resolu sous ``base``.

    ``base`` par defaut : le repertoire de la serie. Un chemin relatif au
    depot s'ecrit avec ``base=DEPOT``.
    """
    racine = Path(base) if base is not None else SERIE
    chemin = racine / nom
    if not chemin.exists():
        raise FileNotFoundError(
            f"carnet introuvable pour la mesure de volume de code : {chemin}")
    return code_loc(chemin)
