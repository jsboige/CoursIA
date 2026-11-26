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

Designation des carnets
-----------------------

Un carnet se designe par son **index de serie** (``TV-00a``) et sa **famille
de noyau** (python, csharp), jamais par son nom de fichier : un carnet Python
et son pendant C# portent le meme index, et le suffixe de noyau peut changer
sans que le carnet designe change (chantier A de #16231). Le fichier se choisit
sur ``metadata.kernelspec.name``, lu sur chaque candidat -- fail-closed.

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

__all__ = ["SERIE", "DEPOT", "FAMILLES", "code_loc", "carnet", "carnet_index"]

#: familles de noyaux de la serie, reconnues sur ``metadata.kernelspec.name``.
#: Criteres volontairement larges : ils couvrent les variantes enumerees par le
#: canon du depot (``PYTHON_KERNELS`` / ``CSHARP_KERNELS`` de
#: ``scripts/notebook_tools/rename_notebooks.py``) sans en importer le module.
FAMILLES = {
    "python": lambda noyau: noyau.startswith("python"),
    "csharp": lambda noyau: "csharp" in noyau,
}


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


def _noyau(chemin) -> str:
    """Noyau declare par un carnet (``metadata.kernelspec.name``), ou ``""``."""
    carnet_json = json.loads(Path(chemin).read_text(encoding="utf-8"))
    return str(carnet_json.get("metadata", {}).get("kernelspec", {}).get("name", ""))


def _chemin_index(index, famille="python", base=None):
    """Fichier du carnet d'``index`` dans la ``famille`` de noyaux.

    Les candidats sont les ``<index>-*.ipynb`` du repertoire (les sorties
    ``*_output.ipynb`` exclues), filtres sur ``metadata.kernelspec.name``.
    Fail-closed : aucun candidat, ou plusieurs, et il leve en nommant ce qu'il
    a trouve -- jamais un choix silencieux entre deux carnets.
    """
    if famille not in FAMILLES:
        raise ValueError(
            f"famille de noyau inconnue : {famille!r} (connues : {sorted(FAMILLES)})")
    racine = Path(base) if base is not None else SERIE
    candidats = sorted(p for p in racine.glob(f"{index}-*.ipynb")
                       if not p.name.endswith("_output.ipynb"))
    retenus = [p for p in candidats if FAMILLES[famille](_noyau(p))]
    if not retenus:
        vus = ", ".join(f"{p.name} (noyau {_noyau(p) or 'absent'})" for p in candidats)
        raise FileNotFoundError(
            f"aucun carnet {index} de la famille {famille!r} sous {racine} ; "
            f"candidats : {vus or 'aucun'}")
    if len(retenus) > 1:
        raise RuntimeError(
            f"plusieurs carnets {index} de la famille {famille!r} sous {racine} : "
            + ", ".join(p.name for p in retenus))
    return retenus[0]


def carnet_index(index, famille="python", base=None) -> int:
    """Volume de code du carnet d'``index`` (``TV-00a``) dans la ``famille``.

    Le carnet est designe par son index de serie et sa famille de noyau, jamais
    par son nom de fichier : renommer un carnet (suffixe ``-Python``,
    ``-CSharp``) ne change pas la designation, et un carnet Python et son
    pendant C# restent deux carnets distincts du meme index.

    ``base`` par defaut : le repertoire de la serie.
    """
    return code_loc(_chemin_index(index, famille, base))
