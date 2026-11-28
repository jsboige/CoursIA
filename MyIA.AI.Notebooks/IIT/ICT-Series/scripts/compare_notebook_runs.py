"""Comparer deux executions du meme carnet : les sorties sont-elles identiques ?

Origine : #22297 (ICT-40a non rejouable). Un carnet se dit deterministe quand
deux executions successives, dans deux processus distincts, produisent les
memes sorties. Ce module est l'organe de cette preuve : il compare cellule par
cellule deux carnets ecrits par papermill et rend un verdict.

Ce qui est compare, et ce qui ne l'est pas
------------------------------------------
- la **source** de chaque cellule : comparer seulement les sorties de deux
  executions d'un code qui a change ne prouverait rien ;
- les **sorties** : texte des flux, puis ``text/plain`` et ``text/html`` des
  resultats, contenu des images ;
- ``execution_count`` : il temoigne que chaque cellule a ete executee, une
  fois, dans l'ordre.

Le seul ecart tolere est ``metadata.papermill`` (horodatages, chemins, durees) :
ce n'est pas une sortie de cellule.

Pourquoi les blocs ``stream`` consecutifs sont concatenes
---------------------------------------------------------
IPython flushe stdout par blocs : le nombre de blocs ``stream`` d'une cellule
depend du minutage des ecritures, pas du calcul. Une execution produit un
bloc, l'autre trois, pour le meme texte. Compares bloc a bloc, deux executions
identiques se lisent donc « divergentes » -- un faux positif, mesure sur
ICT-40a le 28/11. On concatene les blocs **consecutifs** seulement : un
resultat intercale entre deux flux garde l'ordre des sorties.

Module **pur** (json, argparse) : aucune dependance lourde, testable en CI sans
GPU -- meme choix que ``ict25_records.py``.

Usage
-----
    python compare_notebook_runs.py run1.ipynb run2.ipynb [--code-only]

``--code-only`` restreint la comparaison aux cellules de code : le markdown
n'est pas une sortie, et un realignement de prose ne doit pas faire lire
« divergent » une computation identique.

Code de sortie : 0 si identique, 1 si divergent, 2 si un fichier est illisible.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

Sorties = list[tuple[str, str]]

#: nombre de caracteres de sortie affiches par cote pour un ecart
APERCU = 300


def _texte(valeur: Any) -> str:
    """Une source ou une sortie nbformat : chaine ou liste de lignes."""
    if isinstance(valeur, str):
        return valeur
    return "".join(valeur)


def sortie_cellule(cellule: dict[str, Any]) -> Sorties:
    """Sorties canoniques d'une cellule : le contenu, pas le decoupage."""
    canon: Sorties = []
    for sortie in cellule.get("outputs") or []:
        if sortie.get("output_type") == "stream":
            texte = _texte(sortie.get("text") or [])
            if canon and canon[-1][0] == "stream":
                canon[-1] = ("stream", canon[-1][1] + texte)
            else:
                canon.append(("stream", texte))
            continue
        data = sortie.get("data") or {}
        if "text/plain" in data:
            canon.append(("text/plain", _texte(data["text/plain"])))
        elif "text/html" in data:
            canon.append(("text/html", _texte(data["text/html"])))
        elif "image/png" in data:
            canon.append(("image/png", _texte(data["image/png"])))
        else:
            canon.append((str(sortie.get("output_type")), json.dumps(
                {k: v for k, v in sortie.items() if k != "execution_count"},
                sort_keys=True, ensure_ascii=False)))
    return canon


def texte_sortie(cellule: dict[str, Any]) -> str:
    """Texte lisible d'une cellule, pour l'apercu d'un ecart."""
    morceaux = []
    for sortie in cellule.get("outputs") or []:
        if "text" in sortie:
            morceaux.append(_texte(sortie["text"]))
        data = sortie.get("data") or {}
        if "text/plain" in data:
            morceaux.append(_texte(data["text/plain"]))
    return "\n".join(morceaux)


def _en_erreur(cellule: dict[str, Any]) -> bool:
    return any(sortie.get("output_type") == "error"
               for sortie in cellule.get("outputs") or [])


@dataclass
class Ecart:
    """Une cellule dont les deux executions different."""

    index: int
    type_cellule: str
    meme_source: bool
    meme_sortie: bool
    meme_execution_count: bool
    texte_a: str
    texte_b: str


@dataclass
class Rapport:
    """Verdict de la comparaison de deux carnets executes."""

    nb_cellules: tuple[int, int]
    compares: int = 0
    identiques: int = 0
    ecarts: list[Ecart] = field(default_factory=list)
    cellules_en_erreur: list[int] = field(default_factory=list)

    @property
    def identite(self) -> bool:
        return self.nb_cellules[0] == self.nb_cellules[1] and not self.ecarts


def comparer(a: dict[str, Any], b: dict[str, Any],
             code_only: bool = False) -> Rapport:
    """Compare deux carnets cellule par cellule, en parallele d'index."""
    cellules_a = a.get("cells") or []
    cellules_b = b.get("cells") or []
    rapport = Rapport(nb_cellules=(len(cellules_a), len(cellules_b)))
    for i, (ca, cb) in enumerate(zip(cellules_a, cellules_b)):
        if _en_erreur(ca) or _en_erreur(cb):
            rapport.cellules_en_erreur.append(i)
        if code_only and ca.get("cell_type") != "code" \
                and cb.get("cell_type") != "code":
            continue
        rapport.compares += 1
        meme_source = ca.get("source") == cb.get("source")
        meme_sortie = sortie_cellule(ca) == sortie_cellule(cb)
        compte_a = ca.get("execution_count")
        compte_b = cb.get("execution_count")
        meme_execution_count = compte_a == compte_b
        if meme_source and meme_sortie and meme_execution_count:
            rapport.identiques += 1
        else:
            rapport.ecarts.append(Ecart(
                index=i,
                type_cellule=str(ca.get("cell_type")),
                meme_source=meme_source,
                meme_sortie=meme_sortie,
                meme_execution_count=meme_execution_count,
                texte_a=texte_sortie(ca),
                texte_b=texte_sortie(cb),
            ))
    return rapport


def decrire(rapport: Rapport, code_only: bool = False) -> str:
    """Rendu du rapport : les lignes lues par un reviewer, dans l'ordre."""
    n_a, n_b = rapport.nb_cellules
    lignes = [f"cellules : {n_a} vs {n_b}"]
    if rapport.nb_cellules[0] != rapport.nb_cellules[1]:
        lignes.append("VERDICT : DIVERGENT (nombre de cellules different)")
        return "\n".join(lignes)
    if code_only:
        lignes.append("comparaison restreinte aux cellules de code")
    lignes.append("cellules identiques (source + sorties + execution_count) : "
                  f"{rapport.identiques} / {rapport.compares}")
    for ecart in rapport.ecarts:
        lignes.append(
            f"--- cellule {ecart.index} ({ecart.type_cellule}) : "
            f"source={ecart.meme_source} sorties={ecart.meme_sortie} "
            f"exec_count={ecart.meme_execution_count}")
        if not ecart.meme_sortie:
            lignes.append(f"  A: {ecart.texte_a[:APERCU]!r}")
            lignes.append(f"  B: {ecart.texte_b[:APERCU]!r}")
    if rapport.cellules_en_erreur:
        lignes.append("cellules en erreur (identiques ou non) : "
                      f"{rapport.cellules_en_erreur}")
    verdict = "IDENTIQUE" if rapport.identite else "DIVERGENT"
    lignes.append("VERDICT : " + verdict)
    return "\n".join(lignes)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Comparer les sorties de deux executions du meme carnet.")
    parser.add_argument("run1", type=Path)
    parser.add_argument("run2", type=Path)
    parser.add_argument("--code-only", action="store_true",
                        help="ne comparer que les cellules de code")
    args = parser.parse_args(argv)
    carnets = []
    for chemin in (args.run1, args.run2):
        try:
            carnets.append(json.loads(chemin.read_text(encoding="utf-8")))
        except (OSError, ValueError) as exc:
            print(f"illisible : {chemin} ({exc})")
            return 2
    rapport = comparer(carnets[0], carnets[1], code_only=args.code_only)
    print(decrire(rapport, code_only=args.code_only))
    return 0 if rapport.identite else 1


if __name__ == "__main__":
    sys.exit(main())
