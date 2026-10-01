#!/usr/bin/env python3
"""Organe de présence du dispositif d'auto-évaluation (#18207) -- advisory.

Ce qu'il compte
---------------
Le dispositif inséré dans les carnets pilotes de `02-ML-Cours` tient en trois
moments : **avant** (diagnostic de prérequis), **pendant** (vérification),
**après** (transfert). Cet organe compte, carnet par carnet, combien d'appels
`question(...)` portent chacun de ces moments.

Ce qu'il ne juge PAS
--------------------
Il ne dit rien de la qualité pédagogique d'une question : une question mal
posée, ou dont la bonne réponse est fausse, lui est invisible. Il mesure une
**présence**, pas une valeur -- d'où son statut advisory.

Usage
-----
    python scripts/notebook_tools/check_auto_evaluation_presence.py
    python scripts/notebook_tools/check_auto_evaluation_presence.py --json
    python scripts/notebook_tools/check_auto_evaluation_presence.py --strict
    python scripts/notebook_tools/check_auto_evaluation_presence.py --self-test

Sortie : `0` toujours, sauf `--strict` (1 si un carnet pilote ne porte pas les
trois moments) et `--self-test` (1 si la détection elle-même est cassée).
"""

import argparse
import ast
import io
import json
import os
import re
import sys

RACINE = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SERIE = os.path.join(RACINE, "MyIA.AI.Notebooks", "ML", "DataScienceWithAgents")
PILOTES = [
    "02-ML-Cours/2.1-Workflow-ML.ipynb",
    "02-ML-Cours/2.2-Descente-de-gradient.ipynb",
    "02-ML-Cours/2.3-Regression-lineaire-logistique.ipynb",
    "02-ML-Cours/2.4-Arbres-Forets-Ensembles.ipynb",
    "02-ML-Cours/2.5-Biais-Variance-CV-ROC.ipynb",
    "02-ML-Cours/2.6-Clustering-KMeans-PCA.ipynb",
]

MOMENTS = ("avant", "pendant", "apres")
IMPORT = re.compile(r"from\s+auto_evaluation\s+import\s+question")


def _source(cell):
    src = cell.get("source", "")
    return src if isinstance(src, str) else "".join(src)


def moments_appeles(texte):
    """Moments des appels `question(...)` d'une cellule, par analyse AST.

    Un motif textuel a ete essaye d'abord et s'est revele faux : `moment=` arrive
    apres l'explication, donc au-dela de toute fenetre fixe, et tous les appels
    tombaient dans le moment par defaut. L'AST ne fenetre rien.
    """
    try:
        arbre = ast.parse(texte)
    except SyntaxError:
        return []
    trouves = []
    for noeud in ast.walk(arbre):
        if (isinstance(noeud, ast.Call) and isinstance(noeud.func, ast.Name)
                and noeud.func.id == "question"):
            moment = "pendant"
            for mot in noeud.keywords:
                if mot.arg == "moment" and isinstance(mot.value, ast.Constant):
                    moment = mot.value.value
            trouves.append(moment)
    return trouves


def lire_carnet(chemin):
    """Rend {moment: nombre d'appels} et la présence de l'import du dispositif."""
    with io.open(chemin, encoding="utf-8") as f:
        carnet = json.load(f)
    comptes = {m: 0 for m in MOMENTS}
    dispositif = False
    for cellule in carnet.get("cells", []):
        if cellule.get("cell_type") != "code":
            continue
        texte = _source(cellule)
        if IMPORT.search(texte):
            dispositif = True
        for moment in moments_appeles(texte):
            if moment in comptes:
                comptes[moment] += 1
    return comptes, dispositif


def bilan(carnets):
    """Liste de verdicts par carnet : les trois moments sont-ils présents ?"""
    resultats = []
    for chemin in carnets:
        absolu = chemin if os.path.isabs(chemin) else os.path.join(SERIE, chemin)
        try:
            relatif = os.path.relpath(absolu, RACINE).replace("\\", "/")
        except ValueError:  # chemin sur un autre lecteur (self-test en dossier temporaire)
            relatif = absolu.replace("\\", "/")
        if not os.path.exists(absolu):
            resultats.append({"carnet": relatif, "present": False, "motif": "fichier absent"})
            continue
        comptes, dispositif = lire_carnet(absolu)
        manquants = [m for m in MOMENTS if comptes[m] == 0]
        resultats.append({
            "carnet": relatif,
            "present": not manquants and dispositif,
            "dispositif": dispositif,
            "comptes": comptes,
            "manquants": manquants,
        })
    return resultats


def afficher(resultats):
    largeur = max(len(r["carnet"]) for r in resultats)
    for r in resultats:
        if not r["present"] and r.get("motif"):
            print(f"  ABSENT  {r['carnet']:<{largeur}}  {r['motif']}")
            continue
        c = r["comptes"]
        marque = "OK     " if r["present"] else "INCOMPLET"
        detail = f"avant={c['avant']} pendant={c['pendant']} apres={c['apres']}"
        if not r["dispositif"]:
            detail += " import=absent"
        if r["manquants"]:
            detail += " manquants=" + ",".join(r["manquants"])
        print(f"  {marque} {r['carnet']:<{largeur}}  {detail}")
    complets = sum(1 for r in resultats if r["present"])
    print(f"\n{complets}/{len(resultats)} carnet(s) pilote(s) portent les trois moments.")


def self_test():
    """La détection se valide par ses faux négatifs : on lui donne un carnet qui
    porte les trois moments, puis un carnet auquel on retire le transfert."""
    import tempfile

    def cellule(moment):
        # Disposition reelle : l'explication (longue) precede `moment=`, ce qui a
        # fait echouer la premiere detection a fenetre fixe. L'auto-test doit la
        # reproduire, sinon il valide un motif que les carnets ne portent pas.
        return {"cell_type": "code", "source": (
            'question(\n    "Q ?",\n    choix=["a", "b"],\n    bonne="A",\n'
            '    explication="' + "x" * 600 + '",\n'
            f'    moment="{moment}",\n)\n'
        )}

    complet = {"cells": [
        {"cell_type": "code", "source": "from auto_evaluation import question\n"},
        cellule("avant"), cellule("pendant"), cellule("apres"),
    ]}
    incomplet = {"cells": [
        {"cell_type": "code", "source": "from auto_evaluation import question\n"},
        cellule("avant"), cellule("pendant"), cellule("pendant"),
    ]}
    sans_import = {"cells": [cellule("avant"), cellule("pendant"), cellule("apres")]}

    echecs = []
    with tempfile.TemporaryDirectory() as tmp:
        for nom, carnet, attendu in (
            ("complet", complet, True),
            ("incomplet", incomplet, False),
            ("sans_import", sans_import, False),
        ):
            chemin = os.path.join(tmp, nom + ".ipynb")
            with io.open(chemin, "w", encoding="utf-8") as f:
                json.dump(carnet, f)
            verdict = bilan([chemin])[0]["present"]
            if verdict != attendu:
                echecs.append(f"{nom} : present={verdict} (attendu {attendu})")
    if echecs:
        print("SELF-TEST ECHEC : " + " ; ".join(echecs))
        return 1
    print("SELF-TEST OK : 3 carnets synthetiques juges correctement.")
    return 0


def main():
    parseur = argparse.ArgumentParser(description=__doc__,
                                      formatter_class=argparse.RawDescriptionHelpFormatter)
    parseur.add_argument("carnets", nargs="*", default=None,
                         help="carnets a verifier (defaut : les six pilotes de 02-ML-Cours)")
    parseur.add_argument("--json", action="store_true", help="verdict machine")
    parseur.add_argument("--strict", action="store_true",
                         help="exit 1 si un carnet pilote ne porte pas les trois moments")
    parseur.add_argument("--self-test", action="store_true",
                         help="verifie la detection sur des carnets synthetiques")
    args = parseur.parse_args()

    if args.self_test:
        return self_test()

    resultats = bilan(args.carnets or PILOTES)
    if args.json:
        print(json.dumps(resultats, ensure_ascii=False, indent=1))
    else:
        afficher(resultats)
    if args.strict and any(not r["present"] for r in resultats):
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())