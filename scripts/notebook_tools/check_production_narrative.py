"""Mesure le recit de FABRICATION dans les cellules markdown des carnets.

Epic #14446 (reancrage des series dans leur contexte pedagogique) et sa fille
#20844 : un carnet presente a l'apprenant son contenu, pas la narration de sa
fabrication (labels de pull request, dates de fusion, decoupage en
« sous-grains », verdicts de revue). Cet organe compte les marqueurs de ce
recit pour qu'une tranche de reancrage puisse etre mesuree avant/apres.

Ce qui est compte (marqueurs de RECIT) :
  - les labels de production qui servent de noms de contenu (« PR-A », « PR-B ») ;
  - un numero de pull request suivi d'un contexte de fusion ;
  - le bloc de filiation d'une intro (« Filiation », « EPIC parent ») ;
  - le vocabulaire de decoupage de production (« sous-grain ») ;
  - un verdict de revue pose dans le carnet (« SOTA-OK », « CHANGES_REQUESTED »,
    « RECOVERABLE-USER-HAND ») ;
  - un intertitre de recit de production (« Cadre de production ») ;
  - une date de fusion (« mergee 2026-07-10 »).

Ce qui n'est PAS compte (renvois pedagogiques legitimes, qui restent des
renvois de contenu) : « regle #2161 », « protocole #13309 », les liens de
definitions, les references a un incident qui motive une mesure.

Usage
-----
    # Mesure d'une tranche (avant/apres sur la meme commande)
    python scripts/notebook_tools/check_production_narrative.py --paths a.ipynb b.ipynb
    python scripts/notebook_tools/check_production_narrative.py --paths a.ipynb --json

    # Sur l'ensemble d'une sous-serie
    python scripts/notebook_tools/check_production_narrative.py --dir MyIA.AI.Notebooks/.../X

Code de sortie : 0 = aucun marqueur, 1 = marqueur(s) trouve(s), 2 = usage invalide.
"""

import argparse
import json
import os
import sys

# Marqueur -> jeton litteral. Un compte par token, pas par regex : le resultat
# est stable et lisible, et deux runs sur le meme etat donnent le meme nombre.
MARQUEURS = [
    "PR-A",
    "PR-B",
    "SOTA-OK",
    "CHANGES_REQUESTED",
    "RECOVERABLE-USER-HAND",
    "sous-grain",
    "Filiation",
    "EPIC parent",
    "Cadre de production",
    "mergée 2026",
    "mergee 2026",
    "mergée le",
    "mergee le",
]


def marqueurs(source):
    """Compte des marqueurs de recit dans un texte de cellule markdown."""
    return {m: source.count(m) for m in MARQUEURS if m in source}


def mesure_fichier(chemin):
    try:
        with open(chemin, encoding="utf-8") as fh:
            nb = json.load(fh)
    except (OSError, ValueError) as exc:
        return {"fichier": os.path.basename(chemin), "erreur": str(exc),
                "total": 0, "marqueurs": {}}
    compte = {}
    cellules = []
    for i, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "markdown":
            continue
        src = "".join(cell.get("source", []))
        m = marqueurs(src)
        if m:
            cellules.append({"cellule": i, "marqueurs": m})
            for k, v in m.items():
                compte[k] = compte.get(k, 0) + v
    return {"fichier": os.path.basename(chemin),
            "total": sum(compte.values()),
            "marqueurs": compte,
            "cellules": cellules}


def collecte(paths, dossier):
    cibles = []
    for p in paths:
        if not os.path.isfile(p):
            print("introuvable : %s" % p, file=sys.stderr)
            return None
        cibles.append(p)
    if dossier:
        for racine, _dirs, fichiers in os.walk(dossier):
            for nom in sorted(fichiers):
                if nom.endswith(".ipynb"):
                    cibles.append(os.path.join(racine, nom))
    return cibles


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--paths", nargs="+", default=[],
                    help="carnets a mesurer")
    ap.add_argument("--dir", default=None,
                    help="dossier a parcourir (carnets *.ipynb)")
    ap.add_argument("--json", action="store_true",
                    help="sortie structuree")
    args = ap.parse_args(argv)

    if not args.paths and not args.dir:
        ap.error("indiquer --paths et/ou --dir")

    cibles = collecte(args.paths, args.dir)
    if cibles is None:
        return 2

    resultats = [mesure_fichier(c) for c in cibles]
    total = sum(r["total"] for r in resultats)

    if args.json:
        print(json.dumps({"total": total, "fichiers": resultats},
                         ensure_ascii=False, indent=2))
    else:
        for r in resultats:
            print("%-64s %d" % (r["fichier"][:64], r["total"]))
            for k, v in sorted(r.get("marqueurs", {}).items()):
                print("      %-20s %d" % (k, v))
            for c in r.get("cellules", []):
                print("      cellule %-4d %s" % (c["cellule"], c["marqueurs"]))
        print("TOTAL = %d" % total)

    return 1 if total else 0


if __name__ == "__main__":
    sys.exit(main())
