"""Construit le catalogue identifiant <-> chemin canonique du gisement bibliographique.

Tache A5 de l'umbrella #14407 (flux 2) : l'index par identifiant qui manque.
Les CSVs de resolution A1 (arXiv, DOI) portent une colonne `chemin_gisement`
remplie a la main ; ce catalogue la rend mecanisable en associant chaque
identifiant detecte dans le gisement a son chemin canonique.

Deux sources d'extraction par PDF, par confiance decroissante :
  1. le **nom de fichier** (confiance elevee : nommage curate par nous-memes) ;
  2. la **premiere page** (tampon `arXiv:####.#####` des preprints, DOI de
     l'editeur), avec retente apres copie locale si le client Google Drive
     sert le fichier en streaming non hydrate (pattern herite de
     `check_bibliography_pdf_integrity.py`).

Aucun fichier du gisement n'est modifie : le catalogue est un CSV additif,
date, ecrit a la racine du gisement.

Usage:
  python scripts/build_bibliography_identifier_catalog.py
  python scripts/build_bibliography_identifier_catalog.py --root "G:/Mon Drive/MyIA/IA/Bibliographie IA" --out catalogue.csv
  python scripts/build_bibliography_identifier_catalog.py --a1-csv arXiv-A1-resolution.csv --a1-csv DOI-A1-resolution.csv

Options:
  --root PATH        Racine du gisement (defaut G:/Mon Drive/MyIA/IA/Bibliographie IA)
  --out PATH         CSV de sortie (defaut <root>/IDENTIFIANTS-catalogue-YYYY-MM-DD.csv)
  --pages N          Nombre de premieres pages lues par PDF (defaut 2 : couverture + page de titre)
  --max-seconds S    Budget global ; arret propre entre deux fichiers (defaut 600)
  --a1-csv PATH      CSV A1 a joindre ; rend pour chaque identifiant son verdict A1
                     et le chemin resolu par le catalogue (repeter pour plusieurs CSVs)
  --json PATH        Rapport structure optionnel

Limite connue : pas de delai par fichier (heritage du script d'integrite) ;
une lecture bloquee par Drive immobilise le parcours jusqu'au budget global.
"""

from __future__ import annotations

import argparse
import csv
import io
import json
import random
import re
import shutil
import sys
import tempfile
import time
from datetime import date
from pathlib import Path

DEFAULT_ROOT = "G:/Mon Drive/MyIA/IA/Bibliographie IA"

CONTEXTE_MAX = 120

# Nom de fichier : motif nu tolere (nommage curate par nos soins).
ARXIV_BARE_RE = re.compile(r"\b(\d{4}\.\d{4,5})(?:v\d+)?\b")
DOI_BARE_RE = re.compile(r"\b(10\.\d{4,9}/[^\s\"'<>,;]+)", re.IGNORECASE)
# Premiere page : seuls les formes marquees sont de confiance elevee ; les
# matches nus restent collectes en confiance standard (bruit tolerable : la
# jointure A1 ne cherche que des identifiants deja connus).
ARXIV_STAMP_RE = re.compile(r"arXiv[ :]*(\d{4}\.\d{4,5})(?:v\d+)?", re.IGNORECASE)
DOI_MARKED_RE = re.compile(
    r"(?:doi\.org/|doi\s*[:=]\s*|DOI\s*[:=]\s*)(10\.\d{4,9}/[^\s\"'<>,;]+)",
    re.IGNORECASE)


def _force_utf8_streams() -> None:
    """Evite le mojibake cp1252 sur les sorties console Windows."""
    if sys.platform != "win32":
        return
    for name in ("stdout", "stderr"):
        stream = getattr(sys, name, None)
        if getattr(stream, "buffer", None) is None:
            continue
        try:
            setattr(sys, name, io.TextIOWrapper(stream.buffer, encoding="utf-8",
                                                errors="replace"))
        except Exception:
            pass


def _clean_doi(raw: str) -> str:
    """Retire la ponctuation terminale avalée par la regex (point, virgule, parenthese)."""
    return raw.rstrip(".,;)]}")


def _clip(texte: str) -> str:
    """Reduit un contexte a une fenetre lisible autour du match."""
    compact = re.sub(r"\s+", " ", texte).strip()
    if len(compact) <= CONTEXTE_MAX:
        return compact
    return compact[:CONTEXTE_MAX - 3] + "..."


def extraire_du_nom(nom: str) -> list[dict]:
    """Identifiants extraits du seul nom de fichier (confiance elevee)."""
    trouves: list[dict] = []
    for m in ARXIV_BARE_RE.finditer(nom):
        trouves.append({"type_id": "arxiv", "id": m.group(1),
                        "source": "nom_fichier", "confiance": "elevee",
                        "contexte": _clip(nom)})
    for m in DOI_BARE_RE.finditer(nom):
        trouves.append({"type_id": "doi", "id": _clean_doi(m.group(1)),
                        "source": "nom_fichier", "confiance": "elevee",
                        "contexte": _clip(nom)})
    return trouves


def extraire_du_texte(texte: str) -> list[dict]:
    """Identifiants extraits du texte des premieres pages.

    Les formes marquees (`arXiv:`, `doi.org/`) sont elevees ; les formes nues
    sont standard : un numero de rapport interne peut matcher le motif arXiv nu.
    """
    trouves: list[dict] = []
    vus: set[tuple[str, str, str]] = set()

    def ajouter(type_id: str, identifiant: str, confiance: str, fenetre: str) -> None:
        cle = (type_id, identifiant, confiance)
        if cle not in vus:
            vus.add(cle)
            trouves.append({"type_id": type_id, "id": identifiant,
                            "source": "premiere_page", "confiance": confiance,
                            "contexte": _clip(fenetre)})

    for m in ARXIV_STAMP_RE.finditer(texte):
        debut = max(0, m.start() - 40)
        ajouter("arxiv", m.group(1), "elevee", texte[debut:m.end() + 40])
    for m in DOI_MARKED_RE.finditer(texte):
        debut = max(0, m.start() - 40)
        ajouter("doi", _clean_doi(m.group(1)), "elevee", texte[debut:m.end() + 40])
    for m in ARXIV_BARE_RE.finditer(texte):
        debut = max(0, m.start() - 40)
        ajouter("arxiv", m.group(1), "standard", texte[debut:m.end() + 40])
    for m in DOI_BARE_RE.finditer(texte):
        debut = max(0, m.start() - 40)
        ajouter("doi", _clean_doi(m.group(1)), "standard", texte[debut:m.end() + 40])
    return trouves


def lire_premieres_pages(path: Path, nb_pages: int,
                         hydrate_dir: Path | None = None) -> tuple[str | None, str]:
    """Texte concatene des N premieres pages ; retente apres copie locale.

    Renvoie `(texte, message_erreur)` ; texte None = illisible (streaming ou
    corrompu), le message distingue la premiere cause rencontree.
    """

    def _tenter(cible: Path) -> tuple[str | None, str]:
        try:
            from pypdf import PdfReader
        except ImportError:  # pragma: no cover - dependance d'environnement
            raise SystemExit("ERREUR: pypdf manquant. Installer via `pip install pypdf`.")
        try:
            reader = PdfReader(str(cible))
            morceaux = []
            for page in reader.pages[:nb_pages]:
                try:
                    morceaux.append(page.extract_text() or "")
                except Exception:
                    continue
            return "\n".join(morceaux), ""
        except Exception as exc:
            return None, "%s: %s" % (type(exc).__name__, str(exc)[:160])

    texte, err = _tenter(path)
    if texte is not None:
        return texte, ""

    if hydrate_dir is not None:
        try:
            hydrate_dir.mkdir(parents=True, exist_ok=True)
            local = hydrate_dir / ("hydrate-%d.pdf" % random.getrandbits(48))
            shutil.copy2(str(path), str(local))
            texte2, _ = _tenter(local)
            try:
                local.unlink()
            except OSError:
                pass
            if texte2 is not None:
                return texte2, ""
        except Exception as exc:  # copie impossible : on garde la premiere erreur
            err = "%s | copie locale: %s" % (err, type(exc).__name__)

    return None, err


def construire_catalogue(root: Path, nb_pages: int, budget: float,
                         quiet: bool = False) -> dict:
    """Parcourt le gisement et rend le catalogue + le rapport de parcours."""
    pdfs = sorted(p for p in root.rglob("*.pdf") if p.is_file())
    lignes: list[dict] = []
    illisibles: list[dict] = []
    debut = time.time()
    avec_id = 0

    with tempfile.TemporaryDirectory(prefix="biblio-catalogue-") as tmp:
        hydrate_dir = Path(tmp)
        for idx, pdf in enumerate(pdfs, 1):
            if time.time() - debut > budget:
                sys.stderr.write("Budget %.0fs consomme apres %d/%d fichiers ; "
                                 "arret propre.\n" % (budget, idx - 1, len(pdfs)))
                break
            rel = pdf.relative_to(root).as_posix()
            avant = len(lignes)
            lignes.extend({"chemin_gisement": rel, **t}
                          for t in extraire_du_nom(pdf.stem))

            texte, err = lire_premieres_pages(pdf, nb_pages, hydrate_dir)
            if texte is None:
                illisibles.append({"chemin_gisement": rel, "erreur": err})
            else:
                lignes.extend({"chemin_gisement": rel, **t}
                              for t in extraire_du_texte(texte))
            if len(lignes) > avant:
                avec_id += 1
            if not quiet and idx % 50 == 0:
                sys.stderr.write("  ... %d/%d fichiers, %d entrees\n"
                                 % (idx, len(pdfs), len(lignes)))

    # Deduplication : un meme identifiant peut venir du nom ET de la page de
    # titre du meme fichier ; on garde la meilleure confiance puis la source.
    ordre = {"elevee": 0, "standard": 1}
    meilleures: dict[tuple[str, str, str], dict] = {}
    for ligne in lignes:
        cle = (ligne["chemin_gisement"], ligne["type_id"], ligne["id"].lower())
        courante = meilleures.get(cle)
        if courante is None or (ordre[ligne["confiance"]], ligne["source"]) < \
                (ordre[courante["confiance"]], courante["source"]):
            meilleures[cle] = ligne
    catalogue = sorted(meilleures.values(),
                       key=lambda l: (l["chemin_gisement"], l["type_id"], l["id"]))

    ids_uniques = {(l["type_id"], l["id"].lower()) for l in catalogue}
    rapport = {
        "gisement": str(root),
        "pdfs_vus": len(pdfs),
        "pdfs_avec_identifiant": avec_id,
        "entrees_catalogue": len(catalogue),
        "identifiants_distincts": len(ids_uniques),
        "par_type": {t: sum(1 for i in ids_uniques if i[0] == t)
                     for t in ("arxiv", "doi")},
        "par_source": {s: sum(1 for l in catalogue if l["source"] == s)
                       for s in ("nom_fichier", "premiere_page")},
        "illisibles": illisibles,
        "duree_s": round(time.time() - debut, 1),
    }
    return {"catalogue": catalogue, "rapport": rapport}


def joindre_a1(catalogue: list[dict], chemins_csv: list[str]) -> dict:
    """Jointure mecanisante : chaque identifiant A1 retrouve-t-il son chemin ?

    Rend par CSV : total, resolus (et par confiance), non resolus. C'est la
    preuve qu'A1 devient mecanisable : la colonne `chemin_gisement` des CSVs
    de resolution se remplit desormais par lookup dans ce catalogue.
    """
    index: dict[tuple[str, str], dict] = {}
    for ligne in catalogue:
        cle = (ligne["type_id"], ligne["id"].lower())
        courante = index.get(cle)
        if courante is None or ligne["confiance"] == "elevee":
            index[cle] = ligne

    resultats = []
    for chemin in chemins_csv:
        # utf-8-sig : les CSVs A1 du gisement portent un BOM (excel-friendly),
        # qui sinon degenere la premiere colonne en «﻿id».
        with open(chemin, newline="", encoding="utf-8-sig") as fh:
            lecteur = csv.DictReader(fh)
            colonne_id = next((c for c in ("id", "doi", "arxiv") if c in lecteur.fieldnames), None)
            if colonne_id is None:
                resultats.append({"csv": chemin, "erreur": "colonne id/doi absente"})
                continue
            total = resolus = 0
            verdicts: dict[str, int] = {}
            for ligne in lecteur:
                identifiant = (ligne.get(colonne_id) or "").strip()
                if not identifiant:
                    continue
                total += 1
                type_id = "doi" if colonne_id == "doi" else "arxiv"
                hit = index.get((type_id, identifiant.lower()))
                if hit is not None:
                    resolus += 1
                    verdicts[hit["confiance"]] = verdicts.get(hit["confiance"], 0) + 1
            resultats.append({"csv": Path(chemin).name, "total": total,
                              "resolus": resolus, "par_confiance": verdicts,
                              "non_resolus": total - resolus})
    return {"a1": resultats}


def ecrire_csv(catalogue: list[dict], sortie: Path) -> None:
    sortie.parent.mkdir(parents=True, exist_ok=True)
    champs = ["chemin_gisement", "type_id", "id", "source_extraction",
              "confiance", "contexte"]
    with open(sortie, "w", newline="", encoding="utf-8") as fh:
        ecrivain = csv.DictWriter(fh, fieldnames=champs)
        ecrivain.writeheader()
        for ligne in catalogue:
            ecrivain.writerow({"chemin_gisement": ligne["chemin_gisement"],
                               "type_id": ligne["type_id"], "id": ligne["id"],
                               "source_extraction": ligne["source"],
                               "confiance": ligne["confiance"],
                               "contexte": ligne["contexte"]})


def main() -> int:
    _force_utf8_streams()
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", default=DEFAULT_ROOT, help="racine du gisement")
    ap.add_argument("--out", default=None,
                    help="CSV de sortie (defaut <root>/IDENTIFIANTS-catalogue-YYYY-MM-DD.csv)")
    ap.add_argument("--pages", type=int, default=2,
                    help="premieres pages lues par PDF (defaut 2)")
    ap.add_argument("--max-seconds", type=float, default=600.0, help="budget global")
    ap.add_argument("--a1-csv", action="append", default=None,
                    help="CSV A1 a joindre (repeter pour plusieurs)")
    ap.add_argument("--json", default=None, help="rapport structure")
    ap.add_argument("--quiet", action="store_true", help="pas de progres")
    args = ap.parse_args()

    root = Path(args.root)
    if not root.is_dir():
        sys.stderr.write("ERREUR: racine introuvable: %s\n" % root)
        return 2

    res = construire_catalogue(root, args.pages, args.max_seconds, args.quiet)
    catalogue, rapport = res["catalogue"], res["rapport"]

    sortie = Path(args.out) if args.out else \
        root / ("IDENTIFIANTS-catalogue-%s.csv" % date.today().isoformat())
    ecrire_csv(catalogue, sortie)

    print("Catalogue ecrit : %s" % sortie)
    print("PDFs parcourus : %d ; avec identifiant : %d ; illisibles : %d"
          % (rapport["pdfs_vus"], rapport["pdfs_avec_identifiant"],
             len(rapport["illisibles"])))
    print("Entrees : %d ; identifiants distincts : %d (arxiv %d, doi %d)"
          % (rapport["entrees_catalogue"], rapport["identifiants_distincts"],
             rapport["par_type"]["arxiv"], rapport["par_type"]["doi"]))
    print("Sources : nom_fichier %d, premiere_page %d ; duree %.1fs"
          % (rapport["par_source"]["nom_fichier"],
             rapport["par_source"]["premiere_page"], rapport["duree_s"]))
    for illisible in rapport["illisibles"][:10]:
        print("  ILLISIBLE : %s (%s)" % (illisible["chemin_gisement"],
                                         illisible["erreur"][:100]))

    if args.a1_csv:
        jointure = joindre_a1(catalogue, args.a1_csv)
        rapport["jointure_a1"] = jointure
        for resultat in jointure["a1"]:
            if "erreur" in resultat:
                print("Jointure %s : ERREUR %s" % (resultat["csv"], resultat["erreur"]))
                continue
            print("Jointure %s : %d/%d resolus (%s), %d non resolus"
                  % (resultat["csv"], resultat["resolus"], resultat["total"],
                     ", ".join("%s %d" % kv for kv in sorted(resultat["par_confiance"].items())),
                     resultat["non_resolus"]))

    if args.json:
        rapport["sortie_csv"] = str(sortie)
        Path(args.json).write_text(json.dumps(rapport, ensure_ascii=False, indent=2),
                                   encoding="utf-8")
    return 0


if __name__ == "__main__":
    sys.exit(main())
