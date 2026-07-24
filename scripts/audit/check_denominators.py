#!/usr/bin/env python3
"""check_denominators.py — CI leger detectant la divergence entre sources.

Compare les 3 sources (disque / forensic / catalogue) au meme SHA et alerte
si la divergence entre disque et catalogue depasse les exclusions declarees
dans les scripts canoniques (forensic_scan.py EXCLUDE_DIRS et
generate_catalog.py EXCLUDE_PEDAGOGICAL).

Issue : #8050. SHA verifie : be5998073 (2026-07-23).

Usage :
    py scripts/audit/check_denominators.py --root MyIA.AI.Notebooks
    py scripts/audit/check_denominators.py --root MyIA.AI.Notebooks --json-out out.json
    py scripts/audit/check_denominators.py --root MyIA.AI.Notebooks --strict  # exit 1 si drift/phantom

Exit codes :
    0 — OK (drift et phantoms dans les limites declarees)
    1 — Drift catalogue > 0 (notebooks curés manquants) OU phantom catalogue (entry -> fichier inexistant)
    2 — Erreur d'execution (fichier manquant, etc.)

Detecte deux classes de divergence distinctes :
  - DRIFT   : notebooks presents sur disque/forensic mais manquants du catalogue (curation incomplete).
  - PHANTOM : entrees du catalogue qui pointent vers un notebook ABSENT du disque (catalogue drift,
    ex: renommage/suppression non propage). Le catalog-cron ne self-heal pas toujours les phantoms
    (ex: suffixe '-executed' resurgit a chaque regen si le generateur le deduit d'un artefact).
    Un phantom est le signal le plus actionnable : il indique un bug catalogue reel, pas une
    exclusion saine.
"""

import argparse
import json
import sys
from pathlib import Path


# Ces constantes sont COPIEES des scripts canoniques pour eviter une dependance
# d'import. Toute modification ici DOIT etre alignee avec les sources verite.
# Source : scripts/notebook_tools/forensic_scan.py ligne 25-32
FORENSIC_EXCLUDE_DIRS = {
    "_archive_obsoletes",
    "_archives",
    "_old",
    "TrashBin",
    "trashbin",
    ".ipynb_checkpoints",
    "node_modules",
}

# Source : scripts/notebook_tools/generate_catalog.py ligne 39
CATALOG_EXCLUDE_PEDAGOGICAL = {
    "research",
    "archive",
    "_output",
    "output",
    "partner-course",
    "examples",
}


def count_disk(root: Path) -> set:
    """Tous les .ipynb sous root (recursif), comme `find -name '*.ipynb'`."""
    return {
        str(p.relative_to(root)).replace("\\", "/")
        for p in root.rglob("*.ipynb")
    }


def count_forensic(root: Path) -> set:
    """Comme forensic_scan.py : disque moins EXCLUDE_DIRS."""
    paths = count_disk(root)
    filtered = set()
    for p in paths:
        parts = p.split("/")
        if not any(part in FORENSIC_EXCLUDE_DIRS for part in parts):
            filtered.add(p)
    return filtered


def count_catalog(root: Path, catalog_path: Path) -> set:
    """Comme generate_catalog.py : catalogue curé (charge le JSON genere)."""
    if not catalog_path.exists():
        return set()
    with open(catalog_path, encoding="utf-8") as f:
        catalog = json.load(f)
    if not isinstance(catalog, list):
        return set()
    return {entry.get("path") for entry in catalog if entry.get("path")}


def main():
    parser = argparse.ArgumentParser(description="Verifie la coherence des denominateurs notebooks.")
    parser.add_argument("--root", default="MyIA.AI.Notebooks", help="Racine notebooks (defaut: MyIA.AI.Notebooks)")
    parser.add_argument("--catalog", default="COURSE_CATALOG.generated.json", help="Chemin catalogue (defaut: COURSE_CATALOG.generated.json)")
    parser.add_argument("--json-out", default=None, help="Sortie JSON (optionnel)")
    parser.add_argument("--strict", action="store_true", help="Exit 1 si drift catalogue > 0")
    args = parser.parse_args()

    root = Path(args.root)
    catalog_path = Path(args.catalog)

    if not root.is_dir():
        print(f"ERREUR: racine introuvable: {root}", file=sys.stderr)
        return 2

    disk = count_disk(root)
    forensic = count_forensic(root)
    catalog = count_catalog(root, catalog_path)

    # Exclusions catalogue : simule la regle generate_catalog.py
    catalog_excluded = {
        p for p in forensic
        if any(part in CATALOG_EXCLUDE_PEDAGOGICAL for part in p.split("/"))
    }
    catalog_expected = forensic - catalog_excluded
    drift = sorted(catalog_expected - catalog)

    # PHANTOM : entrees catalogue dont le fichier n'existe pas sur disque.
    # Distinct du drift (notebook manquant du catalogue) : ici c'est le catalogue
    # qui reference un notebook absent -> bug catalogue (ex: suffixe '-executed'
    # resurgissant). Le signal le plus actionnable.
    phantoms = sorted(p for p in catalog if p not in disk)

    report = {
        "denominators": {
            "disk": len(disk),
            "forensic": len(forensic),
            "catalog": len(catalog),
        },
        "expected_with_exclusions": len(catalog_expected),
        "drift_count": len(drift),
        "drift_by_series": {},
        "phantom_count": len(phantoms),
        "exclusion_breakdown": {
            "forensic_excluded_dirs": len(disk - forensic),
            "catalog_excluded_pedagogical": len(catalog_excluded),
        },
        "drift_paths": drift,
        "phantom_paths": phantoms,
    }

    # Drift par série (premier segment du path)
    from collections import Counter
    drift_series = Counter()
    for p in drift:
        first = p.split("/")[0] if "/" in p else p
        drift_series[first] += 1
    report["drift_by_series"] = dict(drift_series)

    if args.json_out:
        with open(args.json_out, "w", encoding="utf-8") as f:
            json.dump(report, f, indent=2, ensure_ascii=False)
        print(f"JSON report: {args.json_out}")

    # Sortie texte
    print("=" * 64)
    print("CHECK DENOMINATORS — coherence disque / forensic / catalogue")
    print("=" * 64)
    print(f"Disque    : {len(disk):>5} notebooks (find -name '*.ipynb')")
    print(f"Forensic  : {len(forensic):>5} notebooks (EXCLUDE_DIRS={len(FORENSIC_EXCLUDE_DIRS)} dirs)")
    print(f"Catalogue : {len(catalog):>5} notebooks (EXCLUDE_PEDAGOGICAL={len(CATALOG_EXCLUDE_PEDAGOGICAL)} keywords)")
    print()
    print(f"Exclusions forensic : {len(disk) - len(forensic)} notebooks (archives, TrashBin...)")
    print(f"Exclusions catalogue: {len(catalog_excluded)} notebooks (research/archive/examples/partner-course)")
    print(f"Catalogue attendu   : {len(catalog_expected)} (forensic - exclusions catalogue)")
    print(f"Catalogue reel      : {len(catalog)}")
    print(f"DRIFT catalogue     : {len(drift)} notebooks curés manquants")
    print()
    if drift:
        print("--- DRIFT par serie ---")
        for k in sorted(drift_series.keys()):
            print(f"  {k:<20} : {drift_series[k]} notebooks non-cures")
        print()
        print(f"--- DRIFT paths ({len(drift)}) ---")
        for p in drift[:20]:
            print(f"  + {p}")
        if len(drift) > 20:
            print(f"  ... et {len(drift) - 20} autres")
    else:
        print("OK : drift catalogue = 0")
    print()
    print(f"PHANTOM catalogue  : {len(phantoms)} entrees -> fichier inexistant")
    if phantoms:
        print(f"--- PHANTOM paths ({len(phantoms)}) ---")
        for p in phantoms:
            print(f"  ! {p}  (absent du disque)")
    else:
        print("OK : phantom catalogue = 0")
    print("=" * 64)

    if args.strict and (drift or phantoms):
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
