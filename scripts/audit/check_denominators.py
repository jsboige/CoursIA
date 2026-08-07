#!/usr/bin/env python3
"""check_denominators.py — CI leger detectant la divergence entre sources.

Compare les 4 sources (disque / forensic / catalogue / outil) au meme SHA et
alerte si la divergence entre disque et catalogue depasse les exclusions
declarees dans les scripts canoniques (forensic_scan.py EXCLUDE_DIRS et
generate_catalog.py EXCLUDE_PEDAGOGICAL), ou si catalogue et outil
(count_notebooks_by_series) divergent hors des categories documentees.

Issues : #8050 (disque/forensic/catalogue), #9857 (source outil catalogue-vs-outil).
SHA verifie : e7307a717 (2026-08-07).

Usage :
    py scripts/audit/check_denominators.py --root MyIA.AI.Notebooks
    py scripts/audit/check_denominators.py --root MyIA.AI.Notebooks --json-out out.json
    py scripts/audit/check_denominators.py --root MyIA.AI.Notebooks --strict  # exit 1 si drift/phantom/divergence

Exit codes :
    0 — OK (drift, phantoms et divergence catalogue/outil dans les limites declarees)
    1 — Drift catalogue > 0 (notebooks cures manquants) OU phantom catalogue (entry -> fichier inexistant)
        OU divergence catalogue/outil non documentee (cf docs/reference/notebook-counters.md)
    2 — Erreur d'execution (fichier manquant, etc.)

Detecte trois classes de divergence distinctes :
  - DRIFT   : notebooks presents sur disque/forensic mais manquants du catalogue (curation incomplete).
  - PHANTOM : entrees du catalogue qui pointent vers un notebook ABSENT du disque (catalogue drift,
    ex: renommage/suppression non propage). Le catalog-cron ne self-heal pas toujours les phantoms
    (ex: suffixe '-executed' resurgit a chaque regen si le generateur le deduit d'un artefact).
    Un phantom est le signal le plus actionnable : il indique un bug catalogue reel, pas une
    exclusion saine.
  - DIVERGENCE catalogue/outil : un notebook compte par count_notebooks_by_series mais pas par le
    catalogue (ou inverse), hors des exclusions EXTRA du catalogue (_archive/_archives/output).
    Signale que les deux compteurs a la prose drifting (#9857) ont derive. Cf
    docs/reference/notebook-counters.md.
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
# Le catalogue a l'exclusion pedagogique la plus large (_archive/_archives/output
# explicites). Cf docs/reference/notebook-counters.md §5.
CATALOG_EXCLUDE_PEDAGOGICAL = {
    "research",
    "archive",
    "_archive",
    "_archives",
    "_output",
    "output",
    "partner-course",
    "examples",
}

# Source : scripts/notebook_tools/count_notebooks_by_series.py ligne 33-39
# C'est le compteur "outil" (mode pedagogique) qui alimente la prose README et les
# marqueurs CATALOG-STATUS (pedagogical_count). Exclusion legerement plus etroite
# que le catalogue (pas de _archive/_archives/output explicites) -> un ecart
# catalogue vs outil est possible et doit etre visible (cf notebook-counters.md).
OUTIL_EXCLUDE_ALWAYS = {".ipynb_checkpoints", "obj", "bin", "__pycache__", ".git"}
OUTIL_EXCLUDE_PEDAGOGICAL = {
    "research",
    "archive",
    "_output",
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


def count_outil(root: Path) -> set:
    """Comme count_notebooks_by_series.py (mode pedagogique) : walk les
    sous-repertoires de serie (les .ipynb a la racine de root ne sont PAS
    atteints -- ex: GradeBook.ipynb), applique EXCLUDE_ALWAYS (segments de dir
    exacts) et EXCLUDE_PEDAGOGICAL (substring sur le chemin complet, incluant le
    filename). C'est le 4e compteur de #9857."""
    paths = set()
    for series_dir in sorted(root.iterdir()):
        if not series_dir.is_dir() or series_dir.name.startswith("."):
            continue
        if series_dir.name in OUTIL_EXCLUDE_ALWAYS:
            continue
        for nb_path in series_dir.rglob("*.ipynb"):
            rel = nb_path.relative_to(root)
            parts = rel.parts
            dir_parts = parts[:-1]
            if any(exc in dir_parts for exc in OUTIL_EXCLUDE_ALWAYS):
                continue
            if any(exc in str(rel) for exc in OUTIL_EXCLUDE_PEDAGOGICAL):
                continue
            paths.add(str(rel).replace("\\", "/"))
    return paths


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
    outil = count_outil(root)

    # Divergence catalogue vs outil (4e source, #9857). Les deux ont des filtres
    # pedagogiques legerement differents (cf notebook-counters.md §5) ; un ecart
    # n'est un bug que s'il sort des categories documentees.
    outil_only = sorted(outil - catalog)
    catalog_only_vs_outil = sorted(catalog - outil)

    # Exclusions catalogue : simule la regle generate_catalog.py (substring sur le
    # chemin COMPLET, incluant le filename -- cf #9851/#9867 : un match sur les
    # seuls segments de path rate "research" dans research_l1_tsmom.ipynb et
    # fabrique 78 faux drifts).
    # Univers = notebooks dans un sous-repertoire de serie (contenant "/"). Les
    # singletons racine (ex: GradeBook.ipynb) ne sont jamais atteints par le walk
    # par serie du catalogue ni de count_notebooks_by_series -> hors-univers, pas
    # du drift (ce ne sont pas des notebooks de serie non-cures).
    series_scoped = {p for p in forensic if "/" in p}
    catalog_excluded = {
        p for p in series_scoped
        if any(exc in p for exc in CATALOG_EXCLUDE_PEDAGOGICAL)
    }
    catalog_expected = series_scoped - catalog_excluded
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
            "outil": len(outil),
        },
        "expected_with_exclusions": len(catalog_expected),
        "drift_count": len(drift),
        "drift_by_series": {},
        "phantom_count": len(phantoms),
        "outil_catalog_diff": {
            "outil_not_in_catalog": len(outil_only),
            "catalog_not_in_outil": len(catalog_only_vs_outil),
        },
        "exclusion_breakdown": {
            "forensic_excluded_dirs": len(disk - forensic),
            "catalog_excluded_pedagogical": len(catalog_excluded),
        },
        "drift_paths": drift,
        "phantom_paths": phantoms,
        "outil_only_paths": outil_only,
        "catalog_only_vs_outil_paths": catalog_only_vs_outil,
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
    print(f"Outil     : {len(outil):>5} notebooks (count_notebooks_by_series pedagogical)")
    print()
    print(f"Exclusions forensic : {len(disk) - len(forensic)} notebooks (archives, TrashBin...)")
    print(f"Exclusions catalogue: {len(catalog_excluded)} notebooks (research/archive/examples/partner-course)")
    print(f"Catalogue attendu   : {len(catalog_expected)} (forensic - exclusions catalogue)")
    print(f"Catalogue reel      : {len(catalog)}")
    print(f"DRIFT catalogue     : {len(drift)} notebooks cures manquants")
    print()
    print(f"DIVERGENCE catalogue vs outil : {len(outil_only)} outil-only, {len(catalog_only_vs_outil)} catalogue-only")
    if outil_only:
        print(f"--- OUTIL non catalogue ({len(outil_only)}) ---")
        for p in outil_only[:20]:
            print(f"  > {p}")
        if len(outil_only) > 20:
            print(f"  ... et {len(outil_only) - 20} autres")
    if catalog_only_vs_outil:
        print(f"--- CATALOGUE non outil ({len(catalog_only_vs_outil)}) ---")
        for p in catalog_only_vs_outil[:20]:
            print(f"  < {p}")
    if not outil_only and not catalog_only_vs_outil:
        print("OK : catalogue == outil (ensembles identiques)")
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

    # Divergence catalogue vs outil : un ecart explique par les exclusions EXTRA
    # du catalogue (_archive/_archives/output, cf notebook-counters.md §5) est
    # DOCUMENTE ; le reste est du drift non-explique -> --strict rougit.
    catalog_extra_exclusions = {"_archive", "_archives", "output"}
    outil_only_undocumented = sorted(
        p for p in outil_only
        if not any(exc in p for exc in catalog_extra_exclusions)
    )

    if args.strict and (drift or phantoms or catalog_only_vs_outil or outil_only_undocumented):
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
