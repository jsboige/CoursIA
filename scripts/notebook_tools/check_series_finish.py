"""check_series_finish.py -- verifie qu'une serie respecte les criteres de finition.

Criteres (cf docs/reference/finition-de-serie.md, valide mainteneur 2026-10-05) :

1. **Objectifs de serie** : le README de la serie a une section `## Objectifs d'apprentissage`
   (ou `## Competences`, en titre strict -- pas une phrase en prose).
2. **Blocs de fin de carnet** : chaque carnet du chemin principal a 3 blocs markdown
   en TITRE de niveau 2 (H2) :
   - `## A retenir`
   - `## Verifiez votre comprehension`
   - `## Pour aller plus loin`
3. **Capstone** : signale dans le README si pas applicable (phrase "Pas de capstone").

Le chemin principal exclut les sous-dossiers archive/output, et ne considere que les
carnets presents au top-level d'une sous-serie (pas les recursifs profond).

Usage :
    python scripts/notebook_tools/check_series_finish.py --series ML
    python scripts/notebook_tools/check_series_finish.py --series ML --json
    python scripts/notebook_tools/check_series_finish.py --series ML --report

Codes de sortie :
    0 : serie finie (tous criteres remplis)
    1 : serie non finie (au moins 1 carnet manque un bloc, ou README sans Objectifs)
    2 : erreur (serie inconnue, JSON mal forme, etc.)
"""
import argparse
import collections
import glob
import json
import os
import re
import sys
import unicodedata


SERIES_ROOT = "MyIA.AI.Notebooks"
ARCHIVE_FRAGMENT = "_archive"
OUTPUT_FRAGMENT = "_output"
CHECKPOINT_FRAGMENT = ".ipynb_checkpoints"

# Patterns des 3 blocs (regex tolerant aux accents et a la casse)
# IMPORTANT : `#{2,3}` strict -- un H1 (`#`) ne compte pas (le doc dit H2)
BLOCK_PATTERNS = {
    "a_retenir": re.compile(r"^#{2,3}\s*(à retenir|a retenir|key takeaways?)\s*$", re.IGNORECASE),
    "verifiez": re.compile(
        r"^#{2,3}\s*(vérifiez votre compréhension|verifiez votre comprehension|"
        r"check your understanding|questions? de comprehension|auto-?évaluation|auto-?evaluation)\s*$",
        re.IGNORECASE,
    ),
    "aller_plus_loin": re.compile(
        r"^#{2,3}\s*(pour aller plus loin|going further|further reading)\s*$", re.IGNORECASE
    ),
}

# README : titre strict `## Objectifs` ou `## Competences` (H2 ou H3 uniquement)
README_OBJECTIFS = re.compile(r"^#{2,3}\s*(objectifs?( d['’]apprentissage)?|compétences|competences|learning objectives)\s*$", re.IGNORECASE)
README_CAPSTONE_NONE = re.compile(
    r"(pas de capstone|aucun capstone|no capstone|pas de projet de synthèse|"
    r"no capstone project|does not apply|non applicable|n/?a)",
    re.IGNORECASE,
)


def _norm(t: str) -> str:
    """Normalise unicode vers ASCII lowercase pour la recherche tolérante."""
    return unicodedata.normalize("NFKD", t).encode("ascii", "ignore").decode().lower()


def list_series_notebooks(series: str) -> list[str]:
    """Liste les .ipynb du chemin principal d'une série.

    Exclut : _archive, _output, .ipynb_checkpoints, et les sous-dossiers profonds
    (on considere les carnets a 1 niveau de profondeur max dans chaque sous-série,
    plus les .ipynb au top-level de la serie).
    """
    from pathlib import Path
    root = Path(SERIES_ROOT) / series
    if not root.is_dir():
        return []
    notebooks = []
    for p in root.rglob("*.ipynb"):
        rel = p.relative_to(root).as_posix()
        if any(frag in rel.split("/") for frag in (ARCHIVE_FRAGMENT, OUTPUT_FRAGMENT, CHECKPOINT_FRAGMENT)):
            continue
        depth = rel.count("/")
        if depth > 1:
            continue
        notebooks.append(str(p))
    return sorted(notebooks)


def check_notebook_blocks(path: str) -> dict:
    """Verifie la presence des 3 blocs H2 dans un carnet (markdown cells uniquement)."""
    try:
        with open(path, encoding="utf-8") as fh:
            nb = json.load(fh)
    except Exception as e:
        return {"path": path, "error": f"json_load: {e}", "blocks": {}, "missing": ["__error__"]}
    found = {key: False for key in BLOCK_PATTERNS}
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "markdown":
            continue
        src = "".join(cell.get("source", []))
        for line in src.splitlines():
            for key, pat in BLOCK_PATTERNS.items():
                if pat.match(line.strip()):
                    found[key] = True
    missing = [k for k, v in found.items() if not v]
    return {"path": path, "blocks": found, "missing": missing}


def check_readme(series: str) -> dict:
    """Verifie la presence de `## Objectifs` ou `## Competences` dans le README de la serie."""
    from pathlib import Path
    readme = Path(SERIES_ROOT) / series / "README.md"
    if not readme.exists():
        return {"path": str(readme), "exists": False, "objectifs": False, "capstone_phrase": None}
    try:
        text = readme.read_text(encoding="utf-8")
    except Exception as e:
        return {"path": str(readme), "exists": True, "objectifs": False, "error": f"read: {e}"}
    objectifs = False
    capstone_phrase = None
    for line in text.splitlines():
        if README_OBJECTIFS.match(line.strip()):
            objectifs = True
        m = README_CAPSTONE_NONE.search(line)
        if m and capstone_phrase is None:
            capstone_phrase = m.group(0)
    return {"path": str(readme), "exists": True, "objectifs": objectifs, "capstone_phrase": capstone_phrase}


def run_check(series: str) -> dict:
    """Orchestre la verification d'une serie et retourne un dict verdict."""
    if not series or "/" in series or "\\" in series or series.startswith("."):
        return {"series": series, "error": "invalid_series_name", "finished": False, "rc": 2}
    if not os.path.isdir(os.path.join(SERIES_ROOT, series)):
        return {"series": series, "error": "series_not_found", "finished": False, "rc": 2}
    notebooks = list_series_notebooks(series)
    carnet_results = [check_notebook_blocks(p) for p in notebooks]
    readme_result = check_readme(series)
    carnets_with_missing = [r for r in carnet_results if r.get("missing")]
    carnet_total = len(notebooks)
    carnet_finis = sum(1 for r in carnet_results if not r.get("missing"))
    finished = (
        readme_result.get("objectifs", False)
        and len(carnets_with_missing) == 0
        and carnet_total > 0
    )
    return {
        "series": series,
        "rc": 0 if finished else 1,
        "finished": finished,
        "readme": readme_result,
        "carnet_total": carnet_total,
        "carnet_finis": carnet_finis,
        "carnets_manquants": [
            {"path": r["path"], "missing": r["missing"]} for r in carnets_with_missing
        ],
    }


def render_text(verdict: dict) -> str:
    """Rendu texte humain pour le mode --report."""
    if verdict.get("error"):
        return f"ERREUR: {verdict['error']} (serie={verdict.get('series')})"
    out = []
    out.append(f"Serie : {verdict['series']}")
    out.append(f"Verdict : {'FINIE' if verdict['finished'] else 'NON FINIE'} (rc={verdict['rc']})")
    out.append(f"README : {verdict['readme']['path']}")
    out.append(f"  - existe : {verdict['readme']['exists']}")
    out.append(f"  - section Objectifs : {verdict['readme']['objectifs']}")
    if verdict["readme"].get("capstone_phrase"):
        out.append(f"  - phrase capstone : {verdict['readme']['capstone_phrase']}")
    out.append(f"Carnets : {verdict['carnet_finis']}/{verdict['carnet_total']} ont les 3 blocs")
    if verdict["carnets_manquants"]:
        out.append("Carnets manquants (au moins 1 bloc) :")
        for cm in verdict["carnets_manquants"][:20]:
            rel = cm["path"].replace(os.sep, "/")
            out.append(f"  - {rel} : manque {cm['missing']}")
        if len(verdict["carnets_manquants"]) > 20:
            out.append(f"  ... et {len(verdict['carnets_manquants']) - 20} autres")
    return "\n".join(out)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--series", required=True, help="Nom de la serie (sous-dossier de MyIA.AI.Notebooks/)")
    p.add_argument("--json", action="store_true", help="Sortie JSON")
    p.add_argument("--report", action="store_true", help="Sortie rapport texte")
    args = p.parse_args(argv)

    verdict = run_check(args.series)
    if args.json and not args.report:
        print(json.dumps(verdict, ensure_ascii=False, indent=2))
    else:
        print(render_text(verdict))
    return verdict["rc"]


if __name__ == "__main__":
    sys.exit(main())
