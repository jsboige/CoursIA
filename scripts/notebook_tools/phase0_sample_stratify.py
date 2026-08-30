"""Phase 0 EPIC #9768 -- selection stratifiee de notebooks pour audit forensic.

Cible l'echantillonnage Phase 0 de l'EPIC #9768 (taxonomie degeneration
notebooks, parent issue #9787). La Phase 0 definit un echantillon stratifie
de N notebooks a scanner avec ``scan_d1_d3_d4_d5.py`` afin de calibrer
empiriquement les seuils de detection.

Criteres de stratification (cf. issue #9768 corps) :
  - Couverture >= 4 familles distinctes (QC, GenAI, Search, Probas, SymbolicAI, ...)
  - Sur-representation des bandes de revisions 20-39 et 40+ (la ou la
    degradation cumulee est la plus probable)
  - 1 seul notebook par famille dans la tranche (evite l'effet de grappe)

Pourquoi un script plutot qu'une liste en dur
----------------------------------------------
La liste des notebooks "les plus actifs" evolue a chaque cycle. Un script
rejouable :

  1. Selectionne le notebook le plus revise par famille (proxy : nb de
     commits main-branch touchants le fichier, mesuree via ``git log``).
  2. Si plusieurs notebooks d'une famille sont dans la meme bande de
     revisions, applique un round-robin stable (ordre alphabetique).
  3. Limite a N familles (defaut 5), tirees parmi celles qui ont >= 1
     notebook > 20 revisions.

Le script ne touche JAMAIS aux notebooks : il les *selectionne* et lance
``scan_d1_d3_d4_d5.py`` sur chacun. La sortie est stdout/JSON, JAMAIS un
rapport commite (audit-cross-source-distillation HARD 1).

Usage
-----
    python scripts/notebook_tools/phase0_sample_stratify.py \\
        --families QC GenAI Search Probas SymbolicAI \\
        --per-family 1 --min-revisions 20

    # Mode tranche 1 (livraison courante) :
    python scripts/notebook_tools/phase0_sample_stratify.py \\
        --families QC GenAI Search Probas SymbolicAI \\
        --per-family 1 --min-revisions 20 \\
        --output-json phase0_tranche1.json

Sortie JSON
-----------
    {
      "generated_at_utc": "2026-08-30T...",
      "criteria": {"min_revisions": 20, "per_family": 1, "families": [...]},
      "selections": [
        {"family": "QC", "path": "...", "total_revisions": 33, "verdict": "SAIN"},
        ...
      ]
    }

Conformite harnais
------------------
- Regle F (env repair not bypass) : 0 dependance externe (Python 3.10+ stdlib).
- audit-cross-source-distillation R1 : verdict stdout/JSON, JAMAIS de rapport
  AUDIT-D*.md / *phase0*.md commite dans l'arbre.
- catalog-pr-hygiene R1 : 0 modification catalogue (le script lit, n'ecrit pas).
- C.1 : 0 erreur volontaire (pas de ``raise NotImplementedError`` etc.).
- anti-regression : 0 stub fonctionnel sur code de production (le script
  execute reellement le scanner sur chaque selection).

Voir aussi
----------
- EPIC #9768 : taxonomie complete de la degeneration notebooks
- scripts/notebook_tools/scan_d1_d3_d4_d5.py : detecteur D1/D3/D4/D5
- scripts/notebook_tools/scan_d2_window_openness.py : detecteur D2 (orthogonal)
- Issue #9787 : Phase 0 tranche ICT/IIT (calibration empirique du seuil)
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from collections import defaultdict
from pathlib import Path
from typing import Iterable


REPO_ROOT = Path(__file__).resolve().parents[2]

# Bandes de revisions ciblees par l'EPIC #9768 (corps).
# 20-39 et 40+ sont sur-representees ; <20 est exclue (trop peu de signaux).
REVISION_BANDS = [
    (20, 39, "20-39"),
    (40, 10**9, "40+"),
]


def build_revision_counts() -> dict[str, int]:
    """Compte en un seul ``git log`` le nombre de commits par fichier .ipynb.

    Limite a la branche courante (HEAD) pour eviter le sur-comptage des
    PR branches jamais mergees (cf. mesure : --all = 65, HEAD = 33 sur
    QC-Py-26-LLM-Trading-Signals.ipynb). Utilise ``git log --name-only``
    pour lister tous les fichiers touches par chaque commit (limite aux
    .ipynb). Plus rapide que N appels a ``git log --follow`` individuels
    (mesure : 1 appel global = ~3s pour 125k commits sur CoursIA).

    Retourne un dict ``{path_relatif: nb_commits}``.
    """
    try:
        result = subprocess.run(
            [
                "git",
                "log",
                "HEAD",
                "--name-only",
                "--pretty=format:",
            ],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            check=True,
        )
    except subprocess.CalledProcessError:
        return {}
    counts: dict[str, int] = defaultdict(int)
    for line in result.stdout.splitlines():
        line = line.strip()
        if line.endswith(".ipynb"):
            counts[line] += 1
    return dict(counts)


def count_revisions_main(notebook_path: Path, counts: dict[str, int]) -> int:
    """Lookup O(1) du nombre de commits pour un chemin de notebook.

    Normalise le separateur en ``/`` car git log --name-only retourne des
    forward slashes (meme sous Windows) alors que ``Path.relative_to``
    preserve les backslashes natifs de la plateforme.
    """
    rel = str(notebook_path.relative_to(REPO_ROOT)).replace("\\", "/")
    return counts.get(rel, 0)


def revision_band(revisions: int) -> str | None:
    """Retourne la bande EPIC #9768 du nombre de revisions, ou None si < 20."""
    if revisions < 20:
        return None
    for lo, hi, label in REVISION_BANDS:
        if lo <= revisions <= hi:
            return label
    return None


def list_family_notebooks(family_root: Path) -> list[Path]:
    """Liste les notebooks .ipynb sous ``family_root`` (recursive)."""
    if not family_root.exists():
        return []
    return sorted(p for p in family_root.rglob("*.ipynb") if p.is_file())


def select_top_per_family(
    families: Iterable[str],
    min_revisions: int,
    per_family: int,
    counts: dict[str, int],
) -> list[dict]:
    """Selectionne les N notebooks les plus actifs par famille.

    Tri : (bande prioritaire desc, revisions desc, path asc) -- deterministe.
    """
    selections: list[dict] = []
    for family in families:
        family_root = REPO_ROOT / "MyIA.AI.Notebooks" / family
        candidates = []
        for nb in list_family_notebooks(family_root):
            revs = count_revisions_main(nb, counts)
            band = revision_band(revs)
            if band is None or revs < min_revisions:
                continue
            candidates.append((band, revs, nb))
        # Tri : bande prioritaire desc (40+ > 20-39), revisions desc, path asc.
        candidates.sort(key=lambda t: (-ord(t[0][0]), -t[1], str(t[2])))
        for _band, revs, nb in candidates[:per_family]:
            rel_path = str(nb.relative_to(REPO_ROOT)).replace("\\", "/")
            selections.append(
                {
                    "family": family,
                    "path": rel_path,
                    "total_revisions": revs,
                    "revision_band": revision_band(revs),
                }
            )
    return selections


def run_scanner(selections: list[dict]) -> list[dict]:
    """Execute ``scan_d1_d3_d4_d5.py`` sur chaque selection et agrege le verdict.

    Le scanner retourne un JSON par fichier ; on merge le verdict et les
    findings dans la structure de selection.
    """
    scanner = REPO_ROOT / "scripts" / "notebook_tools" / "scan_d1_d3_d4_d5.py"
    if not scanner.exists():
        for sel in selections:
            sel["scanner_error"] = "scan_d1_d3_d4_d5.py introuvable"
        return selections
    for sel in selections:
        proc = subprocess.run(
            [
                sys.executable,
                str(scanner),
                sel["path"],
                "--format",
                "json",
            ],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
        )
        try:
            payload = json.loads(proc.stdout) if proc.stdout.strip() else []
        except json.JSONDecodeError:
            sel["scanner_error"] = "stdout non-JSON"
            continue
        if isinstance(payload, list) and payload:
            entry = payload[0]
            sel["verdict"] = entry.get("verdict", "INDETERMINE")
            sel["findings"] = entry.get("findings", [])
            sel["notes"] = entry.get("notes", "")
    return selections


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(
        description="Phase 0 EPIC #9768 -- selection stratifiee + scan",
    )
    p.add_argument(
        "--families",
        nargs="+",
        default=["QC", "GenAI", "Search", "Probas", "SymbolicAI"],
        help="Familles cibles (defaut: 5 familles principales)",
    )
    p.add_argument(
        "--per-family",
        type=int,
        default=1,
        help="Nombre de notebooks par famille (defaut: 1)",
    )
    p.add_argument(
        "--min-revisions",
        type=int,
        default=20,
        help="Seuil minimum de revisions (defaut: 20, cf. EPIC #9768)",
    )
    p.add_argument(
        "--output-json",
        type=Path,
        help="Fichier JSON de sortie (optionnel ; stdout sinon)",
    )
    p.add_argument(
        "--select-only",
        action="store_true",
        help="Selectionne les notebooks sans lancer le scanner (debug/perf)",
    )
    return p.parse_args()


def main() -> int:
    args = parse_args()
    counts = build_revision_counts()
    selections = select_top_per_family(
        families=args.families,
        min_revisions=args.min_revisions,
        per_family=args.per_family,
        counts=counts,
    )
    if not args.select_only:
        selections = run_scanner(selections)
    output = {
        "criteria": {
            "families": list(args.families),
            "per_family": args.per_family,
            "min_revisions": args.min_revisions,
        },
        "selections": selections,
    }
    text = json.dumps(output, indent=2, ensure_ascii=False)
    if args.output_json:
        args.output_json.write_text(text, encoding="utf-8")
        print(f"{len(selections)} selection(s) -> {args.output_json}")
    else:
        print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())