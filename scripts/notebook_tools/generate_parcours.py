#!/usr/bin/env python3
"""Generate student learning paths (parcours) from the notebook catalog.

Reads COURSE_CATALOG.generated.json and filters notebooks into 5 pedagogical
paths, outputting structured markdown pages under docs/parcours/.

Usage:
    python generate_parcours.py                       # Generate all parcours
    python generate_parcours.py --check               # Verify coverage
    python generate_parcours.py --parcours ia-classique  # Single path
    python generate_parcours.py --dry-run             # Preview without writing

Parcours definitions:
    ia-classique    — Search/CSP/Sudoku + heuristics + classical algorithms
    ia-symbolique   — Lean/Tweety/SemanticWeb/Planning/SmartContracts
    genai           — GenAI Image/Audio/Video/Text + Vibe-Coding
    trading         — QuantConnect + ML training + Probas
    recherche       — Probas (Infer/Pyro) + IIT + RL + advanced topics
"""

import argparse
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
CATALOG_PATH = REPO_ROOT / "COURSE_CATALOG.generated.json"
PARCOURS_DIR = REPO_ROOT / "docs" / "parcours"

PARCOURS = {
    "ia-classique": {
        "title": "IA Classique",
        "subtitle": "Recherche, CSP et resolution de problemes",
        "description": (
            "Algorithmes de recherche classique, satisfaction de contraintes (CSP), "
            "resolution de Sudoku, planification classique. De A* aux heuristiques "
            "avancees, en passant par les solveurs SAT/SMT."
        ),
        "series": ["Search", "Sudoku"],
        "sous_series_keywords": ["CSP", "Classical", "SAT"],
        "maturity_filter": ["PRODUCTION", "BETA"],
        "icon": "search",
    },
    "ia-symbolique": {
        "title": "IA Symbolique",
        "subtitle": "Preuves formelles, logique et planification",
        "description": (
            "Preuves formelles en Lean 4, logique probabiliste avec Tweety, "
            "web semantique, planification classique et avancee, contrats intelligents. "
            "Du raisonnement deductif a la verification formelle."
        ),
        "series": ["SymbolicAI"],
        "maturity_filter": ["PRODUCTION", "BETA", "ALPHA"],
        "icon": "symbolic",
    },
    "genai": {
        "title": "GenAI Multimodale",
        "subtitle": "Generation d'images, audio, video et texte",
        "description": (
            "Generation d'images (DALL-E, Stable Diffusion, Qwen, ComfyUI), "
            "synthese vocale, generation musicale, video, et orchestration de modeles. "
            "Inclut les workflows Vibe-Coding et les pipelines de production."
        ),
        "series": ["GenAI"],
        "maturity_filter": ["PRODUCTION", "BETA", "ALPHA"],
        "icon": "genai",
    },
    "trading": {
        "title": "Trading Algoritmique",
        "subtitle": "QuantConnect, ML applique et probabilites",
        "description": (
            "Strategies de trading algorithmique avec QuantConnect, pipeline ML "
            "(Transformer, DQN, LSTM), indicateurs techniques avances, et modeles "
            "probabilistes. Du backtesting basique au reinforcement learning."
        ),
        "series": ["QuantConnect", "ML", "Probas"],
        "maturity_filter": ["PRODUCTION", "BETA", "ALPHA"],
        "icon": "trading",
    },
    "recherche": {
        "title": "Recherche Avancee",
        "subtitle": "Inference probabiliste, IIT et RL avance",
        "description": (
            "Inference probabiliste (Infer.NET, Pyro, PyMC), theorie de l'information "
            "integree (IIT), reinforcement learning avance, theorie des jeux "
            "(OpenSpiel). Pour etudiants en master/recherche."
        ),
        "series": ["Probas", "IIT", "RL", "GameTheory"],
        "maturity_filter": ["PRODUCTION", "BETA", "ALPHA"],
        "icon": "research",
    },
}


def load_catalog() -> list[dict]:
    if not CATALOG_PATH.exists():
        print(f"Error: {CATALOG_PATH} not found. Run generate_catalog.py first.")
        sys.exit(1)
    return json.loads(CATALOG_PATH.read_text(encoding="utf-8"))


def filter_for_parcours(entries: list[dict], parcours_id: str) -> list[dict]:
    """Filter catalog entries for a specific parcours."""
    config = PARCOURS[parcours_id]
    series_set = set(config["series"])
    maturity_set = set(config["maturity_filter"])
    keywords = config.get("sous_series_keywords", [])

    filtered = []
    for entry in entries:
        if entry.get("serie") not in series_set:
            continue
        if entry.get("maturity") not in maturity_set:
            continue
        if entry.get("status") == "BROKEN":
            continue
        filtered.append(entry)

    return filtered


def generate_parcours_page(
    parcours_id: str,
    entries: list[dict],
) -> str:
    """Generate markdown page for a single parcours."""
    config = PARCOURS[parcours_id]
    lines = [
        f"# {config['title']}",
        "",
        f"**{config['subtitle']}**",
        "",
        config["description"],
        "",
    ]

    by_serie = {}
    for e in entries:
        s = e["serie"]
        ss = e.get("sous_serie", "")
        key = f"{s}/{ss}" if ss else s
        by_serie.setdefault(key, []).append(e)

    total = len(entries)
    prod = sum(1 for e in entries if e.get("maturity") == "PRODUCTION")
    beta = sum(1 for e in entries if e.get("maturity") == "BETA")
    alpha = sum(1 for e in entries if e.get("maturity") == "ALPHA")

    lines.extend([
        f"## Statistiques",
        "",
        f"| Metrique | Valeur |",
        f"|----------|--------|",
        f"| Notebooks | {total} |",
        f"| PRODUCTION | {prod} |",
        f"| BETA | {beta} |",
        f"| ALPHA | {alpha} |",
        "",
    ])

    for key, items in sorted(by_serie.items()):
        lines.extend([
            f"## {key} ({len(items)} notebooks)",
            "",
            f"| # | Notebook | Maturite | Executable |",
            f"|---|----------|----------|------------|",
        ])
        for i, e in enumerate(items, 1):
            name = e["title"][:55]
            maturity = e.get("maturity", "?")
            exe = "Oui" if e.get("executable_locally") else "Non"
            lines.append(f"| {i} | {name} | {maturity} | {exe} |")
        lines.append("")

    return "\n".join(lines)


def check_coverage(entries: list[dict]) -> None:
    """Check that all PRODUCTION/BETA non-BROKEN notebooks are covered."""
    prod_beta = [
        e for e in entries
        if e.get("maturity") in ("PRODUCTION", "BETA")
        and e.get("status") != "BROKEN"
    ]

    covered = set()
    for pid in PARCOURS:
        for e in filter_for_parcours(entries, pid):
            covered.add(e["path"])

    uncovered = [e for e in prod_beta if e["path"] not in covered]
    total_pb = len(prod_beta)

    print(f"Coverage: {len(covered)}/{total_pb} PRODUCTION/BETA non-BROKEN notebooks")
    if uncovered:
        print(f"\nUncovered ({len(uncovered)}):")
        for e in uncovered:
            print(f"  {e['path']} ({e.get('maturity')}, {e.get('serie')})")
    else:
        print("100% PRODUCTION/BETA covered!")


def main():
    parser = argparse.ArgumentParser(
        description="Generate CoursIA student learning paths (parcours)"
    )
    parser.add_argument(
        "--check", action="store_true",
        help="Check coverage of PRODUCTION/BETA notebooks",
    )
    parser.add_argument(
        "--parcours", type=str, default=None,
        choices=list(PARCOURS.keys()),
        help="Generate only a specific parcours",
    )
    parser.add_argument(
        "--dry-run", action="store_true",
        help="Preview output without writing files",
    )
    args = parser.parse_args()

    entries = load_catalog()

    if args.check:
        check_coverage(entries)
        return

    targets = [args.parcours] if args.parcours else list(PARCOURS.keys())

    for pid in targets:
        filtered = filter_for_parcours(entries, pid)
        page = generate_parcours_page(pid, filtered)

        if args.dry_run:
            print(f"\n{'='*60}")
            print(f"  {pid} ({len(filtered)} notebooks)")
            print(f"{'='*60}")
            print(page[:500] + "..." if len(page) > 500 else page)
        else:
            PARCOURS_DIR.mkdir(parents=True, exist_ok=True)
            out_path = PARCOURS_DIR / f"{pid}.md"
            out_path.write_text(page, encoding="utf-8")
            print(f"  {pid}: {out_path} ({len(filtered)} notebooks)")

    if not args.dry_run and not args.parcours:
        print(f"\nGenerated {len(targets)} parcours pages in {PARCOURS_DIR}")


if __name__ == "__main__":
    main()
