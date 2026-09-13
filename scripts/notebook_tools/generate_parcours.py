#!/usr/bin/env python3
"""Generate student learning paths (parcours) from the notebook catalog.

Reads COURSE_CATALOG.generated.json and filters notebooks into 5 pedagogical
paths, outputting structured markdown pages under docs/curriculum/.

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
from urllib.parse import quote

from generate_catalog import truncate_at_word

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
CATALOG_PATH = REPO_ROOT / "COURSE_CATALOG.generated.json"
PARCOURS_DIR = REPO_ROOT / "docs" / "curriculum"

# Fail-closed (#15882): docs/curriculum/ mixes generated pages (ids of the
# PARCOURS dict, rewritten daily by catalog-cron.yml) with manual pages, and
# nothing in the name tells them apart. A target that exists WITHOUT this
# marker in its opening lines is presumed manual and must never be
# overwritten -- the regen refuses instead. The scan window is limited to the
# head of the file: generated pages carry the marker as their opening comment
# block, and a manual page quoting the phrase mid-body must not opt in by
# accident.
GENERATED_MARKER = "FICHIER GENERE"
GENERATED_MARKER_SCAN_LINES = 15

PARCOURS = {
    "ia-classique": {
        "title": "IA Classique",
        "subtitle": "Recherche, CSP et résolution de problèmes",
        "description": (
            "Algorithmes de recherche classique, satisfaction de contraintes (CSP), "
            "résolution de Sudoku, planification classique. De A* aux heuristiques "
            "avancées, en passant par les solveurs SAT/SMT."
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
            "web sémantique, planification classique et avancée, contrats intelligents. "
            "Du raisonnement déductif à la vérification formelle."
        ),
        "series": ["SymbolicAI"],
        "maturity_filter": ["PRODUCTION", "BETA", "ALPHA"],
        "icon": "symbolic",
    },
    "genai": {
        "title": "GenAI Multimodale",
        "subtitle": "Génération d'images, audio, vidéo et texte",
        "description": (
            "Génération d'images (DALL-E, Stable Diffusion, Qwen, ComfyUI), "
            "synthèse vocale, génération musicale, vidéo, et orchestration de modèles. "
            "Inclut les workflows Vibe-Coding et les pipelines de production."
        ),
        "series": ["GenAI"],
        "maturity_filter": ["PRODUCTION", "BETA", "ALPHA"],
        "icon": "genai",
    },
    "trading": {
        "title": "Trading Algorithmique",
        "subtitle": "QuantConnect, ML appliqué et probabilités",
        "description": (
            "Stratégies de trading algorithmique avec QuantConnect, pipeline ML "
            "(Transformer, DQN, LSTM), indicateurs techniques avancés, et modèles "
            "probabilistes. Du backtesting basique au reinforcement learning."
        ),
        "series": ["QuantConnect", "ML", "Probas"],
        "maturity_filter": ["PRODUCTION", "BETA", "ALPHA"],
        "icon": "trading",
    },
    "recherche": {
        "title": "Recherche Avancée",
        "subtitle": "Inférence probabiliste, IIT et RL avancée",
        "description": (
            "Inférence probabiliste (Infer.NET, Pyro, PyMC), théorie de l'information "
            "intégrée (IIT), reinforcement learning avancé, théorie des jeux "
            "(OpenSpiel). Pour étudiants en master/recherche."
        ),
        "series": ["Probas", "IIT", "RL", "GameTheory"],
        "maturity_filter": ["PRODUCTION", "BETA", "ALPHA"],
        "icon": "research",
    },
}


def _carries_generated_marker(path: Path) -> bool:
    """True si le fichier existant porte l'en-tete de page generee en tete.

    Un echec de lecture (fichier verrouille, illisible) vaut False : ne pas
    pouvoir prouver l'en-tete, c'est ne pas pouvoir ecraser (fail-closed).
    """
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return False
    head = text.splitlines()[:GENERATED_MARKER_SCAN_LINES]
    return any(GENERATED_MARKER in line for line in head)


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
    unresolved: list[str] | None = None,
) -> str:
    """Generate markdown page for a single parcours.

    ``unresolved`` (optional) collects the ``path`` of every catalog entry whose
    notebook is absent from disk; such entries get a BARE label (no markdown
    link) rather than an href that 404s until the next catalogue regeneration.
    """
    config = PARCOURS[parcours_id]
    lines = [
        "<!--",
        "  FICHIER GENERE — ne pas editer a la main.",
        "  Cette page de parcours est derivee du catalogue de notebooks par",
        "  scripts/notebook_tools/generate_parcours.py, puis regeneree chaque jour",
        "  sur `main` par .github/workflows/catalog-cron.yml. Toute edition manuelle",
        "  sera silencieusement ecrasee au prochain passage du cron. Pour corriger",
        "  une derive (comptes, enumerations), corriger la SOURCE (le catalogue /",
        "  les metadonnees de notebook) ou le generateur — jamais cette page.",
        "  Cf .claude/rules/catalog-pr-hygiene.md (les artefacts generes",
        "  appartiennent a l'automatisation).",
        "-->",
        "",
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
        f"| Métrique | Valeur |",
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
            f"| # | Notebook | Maturité | Exécutable |",
            f"|---|----------|----------|------------|",
        ])
        for i, e in enumerate(items, 1):
            name = truncate_at_word(e["title"], 55)
            # Escaped brackets keep titles like "int[][]" from breaking the
            # link label; quote() percent-encodes spaces/accents in paths
            # (e.g. "Créateur de mail personnalisé.ipynb") for markdown hrefs.
            label = name.replace("[", "\\[").replace("]", "\\]")
            maturity = e.get("maturity", "?")
            exe = "Oui" if e.get("executable_locally") else "Non"
            # Harden against the regen window (#14880): between a rename landing
            # on `main` and the next catalogue regeneration, an entry's path can
            # be absent from disk. Emit a BARE label (no href) rather than a
            # link that 404s, and collect it for the stderr report.
            if (REPO_ROOT / "MyIA.AI.Notebooks" / e["path"]).exists():
                href = quote(f"../../MyIA.AI.Notebooks/{e['path']}")
                cell = f"[{label}]({href})"
            else:
                cell = label
                if unresolved is not None:
                    unresolved.append(e["path"])
            lines.append(f"| {i} | {cell} | {maturity} | {exe} |")
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

    refused: list[Path] = []
    unresolved: list[str] = []
    for pid in targets:
        filtered = filter_for_parcours(entries, pid)
        page = generate_parcours_page(pid, filtered, unresolved)

        if args.dry_run:
            print(f"\n{'='*60}")
            print(f"  {pid} ({len(filtered)} notebooks)")
            print(f"{'='*60}")
            print(page[:500] + "..." if len(page) > 500 else page)
        else:
            PARCOURS_DIR.mkdir(parents=True, exist_ok=True)
            out_path = PARCOURS_DIR / f"{pid}.md"
            if out_path.exists() and not _carries_generated_marker(out_path):
                refused.append(out_path)
                print(
                    f"REFUS (fail-closed, #15882): {out_path} existe sans "
                    f"l'en-tete '{GENERATED_MARKER}' -- page presumee "
                    "MANUELLE, regeneration refusee. Renommer la page "
                    "manuelle, ou lui faire porter l'en-tete si elle doit "
                    "etre generee.",
                    file=sys.stderr,
                )
                continue
            # newline="\n" forces LF: on Windows, Path.write_text's default
            # text mode translates "\n" -> "\r\n", polluting the committed LF
            # files (docs/curriculum/*.md are LF per .gitattributes) with a
            # 100%+ line churn on every regen. Force LF so regen is byte-clean.
            out_path.write_text(page, encoding="utf-8", newline="\n")
            print(f"  {pid}: {out_path} ({len(filtered)} notebooks)")

    if unresolved:
        print(
            "WARNING: catalog entries whose notebook path is absent from disk "
            f"(emitted as bare label, {len(set(unresolved))} unique):",
            file=sys.stderr,
        )
        for p in sorted(set(unresolved)):
            print(f"  {p}", file=sys.stderr)

    if refused:
        print(
            f"{len(refused)} page(s) presumee(s) manuelle(s) refusee(s) par "
            "la regen: " + ", ".join(str(p) for p in refused),
            file=sys.stderr,
        )
        sys.exit(2)

    if not args.dry_run and not args.parcours:
        print(f"\nGenerated {len(targets)} parcours pages in {PARCOURS_DIR}")


if __name__ == "__main__":
    main()
