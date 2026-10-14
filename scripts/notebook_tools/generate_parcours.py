#!/usr/bin/env python3
"""Generate student learning paths (parcours) from the notebook catalog.

Reads COURSE_CATALOG.generated.json and filters notebooks into 5 pedagogical
paths, outputting structured markdown pages under docs/curriculum/.

Usage:
    python generate_parcours.py                       # Generate all parcours
    python generate_parcours.py --check               # Verify coverage
    python generate_parcours.py --parcours ia-classique  # Single path
    python generate_parcours.py --dry-run             # Preview without writing
    python generate_parcours.py --manifest branches.json --branch search --accretion csp

Composition manifest (explicit catalog paths, no automatic numbering inference):
    {"branches": [{"id": "search", "notebooks": ["Search/Part1/Search-1.ipynb"]}],
     "accretions": [{"id": "csp", "branch": "search",
                     "notebooks": ["Search/Part2/CSP-1.ipynb"]}]}
    Each group may specify "prerequisites": ["another-selected-id"]. Composition
    writes JSON to stdout and never modifies the five generated curriculum pages.

Parcours definitions:
    ia-classique    — Search/CSP/Sudoku + heuristics + classical algorithms
    ia-symbolique   — Lean/Tweety/SemanticWeb/Planning/SmartContracts
    genai           — GenAI Image/Audio/Video/Text + Vibe-Coding
    trading         — QuantConnect + ML training + Probas
    recherche       — Probas (Infer/Pyro) + IIT + RL + advanced topics
"""

import argparse
import json
import re
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


def compile_parcours(
    entries: list[dict], manifest: dict, branches: list[str],
    accretions: list[str] | None = None,
) -> dict:
    """Compose an explicit subset of canonical branches and optional accretions.

    The manifest owns pedagogical grouping and prerequisites: filename numbering
    alone cannot distinguish twins, missing bases or cross-series dependencies.
    Missing catalog metadata remains unknown rather than being inferred.
    """
    accretions = accretions or []
    if not isinstance(manifest, dict):
        raise TypeError("Manifest must be a JSON object")
    if (not branches or len(branches) != len(set(branches))
            or len(accretions) != len(set(accretions))):
        raise ValueError("Select at least one branch, without duplicate selections")

    groups: dict[str, dict] = {}
    for kind in ("branches", "accretions"):
        definitions = manifest.get(kind, [])
        if not isinstance(definitions, list):
            raise TypeError(f"Manifest {kind} must be a list")
        for group in definitions:
            if not isinstance(group, dict) or not isinstance(group.get("id"), str):
                raise TypeError(f"Invalid {kind} definition")
            group_id = group["id"]
            if not group_id or group_id in groups:
                raise ValueError(f"Duplicate or empty group id: {group_id!r}")
            paths = group.get("notebooks")
            if not isinstance(paths, list) or not paths or any(
                not isinstance(path, str) or not path for path in paths
            ) or len(paths) != len(set(paths)):
                raise ValueError(f"Group {group_id} needs distinct explicit notebook paths")
            prerequisites = group.get("prerequisites", [])
            if not isinstance(prerequisites, list) or any(
                not isinstance(dep, str) for dep in prerequisites
            ):
                raise ValueError(f"Invalid prerequisites for {group_id}")
            groups[group_id] = {**group, "kind": kind}

    selected = branches + accretions
    for group_id in selected:
        if group_id not in groups or (groups[group_id]["kind"] == "branches") != (group_id in branches):
            raise ValueError(f"Unknown or misclassified selection: {group_id}")
    for group_id in accretions:
        parent = groups[group_id].get("branch")
        if parent not in branches:
            raise ValueError(f"Accretion {group_id} requires selected branch {parent}")

    catalog = {entry["path"]: entry for entry in entries}
    if len(catalog) != len(entries):
        raise ValueError("Duplicate paths in catalog")
    seen_paths: set[str] = set()
    ordered: list[str] = []
    visiting: set[str] = set()

    def visit(group_id: str) -> None:
        if group_id in visiting:
            raise ValueError(f"Prerequisite cycle at {group_id}")
        if group_id in ordered:
            return
        visiting.add(group_id)
        group = groups[group_id]
        dependencies = group.get("prerequisites", [])
        if group["kind"] == "accretions":
            dependencies = [group["branch"], *dependencies]
        for dep in dependencies:
            if dep not in selected:
                raise ValueError(f"Missing selected prerequisite {dep} for {group_id}")
            visit(dep)
        visiting.remove(group_id)
        ordered.append(group_id)

    for group_id in selected:
        visit(group_id)

    result = []
    total_minutes = 0
    duration_known = True
    for group_id in ordered:
        group = groups[group_id]
        notebooks = []
        for path in group["notebooks"]:
            if not isinstance(path, str) or path not in catalog:
                raise ValueError(f"Notebook absent from catalog: {path!r}")
            if path in seen_paths:
                raise ValueError(f"Notebook selected twice: {path}")
            seen_paths.add(path)
            entry = catalog[path]
            if entry.get("status") == "BROKEN":
                raise ValueError(f"Broken notebook selected: {path}")
            duration = entry.get("duree_estimee")
            match = (
                re.fullmatch(r"(\d+)\s*min|(\d+)h(?:(\d{1,2}))?", duration.strip(),
                             re.IGNORECASE)
                if isinstance(duration, str) else None
            )
            minutes = (
                int(match[1]) if match[1] else 60 * int(match[2]) + int(match[3] or 0)
            ) if match else None
            if minutes is None:
                duration_known = False
            else:
                total_minutes += minutes
            notebooks.append({
                "path": path,
                "title": entry.get("title", path),
                "duration_minutes": minutes,
                "kernel": entry.get("kernel"),
                "execution_constraints": {
                    key: entry.get(key) for key in (
                        "requires_api", "requires_gpu", "requires_cloud", "requires_wsl",
                        "executable_locally",
                    )
                },
            })
        result.append({
            "id": group_id,
            "kind": group["kind"],
            "prerequisites": ([group["branch"]] if group["kind"] == "accretions" else [])
            + group.get("prerequisites", []),
            "notebooks": notebooks,
        })
    return {"groups": result, "duration_minutes": total_minutes if duration_known else None,
            "known_duration_minutes": total_minutes}


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
    parser.add_argument(
        "--manifest", type=Path,
        help="JSON manifest defining canonical branches and optional accretions",
    )
    parser.add_argument(
        "--branch", action="append", default=[],
        help="Canonical branch id to include (repeat for multiple branches)",
    )
    parser.add_argument(
        "--accretion", action="append", default=[],
        help="Optional accretion id to include (repeat as needed)",
    )
    args = parser.parse_args()

    if args.manifest or args.branch or args.accretion:
        if not args.manifest or not args.branch or args.check or args.parcours or args.dry_run:
            parser.error("Composition requires --manifest and --branch; incompatible with legacy options")
        entries = load_catalog()
        try:
            manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
            result = compile_parcours(entries, manifest, args.branch, args.accretion)
        except (OSError, ValueError, TypeError, json.JSONDecodeError) as exc:
            parser.error(str(exc))
        print(json.dumps(result, ensure_ascii=False, indent=2))
        return

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
