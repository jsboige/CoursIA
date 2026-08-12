#!/usr/bin/env python3
"""Inventaire residuel des timings machine-dep en prose de notebook.

Issu de l'organe demande par issue #10158 : maintenant que le detecteur
`check_machine_dep_timing.py` existe et categorise wallclock vs distribution_param
vs domain_quantity, **combien de notebooks portent encore un timing runtime
mesure (drainable)** vs une **valeur parametrique/config** (frozen, defensable) ?

Ce script prend la sortie JSON du detecteur et applique une **heuristique de
contexte par mots-cles** pour classer chaque finding en :

- **RUNTIME_MEASURED** : valeur runtime drainable, a remplacer par un ordre
  de grandeur ou une borne superieure dans la prose.
- **RUNTIME_HINT** : config/defense parametrable (timeout, delay, rate-limit)
  defendable mais a contextualiser par un commentaire.
- **CONFIG_PARAMETRIC** : duree de sample audio, taille de chanson, duree
  d'un evenement -- frozen, ne pas toucher.
- **AMBIGUOUS** : contexte insuffisant, revue manuelle requise.

L'heuristique est **calibree sur le corpus** : on sait que la majorite des
findings GenAI/Audio/Video sont des `duration` parametriques, alors que les
benchmarks numeriques (4-digit ms) sont des wallclock mesures. La classification
est conservatrice : en cas de doute, on marque AMBIGUOUS.

Sortie :
- JSON structure (par notebook) pour tooling en aval
- Markdown priorise (par famille) pour lecture humaine

Usage
-----

    # Generer l'inventaire (consomme ~30s sur le corpus complet)
    python measure_residual_machine_dep.py --report

    # Sortie JSON
    python measure_residual_machine_dep.py --json

    # Filtre par chemin (debug)
    python measure_residual_machine_dep.py MyIA.AI.Notebooks/GenAI/Audio

    # CI dry-run
    python measure_residual_machine_dep.py --check

Acceptance (#10158)
- [x] Sortie exploitable (JSON structure + Markdown priorise)
- [x] Mode advisory (exit 0 par defaut, --check pour CI bloquant futur)
- [x] Tests qui prouvent le silence sur les 4 categories
- [x] Inventaire chiffre par famille pour orienter les futures tranches
"""
import argparse
import json
import re
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, List, Tuple

# Heuristic word lists -- calibrate on observed corpus (cf. issue #10158).
# These are deliberately conservative : any snippet whose context does not match
# a known bucket is left as AMBIGUOUS for human triage.

# CONFIG_PARAMETRIC : duree/taille de sample, chanson, evenement -- frozen
# Couvre Audio/Video/GenAI ou "max duration", "jusqu'a X", etc.
CONFIG_KEYWORDS = frozenset([
    "audio", "video", "chanson", "song", "sample", "echantillon",
    "duree", "duree du", "duree de", "taille", "taille du", "taille de",
    "duration", "length", "max duration", "max length", "jusqu'a", "jusqu'à",
    "podcast", "speech", "voix", "voice", "fade", "fade in", "fade out",
    "pause", "silence", "intro", "outro", "episode", "track", "playlist",
    "subtitle", "sous-titre", "chunk", "segment", "window", "fenetre", "fenêtre",
    "horizon", "budget", "limite", "limit", "interval", "intervale",
    "timestep", "step", "step size", "pas de", "taille de",
    # Domain-specific : Gaussian/duration of commute, probas examples, etc.
    # These are **distribution parameters** (mean, observation) not runtime.
    "trajet", "min de trajet", "temps de trajet", "min)", "(min)",
    "obs", "observations", "donnees", "data", "dataset", "data set",
    "ecart-type", "ecart type", "variance", "precision", "priori", "prior",
    "trains", "samples", "epidemic",
    # Numerical: ",XX min" or "~XX min" are typically data-point durations
    "min,", "min.",
])

# RUNTIME_HINT : timeout, delay, rate-limit -- defensable mais a contextualiser
RUNTIME_HINT_KEYWORDS = frozenset([
    "timeout", "timed out", "wait", "waiting", "delay", "delai", "délai",
    "rate limit", "rate-limit", "ratelimit", "throttle", "throttling",
    "snooze", "sleep", "backoff", "retry", "max retries", "max retries",
    "ping interval", "health check", "heartbeat", "keepalive",
])

# RUNTIME_MEASURED : tokens explicites runtime, ou nombres 4-digit
RUNTIME_MEASURED_PATTERNS = [
    re.compile(r"\b\d{4,}\s*(?:ms|s)\b", re.IGNORECASE),  # 1234ms / 1234s
    re.compile(r"\bwallclock\b", re.IGNORECASE),
    re.compile(r"\bwall-?clock\b", re.IGNORECASE),
    re.compile(r"\bmeasured\b", re.IGNORECASE),
    re.compile(r"\bmesur[eé]\b", re.IGNORECASE),
    re.compile(r"\bobserved\b", re.IGNORECASE),
    re.compile(r"\bexecuted in\b", re.IGNORECASE),
    re.compile(r"\btook\b", re.IGNORECASE),
    re.compile(r"\bran for\b", re.IGNORECASE),
    re.compile(r"\bdur[eé]e r[eé]elle\b", re.IGNORECASE),
    re.compile(r"\bbenchmark\b", re.IGNORECASE),
    re.compile(r"\bsolve time\b", re.IGNORECASE),
    re.compile(r"\belapsed\b", re.IGNORECASE),
    re.compile(r"\bVRAM\b"),  # GPU-resource bound -> runtime
    re.compile(r"\bRTX\s*\d{4}\b"),  # GPU-specific
    re.compile(r"\bGPU\b"),
    re.compile(r"\bCPU\s+time\b", re.IGNORECASE),
]

CATEGORIES = ("RUNTIME_MEASURED", "RUNTIME_HINT", "CONFIG_PARAMETRIC", "AMBIGUOUS")


def classify_finding(snippet: str, line: str) -> str:
    """Heuristique conservative : retourne l'une des 4 categories.

    Priorite : RUNTIME_MEASURED > RUNTIME_HINT > CONFIG_PARAMETRIC > AMBIGUOUS.
    Un snippet qui matche RUNTIME_MEASURED ne descend jamais en AMBIGUOUS,
    meme s'il contient aussi un keyword config.
    """
    snippet_l = snippet.lower()
    line_l = line.lower()

    # 1. RUNTIME_MEASURED : tokens explicites runtime
    for pat in RUNTIME_MEASURED_PATTERNS:
        if pat.search(snippet) or pat.search(line):
            return "RUNTIME_MEASURED"

    # 2. RUNTIME_HINT : mots-cles config hydraulique
    for kw in RUNTIME_HINT_KEYWORDS:
        if kw in snippet_l or kw in line_l:
            return "RUNTIME_HINT"

    # 3. CONFIG_PARAMETRIC : mots-cles frozen sample/duree
    for kw in CONFIG_KEYWORDS:
        if kw in snippet_l or kw in line_l:
            return "CONFIG_PARAMETRIC"

    # 4. AMBIGUOUS : contexte insuffisant
    return "AMBIGUOUS"


def load_detector_json(repo_root: Path, paths: List[str] = None) -> dict:
    """Invoque check_machine_dep_timing.py --json et parse la sortie.

    Pour des raisons de cycle, on ne re-invoque pas le detecteur sur le
    corpus complet a chaque classification -- on accepte un JSON pre-genere
    via --json ou on l'invoque si pas fourni.
    """
    detector = repo_root / "scripts" / "notebook_tools" / "check_machine_dep_timing.py"
    if not detector.exists():
        raise FileNotFoundError(f"Detector not found: {detector}")

    cmd = [sys.executable, str(detector), "--all", "--json"]
    if paths:
        cmd = [sys.executable, str(detector), "--json"] + paths

    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=600)
    if proc.returncode != 0:
        raise RuntimeError(
            f"Detector failed (exit {proc.returncode}):\n"
            f"stderr={proc.stderr[:500]}"
        )
    return json.loads(proc.stdout)


def classify_corpus(detector_json: dict) -> dict:
    """Classify all findings, returning structured inventory."""
    scanned = detector_json.get("scanned", 0)
    detector_summary = detector_json.get("summary", {})
    findings = detector_json.get("findings", {})

    classified = {}  # notebook -> list of (cell_index, snippet, line, category)
    by_category = Counter()
    by_family = defaultdict(lambda: Counter())
    by_nb_category = defaultdict(lambda: Counter())  # per-notebook counts

    for nb, items in findings.items():
        nb_classified = []
        for it in items:
            cat = classify_finding(it["snippet"], it["line"])
            nb_classified.append({
                "cell_index": it["cell_index"],
                "line_index": it["line_index"],
                "snippet": it["snippet"],
                "category": cat,
                "detector_category": it.get("category", "wallclock"),
            })
            classified[nb] = nb_classified
            by_category[cat] += 1
            by_nb_category[nb][cat] += 1
            # Family = top-2 path segments (e.g. "GenAI/Audio")
            parts = nb.replace("\\", "/").split("/")
            if len(parts) >= 3:
                family = "/".join(parts[1:3])  # skip MyIA.AI.Notebooks
            else:
                family = "/".join(parts[:-1])
            by_family[family][cat] += 1

    return {
        "scanned": scanned,
        "detector_summary": detector_summary,
        "by_category": dict(by_category),
        "by_family": {fam: dict(c) for fam, c in by_family.items()},
        "by_notebook": {nb: dict(c) for nb, c in by_nb_category.items()},
        "classified": classified,
        "total_classified": sum(by_category.values()),
    }


def render_markdown(inventory: dict, top_n_families: int = 15) -> str:
    """Rapport Markdown priorise : familles triees par drainables."""
    lines = []
    lines.append("# Inventaire residuel machine-dep timings (issue #10158)\n")
    lines.append(f"**Date** : scan `check_machine_dep_timing.py --all` "
                 f"sur **{inventory['scanned']}** notebooks.\n")
    lines.append(f"**Detector summary** : "
                 f"{json.dumps(inventory['detector_summary'])}\n")
    lines.append("\n## Classification par categorie\n")
    lines.append("| Categorie | Count | Signification |\n")
    lines.append("|---|---|---|\n")
    desc = {
        "RUNTIME_MEASURED": "Valeur runtime drainable -- a remplacer par ordre de grandeur ou borne superieure.",
        "RUNTIME_HINT": "Timeout/delay/rate-limit -- defensable mais a contextualiser par un commentaire.",
        "CONFIG_PARAMETRIC": "Duree de sample/taille d'evenement -- frozen, ne pas toucher.",
        "AMBIGUOUS": "Contexte insuffisant -- revue manuelle requise.",
    }
    by_cat = inventory["by_category"]
    for cat in CATEGORIES:
        lines.append(f"| {cat} | {by_cat.get(cat, 0)} | {desc[cat]} |\n")
    lines.append("\n")

    # Top families by drainable (RUNTIME_MEASURED + RUNTIME_HINT + AMBIGUOUS)
    families_drainable = []
    for fam, counts in inventory["by_family"].items():
        drainable = counts.get("RUNTIME_MEASURED", 0) + counts.get("RUNTIME_HINT", 0) + counts.get("AMBIGUOUS", 0)
        frozen = counts.get("CONFIG_PARAMETRIC", 0)
        if drainable + frozen == 0:
            continue
        families_drainable.append((fam, drainable, frozen, counts))
    families_drainable.sort(key=lambda x: -x[1])

    lines.append(f"## Top {top_n_families} familles par drainage potentiel\n")
    lines.append("| Famille | Drainable | Frozen | Total |\n")
    lines.append("|---|---|---|---|\n")
    for fam, drainable, frozen, counts in families_drainable[:top_n_families]:
        total = drainable + frozen
        lines.append(f"| `{fam}` | {drainable} | {frozen} | {total} |\n")
    lines.append("\n")

    # Top notebooks by drainable
    nb_drainable = []
    for nb, counts in inventory["by_notebook"].items():
        drainable = counts.get("RUNTIME_MEASURED", 0) + counts.get("RUNTIME_HINT", 0) + counts.get("AMBIGUOUS", 0)
        if drainable == 0:
            continue
        nb_drainable.append((nb, drainable, counts))
    nb_drainable.sort(key=lambda x: -x[1])

    lines.append(f"## Top 20 notebooks par drainage reel (RUNTIME_MEASURED)\n")
    lines.append("| Notebook | Runtime | Hint | Ambiguous | Frozen |\n")
    lines.append("|---|---|---|---|---|\n")
    for nb, _, counts in nb_drainable[:20]:
        lines.append(
            f"| `{nb.split(chr(92))[-1]}` | "
            f"{counts.get('RUNTIME_MEASURED', 0)} | "
            f"{counts.get('RUNTIME_HINT', 0)} | "
            f"{counts.get('AMBIGUOUS', 0)} | "
            f"{counts.get('CONFIG_PARAMETRIC', 0)} |\n"
        )
    lines.append("\n")

    # Total drainable
    total_drainable = by_cat.get("RUNTIME_MEASURED", 0) + by_cat.get("RUNTIME_HINT", 0) + by_cat.get("AMBIGUOUS", 0)
    total_frozen = by_cat.get("CONFIG_PARAMETRIC", 0)
    lines.append(f"## Synthese executoire\n")
    lines.append(f"- **Drainable total** : {total_drainable} findings "
                 f"(RUNTIME_MEASURED + RUNTIME_HINT + AMBIGUOUS)\n")
    lines.append(f"- **Frozen (a ne pas toucher)** : {total_frozen} findings "
                 f"(CONFIG_PARAMETRIC)\n")
    lines.append(f"- **Ratio drainage** : {total_drainable / max(1, total_drainable + total_frozen):.1%}\n")
    lines.append("\n")
    lines.append("Prochaine tranche : prendre la famille avec le plus de "
                 "RUNTIME_MEASURED strict (cf. table ci-dessus) et drainer "
                 "manuellement, puis re-lancer ce script.\n")

    return "".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--json", action="store_true", help="Sortie JSON structuree")
    parser.add_argument("--report", action="store_true", help="Sortie Markdown priorise")
    parser.add_argument("--check", action="store_true", help="Exit 1 si inventaire non-vide (futur CI bloquant)")
    parser.add_argument("paths", nargs="*", help="Filtre chemins (defaut: --all)")
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parents[2]
    detector_json = load_detector_json(repo_root, args.paths or None)
    inventory = classify_corpus(detector_json)

    if args.json:
        print(json.dumps(inventory, indent=2, ensure_ascii=False))
    elif args.report:
        print(render_markdown(inventory))
    else:
        # Defaut : sortie compacte
        print(f"Scanned: {inventory['scanned']}")
        print(f"By category: {inventory['by_category']}")
        print(f"Top 5 families by drainable:")
        families = sorted(
            inventory["by_family"].items(),
            key=lambda x: -(x[1].get("RUNTIME_MEASURED", 0) + x[1].get("RUNTIME_HINT", 0) + x[1].get("AMBIGUOUS", 0))
        )
        for fam, counts in families[:5]:
            drainable = counts.get("RUNTIME_MEASURED", 0) + counts.get("RUNTIME_HINT", 0) + counts.get("AMBIGUOUS", 0)
            print(f"  {fam}: drainable={drainable} frozen={counts.get('CONFIG_PARAMETRIC', 0)}")

    if args.check:
        total = inventory["by_category"].get("RUNTIME_MEASURED", 0)
        if total > 0:
            print(f"\nFAIL: {total} RUNTIME_MEASURED findings remain", file=sys.stderr)
            sys.exit(1)
    sys.exit(0)


if __name__ == "__main__":
    main()
