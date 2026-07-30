#!/usr/bin/env python3
"""
populate_gametheory_cost.py — Peuple `metadata.cost` pour les notebooks GameTheory.

Issue #8056 (P1) — matrice coût/ressource par notebook. EPIC #8056 burn-down
par famille : GenAI/Image 100%, Audio 100%, Texte 100%, Video 100%, ML 100%,
QC 100% (cf PRs #8312, #8585, #8580, etc.). GameTheory = **48 NBs sans cost**,
0/48 couvert au début du c.927. Ce script dédié ferme tranche par tranche.

Profil GameTheory détecté (firsthand c.927) : 0 QC, 0 API externe, 0 GPU, 0 RL.
Stack majoritaire : Python pur (nashpy + numpy + matplotlib + networkx) avec
quelques C# / Lean / OpenSpiel twins. Pattern canonique calqué sur
`Infer-3-Factor-Graphs` (CPU-pure) : api_provider=none, gpu_required=false,
free_alternative=self, validator=papermill (Python) ou dotnet-interactive
(.NET Interactive) ou lean_build (Lean 4).

Idempotent : JAMAIS écraser un bloc `cost` existant (un notebook déjà peuplé
est skippé). Hand-edits byte-surgical sur `nb.metadata['cost']` ; LF-only CR=0
post-write (L965 ★ + L925-E ★).

Usage :
  # Dry-run (par défaut) — affiche ce qui serait peuplé
  python scripts/audit/populate_gametheory_cost.py --tranche 1
  python scripts/audit/populate_gametheory_cost.py --tranche 2

  # Appliquer
  python scripts/audit/populate_gametheory_cost.py --tranche 1 --apply \\
      --by myia-po-2023:CoursIA-2
  python scripts/audit/populate_gametheory_cost.py --tranche 2 --apply \\
      --by myia-po-2023:CoursIA-2

  # Lister les NBs sans cost (audit gap)
  python scripts/audit/populate_gametheory_cost.py --audit
"""

import argparse
import datetime as _dt
import json
import sys
from pathlib import Path


# === Profils canoniques par NB (tranches 1+2) ===
#
# Schéma calqué sur `Infer-3-Factor-Graphs` + `GameTheory-1-Setup` ajusté :
# - Setup : `network: true` (pip install nashpy/openspiel)
# - NormalForm / Topology2x2 / ZeroSum / EvolutionTrust : CPU pure, `network: false`
# - C# twins : `validator: dotnet-interactive` (Microsoft.SemanticKernel local)
# - Lean twins : `validator: lean_build` (lake build)
#
# `cpu_min` estimé heuristique sur cellules code × ~10-15s/cellule (range documenté).

PROFILES = {
    # === Tranche 1 (c.927, GT-1/2/3) ===
    "GameTheory-1-Setup": {
        "kernel": "python3",
        "validator": "papermill",
        "cpu_min": 5,            # pip install + 21 cellules code
        "network": True,         # pip install nashpy/openspiel + imports distants
        "notes": "Setup OpenSpiel + nashpy via pip install WSL; import numpy/matplotlib/networkx. Première cellule = installation.",
    },
    "GameTheory-2-NormalForm": {
        "kernel": "python3",
        "validator": "papermill",
        "cpu_min": 3,            # 16 cellules, équilibre Nash
        "network": False,
        "notes": "Normal-form games via nashpy ; numpy/matplotlib pour visualisations (polygone d'utilité, courbes d'indifférence).",
    },
    "GameTheory-2-NormalForm-Csharp": {
        "kernel": ".net-csharp",
        "validator": "dotnet-interactive",
        "cpu_min": 3,            # 11 cellules .NET Interactive
        "network": False,
        "notes": "Jumeau .NET Interactive C# : Microsoft.SemanticKernel/GametheoryUtils en local. cf L532 MEMORY : strip_probe_banner.py post-re-exec.",
    },
    "GameTheory-3-Topology2x2": {
        "kernel": "gametheory-wsl",
        "validator": "papermill",
        "cpu_min": 4,            # 17 cellules, classification topologique 2×2
        "network": False,
        "notes": "Classification topologique des jeux 2×2 (4 classes : prisoner's dilemma, stag hunt, etc.) ; kernel gametheory-wsl Python+nashpy.",
    },
    "GameTheory-3-Topology2x2-Csharp": {
        "kernel": ".net-csharp",
        "validator": "dotnet-interactive",
        "cpu_min": 4,            # 12 cellules .NET
        "network": False,
        "notes": "Jumeau .NET Interactive C# : classification topologique 2×2. cf L532 MEMORY : strip_probe_banner.py post-re-exec.",
    },
    # === Tranche 2 (c.934, GT-5/6) ===
    "GameTheory-5-ZeroSum-Minimax": {
        "kernel": "gametheory-wsl",
        "validator": "papermill",
        "cpu_min": 4,            # 14 cellules, jeux à somme nulle + théorème Minimax
        "network": False,
        "notes": "Jeux à somme nulle + théorème du Minimax (Von Neumann 1928) ; équilibre via nashpy, visualisations numpy/matplotlib. Kernel gametheory-wsl Python+nashpy.",
    },
    "GameTheory-5-ZeroSum-Minimax-Csharp": {
        "kernel": ".net-csharp",
        "validator": "dotnet-interactive",
        "cpu_min": 3,            # 12 cellules .NET
        "network": False,
        "notes": "Jumeau .NET Interactive C# : jeux à somme nulle + Minimax. cf L532 MEMORY : strip_probe_banner.py post-re-exec.",
    },
    "GameTheory-6-EvolutionTrust": {
        "kernel": "python3",
        "validator": "papermill",
        "cpu_min": 5,            # 20 cellules, dilemme itéré + évolution
        "network": False,
        "notes": "Dilemme du Prisonnier itéré + évolution de la confiance (Axelrod IPD Tournament) ; stratégies TFT, Pavlov, Generous, etc. via numpy. Reproduction déterministe (seed fixe).",
    },
    "GameTheory-6-EvolutionTrust-Csharp": {
        "kernel": ".net-csharp",
        "validator": "dotnet-interactive",
        "cpu_min": 3,            # 12 cellules .NET
        "network": False,
        "notes": "Jumeau .NET Interactive C# : Axelrod IPD Tournament + évolution de la confiance. cf L532 MEMORY : strip_probe_banner.py post-re-exec.",
    },
}


# Mapping tranche -> liste ordonnée de NBs
TRANCHES = {
    1: [
        "GameTheory-1-Setup",
        "GameTheory-2-NormalForm",
        "GameTheory-2-NormalForm-Csharp",
        "GameTheory-3-Topology2x2",
        "GameTheory-3-Topology2x2-Csharp",
    ],
    2: [
        "GameTheory-5-ZeroSum-Minimax",
        "GameTheory-5-ZeroSum-Minimax-Csharp",
        "GameTheory-6-EvolutionTrust",
        "GameTheory-6-EvolutionTrust-Csharp",
    ],
}


def build_cost(notebook_name: str, by: str, today: str) -> dict:
    """Construit le bloc `metadata['cost']` canonique pour un NB GT.

    Champs dérivés : cpu_min, gpu_min, validator, notes, metadata_written.
    Champs constants GT : api_usd_est=0, api_provider=none, gpu_required=false,
    vram_gb=0, vram_tier=NONE, external_account=none, free_alternative=self
    (sentinel canonique, le NB est lui-même l'alternative gratuite), reduced_pedagogical=null,
    reproducibility=HIGH (algorithmes déterministes, seed non requis pour la classification
    topologique / équilibre Nash / stratégie itérée).
    """
    profile = PROFILES[notebook_name]
    return {
        "api_usd_est": 0.0,
        "api_provider": "none",
        "qcc_tokens_est": 0,           # non-QC
        "cpu_min": profile["cpu_min"],
        "gpu_min": 0,
        "gpu_required": False,
        "vram_gb": 0,
        "vram_tier": "NONE",
        "network": profile["network"],
        "external_account": "none",
        "free_alternative": "self",    # sentinel canonique : GT est lui-même l'alternative gratuite (cf cost-matrix.md §Sentinels)
        "reduced_pedagogical": None,   # notebook-specific (jugement humain) ; null = honnête
        "reproducibility": "HIGH",
        "metadata_written": today,
        "validator": profile["validator"],
        "notes": profile["notes"],
    }


def populate_notebook(path: Path, by: str, today: str, apply: bool) -> str:
    """Peuple metadata.cost selon profil canonique. Retourne un code statut."""
    notebook_name = path.name.replace(".ipynb", "")
    if notebook_name not in PROFILES:
        return f"skipped-no-profile ({notebook_name})"

    try:
        nb = json.loads(path.read_text(encoding="utf-8"))
    except Exception as e:
        return f"error: {e}"

    meta = nb.setdefault("metadata", {})
    if "cost" in meta:  # idempotent : ne JAMAIS écraser un bloc existant
        return "skipped-has-cost"

    cost = build_cost(notebook_name, by=by, today=today)
    if not apply:
        return "populated"  # dry-run

    meta["cost"] = cost
    # Round-trip json indent=1 (convention repo) ; LF-only ; pas de churn inutile.
    new_content = json.dumps(nb, indent=1, ensure_ascii=False) + "\n"
    # LF-fix post-write sur Windows (L965 ★ + L925-E ★)
    if "\r\n" in new_content:
        new_content = new_content.replace("\r\n", "\n")
    path.write_bytes(new_content.encode("utf-8"))
    return "populated"


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument(
        "--tranche", type=int, default=1,
        help="Tranche GT costfm à peupler (1 = GT-1/2/3, 2 = GT-5/6)",
    )
    ap.add_argument(
        "--by", default="anonymous",
        help="machine:workspace (provenance, pour le rapport)",
    )
    ap.add_argument(
        "--apply", action="store_true",
        help="Écrire les modifications (défaut : dry-run)",
    )
    ap.add_argument(
        "--today", default=None,
        help="Date ISO pour metadata_written (défaut : aujourd'hui)",
    )
    ap.add_argument(
        "--audit", action="store_true",
        help="Lister les NBs GT sans cost metadata (sans rien écrire)",
    )
    args = ap.parse_args(argv)

    if args.audit:
        gt_dir = Path("MyIA.AI.Notebooks/GameTheory")
        nbs = sorted([p for p in gt_dir.glob("*.ipynb") if "_output" not in p.name])
        n_with_cost = 0
        n_without = 0
        for nb in nbs:
            try:
                data = json.loads(nb.read_text(encoding="utf-8"))
                cost = data.get("metadata", {}).get("cost")
                if cost:
                    n_with_cost += 1
                    print(f"  HAS_COST  {nb.name}")
                else:
                    n_without += 1
                    print(f"  MISSING   {nb.name}")
            except Exception:
                pass
        print(f"\n[AUDIT] {n_with_cost} WITH cost / {n_without} WITHOUT cost (total {len(nbs)})")
        return 0

    if args.tranche not in TRANCHES:
        print(f"ERROR: tranche {args.tranche} pas encore implémentée (1 ou 2)", file=sys.stderr)
        return 2

    today = args.today or _dt.date.today().isoformat()
    nb_names = TRANCHES[args.tranche]
    gt_dir = Path("MyIA.AI.Notebooks/GameTheory")
    counts = {"populated": 0, "skipped-has-cost": 0}
    for name in nb_names:
        nb_path = gt_dir / f"{name}.ipynb"
        if not nb_path.exists():
            print(f"  WARN  {nb_path} introuvable")
            continue
        status = populate_notebook(nb_path, by=args.by, today=today, apply=args.apply)
        if status in counts:
            counts[status] += 1
        marker = "WRITE" if args.apply else "DRY-RUN"
        print(f"  [{marker:7s}] {status:25s} {nb_path.name}")

    mode = "APPLY" if args.apply else "DRY-RUN"
    print(f"\n[{mode}] tranche={args.tranche} by={args.by} today={today}")
    print(f"  populated        : {counts['populated']}")
    print(f"  skipped-existing : {counts['skipped-has-cost']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())