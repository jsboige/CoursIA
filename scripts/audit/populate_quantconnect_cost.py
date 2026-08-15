#!/usr/bin/env python3
"""
populate_quantconnect_cost.py — Peuple `metadata.cost` pour les notebooks QuantConnect.

Issue #8056 (P1) — matrice coût/ressource par notebook. EPIC #8056 burn-down
par famille. Note : le commentaire "QC 100%" dans populate_gametheory_cost.py
était FAUX — audit firsthand (po-2024 c.960) : **111 QC notebooks sans cost**
sur 205. Ce script dédié ferme tranche par tranche.

Profil QuantConnect/ML-Training détecté (firsthand c.960) :
- ML-Training-Pipeline = ML de recherche pur (torch/sklearn/numpy sur données
  CSV locales), **PAS de QuantBook / PAS de QCC / PAS d'API externe**. Alternative
  gratuite = local (lui-même). Deux NBs GPU (TFT m9, LSTM m15) modèles PETITS
  (110K / 5-68K params) — laptop GPU 8 Go suffit, pas de contrainte 24 Go.
- Les NBs QC-Cloud (QCC) et QC-Py (lean-cli local) = tranches futures (2+).

Pattern canonique calqué sur `populate_gametheory_cost.py` (sentinels cost-matrix.md).

Idempotent : JAMAIS écraser un bloc `cost` existant (un notebook déjà peuplé
est skippé). Hand-edits byte-surgical sur `nb.metadata['cost']` ; LF-only CR=0
post-write (L965 ★ + L925-E ★).

Usage :
  # Dry-run (par défaut) — affiche ce qui serait peuplé
  python scripts/audit/populate_quantconnect_cost.py --tranche 1

  # Appliquer
  python scripts/audit/populate_quantconnect_cost.py --tranche 1 --apply \\
      --by myia-po-2024:CoursIA-2

  # Lister les NBs QC sans cost (audit gap global)
  python scripts/audit/populate_quantconnect_cost.py --audit
"""

import argparse
import datetime as _dt
import json
import sys
from pathlib import Path


# === Profils canoniques par NB (firsthand c.960) ===
#
# ML-Training-Pipeline = recherche ML pure, données CSV locales, pas de QC Cloud.
# `cpu_min` / `gpu_min` estimés sur cellules code × runtime observé.
# TFT (m9) : 110 801 params, AMP CUDA, ~2h training full (6 configs) mais le NB
#   analyse des résultats pré-calculés (outputs/tft_m9_*/results.json) + refit léger.
# LSTM (m15) : hidden=32 deployable (~4.8K params, BEATS 52/84 p=0.019) ;
#   hidden>=128 overfitte. Petit modèle, VRAM modeste.

PROFILES = {
    # === Tranche 1 (c.960, ML-Training-Pipeline research) ===
    "research_l1_tsmom": {
        "kernel": "python3", "validator": "papermill",
        "cpu_min": 3, "network": False,
        "notes": "Time-Series Momentum (TSMOM) ; pandas/numpy sur séries crypto. CPU pur, 8 cellules.",
    },
    "research_l2_dual_momentum": {
        "kernel": "python3", "validator": "papermill",
        "cpu_min": 3, "network": False,
        "notes": "Dual momentum (absolu+relatif) ; pandas. CPU pur, 8 cellules.",
    },
    "research_l3_trend": {
        "kernel": "python3", "validator": "papermill",
        "cpu_min": 3, "network": False,
        "notes": "Stratégies de tendance ; pandas/numpy. CPU pur, 9 cellules.",
    },
    "research_l4_decision_transformer": {
        "kernel": "python3", "validator": "papermill",
        "cpu_min": 4, "network": False,
        "notes": "Decision Transformer (overview recherche) ; charge/prépare données. CPU, 6 cellules.",
    },
    "research_what_dl_can_predict": {
        "kernel": "python3", "validator": "papermill",
        "cpu_min": 5, "network": False,
        "notes": "Étude exploratoire deep-learning pour la volatilité ; pandas/numpy. CPU, 15 cellules.",
    },
    "m3_har_asymmetric_semivariance": {
        "kernel": "python3", "validator": "papermill",
        "cpu_min": 3, "network": False,
        "notes": "HAR asymétrique (semi-variance) ; régression OLS numpy. CPU pur, 8 cellules.",
    },
    "m4_dlinear_vol_research": {
        "kernel": "python3", "validator": "papermill",
        "cpu_min": 2, "network": False,
        "notes": "DLinear (Zeng 2022) pour la volatilité ; petit MLP numpy/torch CPU. 4 cellules.",
    },
    "m5_hmm_regime_research": {
        "kernel": "python3", "validator": "papermill",
        "cpu_min": 3, "network": False,
        "notes": "HMM de régime (hmmlearn) ; EM sur séries. CPU pur, 5 cellules.",
    },
    "m9_tft_vol_research": {
        "kernel": "python3", "validator": "papermill",
        "cpu_min": 5, "gpu_min": 10, "gpu_required": True, "vram_gb": 4, "vram_tier": "LOW",
        "network": False,
        "notes": "Temporal Fusion Transformer (Lim 2021), 110 801 params, AMP CUDA. Training full ~2h (6 configs) ; le NB analyse outputs/tft_m9_*/results.json + refit léger. Laptop GPU 8 Go suffit.",
    },
    "m11e_ensemble_research": {
        "kernel": "python3", "validator": "papermill",
        "cpu_min": 3, "network": False,
        "notes": "Ensemble (moyenne/stacking des modèles m*) ; pandas/numpy. CPU pur, 5 cellules.",
    },
    "m12_har_rv_j_research": {
        "kernel": "python3", "validator": "papermill",
        "cpu_min": 3, "network": False,
        "notes": "HAR-RV-J (jumps) ; régression OLS. CPU pur, 5 cellules.",
    },
    "m15_lstm_rv_research": {
        "kernel": "python3", "validator": "papermill",
        "cpu_min": 4, "gpu_min": 5, "gpu_required": True, "vram_gb": 2, "vram_tier": "LOW",
        "network": False,
        "notes": "LSTM (hidden=32 deployable ~4.8K params, BEATS 52/84 p=0.019 ; hidden>=128 overfitte). torch CUDA, petit modèle. Lit scripts/results/m15_lstm_rv_h32/. Laptop GPU 8 Go suffit.",
    },
    "c875_hmm_alpha_dm_research": {
        "kernel": "python3", "validator": "papermill",
        "cpu_min": 2, "network": False,
        "notes": "HMM alpha (research c.875) ; hmmlearn. CPU pur, 4 cellules.",
    },
    "hmm_alpha_research": {
        "kernel": "python3", "validator": "papermill",
        "cpu_min": 8, "network": False,
        "notes": "HMM alpha (recherche complète, 27 cellules) ; hmmlearn + visualisations matplotlib. CPU pur.",
    },
    "ML-Research-Template": {
        "kernel": "python3", "validator": "papermill",
        "cpu_min": 3, "network": False,
        "notes": "Template de notebook de recherche ML (squelette reproductible). CPU, 8 cellules.",
    },
}


# Mapping tranche -> liste ordonnée de NBs (relatif au sous-dossier)
TRANCHES = {
    1: {
        "dir": "MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline",
        "names": list(PROFILES.keys()),
    },
}


def build_cost(notebook_name: str, by: str, today: str) -> dict:
    """Construit le bloc `metadata['cost']` canonique pour un NB QC/ML-Training.

    ML-Training-Pipeline = local pur : pas d'API, pas de QCC, pas de compte
    externe. L'alternative gratuite = lui-même (local). GPU requis uniquement
    pour TFT (m9) et LSTM (m15), modèles petits (VRAM <=4 Go).
    """
    profile = PROFILES[notebook_name]
    gpu_required = profile.get("gpu_required", False)
    return {
        "api_usd_est": 0.0,
        "api_provider": "none",
        "qcc_tokens_est": 0,           # ML-Training n'utilise PAS QuantBook/QC Cloud
        "cpu_min": profile["cpu_min"],
        "gpu_min": profile.get("gpu_min", 0),
        "gpu_required": gpu_required,
        "vram_gb": profile.get("vram_gb", 0),
        "vram_tier": profile.get("vram_tier", "NONE"),
        "network": profile["network"],
        "external_account": "none",
        "free_alternative": "self",    # sentinel : le NB est lui-même l'alternative locale gratuite
        "reduced_pedagogical": None,
        "reproducibility": "HIGH",     # analyse de results.json pré-calculés + seeds fixés (c.893-c.904)
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
    new_content = json.dumps(nb, indent=1, ensure_ascii=False) + "\n"
    # LF-fix post-write sur Windows (L965 ★ + L925-E ★)
    if "\r\n" in new_content:
        new_content = new_content.replace("\r\n", "\n")
    path.write_bytes(new_content.encode("utf-8"))
    return "populated"


def audit_gap() -> int:
    """Liste tous les NBs QC sans cost metadata (toutes tranches, tous sous-dossiers)."""
    qc_root = Path("MyIA.AI.Notebooks/QuantConnect")
    nbs = sorted(p for p in qc_root.rglob("*.ipynb") if "_output" not in p.name)
    n_with = 0
    n_without = 0
    for nb in nbs:
        try:
            data = json.loads(nb.read_text(encoding="utf-8"))
            cost = data.get("metadata", {}).get("cost")
            if cost:
                n_with += 1
            else:
                n_without += 1
                print(f"  MISSING   {nb.relative_to(qc_root)}")
        except Exception:
            pass
    print(f"\n[AUDIT] {n_with} WITH cost / {n_without} WITHOUT cost (total {len(nbs)})")
    return 0


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--tranche", type=int, default=1, help="Tranche QC cost à peupler (1 = ML-Training-Pipeline).")
    ap.add_argument("--by", default="anonymous", help="machine:workspace (provenance).")
    ap.add_argument("--apply", action="store_true", help="Écrire les modifications (défaut : dry-run).")
    ap.add_argument("--today", default=None, help="Date ISO pour metadata_written (défaut : aujourd'hui).")
    ap.add_argument("--audit", action="store_true", help="Lister les NBs QC sans cost (sans rien écrire).")
    args = ap.parse_args(argv)

    if args.audit:
        return audit_gap()

    if args.tranche not in TRANCHES:
        print(f"ERROR: tranche {args.tranche} pas encore implémentée (1 = ML-Training-Pipeline)", file=sys.stderr)
        return 2

    today = args.today or _dt.date.today().isoformat()
    spec = TRANCHES[args.tranche]
    base_dir = Path(spec["dir"])
    counts = {"populated": 0, "skipped-has-cost": 0, "error": 0}
    for name in spec["names"]:
        nb_path = base_dir / f"{name}.ipynb"
        if not nb_path.exists():
            print(f"  WARN  {nb_path} introuvable")
            continue
        status = populate_notebook(nb_path, by=args.by, today=today, apply=args.apply)
        for k in counts:
            if status.startswith(k):
                counts[k] += 1
                break
        marker = "WRITE" if args.apply else "DRY-RUN"
        print(f"  [{marker:7s}] {status:30s} {nb_path.name}")

    mode = "APPLY" if args.apply else "DRY-RUN"
    print(f"\n[{mode}] tranche={args.tranche} by={args.by} today={today}")
    print(f"  populated        : {counts['populated']}")
    print(f"  skipped-existing : {counts['skipped-has-cost']}")
    if counts["error"]:
        print(f"  errors           : {counts['error']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
