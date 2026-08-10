#!/usr/bin/env python3
"""Rend les *_en.ipynb siblings depuis les 3 CSV a text_en peuple.

Usage (depuis la racine du worktree) :
    python _render_batch.py

Reutilise render_notebook.py (livre en #10040). 3 invariants verifies par
le moteur ; ce script est juste un runner + collecteur de stats.

CSV en entree :
  - translations/genai/casestudies.csv (4 notebooks)
  - translations/genai/finetuning.csv (5 notebooks, 1 deja rendu)
  - translations/partner-course-quant-trading/partner-course.csv (7 notebooks)

Total : 16 candidats, 13 livres dans cette PR.

**Exclus (issues separees)** :
  - FT-02-QLoRA-Quantization : 2 cellules (`ift02-gen`/`ift02-cmp`) absentes
    du CSV `finetuning.csv` (cell_id mismatch : CSV=hash, notebook=semantic).
    Rendues en fallback FR → FR_CONTAM sous strict_fr. Tracker : issue #10289.
  - deep_research_optimization : 2 cellules (`66fac460`/`9ac7cfa8`) deja en
    anglais dans la source FR (deep_research import). Tracker : issue #10290.
"""
from __future__ import annotations

import csv
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent

# (csv_path, notebook_rel, output_rel)
TARGETS = [
    # genai/casestudies (4 notebooks)
    ("translations/genai/casestudies.csv",
     "MyIA.AI.Notebooks/GenAI/CaseStudies/Barbie-Schreck/barbie-schreck.ipynb",
     "MyIA.AI.Notebooks/GenAI/CaseStudies/Barbie-Schreck/barbie-schreck_en.ipynb"),
    ("translations/genai/casestudies.csv",
     "MyIA.AI.Notebooks/GenAI/CaseStudies/Fort-Boyard/fort-boyard-python.ipynb",
     "MyIA.AI.Notebooks/GenAI/CaseStudies/Fort-Boyard/fort-boyard-python_en.ipynb"),
    ("translations/genai/casestudies.csv",
     "MyIA.AI.Notebooks/GenAI/CaseStudies/Medical-Chatbot/medical_chatbot.ipynb",
     "MyIA.AI.Notebooks/GenAI/CaseStudies/Medical-Chatbot/medical_chatbot_en.ipynb"),
    ("translations/genai/casestudies.csv",
     "MyIA.AI.Notebooks/GenAI/CaseStudies/Recipe-Maker/receipe_maker.ipynb",
     "MyIA.AI.Notebooks/GenAI/CaseStudies/Recipe-Maker/receipe_maker_en.ipynb"),
    # genai/finetuning (5 notebooks, skip FT-01 deja rendu)
    ("translations/genai/finetuning.csv",
     "MyIA.AI.Notebooks/GenAI/FineTuning/FT-02-QLoRA-Quantization.ipynb",
     "MyIA.AI.Notebooks/GenAI/FineTuning/FT-02-QLoRA-Quantization_en.ipynb"),
    ("translations/genai/finetuning.csv",
     "MyIA.AI.Notebooks/GenAI/FineTuning/FT-03-Supervised-FineTuning-SFT.ipynb",
     "MyIA.AI.Notebooks/GenAI/FineTuning/FT-03-Supervised-FineTuning-SFT_en.ipynb"),
    ("translations/genai/finetuning.csv",
     "MyIA.AI.Notebooks/GenAI/FineTuning/FT-04-RLHF-DPO.ipynb",
     "MyIA.AI.Notebooks/GenAI/FineTuning/FT-04-RLHF-DPO_en.ipynb"),
    ("translations/genai/finetuning.csv",
     "MyIA.AI.Notebooks/GenAI/FineTuning/FT-05-ModelMerging-Routing.ipynb",
     "MyIA.AI.Notebooks/GenAI/FineTuning/FT-05-ModelMerging-Routing_en.ipynb"),
    # partner-course-quant-trading (7 notebooks)
    ("translations/partner-course-quant-trading/partner-course.csv",
     "MyIA.AI.Notebooks/QuantConnect/partner-course-quant-trading/examples/Sector-Momentum/deep_research_optimization.ipynb",
     "MyIA.AI.Notebooks/QuantConnect/partner-course-quant-trading/examples/Sector-Momentum/deep_research_optimization_en.ipynb"),
    ("translations/partner-course-quant-trading/partner-course.csv",
     "MyIA.AI.Notebooks/QuantConnect/partner-course-quant-trading/examples/Sector-Momentum/research_robustness.ipynb",
     "MyIA.AI.Notebooks/QuantConnect/partner-course-quant-trading/examples/Sector-Momentum/research_robustness_en.ipynb"),
    ("translations/partner-course-quant-trading/partner-course.csv",
     "MyIA.AI.Notebooks/QuantConnect/partner-course-quant-trading/examples/Crypto-MultiCanal/research.ipynb",
     "MyIA.AI.Notebooks/QuantConnect/partner-course-quant-trading/examples/Crypto-MultiCanal/research_en.ipynb"),
    ("translations/partner-course-quant-trading/partner-course.csv",
     "MyIA.AI.Notebooks/QuantConnect/partner-course-quant-trading/examples/Crypto-MultiCanal/research_archive.ipynb",
     "MyIA.AI.Notebooks/QuantConnect/partner-course-quant-trading/examples/Crypto-MultiCanal/research_archive_en.ipynb"),
    ("translations/partner-course-quant-trading/partner-course.csv",
     "MyIA.AI.Notebooks/QuantConnect/partner-course-quant-trading/kit-transitoire/01-ML-RandomForest/research.ipynb",
     "MyIA.AI.Notebooks/QuantConnect/partner-course-quant-trading/kit-transitoire/01-ML-RandomForest/research_en.ipynb"),
    ("translations/partner-course-quant-trading/partner-course.csv",
     "MyIA.AI.Notebooks/QuantConnect/partner-course-quant-trading/kit-transitoire/02-ML-XGBoost/research.ipynb",
     "MyIA.AI.Notebooks/QuantConnect/partner-course-quant-trading/kit-transitoire/02-ML-XGBoost/research_en.ipynb"),
    ("translations/partner-course-quant-trading/partner-course.csv",
     "MyIA.AI.Notebooks/QuantConnect/partner-course-quant-trading/kit-transitoire/03-Framework-Composite/research.ipynb",
     "MyIA.AI.Notebooks/QuantConnect/partner-course-quant-trading/kit-transitoire/03-Framework-Composite/research_en.ipynb"),
]


def main() -> int:
    failures = []
    for csv_rel, nb_rel, out_rel in TARGETS:
        csv_path = REPO_ROOT / csv_rel
        nb_path = REPO_ROOT / nb_rel
        out_path = REPO_ROOT / out_rel
        if not csv_path.exists():
            print(f"[skip] CSV missing: {csv_rel}")
            continue
        if not nb_path.exists():
            print(f"[skip] source notebook missing: {nb_rel}")
            failures.append((nb_rel, "source missing"))
            continue
        if out_path.exists():
            print(f"[skip] already rendered: {out_rel}")
            continue
        # Real render (no --dry-run)
        proc = subprocess.run(
            ["python", "scripts/translation/render_notebook.py",
             "--csv", csv_rel, "--notebook", nb_rel, "--lang", "en",
             "--out", out_rel],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
        )
        if proc.returncode != 0:
            print(f"[FAIL] {out_rel}:")
            print(f"  stderr: {proc.stderr.strip()}")
            print(f"  stdout: {proc.stdout.strip()}")
            failures.append((out_rel, f"exit {proc.returncode}"))
            continue
        # Parse stats from stdout (first lines)
        msg = proc.stdout.strip().splitlines()[0] if proc.stdout.strip() else "?"
        print(f"[OK]   {out_rel}: {msg}")
    print(f"\n=== Summary: {len(TARGETS) - len(failures)}/{len(TARGETS)} succeeded ===")
    if failures:
        for f, reason in failures:
            print(f"  FAILED: {f} ({reason})")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
