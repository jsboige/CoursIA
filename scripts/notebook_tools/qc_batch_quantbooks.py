"""Batch-execute fixed quantbook.ipynb notebooks via QC Cloud Docker recipe.

Iterates over target project folders, copies each quantbook.ipynb to the
QC-Batch-Executor workspace project, executes via lean research + nbconvert,
then copies the executed notebook back.

Usage:
    python scripts/notebook_tools/qc_batch_quantbooks.py
    python scripts/notebook_tools/qc_batch_quantbooks.py --start-index 5 --max 10
"""
import json
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path("MyIA.AI.Notebooks/QuantConnect")
WORKSPACE = ROOT / "ESGF-2026" / "lean-workspace"
BATCH_EXEC = WORKSPACE / "QC-Batch-Executor"
RECIPE = Path("scripts/notebook_tools/qc_quantbook_execute.py")

TARGETS = [
    "projects/AdaptiveAssetAllocation/quantbook.ipynb",
    "projects/Alpha-Correlation-Analysis/quantbook.ipynb",
    "projects/Crypto-MultiCanal/quantbook.ipynb",
    "projects/DL-LSTM/quantbook.ipynb",
    "projects/EMA-Cross-Crypto/quantbook.ipynb",
    "projects/EMA-Cross-Index/quantbook.ipynb",
    "projects/ETF-Pairs/quantbook.ipynb",
    "projects/Framework_Composite_TrendWeather/quantbook.ipynb",
    "projects/ML-Classification/quantbook.ipynb",
    "projects/ML-DeepLearning/quantbook.ipynb",
    "projects/ML-EnhancedPairs/quantbook.ipynb",
    "projects/ML-FeatureEngineering/quantbook.ipynb",
    "projects/ML-RandomForest/quantbook.ipynb",
    "projects/ML-Regression/quantbook.ipynb",
    "projects/ML-SVM/quantbook.ipynb",
    "projects/ML-TextClassification/quantbook.ipynb",
    "projects/ML-XGBoost/quantbook.ipynb",
    "projects/Multi-Layer-EMA/quantbook.ipynb",
    "projects/Option-Wheel/quantbook.ipynb",
    "projects/Options-VGT/quantbook.ipynb",
    "projects/OptionsIncome/quantbook.ipynb",
    "projects/PairsTrading/quantbook.ipynb",
    "projects/RL-Portfolio/quantbook.ipynb",
    "projects/VIX-TermStructure/quantbook.ipynb",
]


def verify_exec(nb_path: Path) -> dict:
    try:
        nb = json.loads(nb_path.read_text(encoding="utf-8"))
    except Exception as e:
        return {"cells": 0, "exec": 0, "errors": 0, "status": f"JSON_ERROR: {e}"}
    code = [c for c in nb["cells"] if c["cell_type"] == "code"]
    execd = sum(1 for c in code if c.get("execution_count") is not None)
    errors = sum(
        1
        for c in code
        if any(o.get("output_type") == "error" for o in c.get("outputs", []))
    )
    if errors > 0:
        status = "D"
    elif execd == len(code) and execd > 0:
        status = "A"
    elif execd > 0:
        status = "B"
    else:
        status = "C"
    return {"cells": len(code), "exec": execd, "errors": errors, "status": status}


def run_one(target_rel: str, port: int = 8889, timeout: int = 600) -> dict:
    src = ROOT / target_rel
    nb_name = src.name
    if not src.exists():
        return {"target": target_rel, "ok": False, "error": "SOURCE_MISSING"}

    batch_nb = BATCH_EXEC / nb_name
    shutil.copy2(src, batch_nb)

    try:
        res = subprocess.run(
            [
                sys.executable, str(RECIPE),
                str(BATCH_EXEC),
                "--notebook", nb_name,
                "--port", str(port),
                "--timeout", str(timeout),
            ],
            capture_output=True, text=True, timeout=timeout * 4,
        )
        if not batch_nb.exists():
            return {"target": target_rel, "ok": False, "error": "NB_MISSING_AFTER_EXEC",
                    "rc": res.returncode, "stderr": res.stderr[-500:]}

        v = verify_exec(batch_nb)
        # Always copy back (even D status has partial outputs)
        shutil.copy2(batch_nb, src)

        if v["status"] in ("A", "B"):
            return {"target": target_rel, "ok": True, "verify": v}
        else:
            return {"target": target_rel, "ok": False, "verify": v,
                    "error": f"exec_status={v['status']}"}
    except subprocess.TimeoutExpired:
        return {"target": target_rel, "ok": False, "error": "TIMEOUT"}
    except Exception as e:
        return {"target": target_rel, "ok": False, "error": str(e)}
    finally:
        if batch_nb.exists():
            batch_nb.unlink()


def main():
    import argparse
    p = argparse.ArgumentParser()
    p.add_argument("--start-index", type=int, default=0)
    p.add_argument("--max", type=int, default=len(TARGETS))
    p.add_argument("--port", type=int, default=8889)
    p.add_argument("--timeout", type=int, default=600)
    args = p.parse_args()

    batch = TARGETS[args.start_index : args.start_index + args.max]
    print(f"Batch: {len(batch)} notebooks, starting at index {args.start_index}")
    results = {"ok": [], "fail": []}

    for i, t in enumerate(batch):
        print(f"\n[{i+1}/{len(batch)}] {t}")
        r = run_one(t, port=args.port, timeout=args.timeout)
        if r["ok"]:
            v = r["verify"]
            print(f"  OK: {v['exec']}/{v['cells']} exec, {v['errors']} err -> {v['status']}")
            results["ok"].append(r)
        else:
            v = r.get("verify", {})
            err = r.get("error", "unknown")
            print(f"  FAIL: {err} ({v.get('exec', 0)}/{v.get('cells', 0)} exec)")
            results["fail"].append(r)

    print(f"\n=== RESULTS: {len(results['ok'])} OK, {len(results['fail'])} FAIL ===")
    for f in results["fail"]:
        v = f.get("verify", {})
        print(f"  FAIL: {f['target']} -> {f.get('error', '?')} "
              f"({v.get('exec', 0)}/{v.get('cells', 0)} exec, {v.get('errors', 0)} errors)")

    out_path = Path("_qc_quantbook_results.json")
    out_path.write_text(json.dumps(results, indent=2), encoding="utf-8")
    print(f"Results saved to {out_path}")


if __name__ == "__main__":
    main()
