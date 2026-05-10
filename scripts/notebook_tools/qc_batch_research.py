"""Batch-execute generated research.ipynb notebooks via QC Cloud Docker.

Copies each research.ipynb into QC-Batch-Executor workspace, executes via
lean research + nbconvert, then copies back to the original project folder.

Usage:
    python scripts/notebook_tools/qc_batch_research.py
    python scripts/notebook_tools/qc_batch_research.py --start-index 5 --max 5 --timeout 1800
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

RESEARCH_TARGETS = [
    "projects/Adaptive-Conformal-Risk/research.ipynb",
    "projects/AdaptiveAssetAllocation/research.ipynb",
    "projects/AllWeather/research.ipynb",
    "projects/AssetClassMomentum-QC/research.ipynb",
    "projects/BTC-MACD-ADX/research.ipynb",
    "projects/BTC-ML/research.ipynb",
    "projects/BlackLitterman-Momentum/research.ipynb",
    "projects/CSharp-BTC-MACD-ADX/research.ipynb",
    "projects/CausalEventAlpha/research.ipynb",
    "projects/Chronos-Foundation-Forecasting/research.ipynb",
    "projects/Cloud-DualMomentum-NoTLT/research.ipynb",
    "projects/Cloud-MeanReversion-Sectors/research.ipynb",
    "projects/Cloud-RiskParity-Composite/research.ipynb",
    "projects/Cloud-SectorRotation-Momentum/research.ipynb",
    "projects/Cloud-VolTargeting/research.ipynb",
    "projects/Clustering-Fundamentals-ML/research.ipynb",
    "projects/DL-LSTM/research.ipynb",
    "projects/Dividend-Harvesting-ML/research.ipynb",
    "projects/DualMomentum/research.ipynb",
    "projects/DualMomentumNoTLT/research.ipynb",
    "projects/Dynamic-Options-Wheel/research.ipynb",
    "projects/EMA-Cross-Alpha/research.ipynb",
    "projects/EMA-Cross-Index/research.ipynb",
    "projects/EMA-Cross-Stocks/research.ipynb",
    "projects/ETF-Pairs/research.ipynb",
    "projects/Framework_Composite_EMATrend/research.ipynb",
    "projects/Framework_Composite_FamaFrenchAllWeather/research.ipynb",
    "projects/Framework_Composite_MomentumRegime/research.ipynb",
    "projects/Framework_Composite_TrendWeather/research.ipynb",
    "projects/FuturesTrend/research.ipynb",
    "projects/Gaussian-Direction-Classifier/research.ipynb",
    "projects/GlobalMacro-Regime/research.ipynb",
    "projects/HMM-KMeans-Voting/research.ipynb",
    "projects/HighBookToMarketFScore-QC/research.ipynb",
    "projects/InverseVolatility-Rank/research.ipynb",
    "projects/LeveragedETFMomentum-QC/research.ipynb",
    "projects/LongShortHarvest-QC/research.ipynb",
    "projects/ML-Chronos-Foundation/research.ipynb",
    "projects/ML-Classification/research.ipynb",
    "projects/ML-DeepLearning/research.ipynb",
    "projects/ML-EnhancedPairs/research.ipynb",
    "projects/ML-Ensemble/research.ipynb",
    "projects/ML-FX-SVM-Wavelet/research.ipynb",
    "projects/ML-FeatureEngineering/research.ipynb",
    "projects/ML-FinBERT-Sentiment/research.ipynb",
    "projects/ML-Gaussian-Classifier/research.ipynb",
    "projects/ML-LLM-Summarization/research.ipynb",
    "projects/ML-Regression/research.ipynb",
    "projects/ML-Reversion-Trending/research.ipynb",
    "projects/ML-SVM/research.ipynb",
    "projects/ML-Temporal-CNN/research.ipynb",
    "projects/ML-TextClassification/research.ipynb",
    "projects/ML-Trend-Scanning/research.ipynb",
    "projects/MacroFactorRotation-QC/research.ipynb",
    "projects/Markov-Regime-Detection/research.ipynb",
    "projects/MeanReversion/research.ipynb",
    "projects/MomentumStrategy/research.ipynb",
    "projects/Multi-Layer-EMA/research.ipynb",
    "projects/Option-Wheel/research.ipynb",
    "projects/Options-VGT/research.ipynb",
    "projects/PCA-StatArbitrage/research.ipynb",
    "projects/PairsTrading/research.ipynb",
    "projects/Portfolio-Optimization-ML/research.ipynb",
    "projects/Positive-Negative-Splits-ML/research.ipynb",
    "projects/PuppiesOfTheDow-QC/research.ipynb",
    "projects/RL-DQN-Trading/research.ipynb",
    "projects/RL-Portfolio/research.ipynb",
    "projects/RegimeSwitching/research.ipynb",
    "projects/Reinforcement-Learning-Trading/research.ipynb",
    "projects/SVM-Wavelet-Forecasting/research.ipynb",
    "projects/Sector-ML-Classification/research.ipynb",
    "projects/SectorMomentum/research.ipynb",
    "projects/Simple-Equity-EMA-Crossing/research.ipynb",
    "projects/Stoploss-Volatility-ML/research.ipynb",
    "projects/TermStructureCommodities-QC/research.ipynb",
    "projects/TradingCosts-Optimization/research.ipynb",
    "projects/Trend-Following/research.ipynb",
    "projects/TrendFilteredMeanReversion/research.ipynb",
    "projects/TrendStocks-Alpha/research.ipynb",
    "projects/TrendStocksLite/research.ipynb",
    "projects/TurnOfMonth/research.ipynb",
    "projects/VIX-TermStructure/research.ipynb",
    "projects/VolTarget-Momentum/research.ipynb",
    "projects/composite-c1-multiasset/research.ipynb",
    "projects/composite-c2-equityfactor/research.ipynb",
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


def clear_execution_counts(nb_path: Path):
    """Clear stale execution counts so nbconvert re-executes all cells."""
    nb = json.loads(nb_path.read_text(encoding="utf-8"))
    for cell in nb["cells"]:
        if cell["cell_type"] == "code":
            cell["execution_count"] = None
            cell["outputs"] = []
    nb_path.write_text(json.dumps(nb, indent=1, ensure_ascii=False), encoding="utf-8")


def run_one(target_rel: str, port: int = 8889, timeout: int = 1800) -> dict:
    src = ROOT / target_rel
    nb_name = src.name
    if not src.exists():
        return {"target": target_rel, "ok": False, "error": "SOURCE_MISSING"}

    # Clear stale execution metadata before copying
    clear_execution_counts(src)

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
        shutil.copy2(batch_nb, src)

        if v["status"] in ("A", "B"):
            return {"target": target_rel, "ok": True, "verify": v}
        else:
            return {"target": target_rel, "ok": False, "verify": v,
                    "error": f"exec_status={v['status']} ({v['exec']}/{v['cells']} exec, {v['errors']} errors)"}
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
    p.add_argument("--max", type=int, default=len(RESEARCH_TARGETS))
    p.add_argument("--port", type=int, default=8889)
    p.add_argument("--timeout", type=int, default=1800)
    args = p.parse_args()

    batch = RESEARCH_TARGETS[args.start_index : args.start_index + args.max]
    print(f"Batch: {len(batch)} research notebooks, starting at index {args.start_index}")
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

    out_path = Path("_qc_research_results.json")
    out_path.write_text(json.dumps(results, indent=2), encoding="utf-8")
    print(f"Results saved to {out_path}")


if __name__ == "__main__":
    main()
