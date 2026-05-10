"""Generate research QuantBook notebooks for QC projects missing them.

Reads main.py metadata (class name, tickers, params, docstring) and generates
a structured research notebook with:
1. QuantBook init + universe setup
2. Data exploration (history, stats, correlations)
3. Signal/indicator analysis
4. Parameter sensitivity scan
5. Calibration mapping to main.py
6. Conclusion + next iteration

Usage:
    python scripts/notebook_tools/generate_qc_research.py --projects ML-Gaussian-Classifier HMM-KMeans-Voting
    python scripts/notebook_tools/generate_qc_research.py --all-missing
    python scripts/notebook_tools/generate_qc_research.py --all-missing --dry-run
"""
import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path("MyIA.AI.Notebooks/QuantConnect/projects")

# Docker-available tickers (verified in QC Cloud Docker environment)
DOCKER_TICKERS = {
    "equity": ["AAPL", "GOOGL", "SPY", "QQQ", "IWM", "BAC", "MSFT", "AMZN", "NVDA", "META", "TSLA", "NFLX"],
    "etf": ["SPY", "QQQ", "IWM", "TLT", "GLD", "EFA", "EEM", "USO", "IEF", "DJP", "VNQ", "GSG", "UVXY", "XLK"],
    "crypto": ["BTCUSD", "ETHUSD"],
}

# Research notebook cell templates
CELLS_TEMPLATE = {
    "title": {
        "cell_type": "markdown",
        "source": [
            "# Research: {title}\n",
            "\n",
            "{description}\n",
            "\n",
            "**Calibration target**: `{class_name}` in `main.py`"
        ],
    },
    "qb_init": {
        "cell_type": "code",
        "source": [
            "# Initialize QuantBook\n",
            "from datetime import datetime\n",
            "from QuantConnect.Research import QuantBook\n",
            "\n",
            "qb = QuantBook()\n",
            "\n",
            "# Add universe symbols\n",
            "{symbol_adds}\n",
            "\n",
            "# Request history (date range required for QC Docker)\n",
            "start = datetime(2020, 1, 1)\n",
            "end = datetime(2026, 1, 1)\n",
            "history = qb.history({history_symbols}, start, end, Resolution.DAILY)\n",
            "print(f\"History: {len(history)} rows\")\n",
            "if len(history) > 0:\n",
            "    display(history.head())"
        ],
    },
    "data_exploration": {
        "cell_type": "markdown",
        "source": [
            "## 1. Data Exploration\n",
            "\n",
            "Statistical overview of the universe: returns distribution, correlations, volatility regimes."
        ],
    },
    "explore_code": {
        "cell_type": "code",
        "source": [
            "import pandas as pd\n",
            "import numpy as np\n",
            "\n",
            "if len(history) == 0:\n",
            "    print('WARNING: No history data available')\n",
            "    closes = pd.DataFrame()\n",
            "    returns = pd.DataFrame()\n",
            "else:\n",
            "    # Compute returns\n",
            "    if isinstance(history.index, pd.MultiIndex):\n",
            "        closes = history['close'].unstack(level=0)\n",
            "    else:\n",
            "        closes = history['close']\n",
            "\n",
            "    returns = closes.pct_change().dropna()\n",
            "    print('=== Returns Summary ===')\n",
            "    print(returns.describe().round(4))\n",
            "    print()\n",
            "\n",
            "    print('=== Correlation Matrix ===')\n",
            "    corr = returns.corr().round(3)\n",
            "    print(corr)"
        ],
    },
    "signal_analysis": {
        "cell_type": "markdown",
        "source": [
            "## 2. Signal Analysis\n",
            "\n",
            "{signal_description}"
        ],
    },
    "signal_code": {
        "cell_type": "code",
        "source": [
            "# Signal computation\n",
            "{signal_code}\n",
            "\n",
            "print(\"=== Signal Statistics ===\")\n",
            "print(f\"Signal mean: {signal.mean():.6f}\")\n",
            "print(f\"Signal std: {signal.std():.6f}\")\n",
            "print(f\"Signal range: [{signal.min():.6f}, {signal.max():.6f}]\")\n",
            "signal.describe()"
        ],
    },
    "param_scan": {
        "cell_type": "markdown",
        "source": [
            "## 3. Parameter Sensitivity\n",
            "\n",
            "Test different parameter values for {params_list}."
        ],
    },
    "param_code": {
        "cell_type": "code",
        "source": [
            "# Parameter sensitivity scan\n",
            "{param_scan_code}\n",
            "\n",
            "print(\"=== Parameter Scan Results ===\")\n",
            "for params, metric in results:\n",
            "    print(f\"  {params}: metric={metric:.4f}\")\n",
            "print(f\"\\nBest: {best_params}\")"
        ],
    },
    "calibration": {
        "cell_type": "markdown",
        "source": [
            "## 4. Calibration to main.py\n",
            "\n",
            "Mapping research findings to algorithm parameters:\n",
            "\n",
            "{calibration_table}"
        ],
    },
    "calibration_code": {
        "cell_type": "code",
        "source": [
            "# Calibration summary\n",
            "calibration = {\n",
            "{calibration_dict}\n",
            "}\n",
            "\n",
            "print(\"=== Calibration Parameters ===\")\n",
            "for k, v in calibration.items():\n",
            "    print(f\"  {k}: {v}\")\n",
            "print(\"\\nTo apply: update get_parameter() defaults in main.py\")"
        ],
    },
    "conclusion": {
        "cell_type": "markdown",
        "source": [
            "## 5. Conclusion & Next Iteration\n",
            "\n",
            "{conclusion_text}"
        ],
    },
}


def extract_metadata(main_py_path: Path) -> dict:
    """Extract key metadata from main.py for notebook generation."""
    code = main_py_path.read_text(encoding="utf-8")

    # Class name
    cls_match = re.search(r"class (\w+)\(QCAlgorithm\)", code)
    class_name = cls_match.group(1) if cls_match else "UnknownAlgorithm"

    # Docstring
    doc_match = re.search(r'"""(.*?)"""', code, re.DOTALL)
    docstring = doc_match.group(1).strip() if doc_match else ""

    # Extract description from docstring (first paragraph)
    desc_lines = []
    for line in docstring.split("\n"):
        line = line.strip()
        if line.startswith("Reference:") or line.startswith("How it works:") or line.startswith("Parameters:"):
            break
        if line:
            desc_lines.append(line)
    description = " ".join(desc_lines[:3]) if desc_lines else f"Research notebook for {class_name}"

    # Extract tickers from add_equity calls
    tickers = re.findall(r'add_equity\(["\']([\w.]+)["\']', code)

    # Extract from self.tickers list
    if not tickers:
        tickers_match = re.search(r'self\.tickers\s*=\s*\[([^\]]+)\]', code)
        if tickers_match:
            tickers = re.findall(r'"(\w+)"', tickers_match.group(1))

    # Extract from symbol creation
    if not tickers:
        tickers = re.findall(r'Symbol\.create\("(\w+)"', code)

    # Fallback: scan for common tickers
    if not tickers:
        all_caps = re.findall(r'"([A-Z]{2,5})"', code[:3000])
        valid = [t for t in all_caps if t in sum(DOCKER_TICKERS.values(), [])]
        tickers = list(dict.fromkeys(valid))[:5]

    # Extract parameters
    params = re.findall(r"get_parameter\(['\"](\w+)['\"]", code)

    # Determine strategy type
    code_lower = code.lower()
    if "markov" in code_lower or "regime" in code_lower:
        strategy_type = "regime"
    elif "pca" in code_lower or "stat_arb" in code_lower or "statarb" in code_lower:
        strategy_type = "stat_arb"
    elif "gaussian" in code_lower or "naive_bayes" in code_lower or "gaussiannb" in code_lower:
        strategy_type = "classification"
    elif "hmm" in code_lower or "kmeans" in code_lower or "k-means" in code_lower:
        strategy_type = "clustering"
    elif "svm" in code_lower or "support_vector" in code_lower:
        strategy_type = "classification"
    elif "cnn" in code_lower or "temporal" in code_lower:
        strategy_type = "deep_learning"
    elif "momentum" in code_lower:
        strategy_type = "momentum"
    elif "mean_rever" in code_lower or "reversion" in code_lower:
        strategy_type = "mean_reversion"
    elif "volatility" in code_lower or "vol_target" in code_lower:
        strategy_type = "volatility"
    elif "ema" in code_lower or "cross" in code_lower:
        strategy_type = "trend_following"
    elif "dividend" in code_lower:
        strategy_type = "fundamental"
    elif "sentiment" in code_lower or "finbert" in code_lower:
        strategy_type = "sentiment"
    elif "black.litterman" in code_lower or "blacklitterman" in code_lower:
        strategy_type = "optimization"
    elif "stoploss" in code_lower or "stop_loss" in code_lower:
        strategy_type = "risk_management"
    else:
        strategy_type = "general"

    return {
        "class_name": class_name,
        "description": description,
        "tickers": tickers,
        "params": params,
        "strategy_type": strategy_type,
        "code_length": len(code),
    }


def generate_signal_code(metadata: dict) -> str:
    """Generate signal analysis code based on strategy type."""
    stype = metadata["strategy_type"]
    tickers = metadata["tickers"][:3]

    if stype == "regime":
        return (
            "# Compute regime indicators\n"
            "spy_close = closes.iloc[:, 0] if closes.shape[1] > 0 else closes\n"
            "returns_20d = spy_close.pct_change(20)\n"
            "vol_20d = spy_close.pct_change().rolling(20).std() * np.sqrt(252)\n"
            "signal = vol_20d.dropna()\n"
            "signal.name = 'realized_vol_20d'"
        )
    elif stype == "classification":
        return (
            "# Compute classification features\n"
            "for col in closes.columns[:5]:\n"
            "    returns[f'{col}_lag1'] = returns[col].shift(1)\n"
            "    returns[f'{col}_lag5'] = returns[col].shift(5)\n"
            "    returns[f'{col}_lag10'] = returns[col].shift(10)\n"
            "features = returns.dropna()\n"
            "signal = features.iloc[:, 0]\n"
            "signal.name = 'primary_feature'"
        )
    elif stype == "clustering":
        return (
            "# Compute clustering features\n"
            "means = returns.mean() * 252\n"
            "vols = returns.std() * np.sqrt(252)\n"
            "sharpe = means / vols\n"
            "signal = sharpe\n"
            "signal.name = 'annualized_sharpe'"
        )
    elif stype == "stat_arb":
        return (
            "# Compute PCA residual signals\n"
            "from numpy.linalg import svd\n"
            "log_prices = np.log(closes.dropna())\n"
            "if log_prices.shape[1] >= 3:\n"
            "    U, S, Vt = svd(log_prices.values, full_matrices=False)\n"
            "    residuals = log_prices.values - U[:, :3] @ np.diag(S[:3]) @ Vt[:3, :]\n"
            "    signal = pd.Series(residuals[:, 0], index=log_prices.index)\n"
            "else:\n"
            "    signal = log_prices.iloc[:, 0].diff()\n"
            "signal.name = 'pca_residual'"
        )
    elif stype == "momentum":
        return (
            "# Compute momentum signals\n"
            "mom_12m = closes.pct_change(252).dropna()\n"
            "mom_6m = closes.pct_change(126).dropna()\n"
            "mom_3m = closes.pct_change(63).dropna()\n"
            "signal = mom_12m.iloc[:, 0] if mom_12m.shape[1] > 0 else mom_12m\n"
            "signal.name = 'momentum_12m'"
        )
    elif stype == "mean_reversion":
        return (
            "# Compute mean-reversion signals\n"
            "spy_close = closes.iloc[:, 0] if closes.shape[1] > 0 else closes\n"
            "sma_20 = spy_close.rolling(20).mean()\n"
            "z_score = (spy_close - sma_20) / spy_close.rolling(20).std()\n"
            "signal = z_score.dropna()\n"
            "signal.name = 'z_score_20d'"
        )
    elif stype == "volatility":
        return (
            "# Compute volatility metrics\n"
            "realized_vol = returns.rolling(21).std() * np.sqrt(252)\n"
            "avg_vol = realized_vol.mean(axis=1)\n"
            "signal = avg_vol.dropna()\n"
            "signal.name = 'avg_realized_vol'"
        )
    elif stype == "trend_following":
        return (
            "# Compute trend signals\n"
            "spy_close = closes.iloc[:, 0] if closes.shape[1] > 0 else closes\n"
            "ema_50 = spy_close.ewm(span=50).mean()\n"
            "ema_200 = spy_close.ewm(span=200).mean()\n"
            "trend_signal = (ema_50 - ema_200) / ema_200\n"
            "signal = trend_signal.dropna()\n"
            "signal.name = 'ema_cross_signal'"
        )
    else:
        return (
            "# Compute generic signals\n"
            "primary = closes.iloc[:, 0] if closes.shape[1] > 0 else closes\n"
            "returns_5d = primary.pct_change(5)\n"
            "vol_10d = primary.pct_change().rolling(10).std()\n"
            "signal = returns_5d.dropna()\n"
            "signal.name = 'return_5d'"
        )


def generate_param_scan(metadata: dict) -> str:
    """Generate parameter sensitivity scan code."""
    params = metadata["params"]
    if not params:
        return (
            "# Generic parameter scan\n"
            "lookbacks = [10, 20, 30, 60]\n"
            "results = []\n"
            "for lb in lookbacks:\n"
            "    vol = closes.iloc[:, 0].pct_change().rolling(lb).std().mean()\n"
            "    results.append((f'lookback={lb}', vol))\n"
            "best_params = min(results, key=lambda x: x[1])[0]"
        )

    first_param = params[0]
    return (
        f"# Parameter scan for {first_param}\n"
        f"scan_values = [5, 10, 20, 30, 60]\n"
        f"results = []\n"
        f"for val in scan_values:\n"
        f"    # Compute metric for each parameter value\n"
        f"    vol = closes.iloc[:, 0].pct_change().rolling(val).std().mean()\n"
        f"    results.append((f'{first_param}={{val}}', vol))\n"
        f"best_params = min(results, key=lambda x: x[1])[0]"
    )


def generate_notebook(project_name: str, metadata: dict) -> dict:
    """Generate a complete research notebook as a dict."""
    tickers = metadata["tickers"]
    if not tickers:
        tickers = ["SPY", "TLT", "GLD"]

    # Limit to Docker-available tickers
    docker_available = set(sum(DOCKER_TICKERS.values(), []))
    safe_tickers = [t for t in tickers if t in docker_available]
    if not safe_tickers:
        safe_tickers = ["SPY", "TLT", "GLD"]

    # Symbol adds
    symbol_adds = "\n".join(
        f"symbols['{t}'] = qb.add_equity('{t}', Resolution.DAILY).symbol"
        for t in safe_tickers
    )

    # History symbols
    if len(safe_tickers) == 1:
        hist_sym = f"symbols['{safe_tickers[0]}']"
    else:
        hist_sym = "[" + ", ".join(f"symbols['{t}']" for t in safe_tickers) + "]"

    # Signal description
    signal_desc = {
        "regime": "Analyze volatility regimes and regime transition dynamics.",
        "classification": "Evaluate classification features and predictive power for direction forecasting.",
        "clustering": "Assess clustering structure and regime separation in the universe.",
        "stat_arb": "Compute PCA-based residual signals for mean-reversion opportunities.",
        "momentum": "Evaluate momentum signals across multiple timeframes.",
        "mean_reversion": "Compute z-score and mean-reversion signals.",
        "volatility": "Analyze volatility targeting and risk-adjusted metrics.",
        "trend_following": "Evaluate trend-following indicators (EMA crosses, SMA filters).",
        "deep_learning": "Analyze temporal features for CNN/LSTM model inputs.",
        "sentiment": "Explore sentiment features and their correlation with returns.",
        "optimization": "Analyze portfolio optimization inputs (covariance, expected returns).",
        "risk_management": "Evaluate stop-loss and volatility-based risk metrics.",
        "fundamental": "Analyze fundamental factors (dividends, earnings).",
        "general": "Evaluate primary signals and their statistical properties.",
    }

    # Signal code
    sig_code = generate_signal_code(metadata)

    # Param scan
    param_scan = generate_param_scan(metadata)
    params_list = ", ".join(metadata["params"]) if metadata["params"] else "lookback"

    # Calibration table
    if metadata["params"]:
        cal_rows = "\n".join(
            f"| `{p}` | (research value) | default |"
            for p in metadata["params"]
        )
        cal_header = "| Parameter | Research Value | main.py Default |\n|-----------|---------------|----------------|\n"
        calibration_table = cal_header + cal_rows
    else:
        calibration_table = "| Parameter | Research Value | main.py Default |\n|-----------|---------------|----------------|\n| lookback | (optimal) | default |"

    # Calibration dict
    if metadata["params"]:
        cal_dict = ",\n".join(f'    "{p}": "<research_value>"' for p in metadata["params"])
    else:
        cal_dict = '    "lookback": "<research_value>"'

    # Conclusion
    conclusion = (
        f"**Findings:**\n"
        f"- Universe ({', '.join(safe_tickers[:5])}) analyzed with {metadata['strategy_type']} signals\n"
        f"- Parameter sensitivity for {params_list} scanned\n\n"
        f"**Next iteration:**\n"
        f"- Test alternative universe composition\n"
        f"- Add regime-conditional analysis\n"
        f"- Validate against backtest results in main.py"
    )

    # Build cells
    cells = []

    def make_cell(cell_type, source_list):
        cell = {
            "cell_type": cell_type,
            "metadata": {},
            "source": source_list,
        }
        if cell_type == "code":
            cell["execution_count"] = None
            cell["outputs"] = []
        return cell

    # Cell 1: Title
    cells.append(make_cell("markdown", [
        f"# Research: {project_name}\n",
        "\n",
        f"{metadata['description']}\n",
        "\n",
        f"**Calibration target**: `{metadata['class_name']}` in `main.py`",
    ]))

    # Cell 2: QB init
    cells.append(make_cell("code", [
        "# Initialize QuantBook\n",
        "from datetime import datetime\n",
        "from QuantConnect.Research import QuantBook\n",
        "\n",
        "qb = QuantBook()\n",
        "symbols = {}\n",
        "\n",
        f"{symbol_adds}\n",
        "\n",
        "start = datetime(2020, 1, 1)\n",
        "end = datetime(2026, 1, 1)\n",
        f"history = qb.history({hist_sym}, start, end, Resolution.DAILY)\n",
        'print(f"History: {len(history)} rows")\n',
        "if len(history) > 0:\n",
        "    display(history.head())",
    ]))

    # Cell 3: Data exploration header
    cells.append(make_cell("markdown", [
        "## 1. Data Exploration\n",
        "\n",
        "Statistical overview: returns distribution, correlations, volatility.",
    ]))

    # Cell 4: Data exploration code
    cells.append(make_cell("code", [
        "import pandas as pd\n",
        "import numpy as np\n",
        "\n",
        "if len(history) == 0:\n",
        "    print('WARNING: No history data available')\n",
        "    closes = pd.DataFrame()\n",
        "    returns = pd.DataFrame()\n",
        "else:\n",
        "    if isinstance(history.index, pd.MultiIndex):\n",
        "        closes = history['close'].unstack(level=0)\n",
        "    else:\n",
        "        closes = history['close']\n",
        "    returns = closes.pct_change().dropna()\n",
        '    print("=== Returns Summary ===")\n',
        "    print(returns.describe().round(4))\n",
        "    print()\n",
        '    print("=== Correlation Matrix ===")\n',
        "    print(returns.corr().round(3))",
    ]))

    # Cell 5: Signal analysis header
    cells.append(make_cell("markdown", [
        "## 2. Signal Analysis\n",
        "\n",
        f"{signal_desc.get(metadata['strategy_type'], 'Evaluate primary signals.')}",
    ]))

    # Cell 6: Signal code
    # Indent multi-line generated code for else block
    sig_code_indented = "\n".join("    " + line for line in sig_code.strip().split("\n"))
    param_scan_indented = "\n".join("    " + line for line in param_scan.strip().split("\n"))
    cells.append(make_cell("code", [
        "# Signal computation\n",
        "if len(returns) == 0:\n",
        "    print('No data for signal analysis')\n",
        "    signal = pd.Series(dtype=float)\n",
        "else:\n",
        f"{sig_code_indented}\n",
        "\n",
        'print("=== Signal Statistics ===")\n',
        'if len(signal) > 0:\n',
        '    print(f"Signal mean: {signal.mean():.6f}")\n',
        '    print(f"Signal std: {signal.std():.6f}")\n',
        '    print(f"Signal range: [{signal.min():.6f}, {signal.max():.6f}]")',
    ]))

    # Cell 7: Param scan header
    cells.append(make_cell("markdown", [
        "## 3. Parameter Sensitivity\n",
        "\n",
        f"Test different parameter values for {params_list}.",
    ]))

    # Cell 8: Param scan code
    cells.append(make_cell("code", [
        "# Parameter sensitivity scan\n",
        "if len(returns) == 0:\n",
        "    print('No data for parameter scan')\n",
        "    results = []\n",
        "    best_params = 'N/A'\n",
        "else:\n",
        f"{param_scan_indented}\n",
        "\n",
        'print("=== Parameter Scan Results ===")\n',
        "for params, metric in results:\n",
        '    print(f"  {params}: metric={metric:.4f}")\n',
        f'print(f"\\nBest: {{best_params}}")',
    ]))

    # Cell 9: Calibration header
    cells.append(make_cell("markdown", [
        "## 4. Calibration to main.py\n",
        "\n",
        "Mapping research findings to algorithm parameters:\n",
        "\n",
        calibration_table,
    ]))

    # Cell 10: Calibration code
    cells.append(make_cell("code", [
        "# Calibration summary\n",
        "calibration = {\n",
        f"{cal_dict}\n",
        "}\n",
        "\n",
        'print("=== Calibration Parameters ===")\n',
        "for k, v in calibration.items():\n",
        f'    print(f"  {{k}}: {{v}}")\n',
        'print("\\nTo apply: update get_parameter() defaults in main.py")',
    ]))

    # Cell 11: Conclusion
    cells.append(make_cell("markdown", [
        "## 5. Conclusion & Next Iteration\n",
        "\n",
        conclusion,
    ]))

    notebook = {
        "cells": cells,
        "metadata": {
            "kernelspec": {
                "display_name": "Python 3",
                "language": "python",
                "name": "python3",
            },
            "language_info": {
                "name": "python",
                "version": "3.10.0",
            },
        },
        "nbformat": 4,
        "nbformat_minor": 5,
    }

    return notebook


def find_missing_projects() -> list:
    """Find projects with main.py but no research notebook."""
    missing = []
    for pdir in sorted(ROOT.iterdir()):
        if not pdir.is_dir():
            continue
        if not (pdir / "main.py").exists():
            continue
        has_research = any(
            f.name.startswith("research") and f.suffix == ".ipynb"
            for f in pdir.iterdir()
        )
        if not has_research:
            missing.append(pdir.name)
    return missing


def main():
    parser = argparse.ArgumentParser(description="Generate research QuantBook notebooks")
    parser.add_argument("--projects", nargs="+", help="Specific project names")
    parser.add_argument("--all-missing", action="store_true", help="Generate for all projects missing research notebooks")
    parser.add_argument("--dry-run", action="store_true", help="Show what would be generated")
    parser.add_argument("--max", type=int, default=20, help="Max notebooks to generate")
    args = parser.parse_args()

    if args.projects:
        targets = args.projects
    elif args.all_missing:
        targets = find_missing_projects()
    else:
        print("Specify --projects or --all-missing")
        sys.exit(1)

    targets = targets[: args.max]

    print(f"Generating {len(targets)} research notebooks")
    print(f"Targets: {targets}")
    print()

    generated = []
    for name in targets:
        pdir = ROOT / name
        main_py = pdir / "main.py"
        if not main_py.exists():
            print(f"  SKIP {name}: no main.py")
            continue

        metadata = extract_metadata(main_py)
        notebook = generate_notebook(name, metadata)
        out_path = pdir / "research.ipynb"

        if args.dry_run:
            print(f"  WOULD CREATE: {out_path} ({len(notebook['cells'])} cells, type={metadata['strategy_type']})")
        else:
            out_path.write_text(json.dumps(notebook, indent=1, ensure_ascii=False), encoding="utf-8")
            print(f"  CREATED: {out_path} ({len(notebook['cells'])} cells, type={metadata['strategy_type']})")

        generated.append({
            "name": name,
            "path": str(out_path),
            "type": metadata["strategy_type"],
            "tickers": metadata["tickers"][:5],
        })

    print(f"\nGenerated: {len(generated)} notebooks")

    if generated and not args.dry_run:
        print("\nTo execute via QC Cloud Docker:")
        print("  python scripts/notebook_tools/qc_batch_quantbooks.py --start-index X --timeout 1800")
        print("\nNote: update TARGETS list in qc_batch_quantbooks.py to include these projects")


if __name__ == "__main__":
    main()
