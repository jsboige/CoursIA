#!/usr/bin/env python3
"""
Generate research notebooks for QuantConnect strategies.

This script creates optimization research notebooks following the pattern
established in the robustness research workflow.
"""

import json
from pathlib import Path

# Strategy configurations
strategies = [
    {
        "name": "BTC-MACD-ADX-Researcher",
        "project_id": "28418632",  # Déjà créé
        "symbol": "BTCUSDT",
        "start_date": "2019-04-01",
        "end_date": "2025-02-01",
        "parameters": {
            "macd_fast": [12, 15, 18],
            "macd_slow": [21, 26, 30],
            "adx_window": [80, 100, 140],
            "adx_lower": [5, 10, 15],
            "adx_upper": [85, 90, 95]
        },
        "description": "BTC MACD+ADX with adaptive percentile thresholds"
    },
    {
        "name": "Sector-Momentum-Researcher",
        "project_id": "28433643",
        "symbol": "SPY",
        "start_date": "2020-01-01",
        "end_date": "2025-02-01",
        "parameters": {
            "vix_threshold": [20, 25, 30],
            "momentum_period": [1, 2, 4],  # weeks
            "leverage": [1.0, 1.5, 2.0]
        },
        "description": "Sector momentum with VIX filter"
    },
    {
        "name": "ETF-Pairs-Researcher",
        "project_id": "28433746",
        "symbol": "SPY+XLK+XLE+XLF+XLV",
        "start_date": "2020-01-01",
        "end_date": "2025-02-01",
        "parameters": {
            "z_entry": [-2.0, -1.5, -1.0],
            "z_exit": [0.0, 0.5, 1.0],
            "half_life": [20, 30, 40],  # days
            "correlation_threshold": [0.7, 0.8, 0.9]
        },
        "description": "ETF pairs trading with cointegration filter"
    },
    {
        "name": "Multi-Layer-EMA-Researcher",
        "project_id": "28433748",
        "symbol": "SPY",
        "start_date": "2020-01-01",
        "end_date": "2025-02-01",
        "parameters": {
            "fast_ema": [8, 12, 18],
            "slow_ema": [21, 26, 34],
            "trend_ema": [50, 100, 200],
            "trailing_stop": [0.08, 0.10, 0.12]  # 8%, 10%, 12%
        },
        "description": "Multi-layer EMA with trailing stop"
    },
    {
        "name": "Option-Wheel-Researcher",
        "project_id": "28433749",
        "symbol": "SPY",
        "start_date": "2019-01-01",
        "end_date": "2025-02-01",
        "parameters": {
            "delta_target": [-20, -30, -40],  # Short put delta
            "dte_entry": [25, 30, 40],  # Days to expiration
            "dte_exit": [7, 14, 21],
            "strike_width": [5, 10, 15]  # Strike spacing
        },
        "description": "Option wheel strategy for income generation"
    },
    {
        "name": "BTC-ML-Researcher",
        "project_id": "28433750",
        "symbol": "BTCUSDT",
        "start_date": "2019-01-01",
        "end_date": "2025-02-01",
        "parameters": {
            "lookback_period": [365, 730, 1090],  # days
            "retraining_frequency": [30, 60, 90],  # days
            "train_period": ["2019-2022", "2020-2023", "2021-2024"]
        },
        "description": "BTC Machine Learning with walk-forward"
    }
]

def create_notebook_template(strategy):
    """Create a research notebook template for a strategy."""

    cells = [
        {
            "cell_type": "markdown",
            "metadata": {},
            "source": [
                f"# {strategy['name']} - Robustness Research\n",
                "\n",
                f"**Objective**: Analyze the {strategy['description']} across different market regimes and optimize parameters.\n",
                "\n",
                f"**Symbol**: {strategy['symbol']}\n",
                f"**Period**: {strategy['start_date']} to {strategy['end_date']}\n",
                "\n",
                "**Research Goals**:\n",
                "1. Identify market regimes (bull/bear/sideways)\n",
                "2. Analyze performance by regime\n",
                "3. Test parameter sensitivity\n",
                "4. Validate robustness with walk-forward analysis"
            ]
        },
        {
            "cell_type": "code",
            "execution_count": None,
            "metadata": {},
            "outputs": [],
            "source": [
                "# Cell 1: Setup QuantBook and load data\n",
                "from QuantConnect.Research import QuantBook\n",
                "import pandas as pd\n",
                "import numpy as np\n",
                "import matplotlib.pyplot as plt\n",
                "from datetime import datetime, timedelta\n",
                "\n",
                "# Initialize QuantBook\n",
                "qb = QuantBook()\n",
                "\n",
                f"# Add assets\n",
                f"symbol_list = '{strategy['symbol']}'.replace(' ', '').split('+')\n",
                "symbols = [qb.AddEquity(a, Resolution.DAILY).Symbol for a in symbol_list]\n",
                "\n",
                f"# Fetch historical data\n",
                f"start_date = datetime({strategy['start_date'][:4].replace('-', ', ')})\n",
                f"end_date = datetime({strategy['end_date'][:4].replace('-', ', ')})\n",
                "\n",
                "print(f\"Fetching data from {start_date} to {end_date}...\")\n",
                "history = qb.History(symbols, start_date, end_date, Resolution.DAILY)\n",
                "print(f\"Loaded {len(history)} bars\")"
            ]
        },
        {
            "cell_type": "code",
            "execution_count": None,
            "metadata": {},
            "outputs": [],
            "source": [
                "# Cell 2: Detect market regimes\n",
                "\n",
                "def detect_regimes(prices, window=50):\n",
                "    \"\"\"Detect bull/bear/sideways regimes based on trend and volatility.\"\"\"\n",
                "    returns = prices.pct_change()\n",
                "    rolling_return = returns.rolling(window).sum()\n",
                "    \n",
                "    regimes = pd.Series(index=returns.index, dtype=object)\n",
                "    for i in range(window, len(returns)):\n",
                "        if rolling_return.iloc[i] > 0.05:\n",
                "            regimes.iloc[i] = \"BULL\"\n",
                "        elif rolling_return.iloc[i] < -0.05:\n",
                "            regimes.iloc[i] = \"BEAR\"\n",
                "        else:\n",
                "            regimes.iloc[i] = \"SIDEWAYS\"\n",
                "    return regimes\n",
                "\n",
                "# TODO: Implement regime detection\n",
                "print(\"Regime detection to be implemented\")"
            ]
        },
        {
            "cell_type": "code",
            "execution_count": None,
            "metadata": {},
            "outputs": [],
            "source": [
                "# Cell 3: Parameter grid search\n",
                "\n",
                "parameters = " + json.dumps(strategy['parameters'], indent=2) + "\n",
                "\n",
                "print(\"Testing parameter combinations:\")\n",
                "for param, values in parameters.items():\n",
                "    print(f\"  {param}: {values}\")\n",
                "\n",
                "# TODO: Implement grid search with backtesting\n",
                "print(\"\\nGrid search to be implemented\")"
            ]
        },
        {
            "cell_type": "code",
            "execution_count": None,
            "metadata": {},
            "outputs": [],
            "source": [
                "# Cell 4: Walk-forward validation\n",
                "\n",
                "def walk_forward_analysis(prices, params):\n",
                "    \"\"\"Perform walk-forward analysis.\"\"\"\n",
                "    # TODO: Implement walk-forward\n",
                "    pass\n",
                "\n",
                "# TODO: Validate robustness (OOS/IS ratio > 60%)\n",
                "print(\"Walk-forward analysis to be implemented\")"
            ]
        },
        {
            "cell_type": "markdown",
            "metadata": {},
            "source": [
                "## Next Steps\n",
                "\n",
                "1. Execute this notebook with QuantConnect Jupyter MCP\n",
                "2. Implement the TODO cells above\n",
                "3. Analyze results and optimize parameters\n",
                "4. Export recommendations as JSON\n",
                "5. Apply changes to strategy code\n",
                "6. Run backtest to validate improvements"
            ]
        }
    ]

    notebook = {
        "cells": cells,
        "metadata": {
            "kernelspec": {
                "display_name": "Python 3",
                "language": "python",
                "name": "python3"
            }
        },
        "nbformat": 4,
        "nbformat_minor": 4
    }

    return notebook

def main():
    """Generate notebooks for all strategies."""

    base_path = Path("c:/dev/CoursIA/MyIA.AI.Notebooks/QuantConnect/ESGF-2026/examples")

    for strategy in strategies:
        # Create directory
        strategy_path = base_path / strategy['name']
        strategy_path.mkdir(parents=True, exist_ok=True)

        # Generate notebook
        notebook = create_notebook_template(strategy)

        # Save notebook
        notebook_path = strategy_path / "research_optimization.ipynb"
        with open(notebook_path, 'w') as f:
            json.dump(notebook, f, indent=2)

        print(f"✓ Created: {notebook_path}")

    print(f"\nGenerated {len(strategies)} research notebooks")
    print("\nStrategies:")
    for s in strategies:
        print(f"  - {s['name']} (Project ID: {s['project_id']})")

if __name__ == "__main__":
    main()
