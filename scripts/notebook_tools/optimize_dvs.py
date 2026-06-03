"""Optimize DynamicVIXSpyRegime-QC notebook for faster execution."""
import json
import sys

path = r"c:\dev\CoursIA\MyIA.AI.Notebooks\QuantConnect\projects\DynamicVIXSpyRegime-QC\research.ipynb"
with open(path, "r", encoding="utf-8") as f:
    nb = json.load(f)

cells = nb["cells"]

# Cell 4: shorten date range from 2005 to 2015
cells[4]["source"] = [
    "TICKERS = ['SPY', 'TLT', 'GLD', 'BIL']\n",
    "DATA_START = '2015-01-01'\n",
    "DATA_END = '2025-12-31'\n",
    "\n",
    'print("Telechargement donnees yfinance...")\n',
    "raw = yf.download(TICKERS + ['^VIX'], start=DATA_START, end=DATA_END, auto_adjust=True)\n",
    "\n",
    "# Extract close prices\n",
    "if isinstance(raw.columns, pd.MultiIndex):\n",
    "    prices = raw['Close'][TICKERS].dropna()\n",
    "    vix_raw = raw['Close']['^VIX'].dropna()\n",
    "else:\n",
    "    prices = raw[TICKERS].dropna()\n",
    "    vix_raw = raw['^VIX'].dropna()\n",
    "\n",
    "vix = vix_raw.reindex(prices.index).ffill().bfill()\n",
    "prices = prices.reindex(vix.index).dropna()\n",
    "\n",
    'print(f"Periode: {prices.index[0].date()} a {prices.index[-1].date()}")\n',
    'print(f"Jours de trading: {len(prices)}")\n',
    'print(f"\\nRendements annuels (SPY):")\n',
    "spy_ret = prices['SPY'].pct_change().dropna()\n",
    "ann_ret = spy_ret.resample('YE').apply(lambda x: (1+x).prod()-1)\n",
    'for y, r in ann_ret.items():\n',
    '    print(f"  {y.year}: {r:.1%}")\n',
]

# Cell 11: H1 reduce thresholds from 5 to 3
cells[11]["source"] = [
    "thresholds = [0.50, 0.60, 0.70]\n",
    "results_h1 = []\n",
    "fig, axes = plt.subplots(1, 2, figsize=(16, 6))\n",
    "for thr in thresholds:\n",
    "    eq, met = backtest_dvs(prices, vix, {'ml_threshold': thr})\n",
    "    met['threshold'] = thr\n",
    "    results_h1.append(met)\n",
    "    axes[0].plot(eq.index, eq.values, label=f\"thr={thr} S={met['Sharpe']:.2f}\", linewidth=1)\n",
    "\n",
    'axes[0].set_title("H1: Impact du seuil ML")\n',
    "axes[0].legend(fontsize=8)\n",
    "axes[0].grid(True, alpha=0.3)\n",
    "\n",
    "df_h1 = pd.DataFrame(results_h1)\n",
    "axes[1].bar(range(len(df_h1)), df_h1['Sharpe'], tick_label=[str(t) for t in thresholds], color='steelblue')\n",
    'axes[1].set_title("Sharpe par seuil ML")\n',
    "plt.tight_layout()\n",
    "plt.show()\n",
    'print("\\nH1 Resultats:")\n',
    "print(df_h1[['threshold', 'Sharpe', 'CAGR', 'MaxDD', 'WinRate']].to_string(index=False))\n",
]

# Cell 13: H2 reduce VIX configs from 5 to 3
cells[13]["source"] = [
    "vix_configs = [\n",
    "    {'label': 'Defaut (13/80)', 'vix_low': 13, 'vix_pctile': 80},\n",
    "    {'label': 'Large (10/85)', 'vix_low': 10, 'vix_pctile': 85},\n",
    "    {'label': 'Reactif (16/70)', 'vix_low': 16, 'vix_pctile': 70},\n",
    "]\n",
    "results_h2 = []\n",
    "fig, ax = plt.subplots(figsize=(14, 6))\n",
    "for cfg in vix_configs:\n",
    "    eq, met = backtest_dvs(prices, vix, {'vix_low': cfg['vix_low'], 'vix_pctile': cfg['vix_pctile']})\n",
    "    met['config'] = cfg['label']\n",
    "    results_h2.append(met)\n",
    "    ax.plot(eq.index, eq.values, label=f\"{cfg['label']} S={met['Sharpe']:.2f}\", linewidth=1)\n",
    'ax.set_title("H2: Impact des frontieres VIX")\n',
    "ax.legend(fontsize=8)\n",
    "ax.grid(True, alpha=0.3)\n",
    "plt.tight_layout()\n",
    "plt.show()\n",
    "df_h2 = pd.DataFrame(results_h2)\n",
    'print("\\nH2 Resultats:")\n',
    "print(df_h2[['config', 'Sharpe', 'CAGR', 'MaxDD', 'WinRate']].to_string(index=False))\n",
]

# Cell 15: H3 reduce exposures from 5 to 3
cells[15]["source"] = [
    "exposures = [1.0, 1.5, 2.0]\n",
    "results_h3 = []\n",
    "fig, axes = plt.subplots(1, 2, figsize=(16, 6))\n",
    "for exp in exposures:\n",
    "    eq, met = backtest_dvs(prices, vix, {'gross': exp})\n",
    "    met['exposure'] = exp\n",
    "    results_h3.append(met)\n",
    "    axes[0].plot(eq.index, eq.values, label=f\"G={exp:.2f} S={met['Sharpe']:.2f}\", linewidth=1)\n",
    'axes[0].set_title("H3: Impact de l exposition brute")\n',
    "axes[0].legend(fontsize=8)\n",
    "axes[0].grid(True, alpha=0.3)\n",
    "df_h3 = pd.DataFrame(results_h3)\n",
    "axes[1].bar(range(len(df_h3)), df_h3['Sharpe'], tick_label=[str(e) for e in exposures], color='steelblue')\n",
    'axes[1].set_title("Sharpe vs Exposition")\n',
    "plt.tight_layout()\n",
    "plt.show()\n",
    'print("\\nH3 Resultats:")\n',
    "print(df_h3[['exposure', 'Sharpe', 'CAGR', 'MaxDD', 'WinRate']].to_string(index=False))\n",
]

# Cell 17: H4 reduce train windows from 5 to 3
cells[17]["source"] = [
    "windows = [252*3, 252*4, 252*5]\n",
    "window_labels = ['3Y', '4Y', '5Y']\n",
    "results_h4 = []\n",
    "fig, ax = plt.subplots(figsize=(14, 6))\n",
    "for w, lbl in zip(windows, window_labels):\n",
    "    eq, met = backtest_dvs(prices, vix, {'train_window': w})\n",
    "    met['window'] = lbl\n",
    "    results_h4.append(met)\n",
    "    ax.plot(eq.index, eq.values, label=f\"{lbl} S={met['Sharpe']:.2f}\", linewidth=1)\n",
    'ax.set_title("H4: Impact de la fenetre d entrainement")\n',
    "ax.legend(fontsize=9)\n",
    "ax.grid(True, alpha=0.3)\n",
    "plt.tight_layout()\n",
    "plt.show()\n",
    "df_h4 = pd.DataFrame(results_h4)\n",
    'print("\\nH4 Resultats:")\n',
    "print(df_h4[['window', 'Sharpe', 'CAGR', 'MaxDD', 'WinRate']].to_string(index=False))\n",
]

# Cell 21: Walk-forward reduce to 2 periods (data starts 2015 now)
cells[21]["source"] = [
    "wf_periods = [\n",
    "    ('2016-2019', '2016-01-01', '2019-12-31'),\n",
    "    ('2020-2025', '2020-01-01', '2025-12-31'),\n",
    "]\n",
    "\n",
    "wf_results = []\n",
    "fig, ax = plt.subplots(figsize=(14, 6))\n",
    "\n",
    "for label, start, end in wf_periods:\n",
    "    ws = pd.Timestamp(start) - pd.DateOffset(years=4)\n",
    "    mask_full = (prices.index >= ws) & (prices.index <= end)\n",
    "    p_full = prices.loc[mask_full]\n",
    "    v_full = vix.reindex(p_full.index).ffill().bfill()\n",
    "    p_full = p_full.dropna()\n",
    "\n",
    "    eq, met = backtest_dvs(p_full, v_full)\n",
    "    mask_sub = (eq.index >= start) & (eq.index <= end)\n",
    "    eq_sub = eq.loc[mask_sub]\n",
    "    met_sub = calculate_metrics(eq_sub)\n",
    "    met_sub['Period'] = label\n",
    "    wf_results.append(met_sub)\n",
    "    ax.plot(eq_sub.index, eq_sub.values,\n",
    "            label=f\"{label} S={met_sub['Sharpe']:.2f}\", linewidth=1)\n",
    "\n",
    'ax.set_title("Walk-Forward: Equity par periode")\n',
    "ax.legend()\n",
    "ax.grid(True, alpha=0.3)\n",
    "plt.tight_layout()\n",
    "plt.show()\n",
    "\n",
    "df_wf = pd.DataFrame(wf_results)\n",
    'print("\\nWalk-Forward Resultats:")\n',
    "print(df_wf[['Period', 'Sharpe', 'CAGR', 'MaxDD', 'WinRate']].to_string(index=False))\n",
]

# Clear all execution_count and outputs
for cell in cells:
    if cell["cell_type"] == "code":
        cell["execution_count"] = None
        cell["outputs"] = []

with open(path, "w", encoding="utf-8") as f:
    json.dump(nb, f, indent=1, ensure_ascii=False)

print("DynamicVIX optimized:")
print("  - Date range: 2015-2025 (was 2005-2025)")
print("  - H1 thresholds: 3 (was 5)")
print("  - H2 VIX configs: 3 (was 5)")
print("  - H3 exposures: 3 (was 5)")
print("  - H4 train windows: 3 (was 5)")
print("  - Walk-forward: 2 periods (was 3)")
print(f"  - Total backtests: ~15 (was ~24)")
