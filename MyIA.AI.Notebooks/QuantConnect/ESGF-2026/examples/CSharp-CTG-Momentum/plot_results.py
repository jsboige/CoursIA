# Generate visual summary of research results
import pandas as pd
import numpy as np
from datetime import datetime
import matplotlib.pyplot as plt
import yfinance as yf
import warnings
warnings.filterwarnings('ignore')

# Load data (quick version)
spy_data = yf.download('SPY', start='2015-01-01', end='2026-02-17', progress=False)
if isinstance(spy_data.columns, pd.MultiIndex):
    spy_data.columns = spy_data.columns.droplevel(1)

spy_data['SMA_200'] = spy_data['Close'].rolling(200).mean()
spy_data['Regime'] = (spy_data['Close'] > spy_data['SMA_200']).astype(int)

# Create visualization
fig, axes = plt.subplots(2, 1, figsize=(16, 10))

# Plot 1: SPY with SMA(200) and regime shading
ax1 = axes[0]
ax1.plot(spy_data.index, spy_data['Close'], label='SPY Close', linewidth=1.5, color='blue')
ax1.plot(spy_data.index, spy_data['SMA_200'], label='SMA(200)', linewidth=1.5, linestyle='--', color='orange')
ax1.fill_between(spy_data.index, 0, spy_data['Close'].max() * 1.1, 
                 where=spy_data['Regime']==0, alpha=0.2, color='red', label='Risk-OFF')
ax1.set_ylabel('SPY Price ($)', fontsize=12)
ax1.set_title('CTG-Momentum Strategy: SPY SMA(200) Regime Filter (2015-2025)', fontsize=14, fontweight='bold')
ax1.legend(loc='upper left', fontsize=10)
ax1.grid(alpha=0.3)

# Annotate key periods
ax1.annotate('COVID Crash', xy=(datetime(2020, 3, 15), 250), xytext=(datetime(2020, 6, 1), 200),
            arrowprops=dict(arrowstyle='->', color='red', lw=1.5), fontsize=10, color='red')
ax1.annotate('Inflation Bear', xy=(datetime(2022, 6, 15), 380), xytext=(datetime(2022, 9, 1), 320),
            arrowprops=dict(arrowstyle='->', color='red', lw=1.5), fontsize=10, color='red')
ax1.annotate('AI Bull', xy=(datetime(2023, 6, 1), 440), xytext=(datetime(2023, 3, 1), 520),
            arrowprops=dict(arrowstyle='->', color='green', lw=1.5), fontsize=10, color='green')

# Plot 2: Walk-forward results
wf_data = {
    'period': ['2017-01', '2017-07', '2018-01', '2018-07', '2019-01', '2019-07',
               '2020-01', '2020-07', '2021-01', '2021-07', '2022-01', '2022-07',
               '2023-01', '2023-07', '2024-01', '2024-07'],
    'strategy': [8.18, 31.56, 16.89, -11.26, -0.98, 5.51, 1.39, 56.68, -7.52, 18.84,
                 -19.77, -6.45, 41.62, -4.81, 31.66, 23.43],
    'spy': [8.35, 11.29, 1.79, -7.11, 18.20, 9.90, -4.10, 21.40, 16.83, 11.09,
            -20.44, 1.19, 17.28, 7.92, 15.87, 8.16]
}
wf_df = pd.DataFrame(wf_data)

ax2 = axes[1]
x = np.arange(len(wf_df))
width = 0.35
bars1 = ax2.bar(x - width/2, wf_df['strategy'], width, label='Stratégie CTG-Momentum', color='steelblue')
bars2 = ax2.bar(x + width/2, wf_df['spy'], width, label='SPY', color='lightcoral')

ax2.axhline(0, color='black', linewidth=0.8, linestyle='-')
ax2.set_ylabel('Rendement (%)', fontsize=12)
ax2.set_xlabel('Période (6 mois)', fontsize=12)
ax2.set_title('Walk-Forward Validation: Stratégie vs SPY (périodes de 6 mois)', fontsize=14, fontweight='bold')
ax2.set_xticks(x)
ax2.set_xticklabels(wf_df['period'], rotation=45, ha='right', fontsize=9)
ax2.legend(fontsize=10)
ax2.grid(axis='y', alpha=0.3)

plt.tight_layout()
plt.savefig('research_robustness_charts.png', dpi=150, bbox_inches='tight')
print("✅ Graphique sauvegardé: research_robustness_charts.png")
plt.close()

# Create summary stats table
print("\n" + "="*70)
print("RÉSUMÉ STATISTIQUES")
print("="*70)
print(f"\nSharpe Ratio: 1.050")
print(f"CAGR: 23.45%")
print(f"Max Drawdown: 31.03%")
print(f"Total Return (11.1 ans): +935.90%")
print(f"\nRisk-ON time: 76.8%")
print(f"Win rate (6-month periods): 62.5% (10/16)")
print(f"Alpha moyen vs SPY: +4.21%")
print("\n✅ Recherche terminée avec succès!")
