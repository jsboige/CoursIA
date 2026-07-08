# EMA-Cross-Crypto

**Classe d'actifs :** Crypto (BTC, ETH)
**ID projet Cloud :** Aucun (local uniquement)

## Description

Croisement dual EMA sur crypto. Prend position long quand EMA(20) > EMA(60) sur BTC/ETH.

## Figures du notebook de recherche

Le notebook [`research.ipynb`](research.ipynb) analyse le comportement du croisement EMA sur BTC : cours et moyennes mobiles, comparaison des configurations testées (CAGR, Sharpe, drawdown) et analyse des drawdowns par période. Provenance détaillée : [`MANIFEST.md`](assets/readme/MANIFEST.md).

<table>
<tr>
<td align="center"><img src="assets/readme/emacrypto-btc-emas.png" alt="BTC + moyennes mobiles" width="420"/><br/><sub>BTC — cours &amp; moyennes mobiles (EMA 20/60)</sub></td>
<td align="center"><img src="assets/readme/emacrypto-cagr.png" alt="CAGR par configuration" width="420"/><br/><sub>CAGR — comparaison des configurations</sub></td>
</tr>
<tr>
<td align="center"><img src="assets/readme/emacrypto-metrics.png" alt="Métriques Sharpe/CAGR/drawdown" width="420"/><br/><sub>Métriques — Sharpe / CAGR / drawdown</sub></td>
<td align="center"><img src="assets/readme/emacrypto-sharpe.png" alt="Sharpe par configuration" width="420"/><br/><sub>Sharpe — comparaison des configurations</sub></td>
</tr>
<tr>
<td align="center"><img src="assets/readme/emacrypto-drawdowns.png" alt="Drawdowns par période" width="420"/><br/><sub>Drawdowns — analyse par période (§9)</sub></td>
<td align="center"></td>
</tr>
</table>

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/EMA-Cross-Crypto"`
**QC Cloud :** Pas encore déployée. Copier les fichiers dans un nouveau projet QC Cloud pour l'exécuter.

## Métriques de backtest

| Métrique | Valeur |
|----------|--------|
| Méthode | Croisement EMA 20/60 |
| Univers | BTC, ETH |
| Rebalance | Quotidien |

## Fichiers

- main.py - Stratégie
