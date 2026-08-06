# EMA-Cross-Stocks

**Classe d'actifs :** Actions US (Grandes capitalisations tech)
**ID projet Cloud :** 28789946

## Description

Stratégie de croisement EMA dual (rapide=20, lente=50) appliquée à 5 grandes valeurs
tech (AAPL, MSFT, GOOGL, AMZN, NVDA), avec allocation equal-weight entre les actions en
tendance haussière. Long sur chaque action lorsque son EMA20 > EMA50, sinon flat ;
rebalance quotidien, seuil de 5 % pour déclencher un trade, 5 positions max.

Version « algorithm manual » (logique de signal écrite à la main dans `on_data`), à
distinguer du sibling **EMA-Cross-Alpha** qui expose le même signal EMA 20/50 via le
framework QuantConnect Alpha Model.

Paramètre `brokerage` : par défaut IBKR Margin (frais réalistes) ; passer
`brokerage=none` pour une baseline sans frais.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/EMA-Cross-Stocks"`
```bash
lean backtest --project .
```

**QC Cloud :** Ouvrir le projet 28789946 dans l'IDE QuantConnect et cliquer sur « Backtest ».

## Métriques de backtest (2015-2024)

| Métrique | Valeur |
|----------|--------|
| Sharpe Ratio | 0.991 |
| CAGR | 29.230% |
| Max Drawdown | 35.700% |
| Net Profit | 1201.476% |
| PSR | 33.664% |
| Total Orders | 1424 |
| Benchmark | SPY |
| Rebalance | Quotidien |
| Univers | 5 actions tech (Mag7) |
| Brokerage | IBKR Margin |

> **Provenance** : backtest QC Cloud `ecfe78ddcf385d2ba795bcb88644e607` (2026-08-06),
> projet 28789946, IBKR margin, capital initial 100 000 $, 2516 jours tradeables
> (2015-01-01 → 2024-12-31). Re-exécuter via QC Cloud pour recalculer.
>
> **Lecture honnête** : un CAGR de 29,2 % et un Net Profit de +1201 % paraissent
> spectaculaires, mais sont **essentiellement dus au beta du marché, pas au signal EMA**.
> L'univers (AAPL, MSFT, GOOGL, AMZN, NVDA — les « Mag7 ») a multiplié sa valeur par
> ~10 sur la décennie ; un simple buy & hold de ces 5 actions aurait produit un
> rendement similaire voire supérieur. Le signal EMA (long-only quand EMA20 > EMA50)
> agit comme un filtre de tendance sur un univers déjà fortement haussier — il n'extrait
> pas d'alpha. Le Sharpe de 0,991 est correct, mais le PSR de 33,7 % (< 50 %) reste sous
> le seuil de confiance statistique, et le Max Drawdown de 35,7 % (creux de 2022)
> illustre un risque réel. **Cette stratégie est une démonstration pédagogique du
> croisement EMA, pas une stratégie alpha.** Comparer avec le contre-exemple
> EMA-Cross-Alpha (même signal via le framework Alpha Model), qui sous-performe SPY
> (Sharpe -0,01).

## Fichiers

- `main.py` - Stratégie de croisement EMA (algorithm « manual », sans Alpha Model)
- `README.en.md` - Version anglaise (original historique, non mise à jour)

## Références

- Sibling : EMA-Cross-Alpha (même signal EMA 20/50 via le framework Alpha Model)
- Réf : Brock et al. (1992), moving average trading rules
