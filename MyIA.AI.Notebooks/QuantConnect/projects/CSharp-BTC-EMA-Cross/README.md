# BTC EMA Cross Daily (C#)

Croisement EMA rapide/lente sur `BTCUSDT` en C#. Algorithme de référence pour
l'enseignement de la structure d'un algorithme QuantConnect en C#, des indicateurs
EMA paramétrables, et du modèle de brokerage Binance (compte Cash, USDT).

## Stratégie

- **Actif** : `BTCUSDT` (Binance, résolution Daily, compte Cash en USDT)
- **Signaux** : EMA rapide 18 / EMA lente 23 (périodes proches → croisements fréquents)
- **Filtre anti-whipsaw** : bande de marge ±0,1 % (`UpCrossMargin 1.001` / `DownCrossMargin 0.999`) — on n'entre ou ne sort que sur dépassement franchi, pas sur micro-croisement
- **Position** : long-only, 100 % (`SetHoldings 1.0`) à l'achat, `Liquidate` à la vente
- **Capital initial** : 600 000 USDT
- **Période** : 2017-10-01 → 2025-01-01 (bull 2017, bear 2018, recovery 2019, COVID 2020, bull 2020-21, bear 2022, recovery 2023-25)

## Métriques de backtest (QC Cloud, run frais 2026-08-06)

Backtest single-asset Daily sur 2 650 jours tradables, 50 ordres exécutés (≈ 25
allers-retours, soit ~3,5 par an — la bande de marge filtre efficacement les
micro-croisements).

| Métrique | Valeur |
|----------|--------|
| Sharpe Ratio | 1.287 |
| CAGR (rendement annuel composé) | 44.75 % |
| Drawdown maximal | 54.60 % |
| Rendement total net | +1367.5 % |
| Probabilistic Sharpe Ratio (PSR) | 49.77 % |
| Ordres exécutés | 50 |

## Lecture honnête

Le résultat est **nuancé**, et c'est ce qui le rend pédagogiquement intéressant —
on n'est ni dans l'échec franc, ni dans l'edge miraculeux.

1. **Sous-performance vs buy-and-hold en rendement brut.** Sur la même période, le
   BTC nu passe de ~4 300 $ (oct. 2017) à ~96 000 $ (janv. 2025), soit ~+2 100 % et
   un CAGR de l'ordre de ~53 % (estimation depuis les prix publics ; le benchmark
   exact n'est pas repris dans les statistiques retournées). La stratégie
   (+1 367 %, CAGR 44.75 %) laisse donc de l'argent sur la table : long-only avec
   sortie sur croisement descendant, elle reste en USDT pendant les jambes de
   reprise précoce et rate une partie de la tendance dominante. C'est le coût
   structurel d'un indicateur lagging (l'EMA confirme la tendance après le fait)
   sur un actif à tendance long-terme marquée.

2. **Réduction du drawdown.** L'avantage : la stratégie coupe le portefeuille en
   USDT sur les croisements descendants, ce qui limite le drawdown à 54.60 %, contre
   ~80 % pour le BTC nu (krach 2018 ≈ -84 %, krach 2022 ≈ -76 %). Le timing achète
   donc moins de rendement contre moins de douleur — un compromis risk-return, pas
   un alpha.

3. **Sharpe 1.287 mais PSR ~50 %.** Le Probabilistic Sharpe Ratio de 49.77 % signifie
   que le Sharpe observé n'est **pas statistiquement distinguable du hasard** au seuil
   usuel (on viserait PSR > 95 % pour un edge robuste). Sur un seul actif et une seule
   période, ce n'est pas une preuve d'edge : c'est cohérent avec l'hypothèse qu'une
   EMA cross est un filtre de tendance, pas un prédicteur.

**Verdict honnête** : NO-BEATS en rendement brut (inférieur au buy-and-hold),
drawdown réduit (54.6 % vs ~80 %), edge statistiquement non robuste (PSR ~50 %).
Stratégie valable comme illustration pédagogique d'un croisement de moyennes avec
filtre de marge et brokerage crypto — pas comme source d'alpha.

## Fichiers

- `Main.cs` — `BtcEmaCrossDaily1Algorithm` : EMA cross avec marges configurables,
  charting (Price / Portfolio Value / Fast EMA / Slow EMA), Binance Cash brokerage
- `research_robustness.ipynb` — étude de robustesse (C# Research Environment)
- `RESEARCH_INSTRUCTIONS.md` — consignes de l'étude de recherche

## Concepts enseignés

- Structure d'un algorithme QuantConnect en C# (`QCAlgorithm`)
- Indicateurs EMA paramétrés (`[Parameter]` ema-fast / ema-slow / marges)
- Bande de marge anti-whipsaw (up/down cross margin)
- Chart API (`Chart` / `Series` / `Plot`) + `Schedule.On`
- Modèle de brokerage Binance, compte Cash, devise USDT
- Lecture critique d'un backtest : rendement vs drawdown vs significance statistique (PSR)
