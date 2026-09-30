# OpeningRangeBreakout (ORB Stocks in Play)

Stratégie de **day-trading opening range breakout** sur actions US : portage fidèle
de l'article QuantConnect Research 18444 (Derek Melchin, QC Staff), lui-même une
reproduction partielle du papier Zarattini, Barbon & Aziz 2024, *A Profitable Day
Trading Strategy For The U.S. Equity Market* (SSRN 4729284).

## Mécanisme

1. **Univers** : les `universe_size` (défaut 1000) actions les plus liquides du coarse
   universe (prix > 5 $).
2. **"In play"** : volume relatif = volume des 5 premières minutes du jour / moyenne
   14 jours de ce même volume d'ouverture. Seuil > 1. Filtre ATR(14) > 0,50 $
   (volatility suffisante pour payer les frais).
3. **Range d'ouverture** : high/low des 5 premières minutes (résolution minute).
4. **Entrée** : ordre stop-market au niveau du haut du range après barre d'ouverture
   haussière (long) — symétrique au bas après barre baissière (short). 20 positions
   max, allouées par volume relatif décroissant.
5. **Stop** : entrée ∓ k × ATR(14), k = 1,0 par défaut (le corps de l'article ne
   chiffre pas k ; les backtests sources l'utilisent à 1,0).
6. **Sizing** : 1 % de risque par trade (distance au stop), plafonné au poids
   equal-weight 1/20.
7. **Sortie** : liquidation totale à 15:50 (stratégie intraday, flat au close).

## Paramètres (tous surchargeables en backtest)

| Paramètre | Défaut | Rôle |
|-----------|--------|------|
| `start_date` | 2016-01-01 | début de fenêtre (dev) |
| `end_date` | 2019-12-31 | fin de fenêtre (dev) |
| `universe_size` | 1000 | taille du coarse universe |
| `max_positions` | 20 | positions simultanées max |
| `opening_minutes` | 5 | durée du range d'ouverture |
| `atr_threshold` | 0.50 | ATR(14) minimal ($) |
| `stop_atr_distance` | 1.0 | multiplicateur k du stop |
| `risk_per_trade` | 0.01 | risque fraction par position |

## Garde-fous du portage (issue #16355)

1. **Fenêtre pleine 2016-2023** : dev 2016-2019 / OOS 2020-2023 via les paramètres
   `start_date` / `end_date` — l'article ne teste que 2016.
2. **Frais réalistes** : modèles QC par défaut (brokerage IBKR : commissions +
   slippage). La communauté mesure ~25 % de drag sur le PnL de cette stratégie.
3. **Params papier ET variante communauté** : 5 min / 1000 (article) et
   1 min / 2000 (variante communautaire) via `opening_minutes` / `universe_size`.
4. **Verdict conditionnel** : si l'edge ne survit pas aux frais sur la fenêtre
   pleine, verdict IGNORE avec preuve — la piste famille se referme.

## Piège de portage : la course scan/consolidateur

Première version du portage : 4 ans de backtest « Completed » avec **0 ordre**,
aucune erreur. Cause (mesurée par instrumentation, logs d'un run T1-2016) :
l'événement planifié `schedule.on(..., at(9, 35))` s'exécute **avant** la
distribution des données de 9:35 — celle-là même qui fait émettre au
`TradeBarConsolidator` sa barre 9:30-9:35. Le scan lisait donc un range
toujours vide (remis à `None` par les barres suivantes avant le lendemain
9:36). Correctif : scanner à `9:30 + opening_minutes + 2` — dans la fenêtre
où le range est émis et pas encore effacé.

Trois autres pièges Python/.NET démasqués en cascade une fois la chaîne
débloquée : la comparaison directe `indicator > x` et `float(indicator)`
échouent (utiliser `indicator.current.value`) ; le 4e argument positionnel
de `stop_market_order` est `asynchronous` (passer `tag=` en keyword) ; et
`total_portfolio_value` est un `decimal` C# (cast `float()` explicite avant
arithmétique Python).

Validation de la chaîne sur T1 2016 (2016-01-01 → 2016-03-31, code
instrumenté) : **2 376 ordres, Sharpe 2.098, CAGR 27.3 %, MaxDD 3.6 %**,
win rate 50 %, frais $1 726 (IBKR, inclus).

## Métriques de backtest

| Fenêtre | Période | Params | Sharpe | CAGR | MaxDD | PSR | Ordres | Frais | Verdict |
|---------|---------|--------|--------|------|-------|-----|--------|-------|---------|
| Dev (papier) | 2016-2019 | 5 min / 1000 | 0.167 | +4.10 % | 7.90 % | 2.11 % | 48 364 | $31 997 | NO BEATS (frais) |
| OOS | 2020-2023 | 5 min / 1000 | −0.467 | −5.23 % | 24.60 % | 0.02 % | 49 444 | $32 354 | NO BEATS |
| Communauté | 2016-2023 | 1 min / 2000 | *(en cours — run `3bf7776f…`, lancé 2026-09-20 12:02 UTC, params confirmés : « ~2000 symbols » au terminal)* | | | | | | |

Lecture fenêtre pleine (DEV + OOS) : l'edge de l'article **ne survit pas**. Sur DEV,
le net reste positif (+17.4 % sur 4 ans) mais les frais IBKR avalent ~32 % du capital
initial ($31 997 sur $100 000, turnover ~103 %/an) et le Sharpe tombe à 0.167 —
là où le T1 2016 isolé affichait 2.098 : cette fenêtre courte était une fenêtre
faste, pas une preuve. Sur OOS 2020-2023, la dégradation devient franche : net
−19.3 %, drawdown 24.6 %, PSR 0.02 %, rolling Sharpe 12 mois négatif sur presque
toute la fenêtre. Le garde-fou #4 (verdict IGNORE avec preuve) est armé sauf
revirement complet de la variante communauté — en cours.

## Références

- Melchin, D. (2024). *Opening Range Breakout Leveraging Opening Range & In Play
  Stocks*. QuantConnect Research 18444.
- Zarattini, C., Barbon, A., & Aziz, A. (2024). *A Profitable Day Trading Strategy
  For The U.S. Equity Market*. SSRN 4729284, DOI 10.2139/ssrn.4729284.
