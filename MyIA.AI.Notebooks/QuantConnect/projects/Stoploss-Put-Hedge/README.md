# Stoploss-Put-Hedge (HandsOn Ex08, partie 3)

**Classe d'actifs :** actions US (KO) + options KO (puts hebdomadaires)
**Exemple du livre :** 06/08/03 — ML Put Option Hedge

## Description

Portage de la troisième variante de l'exemple 08 du chapitre 06 : au lieu de
placer un stop, l'algorithme **couvre** sa position hebdomadaire sur KO par
l'achat d'un put. La même régression Lasso que
[Stoploss-Volatility-ML](../Stoploss-Volatility-ML/) (06/08/02) prédit le
rendement de l'ouverture de la semaine au plus bas de la semaine ; le plus bas
prédit sélectionne le strike (le plus haut strike sous `plus_bas_prédit +
ask`). Si le put est exercé, il clôt le sous-jacent ; sinon, put et actions
sont liquidés à l'ouverture de la semaine suivante.

Conditions du livre par défaut : 2018-12-31 → 2024-04-01, capital 100 k,
frais IBKR (modèle de brokerage), KO en `RAW`.

## Adaptation Cloud (même choix que 06/08/02)

Le VIX (`add_data(CBOE, "VIX")` dans le livre, moteur LEAN local) n'est pas
servi sur QC Cloud : la **volatilité réalisée de SPY** tient le rôle de
facteur de volatilité de marché. Les facteurs ATR et StdDev sont inchangés.

## Écarts au livre, écrits

- frais IBKR via `set_brokerage_model` (le livre pose
  `InteractiveBrokersFeeModel` par un security initializer) ;
- facteurs en listes Python plutôt que le `DataFrame` du livre ;
- si aucun put coté ne se qualifie sous le plus bas prédit, la semaine est
  journalisée et les actions restent nues (le livre planterait sur
  `sorted()[-1]`).

## Comment lancer

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Stoploss-Put-Hedge"`
**QC Cloud :** projet à créer (MCP `create_project`), puis `create_compile` → `create_backtest`.

## Métriques

À compléter par la comparaison à trois (stop fixe 06/08/01 · stop appris
06/08/02 · couverture par put 06/08/03) sur la même période, frais inclus —
voir `BOOK_MAPPING.md` lignes 08/01 à 08/03.

## Références

- Hands-On AI Trading, chapitre 06, exemple 08, partie 3
- Dépôt du livre : `QuantConnect/HandsOnAITradingBook` @ `e025f21`
