# TradingCosts-Optimization (Hands-On AI Trading, Exemple 12)

**Classe d'actifs :** Crypto — BTCUSDC (Bybit)
**ID projet Cloud :** Aucun (local uniquement — voir `## État d'exécution`)
**Référence :** *Hands-On AI Trading with Python, QuantConnect, and AWS*, Chapitre 6 (Applied Machine Learning), Exemple 12

## Description

Démonstration pédagogique de **prédiction du coût d'exécution** par apprentissage
supervisé. Un `DecisionTreeRegressor` prédit le coût total (frais + slippage) d'un
ordre de marché BTCUSDC à partir de cinq facteurs micro-structurels. La
stratégie n'exécute la sortie **que si le coût prédit par dollar tombe sous la
moyenne mobile historique** — sinon elle attend l'heure suivante.

L'objectif n'est **pas** d'optimiser un Sharpe. C'est d'illustrer comment un
classifieur léger peut servir de **policy de时机** (timing) sur l'exécution, en
distinguant les fenêtres où le carnet est favorable.

## Univers et fenêtre

| Paramètre | Valeur | Source |
|-----------|--------|--------|
| Ticker | `BTCUSDC` | `main.py:69` (`self.add_crypto("BTCUSDC", market=Market.BYBIT)`) |
| Brokerage | `BINANCE`, `AccountType.CASH` | `main.py:51` |
| Date début | 2015-01-01 | `main.py:43` |
| Date fin | 2024-01-01 | `main.py:44` |
| Capital initial | 10 000 000 USDC | `main.py:45` |
| Univers | 1 actif (BTCUSDC) — hors Mag7, hors FAANG, pas de contamination secteurs | déduit verbatim |
| Fenêtre | 9 ans (cycle complet incluant bull 2020-21 + bear 2022) | déduit verbatim |

> **Note sur le périmètre.** L'univers étant réduit à un seul actif crypto
> (BTC), les garde-fous anti-Mag7 / anti-FAANG imposés aux stratégies actions
> (`Mag7-bêta`, C865/C843) **ne s'appliquent pas ici** — il n'y a pas
> d'exposition aux GAFAM, Nvidia ou Tesla. Le data leakage Mag7 documenté sur
> `#9434` ne concerne pas cette stratégie.

## Mécanique d'exécution

| Étape | Heure UTC | Rôle | Source |
|-------|-----------|------|--------|
| Entrée | 00:00 chaque jour | Market order buy 10 BTC si pas déjà en position | `main.py:_entry` (L93-99) |
| Scan décision | continu (entre 01:00 et 23:59) | Si le coût prédit/dollar < SMA(10) → exit signal | `main.py:on_data` (L161-201) |
| Sortie benchmark | 01:00 chaque jour | Liquidate immédiat (mode `benchmark=True`) | `main.py:_exit_schedule` (L106-114) |
| Sortie ML | 01:00-23:59 | `market_order(-10, tag=...)` quand la politique ML le permet | `main.py:on_data` (L196-201) |
| Retrain modèle | 00:00 chaque 1er du mois | `_train_model` sur les 100 derniers fills | `main.py:initialize` (L91) |

## Modèle et facteurs

`DecisionTreeRegressor(max_depth=5, random_state=0)` (L137-140). Cinq facteurs
extraits du carnet Bybit au moment du scan :

| # | Facteur | Calcul |
|---|---------|--------|
| 1 | `abs_order_quantity` | `abs(self._quantity)` |
| 2 | `atr` | ATR(14) journalier (`self._atr`) |
| 3 | `avg_daily_volume` | SMA(10) du volume journalier (`self._sma`) |
| 4 | `spread_pct` | `(ask - bid) / bid` |
| 5 | `top_of_book_size` | `ask_size * ask` (en USD) |

Le modèle est **réentraîné mensuellement** sur les 100 derniers fills réels
(`on_order_event` enregistre chaque coût = `order_fee.value + slippage_per_share * quantity`).
La fenêtre d'entraînement vivante est élaguée via `_trim_samples` (L151-153).

## Sortie de l'algorithme

À `on_end_of_algorithm` (L242-246), le DataFrame `_order_fills` est **persisté
dans l'Object Store QuantConnect** sous deux clés : `benchmark_order_fills` ou
`candidate_order_fills` selon le mode. Ce sont les seuls artefacts conservés
hors mémoire vive — l'algorithme ne **retourne pas** un Sharpe/CAGR car sa
métrique de validation est le coût prédit vs coût réel, pas une courbe
d'equity.

## État d'exécution (lecture honnête)

| Item | État au 2026-08-06 |
|------|---------------------|
| Code de la stratégie | ✅ Présent sur main (`main.py` intact) |
| Notebook QC Cloud (`quantbook.ipynb`) | ❌ Absent — projet cloud jamais créé |
| Backtest live exécuté via Lean CLI / MCP | ❌ Jamais exécuté localement |
| Notebook recherche local (`research.ipynb`) | ❌ Absent — pas de backtest companion |
| Métriques chiffrées | ⚠️ **AUCUNE** dans ce README — le code ne les produit pas, et aucune exécution préalable n'est disponible |
| `Sharpe Ratio` hardcodé dans README original | ❌ Aucun (la version EN non plus — claim honnête par défaut) |

> **Lecture critique.** Le README original (EN) indique _« Educational demo »_
> et _« Not yet deployed »_, ce qui est conforme à la réalité du code
> (`Cloud project ID: None`). Aucun Sharpe/CAGR/MaxDD n'apparaît — la lecture
> honnête prime sur la fabrication de chiffres. Pour obtenir des métriques
> réelles, deux chemins existent :
>
> 1. **Déployer sur QC Cloud** (`lean cloud push` via l'orchestrateur Stop&Repair
>    livré par #9749 puis `lean cloud backtest`) — bloqué tant que G529-L1
>    (`[ASK USER] clés API/QC-Cloud`) n'est pas levé.
> 2. **Exécuter localement via Lean CLI** (`lean backtest "..."`) — hors portée
>    de cette PR (refactor QC distinct, scope séparé).

## Diagnostic dérive (cf EPIC #8052/#3801)

> Section obligatoire pour toute PR d'alignement de README doc-honesty (cf
> PR #8052, #3801, #9511, #9527, #9530, #9537, #9542, #9550, #9569, #9610,
> #9667, #9696, #9714, #9748, #9754, #9757).

**(a) env / kernel** — N/A : PR strictement README, aucun code exécuté.
**(b) claim antérieure fabriquée** — N/A : le README EN originel ne comporte
**aucun** chiffre de performance (ni Sharpe, ni CAGR, ni MaxDD). Pas de
fabrication à corriger — la transparence par défaut est l'état d'arrivée.
**(c) moteur upstream** — `DecisionTreeRegressor` sklearn 1.x, `pandas` Series,
`pd.DataFrame` columns ; environnement QC Lean non modifié par cette PR.
**(d) régression dépendance** — N/A.
**(e) stochasticité non-seedée** — `random_state=0` dans
`DecisionTreeRegressor` (L138), mais ce seed est **interne au modèle** — le
backtest lui-même dérive de la chronologie Bybit (déterministe pour une
fenêtre et un ticker fixés). Pas de stochastique non-seedée à signaler.

### Verdict

**`CAUSE_DOCUMENTED_ONLY`** — aucun chiffre ré-aligné, pas d'output de cellule
à modifier, pas de mesure de performance touchée. La doc-honesty arrive en
l'état « déjà honnête » : seule la traduction FR-first + préservation EN est
livrée. **Aucune issue fille n'est nécessaire** car il n'y a pas de cause
sous-jacente à corriger — le code est cohérent avec sa documentation.

## Fichiers

- `main.py` — la stratégie complète (251 lignes, voir le diff pour traçabilité).
- `README.en.md` — version anglaise préservée (gold set de référence Phase 3
  de l'EPIC #1650, traduction).

## Voir aussi

- **EPIC #1621** — Consolidation QC/Trading (projets, checkpoints, papertrading).
- **#3976** — READMEs feuilles QuantConnect (owner po-2024 verbatim).
- **#9434** — mandat « quantitatif tenu par le CI, pas par la prose » (fabrication
  de chiffres en README interdite).
- **#9749** — orchestrateur Stop&Repair (machinerie `lean cloud push` + exec).
- **#9511 / #9527 / #9530 / #9537 / #9542 / #9550 / #9569 / #9610 / #9667 /
  #9696 / #9714 / #9748 / #9754 / #9757** — précédents tranches #1621 appliquant
  le même pattern de relecture honnête.
- *Hands-On AI Trading with Python, QuantConnect, and AWS* — Jared Broad et
  al., Chapitre 6 _Applied Machine Learning_, Exemple 12.
