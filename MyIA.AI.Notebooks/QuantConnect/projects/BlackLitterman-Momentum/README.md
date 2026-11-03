# BlackLitterman-Momentum

**Classe d'actifs :** Actions/ETF US (multi-actifs)
**ID projet Cloud :** 29816300

## Description

Portefeuille Black-Litterman avec vues de momentum multi-fenêtres (1M, 3M, 6M, 12M). L'optimisation BL produit les poids finaux.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/BlackLitterman-Momentum"`

**QC Cloud :** Déployé en tant que projet 29816300.

**Paramètres** (#23186) :

| Paramètre | Valeurs | Défaut |
|-----------|---------|--------|
| `mode` | `strategy` (la stratégie) ; `spy` (SPY 100 % détenu) ; `6040` (SPY 60 % / BND 40 %) ; `ew15` (les quinze titres de l'univers à poids égal) | `strategy` |
| `start_date`, `end_date` | dates `AAAA-MM-JJ` | `2015-01-01`, `2026-01-01` |

Les quatre modes suivent le même calendrier : premier jour de bourse du mois, 30 minutes après l'ouverture. Le graphique `shadow` trace la valeur du portefeuille à chaque ouverture de séance du SPY. C'est l'entrée du calcul de significativité (`Paradox46Benchmarks/significance.py`).

## Correction de l'exécution (#23186)

Jusqu'à #23186, le rééquilibrage appelait `liquidate()`, puis un `set_holdings` par titre. En résolution journalière, les ordres passés en séance se remplissent à la clôture. Le second appel calculait donc ses quantités contre des positions qui n'étaient pas encore vendues, et n'envoyait que l'écart. Quand la cible d'un titre était inférieure à sa position, l'écart s'ajoutait à la vente de liquidation, et la ligne passait à découvert. La stratégie est pourtant conçue sans vente à découvert (poids bornés entre 1 et 20 %).

Le rejeu des ordres du backtest publié le 2026-08-07 l'a mesuré : **119 dates de rééquilibrage sur 132** laissaient au moins une position courte. Relancé le 2026-10-28, le même code en laisse à **126 dates sur 132**, avec 8 ordres invalides. Les chiffres publiés jusque-là décrivaient donc ce livre de résidus, et non la stratégie.

Le rééquilibrage passe maintenant par `self.transactions.cancel_open_orders()`, puis par un seul `set_holdings([PortfolioTarget(...)], liquidate_existing_holdings=True)` sur les cibles finales. Le calcul Black-Litterman n'est pas modifié : covariance, vues, postérieure, optimisation et ciblage de volatilité restent identiques. Au rejeu des ordres, le code corrigé n'a **aucune position courte et aucun ordre invalide**, sur les deux fenêtres.

## Métriques du backtest

Backtests QC Cloud du 2026-10-28, capital de départ 100 000, frais de courtage modélisés par Lean, rééquilibrage mensuel. Chaque ligne est un run du code corrigé, avec le `mode` indiqué. Résultats lus après `completed: true`.

**w1 : 2015-01-01 → 2024-12-31** (2516 dates négociables)

| Bras | Sharpe QC | CAGR | Drawdown max | PSR | Profit net |
|------|-----------|------|--------------|-----|------------|
| **`strategy`** | **0.895** | **18.45 %** | **21.5 %** | 26.0 % | 444.5 % |
| `spy` (référence) | 0.542 | 13.18 % | 33.7 % | 3.3 % | 245.1 % |
| `6040` (référence) | 0.453 | 8.55 % | 21.4 % | 1.6 % | 127.3 % |
| `ew15` (diagnostic) | 0.944 | 23.90 % | 35.0 % | 30.0 % | 754.0 % |

**w2 : 2025-01-01 → 2026-07-01** (374 dates négociables, dernière séance le 2026-06-30)

| Bras | Sharpe QC | CAGR | Drawdown max | PSR | Profit net |
|------|-----------|------|--------------|-----|------------|
| **`strategy`** | **-0.14** | **2.33 %** | **19.2 %** | 4.6 % | 3.5 % |
| `spy` (référence) | 0.619 | 17.89 % | 18.6 % | 25.6 % | 28.0 % |
| `6040` (référence) | 0.548 | 12.80 % | 11.2 % | 22.9 % | 19.8 % |
| `ew15` (diagnostic) | 0.676 | 18.71 % | 19.1 % | 28.4 % | 29.3 % |

Le Sharpe de QC retire un taux sans risque. Les tests ci-dessous utilisent un Sharpe à taux nul, calculé sur les rendements journaliers du graphique `shadow`.

**Significativité** (Ledoit-Wolf, bootstrap stationnaire, Newey-West). La correction de Holm porte d'un côté sur les deux références du verdict, de l'autre sur le diagnostic :

| Fenêtre | Comparaison | Sharpe à taux nul (stratégie / bras) | p de Holm, écart de Sharpe (Ledoit-Wolf ; bootstrap) |
|---------|-------------|---------------------------------------|------------------------------------------------------|
| w1 | vs `spy` | 1.23 / 0.80 | 0.143 ; 0.135 |
| w1 | vs `6040` | 1.23 / 0.82 | 0.183 ; 0.183 |
| w1 | vs `ew15` | 1.23 / 1.21 | 1.0 ; 1.0 |
| w2 | vs `spy` | 0.19 / 1.01 | 0.671 ; 0.671 |
| w2 | vs `6040` | 0.19 / 1.16 | 0.671 ; 0.671 |
| w2 | vs `ew15` | 0.19 / 1.07 | 0.188 ; 0.188 |

Sur w1, l'écart de rendement moyen journalier contre le 60/40 reste significatif après Holm (p = 0,016). Les tests sur l'écart de Sharpe, eux, ne le sont pas.

## Verdict : INCONCLUSIVE sur 2015-2024, NO BEATS sur 2025-2026

Le protocole (#23012, repris dans #23186) donne BEATS seulement si le Sharpe dépasse celui du SPY détenu **et** que l'écart reste significatif après Holm contre les deux références. Il donne NO BEATS si le Sharpe est inférieur à celui du SPY détenu, et INCONCLUSIVE sinon.

- **w1 (2015-2024) : INCONCLUSIVE.** Une fois l'exécution corrigée, la stratégie fait mieux que SPY détenu : Sharpe 0.895 contre 0.542, CAGR 18,5 % contre 13,2 %, drawdown 21,5 % contre 33,7 %. Mais l'écart de Sharpe n'est pas significatif après Holm (p = 0,14 contre SPY, p = 0,18 contre le 60/40).
- **w2 (2025 → mi-2026) : NO BEATS.** Sharpe -0.14 contre 0.619 pour SPY détenu, CAGR 2,3 % contre 17,9 %. Le drawdown (19,2 %) n'est pas plus faible que celui du SPY (18,6 %).

**Ce que mesure le diagnostic `ew15`.** L'univers de quinze titres a été choisi après coup : il contient NVDA et TSLA. Sur w1, les quinze titres à poids égal ont un Sharpe à taux nul de 1,21, celui de la stratégie est de 1,23, et l'écart n'est pas mesurable (p = 1,0 après Holm). L'avance sur SPY se retrouve donc dans l'univers seul, sans le moteur Black-Litterman. Le moteur réduit le drawdown par rapport à `ew15` (21,5 % contre 35,0 %), grâce au ciblage de volatilité et au plafond sectoriel, mais il rend moins (CAGR 18,5 % contre 23,9 %), et le Sharpe ne bouge pas. Sur w2, la stratégie est sous les quinze titres à poids égal (Sharpe 0,19 contre 1,07), sans écart significatif après Holm (p = 0,19).

**Ce qui change par rapport au verdict publié le 2026-08-07.** Ce verdict concluait à un NO-BEATS avec un profil défensif (drawdown 16,1 %), et comparait le CAGR à une estimation du SPY. Les deux reposaient sur le livre des positions courtes résiduelles. Relancé à l'identique le 2026-10-28, ce même code ne reproduit pas non plus ses chiffres : Sharpe 0.457, CAGR 10,53 %, drawdown 22,7 %, PSR 1,18 %. Un livre fait d'écarts mensuels est sensible aux petites réécritures des prix ajustés entre deux runs. Pas de re-tuning des paramètres (TAU, SIGMOID_STEEPNESS, TARGET_VOL) : un ajustement rétrospectif serait du surapprentissage (EPIC #9768).

## Fichiers

- main.py - Stratégie (BL momentum ; exécution corrigée par #23186, modes de référence)

## Références

- Black & Litterman (1992), Global Portfolio Optimization
