# Adaptive-Conformal-Risk

**Classe d'actifs :** Actions/ETF US (multi-facteurs)
**Cloud project IDs :** `29841071` (original, étudiant ECE sans frais 2015-2026) · `33278416` (`1630-baseline-AdaptiveConformalRisk`, IBKR + aligné 2018-2025)
**Projets de la mesure #21469 :** `38121196` (code actuel, avec les modes de référence) · `38121126` (contrôle, code d'origine)
**Source :** Projet étudiant ECE (El Bakkali, Gr02), adapté pour le pool ESGF — Issue #238.

## Description

Couche de risque *Adaptive Conformal Inference* (ACI) sur du momentum multi-facteurs. Implémente l'algorithme ACI (Gibbs & Candès, 2021) comme surcouche dynamique de gestion du risque : l'ajustement en ligne de l'alpha élargit/rétreint l'intervalle de prédiction conforme en réponse aux violations de couverture récentes, et la taille de position est fixée de manière inversement proportionnelle à la largeur de l'intervalle — un intervalle plus large (plus d'incertitude) signifie une position plus petite. Appliqué sur un univers de 15 grandes capitalisations réparties sur 5 secteurs, avec une cible de volatilité de 15 % et un rééquilibrage mensuel.

## Paramètres

| Paramètre | Valeurs | Défaut | Rôle |
|---|---|---|---|
| `mode` | `strategy`, `spy`, `6040`, `ew15` | `strategy` | `strategy` garde la décision du code ; `spy` détient SPY à 100 % ; `6040` détient SPY à 60 % et BND à 40 % ; `ew15` détient les 15 titres de l'univers à poids égal. Les références sont rééquilibrées au début de chaque mois, une minute après l'ouverture |
| `start_date` | date `%Y%m%d` | 2015-01-01 | début de la fenêtre |
| `end_date` | date `%Y%m%d` | 2026-01-01 | fin de la fenêtre |

Les quatre modes tracent chaque jour la valeur du portefeuille à l'ouverture de SPY (graphique `shadow`, séries `e0` à `e4`). En mode référence, la mise à jour quotidienne de la stratégie ne fait rien. SPY et BND ne sont abonnés qu'en mode référence. Sans paramètre, la décision de la stratégie ne change pas : le contrôle ci-dessous le vérifie ordre par ordre.

## Verdict contre références détenues (#21469)

Le protocole a été écrit dans #21469 avant le premier backtest, sur le modèle de #21329. Les deux références du verdict, SPY détenu et le 60/40, tournent dans le même algorithme que la stratégie, sous le même modèle de courtage. Une troisième référence, les 15 titres de l'univers à poids égal (`ew15`), sert de diagnostic et ne compte pas dans le verdict.

Deux propriétés du code sont gardées telles quelles :

- la stratégie n'est pas toujours investie à 100 % : le ciblage de volatilité à 15 % peut réduire l'exposition, et le reste est en liquidités ;
- son premier rééquilibrage tombe à la 21e séance. Elle reste en liquidités pendant les 21 premières séances de chaque fenêtre, alors que les références sont investies dès la première.

Les séries comparées sont la valeur du portefeuille à chaque ouverture de SPY. Les tests passent par `Paradox46Benchmarks/significance.py`, avec un taux sans risque nul :

- écart de Sharpe de Ledoit-Wolf ;
- bootstrap stationnaire ;
- écart de moyennes de Newey-West.

Sur chaque fenêtre, la correction de Holm porte sur les six p-valeurs du verdict. Le diagnostic est une exécution séparée, avec sa propre correction de Holm sur trois p-valeurs.

Règle de verdict, écrite avant la mesure :

- `BEATS` : écart de Sharpe positif et significatif (Holm < 0,05) contre les deux références ;
- `NO BEATS` : Sharpe de la stratégie inférieur à celui de SPY détenu ;
- `INCONCLUSIVE` : tous les autres cas.

**Contrôle d'innocuité : tenu.** En mode `strategy`, sur la fenêtre codée, le code instrumenté reproduit le backtest du code d'origine (`319338b45cae70aabe773a57cc0777b0`, projet 38121126) :

- 1 533 ordres sur 1 533, sans écart de date, de symbole ni de quantité ;
- 27 statistiques QC sur 27.

Les ordres de la stratégie sont soumis à 9 h 40, heure de New York, et remplis à la clôture du même jour, sur les deux fenêtres ; aucun n'est passé à minuit.

| Fenêtre | Séances | Sharpe stratégie (taux nul) | SPY détenu (taux nul) | 60/40 (taux nul) | p Holm (Ledoit-Wolf, SPY / 60/40) | Verdict |
|---|---|---|---|---|---|---|
| Codée, 2015-01-02 → 2025-12-31 | 2766 | 0,888 | 0,803 | 0,837 | 1,0 / 1,0 | **INCONCLUSIVE** |
| Hors échantillon, 2026-01-02 → 2026-07-21 | 137 | 0,198 | 1,255 | 1,173 | 1,0 / 1,0 | **NO BEATS** |

Statistiques QC (calculées par QC avec son propre taux sans risque). Leurs Sharpe ne se comparent pas à ceux de la table du dessus : QC retranche un taux sans risque non nul et part de ses propres séries quotidiennes, alors que le protocole prend un taux nul sur la valeur du portefeuille à l'ouverture. Le classement des portefeuilles peut donc changer d'une table à l'autre, et le verdict se lit sur la table du dessus.

| Fenêtre | Mode | Sharpe QC (taux de QC, autre échelle) | CAGR | Pire baisse | Ordres | Backtest |
|---|---|---|---|---|---|---|
| Codée | stratégie | 0,583 | 13,15 % | 30,9 % | 1533 | `393e73a6fca6edabf1585e275381b055` |
| Codée | SPY détenu | 0,535 | 13,39 % | 33,7 % | 1 | `596d95b8eae1a9062771402d3dc65eed` |
| Codée | 60/40 | 0,451 | 8,86 % | 21,7 % | 221 | `c7a90f1e38874b2ca7785c11df233d38` |
| Codée | 15 titres à poids égal | 0,891 | 22,88 % | 35,1 % | 1196 | `732abf4b8de0080d5c3cfcb02a93c6d2` |
| Hors échantillon | stratégie | −0,086 | 3,49 % | 8,5 % | 69 | `362eada8ff0d63be8eaaecad9f281ab7` |
| Hors échantillon | SPY détenu | 0,865 | 19,08 % | 8,9 % | 1 | `a2e3ad4f1e1b41015b9c49aed0a43ad0` |
| Hors échantillon | 60/40 | 0,570 | 11,30 % | 5,8 % | 12 | `f141c04c23d40f7658d40e4c5153f665` |
| Hors échantillon | 15 titres à poids égal | 1,108 | 22,20 % | 8,4 % | 81 | `6a9dee5d757418e42233aec2799a88dc` |

Le backtest hors échantillon a été demandé jusqu'au 2026-10-19, mais il s'arrête le 2026-07-21 : les nœuds QC utilisés coupent les backtests environ 90 jours avant la date du jour. Sur ses 137 séances, la stratégie en passe 21 en liquidités, et la fenêtre n'a presque pas de puissance. Aucun paramètre n'a été réglé sur cette période.

**Lecture.** Sur la fenêtre codée, la stratégie a le Sharpe ponctuel le plus élevé des trois portefeuilles du verdict. Sa volatilité annuelle (15,3 %) tient sa cible et reste sous celle de SPY détenu (17,8 %), pour un rendement moyen proche (13,6 % par an contre 14,3 %). L'écart de Sharpe n'est pas significatif : p brute de Ledoit-Wolf 0,69 contre SPY détenu, intervalle bootstrap à 95 % de −0,36 à +0,49. Hors échantillon, son Sharpe passe sous celui de SPY détenu. Le code actuel ne bat donc aucune des deux références de façon mesurable.

**Diagnostic : les 15 titres à poids égal font mieux que la stratégie.** Sur la fenêtre codée, leur Sharpe à taux nul est de 1,161, contre 0,888 pour la stratégie. L'écart de Sharpe n'est pas significatif (p de Holm 0,33 pour Ledoit-Wolf, intervalle bootstrap de −0,70 à +0,09). L'écart de rendement moyen, lui, l'est : 22,6 % par an contre 13,6 %, p de Holm 0,016 pour Newey-West. Hors échantillon, l'ordre est le même (1,529 contre 0,198, non significatif). La règle écrite avant la mesure dit qu'un Sharpe inférieur à celui de `ew15` signifie que la surcouche (momentum et intervalle conforme) n'ajoute rien de mesurable au choix des titres. C'est le cas ici. Le rendement de la stratégie vient de son univers, choisi après coup parmi les grands gagnants de la décennie, et pas de la surcouche, qui le réduit.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Adaptive-Conformal-Risk"`
**QC Cloud :** Déployé (voir les Cloud project IDs ci-dessus). Le `main.py` commité ici est la copie canonique avec `set_brokerage_model(IBKR, MARGIN)` (frais réels).
**Mesure du 2026-10-19 (#21469) :** voir la section « Verdict contre références détenues ». Les paramètres `mode`, `start_date` et `end_date` se passent au backtest.

## Métriques de backtest

Mesures antérieures, sur d'autres projets QC et d'autres fenêtres. Le code actuel, avec le modèle de courtage de son `main.py`, donne un Sharpe QC de 0,583 sur 2015-2026 (section précédente).

| Métrique | Valeur | Fenêtre / frais |
|----------|--------|-----------------|
| Méthode | Couche de risque ACI + momentum multi-facteurs à 3 fenêtres | — |
| Rééquilibrage | Mensuel (mise à jour alpha ACI quotidienne) | — |
| Sharpe | **0.449** | 2018-2025, IBKR frais réels (#1630-aligned) |
| CAGR | 11.5 % | 2018-2025, IBKR |
| MaxDD | 22.5 % | 2018-2025, IBKR |
| PSR | 12.5 % (non significatif) | 2018-2025, IBKR |
| Sharpe (préalable, sans frais) | 0.604 | 2015-2026, modèle de frais par défaut (négligeable) |

**Caveat #1630 (vérifié 2026-06-23).** Deux constats : (a) le rééquilibrage mensuel à faible rotation + le vol-targeting ACI rendent la couverture **résistante aux frais** (0.449 avec IBKR n'est que modérément inférieur à 0.604 sans frais, et une bonne part de cet écart tient à la fenêtre alignée plus exigeante) — ce qui confirme le discriminateur *realized-turnover* du #1630 ; (b) **mais l'univers est lourd en Mag7** (AAPL/MSFT/NVDA/AMZN/TSLA = 5 des 7 Mag7), donc le Sharpe relève pour l'essentiel de la dérive de survivance Mag7 plutôt que de la valeur marginale de la couche conforme (même classe de caveat qu'EMATrend). Analyse complète : `docs/qc/qc-comparative-backtests.md` finding #38 (See #1630).

Le diagnostic `ew15` de #21469 mesure le constat (b) : détenus à poids égal, les mêmes 15 titres ont un Sharpe plus élevé que la stratégie.

## Fichiers

- `main.py` — Stratégie (couche ACI + momentum multi-facteurs, brokerage IBKR).

## Références

- Gibbs, I. & Candès, E. (2021), *Adaptive Conformal Inference Under Distribution Shift*. (L'algorithme ACI d'alpha en ligne implémenté ici.)
- Romano, Y., Patterson, E. & Candès, E. (2020), *Conformalized Quantile Regression*. (Cadre des intervalles de prédiction conforme.)
