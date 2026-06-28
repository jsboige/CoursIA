# Adaptive-Conformal-Risk

**Classe d'actifs :** Actions/ETF US (multi-facteurs)
**Cloud project IDs :** `29841071` (original, étudiant ECE sans frais 2015-2026) · `33278416` (`1630-baseline-AdaptiveConformalRisk`, IBKR + aligné 2018-2025)
**Source :** Projet étudiant ECE (El Bakkali, Gr02), adapté pour le pool ESGF — Issue #238.

## Description

Couche de risque *Adaptive Conformal Inference* (ACI) sur du momentum multi-facteurs. Implémente l'algorithme ACI (Gibbs & Candès, 2021) comme surcouche dynamique de gestion du risque : l'ajustement en ligne de l'alpha élargit/rétreint l'intervalle de prédiction conforme en réponse aux violations de couverture récentes, et la taille de position est fixée de manière inversement proportionnelle à la largeur de l'intervalle — un intervalle plus large (plus d'incertitude) signifie une position plus petite. Appliqué sur un univers de 15 grandes capitalisations réparties sur 5 secteurs, avec une cible de volatilité de 15 % et un rééquilibrage mensuel.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Adaptive-Conformal-Risk"`
**QC Cloud :** Déployé (voir les Cloud project IDs ci-dessus). Le `main.py` commité ici est la copie canonique avec `set_brokerage_model(IBKR, MARGIN)` (frais réels).

## Métriques de backtest

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

## Fichiers

- `main.py` — Stratégie (couche ACI + momentum multi-facteurs, brokerage IBKR).

## Références

- Gibbs, I. & Candès, E. (2021), *Adaptive Conformal Inference Under Distribution Shift*. (L'algorithme ACI d'alpha en ligne implémenté ici.)
- Romano, Y., Patterson, E. & Candès, E. (2020), *Conformalized Quantile Regression*. (Cadre des intervalles de prédiction conforme.)
