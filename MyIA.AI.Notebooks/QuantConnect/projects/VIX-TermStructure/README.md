# VIX-TermStructure

**Classe d'actifs :** Volatilité (VIXY, shorté pour le harvest)
**Cloud project ID :** 28657907 (VIX-TermStructure-Researcher)
**Statut :** ACTIF — consolidation v6.0 (dual-signal eVRP, #13892)

## Description

Stratégie de harvest de la prime de risque volatilité (VRP) par **double signal**, consolidation de l'article QuantConnect research #21143 dans le projet existant :

1. **eVRP** (expected volatility risk premium) = VIX − eRV30, où eRV30 = écart-type roulant 10 j des rendements quotidiens SPY, annualisé (√252 × 100). eVRP > 0 : la vol implicite surfacture la vol réalisée → prime short-vol disponible.
2. **Structure de terme VIX** : VIX < VIX3M = contango (régime normal) ; VIX > VIX3M = backwardation (stress).

**4 états** (poids cible sur VIXY, magnitude scalée au niveau de VIX) :

| eVRP | Terme | Position |
|---|---|---|
| > 0 | contango | short vol plein (−VIX/100) + reliquat SPY |
| < 0 | contango | short vol moitié (−VIX/100 × 0.5) + reliquat SPY |
| < 0 | backwardation | long vol (+VIX/100) |
| > 0 | backwardation | cash (signaux conflictuels) |

Exécution 16 min avant clôture ; rebalance seulement si changement de signe ou Δpoids > 2 %.

**Pourquoi la v6.0** : l'historique v2→v5.1 (SVXY, signal de terme seul) documente un plafond à Sharpe ~+0.05 — le projet était archivé sur ce constat. L'article #21143 (et le papier SSRN sous-jacent) démontre que le signal de terme **seul** ne suffit pas : le gating eVRP est le second signal absent, et le poids scalé au niveau de VIX remplace la taille fixe. Réactivation par consolidation, pas création.

## Comment exécuter

**QC Cloud :** projet `VIX-TermStructure-Researcher` (28657907) — compile puis backtest, dates pilotées par paramètres `start` / `end` (défaut 2016-01-01 → 2026-06-30), `rv_window` (défaut 10), `evrp_threshold` (défaut 0).

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/VIX-TermStructure"`

### Données VIX (quantbook)

Le quantbook charge les séries VIX / VIX3M depuis des CSV locaux (`vix_daily.csv`,
`vix3m_daily.csv`). `qb.add_data(CBOE, ...)` nécessite l'infra alternative-data de
QC Cloud (vide en recherche Docker locale) ; VIX/VIX3M sont les **indices publics
CBOE** (volatilité implicite 30 / 93 jours), disponibles gratuitement via yfinance
(`^VIX` / `^VIX3M`). Les CSV sont **gitignorés** (`*.csv` sous `projects/`) — pour
les régénérer de façon reproductible (1 commande) :

```bash
python scripts/quantconnect/provision_vix_csv.py --out-folder lean-workspace/data
```

## Métriques de backtest v6.0 (fenêtres dev / OOS séparées)

| Métrique | Dev 2016-2021 | OOS 2022-2026 | Full 2016-2026 |
|----------|---------------|---------------|----------------|
| Sharpe Ratio | **0.886** | **−0.007** | **0.526** |
| CAGR | 26.708 % | 3.923 % | 16.558 % |
| Max Drawdown | 33.400 % | 38.500 % | 38.500 % |
| Net Profit | 314.370 % | 18.897 % | 399.967 % |
| PSR | 26.5 % | 0.5 % | 2.0 % |

**Lecture honnête.** Le claim de l'article (Sharpe 0.729 pleine période 2016-01..2026-07 vs SPY 0.582, grille 25 paramètres 0.713-0.773) **ne se réplique pas sur notre harnais** : pleine période mesurée **0.526** (sous le claim ET sous le benchmark annoncé), fenêtre dev (2016-2021) 0.886, OOS (2022-2026) **−0.007** avec drawdown 38.5 % — l'edge est concentré sur 2016-2021 (Volmageddon 2018, COVID 2020 : les états long-vol et le harvest de contango y payent). PSR < 50 % sur les trois fenêtres : **aucun Sharpe n'est statistiquement significatif**. Verdict consolidation : mécanisme dual-signal documenté et mesuré, amélioration nette vs v5.1 (−0.125), mais pas d'edge démontré — « mesuré, pas prouvé ».

Historique : v2.0 −0.97 · v3.1 −0.27 · v4.0 −0.65 · v4.1 +0.05 · v4.2 −0.23 · v4.3 +0.03 · v5.0 −0.10 · v5.1 −0.13 (détail complet dans ARCHIVE.md).

## Fichiers

- main.py - Stratégie (v6.0, dual-signal eVRP + term structure)
- research.ipynb - Analyse du spread VIX et test de régimes
- ARCHIVE.md - Historique complet des itérations et analyse du plafond structurel v2-v5.1

## Références

- **Zarattini, C., Aziz, A., & Mele, A. (2025).** « The Volatility Edge: A Dual Approach For VIX ETNs Trading ». Swiss Finance Institute Research Paper No. 25-91, SSRN 5316487 — **source primaire** (vérifiée : ordre d'auteurs Zarattini/Aziz/Mele, 38 p., testée 2008-2025 sur ETNs liés au VIX ; l'article QC l'ordonnait Zarattini/Mele/Aziz)
- **Melchin, D. (2026).** « Harvesting the Volatility Risk Premium with a Dual VIX Signal ». quantconnect.com/research/21143 (article de blog — point d'entrée, adaptation VIXY/±VIX/100 propre à l'article)
- Simon & Campasano (2014), "The VIX Fix"
- Whaley (2009), "Understanding the VIX"
