# ARCHIVE - PairsTrading (Statistical Arbitrage contre-exemple)

**Status** : ARCHIVED (substance pédagogique préservée, contre-exemple)
**Date d'archive** : 2026-07-21
**Sharpe** : -0.361 (BROKEN, contre-exemple pédagogique)
**Issue de reference** : #7575 (bug-class `PREEXISTING_UNEXEC` quantbooks sans `config.json`)

## Strategy Summary

Stratégie de pairs trading (statistical arbitrage) sur 3 paires d'ETF
sectoriels US, exploitant la **cointégration structurelle** entre
actifs liés économiquement :

- **XLF / XLK** : Financials vs Technology (paire sectorielle)
- **GLD / GDX** : Gold vs Gold Miners (chaîne commodity)
- **EWA / EWC** : Australia vs Canada (économies commodity-linked)

Mécanisme (Gatev, Goetzmann & Rouwenhorst 2006 ; Vidyamurthy 2004) :
1. Tracking du spread logarithmique entre les deux jambes
2. Calcul du **z-score roulant** (lookback 60 jours)
3. **Entrée** : z-score > +2 (long spread) ou < -2 (short spread)
4. **Exit** : z-score croise 0 (mean-reversion complétée)
5. **Stop-loss** : |z-score| > 4 (cointégration rompue / blowout)

Architecture : `PairsTrading(QCAlgorithm)`, rolling 60-day z-score
window, dollar-neutral equal-weight, entry 2σ, exit 0σ, stop 4σ.

## Backtest Metrics (vérifié, contre-exemple)

| Metric | Value |
|--------|-------|
| Univers | XLF/XLK, GLD/GDX, EWA/EWC (3 paires ETF) |
| Period | 2015-2024 |
| Rebalance | Daily check |
| Sharpe ratio | **-0.361** |
| Verdict | **BROKEN** (cointégration instable) |

## Verdict

Le **Sharpe -0.361** confirme l'échec de la stratégie sur la fenêtre
2015-2024. **Cause racine identifiée** : la **cointégration entre les
paires n'est pas stable** sur la période — les régimes macro
(COVID 2020, choc inflation 2022, transition energy 2023+) ont rompu
les liens structurels entre les jambes.

**Contre-exemple pédagogique** : ce projet documente **explicitement**
l'échec avec cause racine. C'est un exemple rare et précieux : la
plupart des pairs trading backtests en ligne masquent l'instabilité
de la cointégration. Le `main.py` reste un **template valide** pour
étudier le pattern, mais l'edge n'existe pas sur cette fenêtre.

## Notes d'infrastructure

- **QC Cloud** : déployé partiellement (au moins un backtest effectué,
  Sharpe -0.361 mesuré). Le `config.json` est absent du repo, ce qui
  rend la **re-productibilité du backtest** incertaine (pas de seed,
  pas de paramètres exacts commités).
- **quantbook.ipynb** : 4/7 cellules non-exécutées — substance
  préservée dans `main.py` (176 lignes, `PairsTrading`) + `README.md`
  (analyse cause racine).
- **Cause racine pédagogique** : la doc README explique que le
  problème est **la cointégration instable**, pas le code. Pattern
  transférable : un backtest négatif avec cause racine identifiée
  est plus utile qu'un backtest positif sans analyse.

## Leçons retenues

1. **Cointégration ≠ corrélation** : deux actifs corrélés ne sont
   pas nécessairement cointégrés. La cointégration implique une
   relation stationnaire de long terme qui peut se **rompre** lors
   de changements structurels (régime change).
2. **Backtest négatif avec cause racine > backtest positif sans
   analyse** : le pattern "j'ai backtesté, ça marche" est
   dangereux. Le pattern "j'ai backtesté, ça ne marche pas, voici
   pourquoi" est **didactiquement supérieur**.
3. **Le Sharpe négatif comme feature pédagogique** : ne pas
   supprimer un projet qui ne marche pas — le documenter
   honnêtement. La communauté ML/quant a besoin de **morts
   publishables** pour calibrer ses priors.
4. **Le `config.json` manquant sur un projet déployé** : la
   re-productibilité d'un backtest négatif est **plus critique**
   que celle d'un backtest positif (sinon personne ne peut
   vérifier le diagnostic).

## Fichiers

- `main.py` (8.3 KB) — `PairsTrading` (176 lignes, `compute_spread_zscore`
  + `check_pairs` schedule)
- `quantbook.ipynb` (32 KB) — exploration QuantBook (4/7 cells unexec)
- `README.md` — Description + analyse cause racine cointégration instable
  + Sharpe -0.361 BROKEN

## References

- #7575 (issue parent) — bug-class `PREEXISTING_UNEXEC` quantbooks
- Gatev, Goetzmann & Rouwenhorst (2006), *"Pairs Trading: Performance
  of a Relative-Value Arbitrage Rule"*, Review of Financial Studies
- Vidyamurthy (2004), *"Pairs Trading: Quantitative Methods for
  Analysis of Portfolio Performance"*
- `scripts/quantconnect/audit_quantbooks_unexec.py` — détecteur