# MomentumRegime-AdaptiveWeights

**Classe d'actifs :** Actions US (SPY/QQQ/IEF/GLD)
**Cloud project ID :** 31524424
**Baseline :** Framework_Composite_MomentumRegime (Sharpe 0.185, CAGR 4.73 %)

## Description

Variante à poids adaptatifs de Framework_Composite_MomentumRegime.
Décale l'allocation vers SectorMomentum (85/15 contre 60/40 pour la baseline),
élargit l'univers de momentum pour inclure QQQ et privilégie des lookbacks plus courts.

## Résultats de backtest

| Métrique | Baseline (T60/RS40) | Cette variante (T85/RS15) | Delta |
|----------|---------------------|---------------------------|-------|
| Sharpe Ratio | 0.185 | **-0.74** | -0.925 |
| CAGR | 4.73 % | 1.76 % | -2.97 pp |
| Max Drawdown | - | 4.4 % | - |
| Net Profit | - | 21.1 % | - |
| Beta (vs SPY) | - | 0.081 | - |
| Total Orders | - | 403 | - |
| Win Rate | - | 71 % | - |

**Verdict : NO BEATS.** Sharpe ratio négatif. Le décalage 85/15 a détruit de la valeur.

## Analyse

La variante sous-performe dramatiquement la baseline. Causes profondes :

1. **Sur-concentration sur SectorMomentum** : à 85 % de poids, SectorMomentum
   domine les allocations. Quand son signal mensuel s'inverse (fréquent avec des
   lookbacks courts 0.5/0.2/0.2/0.1), le portefeuille navigue entre les actifs.

2. **L'ajout de QQQ dilue la qualité du signal** : ajouter QQQ à l'univers de
   SectorMomentum crée une course à 4 où l'actif au meilleur score tourne fréquemment,
   générant un turnover inutile.

3. **Beta faible (0.081)** : la stratégie passe l'essentiel du temps dans des actifs
   défensifs (IEF/GLD) malgré des conditions de marché haussier, ce qui suggère que le
   scoring composite de SectorMomentum, avec un biais court terme, surpondère les
   replis transitoires.

4. **RegimeSwitching à 15 %** : trop faible pour compter. Le filet de sécurité de
   commutation de régime qui protège en marché baissier/latéral est effectivement
   désactivé.

## Fichiers

- main.py - Stratégie (allocation T85/RS15)
- alpha_models.py - Modèles alpha SectorMomentum + RegimeSwitching
- portfolio_construction.py - Construction de portefeuille MultiStrategyPCM

## Références

- Hands-On AI Trading, Section 06
- Baseline : Framework_Composite_MomentumRegime
