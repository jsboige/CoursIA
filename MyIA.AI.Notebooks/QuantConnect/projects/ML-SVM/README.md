# ML-SVM — SVM linéaire sur ETF sectoriels (le contre-point de ML-RandomForest)

**Classe d'actifs :** Actions US via ETF sectoriels (8 ETF)
**Cloud project ID :** 29434752
**Période backtestée :** 2015-01-01 → 2024-12-31

## Description

Stratégie de classification par **SVM** (sklearn `SVC`, **noyau linéaire**, `C=0.5`) sur 8 ETF actions US (SPY, QQQ, IWM, DIA, XLK, XLF, XLV, XLY). Utilise 8 features techniques (RSI, position Bollinger, MACD, momentum, volatilité, prix/SMA) pour classifier le signe du rendement à 10 jours.

Entraînement mensuel, rebalancement bimensuel. Seuil 0.55, 4 positions max.

**Version anglaise préservée** : [README.en.md](README.en.md).

## Configuration déployée (v3, `main.py` Cloud 29434752)

| Composant | Paramètre | Rôle |
|-----------|-----------|------|
| Univers | SPY, QQQ, IWM, DIA, XLK, XLF, XLV, XLY | 8 ETF sectoriels |
| Features | 8 (RSI, BB, MACD, mom, vol, prix/SMA) | Signal technique |
| Noyau | `linear` | SVM linéaire (sous-ajustement — cf. lecture) |
| `C` | 0.5 | Régularisation (conservatif) |
| Lookback | 120 jours | Fenêtre d'entraînement |
| Seuil | 0.55 | Probabilité min pour ouvrir |
| Positions max | 4 @ 22.5 % | Concentration |
| Rebalance | Bimensuel | Tous les 2 lundis |
| Entraînement | Mensuel | recalibrage |
| Graine | `random_state=42` | **Single seed** (cf. lecture honnête) |

## Backtest réel (QC Cloud, frais IBKR inclus)

| Métrique | Valeur |
|----------|--------|
| Sharpe ratio | **0.166** |
| CAGR | **5.70 %** |
| Drawdown max | **32.50 %** |
| Rendement total net | 90.2 % (+90 168 $ sur 100 k $) |
| PSR (Probabilistic Sharpe Ratio) | **0.028 %** |
| Ordres exécutés | 841 |
| Jours tradés | 2914 |

*Backtest frais via QC Cloud project 29434752 (compile `BuildSuccess`, 2026-08-06). Sharpe documenté 0.147 confirmé reproductible (0.166, Δ < seed-variance).*

### Lecture honnête — quasi-bruit, plafond structurel confirmé

Le README anglais disait déjà : « *Structural ceiling: SVM for ETF direction prediction has limited signal-to-noise ratio. Sharpe 0.147 reflects this ceiling, not a code issue.* » Le backtest frais (Sharpe 0.166, **PSR 0.028 %**) **confirme et durcit** ce diagnostic :

1. **PSR 0.028 % ≈ zéro** : la probabilité que le Sharpe observé soit statistiquement supérieur à zéro est **quasi nulle** (0.03 %). C'est le PSR le plus bas de la famille ML — la stratégie est **indiscernable du bruit**. Le CAGR 5.70 % (à peine au-dessus du cash sur la décennie) est compatible avec une fluctuation aléatoire.

2. **Noyau linéaire = sous-ajustement** : un SVM linéaire ne capture que des frontières de décision *affines*. Les features techniques (RSI, momentum) ont une relation **non linéaire** avec les rendements futurs — un noyau linéaire ne peut pas l'exprimer. Contrast avec ML-RandomForest (`max_depth=5`) qui, via les arbres, capture ces non-linéarités. Le SVM linéaire sous-ajuste là où le RF sur-ajuste : **deux échecs ML différents** (underfit vs overfit).

3. **Platt scaling + seuil 0.55 = bruit de décision** : `SVC(probability=True)` calibre les probabilités via **Platt scaling** (régression logistique sur les scores), connu pour être **bruité** loin des marges. Un seuil de décision à 0.55 sur des probabilités Platt = couper au cœur du bruit calibration. La moitié des positions ouvertes sont probablement des artifacts de calibration, pas du signal.

4. **Univers ETF vs Mag7 (contraste avec ML-RandomForest)** : ML-RandomForest (10 actions dont 7 Mag7) atteint CAGR 24.25 % — mais c'est du **beta Mag7** (§C pt5). ML-SVM (8 ETF sectoriels) atteint seulement 5.70 % : l'univers ETF **dilue** l'effet de concentration Mag7 que RF exploite (XLK/QQQ portent du Mag7-beta, mais dilué dans SPY/DIA/IWM). **Aucune des deux n'est de l'alpha** : RF sur-performe par beta Mag7, SVM sous-performe par under-fit. Le duo forme un **diptyque pédagogique** sur (a) l'univers comme variable confondante et (b) le choix du modèle.

5. **Single seed (`random_state=42`)** : §C exige ≥4 seeds. PSR 0.028 % rend la question académique (aucune graine ne sauvera un signal absent), mais la robustesse n'est pas démontrée.

**Conclusion honnête** : ne PAS présenter ML-SVM comme une stratégie « qui marche moyennement ». C'est une **stratégie au plafond structurel** — SVM linéaire sur ETF avec Platt scaling = quasi-bruit confirmé (PSR 0.03 %). Sa **valeur pédagogique est le contre-point de ML-RandomForest** : même pipeline ML, modèle linéaire vs arbres, univers ETF vs Mag7 → résultats radicalement différents (CAGR 5.7 % vs 24.2 %), et **aucun des deux n'est de l'alpha** (RF = beta Mag7, SVM = bruit).

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/ML-SVM"`
**QC Cloud :** Déployé comme project 29434752.

## Fichiers

- `main.py` — Stratégie `MLSVMAlgorithm` v3 (`SVC` linéaire).
- `quantbook.ipynb` — Recherche.

## Concepts enseignés

- **SVM linéaire vs arbres (RF)** : frontière affine vs frontière par morceaux. Sur features non linéaires, le SVM linéaire sous-ajuste (under-fit), le RF peut sur-ajuster (over-fit). Deux modes d'échec ML distincts.
- **Platt scaling (`probability=True`)** : la calibration probabiliste d'un SVM est **bruitée** loin des marges — un seuil de décision à 0.55 sur probabilités Platt = couper dans le bruit.
- **Univers comme variable confondante** : ETF sectoriels (SVM) vs actions Mag7 (RF) → dilution vs concentration du beta Mag7. Comparer les deux isole l'effet de l'univers.
- **Probabilistic Sharpe Ratio (PSR)** : PSR 0.028 % = la stratégie est indiscernable du bruit (le diagnostic le plus tranché de la famille ML).
- **Single seed** : `random_state=42` seul ; §C exige ≥4 seeds + edge 2σ pour tout claim.
- **Diptyque ML-RF ↔ ML-SVM** : même pipeline, modèle/univers différents → résultats divergents, **aucun des deux n'est de l'alpha** (RF = beta, SVM = bruit).

## Références

- Vapnik (1995), *Support-Vector Networks*.
- *Hands-On AI Trading* (Jared Broad), Section 06.
- Diptyque : [ML-RandomForest](../ML-RandomForest/README.md) (contre-point : RF sur Mag7, CAGR 24 % = beta ; vs SVM sur ETF, CAGR 5.7 % = bruit).
