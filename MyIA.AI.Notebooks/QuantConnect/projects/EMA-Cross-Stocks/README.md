# EMA-Cross-Stocks

**Classe d'actifs :** Actions US (Grandes capitalisations tech)
**ID projet Cloud :** 28789946

## Description

Stratégie de croisement EMA dual (rapide=20, lente=50) appliquée à 5 grandes valeurs
tech (AAPL, MSFT, GOOGL, AMZN, NVDA), avec allocation equal-weight entre les actions en
tendance haussière. Long sur chaque action lorsque son EMA20 > EMA50, sinon flat ;
rebalance quotidien, seuil de 5 % pour déclencher un trade, 5 positions max.

Version « algorithm manual » (logique de signal écrite à la main dans `on_data`), à
distinguer du sibling **EMA-Cross-Alpha** qui expose le même signal EMA 20/50 via le
framework QuantConnect Alpha Model.

Paramètre `brokerage` : par défaut IBKR Margin (frais réalistes) ; passer
`brokerage=none` pour une baseline sans frais.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/EMA-Cross-Stocks"`
```bash
lean backtest --project .
```

**QC Cloud :** Ouvrir le projet 28789946 dans l'IDE QuantConnect et cliquer sur « Backtest ».

## Métriques de backtest (2015-2024)

| Métrique | 2026-08-06, code d'origine | 2026-10-10, code d'origine | 2026-10-10, code corrigé |
|----------|---------------------------:|---------------------------:|-------------------------:|
| Sharpe Ratio | 0.991 | 0.986 | **1.124** |
| CAGR | 29.230% | 29.070% | **34.664%** |
| Max Drawdown | 35.700% | 36.500% | **36.400%** |
| Net Profit | 1201.476% | 1185.505% | **1865.414%** |
| PSR | 33.664% | 33.155% | **48.530%** |
| Total Orders | 1424 | 1423 | **615** |

Benchmark SPY, rééquilibrage quotidien, univers de 5 actions tech, modèle de courtier
natif de Lean (compte sur marge), capital initial 100 000 $, 2516 jours de cotation
(2015-01-01 → 2024-12-31).

> **Provenance** :
> - colonne 1 : backtest QC Cloud `ecfe78ddcf385d2ba795bcb88644e607`, projet 28789946 ;
> - colonne 2 : même code, backtest `78998fb5cc899a59b06e6a9db99473f7`, projet 37623161. Le
>   léger écart avec la colonne 1 vient des données ou du moteur entre les deux dates : le code
>   est identique ;
> - colonne 3 : code de ce dossier, backtest `8b783209c602dd864eca3524532c7881`, projet 37623163.
>
> Le Sharpe de QC intègre un taux sans risque ; les Sharpe de la mesure ci-dessous sont à taux nul.

### Défaut corrigé : la tranche de minuit (#20258)

En données journalières, Lean livre les avis de dividende et de division dans une tranche
datée de minuit, qui ne contient aucune barre de cotation. L'ancien `on_data` y lançait le
rééquilibrage du jour. Aucun titre n'avait de donnée, donc tous étaient liquidés. La vraie
barre de la clôture arrivait ensuite, mais le rééquilibrage du jour était déjà marqué comme
fait : les lignes n'étaient rachetées que le lendemain.

Sur 2015-2024, 442 des 1423 ordres partaient ainsi à minuit, sur 111 jours. Le correctif saute
toute tranche qui n'a aucune barre pour l'univers ; la règle de détention ne change pas. Avec
lui, aucun ordre ne part plus à minuit, le nombre d'ordres passe de 1423 à 615 et les frais
sont divisés par 2,2. Les chiffres de la colonne 3 sont ceux de la stratégie telle qu'elle est
écrite.

## Mesure hors échantillon (#20258)

La version publiée mélange deux effets : le **choix des cinq titres**, fait en connaissant leur
parcours jusqu'en 2024, et le **signal EMA**, qui décide quand les détenir. La règle de mesure,
inscrite dans #20258 avant le premier backtest puis amendée pour le correctif ci-dessus, les
sépare.

**Paramètres ajoutés à `main.py`**, sans effet avec leurs valeurs par défaut :

| Paramètre | Défaut | Rôle |
|---|---|---|
| `start`, `end` | 2015-01-01, 2024-12-31 | fenêtre du backtest |
| `universe` | `fixed` | `fixed` : les cinq titres ; `pit` : chaque mois, les `top_n` plus grosses capitalisations US connues à cette date (action principale, pas de certificat de dépôt, prix > 5) |
| `top_n` | 5 | taille de l'univers `pit` |
| `mode` | `ema` | `hold` : mêmes titres, mêmes parts, même bande de 5 %, sans condition EMA |
| `fee_mult` | 1 | multiplicateur des frais du courtier |
| `trace` | 0 | 1 : graphique `shadow` au format de la ligue de stratégies (#19821) |

**Non-régression** : avec les valeurs par défaut, le nouveau code (avant correctif) reproduit le
code d'origine à l'identique, statistiques QC et 1423 ordres comparés un par un.

**Découpage** : chaque configuration tourne du 2005-01-01 au 2026-06-30. L'**échantillon** est
2015-2024, la fenêtre où la stratégie a été présentée. Le **hors échantillon** est 2005-2014 suivi
de 2025-01-02 → 2026-06-30, mis bout à bout ; c'est lui qui porte le verdict. Sharpe à taux sans
risque nul, annualisé sur 252 séances ; bootstrap circulaire par blocs de 21 séances,
10 000 tirages, graine 18921 ; correction de Holm sur les deux références.

**La candidate est l'univers au fil de l'eau** (`universe=pit`, `mode=ema`) : pour l'univers fixe,
le choix des titres reste rétrospectif même avant 2015. Ses deux références sont SPY détenu sans
frais, et le même univers au fil de l'eau détenu sans condition EMA (`pit-hold`).

| Configuration | Sharpe HE | CAGR HE | Max DD HE | Sharpe éch. | CAGR éch. | Max DD éch. |
|---|---:|---:|---:|---:|---:|---:|
| `fixed-ema` (la stratégie publiée) | 0.92 | 20.4 % | −48.2 % | 1.32 | 34.6 % | −36.4 % |
| `fixed-hold` | 0.86 | 20.1 % | −62.3 % | 1.32 | 34.8 % | −39.0 % |
| `pit-ema` (candidate) | 0.33 | 4.0 % | −36.4 % | 0.85 | 17.7 % | −42.7 % |
| `pit-hold` | 0.45 | 6.5 % | −38.9 % | 0.94 | 21.1 % | −37.3 % |
| SPY détenu | 0.54 | 9.1 % | −55.2 % | 0.78 | 13.0 % | −33.7 % |

HE = hors échantillon, éch. = échantillon 2015-2024.

**Verdict : NO BEATS.**

| Candidate `pit-ema` contre | Écart de Sharpe HE | IC 95 % | p de Holm | 2005-2009 | 2010-2014 | 2025-2026 S1 |
|---|---:|---:|---:|---:|---:|---:|
| SPY détenu | −0.21 | [−0.70 ; 0.24] | 1.00 | −0.11 | −0.26 | −0.95 |
| `pit-hold` | −0.12 | [−0.42 ; 0.17] | 1.00 | −0.01 | −0.17 | −0.65 |

L'écart est négatif contre les deux références et sur les trois sous-périodes. Le run à frais
doublés, prévu seulement si p < 0,05 contre les deux, n'a pas été lancé.

**Contrôles descriptifs, hors verdict** :

| Écart de Sharpe | HE (p unilatéral) | Échantillon (p unilatéral) |
|---|---:|---:|
| `fixed-ema` − `fixed-hold` : apport du signal EMA à univers fixe | +0.06 (0.40) | −0.00 (0.50) |
| `fixed-hold` − `pit-hold` : prime du choix rétrospectif des titres | +0.41 (0.019) | +0.37 (0.001) |
| `fixed-ema` − SPY | +0.38 (0.087) | +0.53 (0.013) |
| `pit-ema` − SPY | −0.21 (0.82) | +0.07 (0.40) |

Compteurs : l'univers au fil de l'eau a connu 261 revues mensuelles et 18 titres distincts. Le
signal EMA détient en moyenne 3,4 titres sur 5 à univers fixe et 3,1 au fil de l'eau ; il passe
459 et 412 séances entièrement en liquidités.

### Ce que la mesure établit

- **Le signal EMA n'ajoute rien de mesurable à la détention des mêmes titres.** À univers fixe,
  l'écart de Sharpe est nul sur l'échantillon et non significatif hors échantillon. Il réduit
  la pire baisse (−48 % contre −62 % hors échantillon), au prix de 18 fois plus d'ordres.
- **Le rendement publié vient du choix des titres.** Détenir les cinq titres choisis avec le
  recul bat nettement la détention des cinq plus grosses capitalisations du moment, y compris
  avant 2015. Hors échantillon, l'écart vient de 2005-2009 (+0,85) ; il est nul sur 2010-2014
  (−0,01) et faible sur 2025-2026 (+0,05).
- **Sans ce choix, la stratégie ne bat pas le marché.** Au fil de l'eau, la règle fait moins bien
  que SPY détenu hors échantillon, et à peine mieux sur l'échantillon (écart non significatif).

**Cette stratégie reste une démonstration pédagogique du croisement EMA, pas une stratégie
alpha.** Le sibling EMA-Cross-Alpha (même signal via le framework Alpha Model) sous-performe SPY
(Sharpe −0,01).

> **Première passe déclarée** : une première série de runs, lancée avant la découverte du
> défaut de minuit, donnait le même verdict (`pit-ema` − SPY −0,13, − `pit-hold` −0,07, p de Holm
> 1,00). Ses résultats restent publiés dans #20258 ; ceux de ce README sont ceux du code corrigé.
> Traces et outils d'analyse : hors dépôt (`QC-traces/20258-ema-cross-stocks/`).

## Fichiers

- `main.py` - Stratégie de croisement EMA (algorithm « manual », sans Alpha Model)
- `quantbook.ipynb` - Research QuantBook multi-stock : EMA crossover sur le panier AAPL/MSFT/GOOGL/AMZN/NVDA, avec variantes de périodes EMA et d'allocation (momentum vs equal-weight)
- `README.en.md` - Version anglaise (original historique, non mise à jour)

## Références

- Sibling : EMA-Cross-Alpha (même signal EMA 20/50 via le framework Alpha Model)
- Réf : Brock et al. (1992), moving average trading rules
