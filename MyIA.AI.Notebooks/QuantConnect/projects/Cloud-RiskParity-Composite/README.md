# Cloud-RiskParity-Composite

**Classe d'actifs :** Multi-actifs (Actions, Obligations, Matières premières)

**ID projet Cloud :** 30820857

## Description

Rotation tactique à travers six classes d'actifs (SPY, TLT, GLD, EFA, EEM, DBC) en utilisant un double filtre : prix au-dessus du SMA200 ET momentum positif sur 6 mois. Les actifs passant les deux filtres reçoivent une pondération égale. Rebalance tous les 30 jours. Inspiré de l'approche de trend-following avec allocation en parité de risque de Hurst, Ooi et Pedersen (2014) chez AQR.

## Comment exécuter

### Lean CLI
```bash
lean backtest --algorithm Cloud-RiskParity-Composite/main.py
```

### QC Cloud
Projet 30820857. Téléverser `main.py`, compiler et lancer un backtest. Fenêtre par défaut : **2018-01-01 → 2025-01-01** (alignée sur la baseline cross-stratégie #1630), modifiable par les paramètres `start_date` et `end_date` (`%Y%m%d`). Paramètres optionnels :

- `rebalance_days` (défaut 30) ;
- `mode` : `strategy` par défaut, `spy` et `6040` pour les deux références de la section [Verdict contre références détenues](#verdict-contre-références-détenues-21534).

## Métriques de backtest

Backtest frais via QC Cloud MCP, 2026-08-14 (`RiskParity-Composite-2018-2025-aligned-status-2026-08`, projet 30820857, compile `BuildSuccess`, 1761 dates négociables, 297 ordres) :

| Indicateur | Valeur | Lecture |
|---|---|---|
| Ratio de Sharpe | **0,027** | quasi nul |
| CAGR | **3,50 %** | sous le buy-hold SPY sur la période |
| Drawdown max | **24,400 %** | élevé |
| Profit net total | **27,282 %** (+17 435 $) | sur la période |
| PSR | **0,094 %** | non distinguable du bruit |
| Ordres | 297 | backtest réel |

**Verdict de cette mesure (2026-08-14) : NO-BEATS.** Il comparait le CAGR de la stratégie (~3,5 %) au CAGR à deux chiffres de SPY sur 2018-2025, sans backtest de SPY ni test. La section [Verdict contre références détenues](#verdict-contre-références-détenues-21534) le remplace par une comparaison testée : `NO BEATS` sur la fenêtre codée, `INCONCLUSIVE` hors échantillon.

| Méthode | Rebalance | Paramètres clés |
|---------|-----------|-----------------|
| Parité de risque à double filtre | 30 jours | SMA200 + momentum 6 mois, pondération égale entre les actifs retenus |

## Tranche de minuit (#20264)

En résolution journalière, Lean livre les avis de dividende dans une tranche datée de minuit qui ne porte aucune barre, et TLT verse un dividende chaque mois. Avant le correctif, quand l'échéance des 30 jours était déjà échue à minuit, cette tranche déclenchait le rééquilibrage. La sélection et les quantités étaient alors calculées sur les clôtures de la veille, et les ordres remplis une séance plus tôt. Les autres mois, la décision se prenait à 16:00 sur la clôture du jour. Le garde placé en tête de `on_data` ignore toute tranche sans barre : chaque rééquilibrage part désormais à 16:00. Les jours de rééquilibrage ne changent pas, seul l'instant de la décision change.

Mesure avant (`main` à `064dc1c732`) et après, sur quatre backtests QC pré-enregistrés ([protocole](https://github.com/jsboige/CoursIA/issues/20264#issuecomment-6149675428)) :

| Indicateur | Codée, avant | Codée, après | Hors échantillon, avant | Hors échantillon, après |
|---|---|---|---|---|
| Fenêtre | 2018-01-01 → 2025-01-01 | idem | 2025-01-02 → 2026-07-10 | idem |
| Rééquilibrages partis à minuit | 9 sur 80 | 0 sur 80 | 1 sur 18 | 0 sur 18 |
| Rééquilibrages à sélection différente | | 1 sur 80 | | 1 sur 18 |
| Ratio de Sharpe | 0,029 | 0,035 | 1,014 | 0,963 |
| CAGR | 3,49 % | 3,58 % | 23,01 % | 22,05 % |
| Drawdown max | 24,5 % | 24,4 % | 11,9 % | 12,1 % |
| Profit net | 27,14 % | 27,90 % | 36,98 % | 35,37 % |
| PSR | 0,096 % | 0,102 % | 45,07 % | 42,56 % |
| Ordres | 298 | 296 | 77 | 76 |
| Backtest | `3a4eae48` | `1b75d5ce` | `d0b4101a` | `42018e5d` |

- **Fenêtre codée.** L'écart de Sharpe (+0,006) reste sous le seuil de 0,05 fixé au protocole : les métriques de la section précédente restent celles du README, et le verdict NO-BEATS est inchangé. La variante avant reproduit 298 ordres et un Sharpe de 0,029, contre 297 et 0,027 annoncés le 2026-08-14. Une seule sélection diffère : le 2018-08-01, DBC et SPY avant, SPY seul après.
- **Hors échantillon.** La règle du protocole classe le résultat en **dégradation** : le CAGR perd 0,95 point, au-delà du seuil de 0,5 point, et le Sharpe perd 0,051, en deçà du seuil de 0,10. L'écart tient à une seule décision. Le 2025-02-03, la variante avant décide à minuit sur la clôture du vendredi 31 janvier et retient EEM ; la variante après décide à 16:00 sur la clôture du lundi et l'écarte, puis le reprend au rééquilibrage suivant (2025-03-05).

Le correctif ne vise pas la performance : il fait partir toutes les décisions à la même heure, sur la clôture du jour de rééquilibrage.

## Verdict contre références détenues (#21534)

Le protocole a été écrit dans #21534 avant le premier backtest, sur le modèle de #21329. Pour un portefeuille multi-actifs, le 60/40 (SPY 60 %, BND 40 %, rééquilibré au début de chaque mois) est la référence naturelle ; SPY détenu fixe le seuil du verdict `NO BEATS`. Les deux références tournent dans le même algorithme que la stratégie :

- avec les mêmes six abonnements ;
- sous le même modèle de courtage ;
- avec le même préchauffage de 252 séances.

En mode référence, `on_data` ne fait rien.

Les séries comparées sont la valeur du portefeuille à chaque ouverture de SPY (trace `shadow`). Les tests passent par `Paradox46Benchmarks/significance.py`, avec un taux sans risque nul :

- écart de Sharpe de Ledoit-Wolf ;
- bootstrap stationnaire ;
- écart de moyennes de Newey-West.

Sur chaque fenêtre, la correction de Holm porte sur les six p-valeurs.

Règle de verdict, écrite avant la mesure :

- `BEATS` : écart de Sharpe positif et significatif (Holm < 0,05) contre les deux références ;
- `NO BEATS` : Sharpe de la stratégie inférieur à celui de SPY détenu ;
- `INCONCLUSIVE` : tous les autres cas.

**Contrôle d'innocuité : tenu.** En mode `strategy`, sur la fenêtre codée, le code instrumenté (projet 38145133) reproduit le backtest du code d'origine (`63302edb192f3ac25750fe0021c1016b`, projet 38145130) :

- 296 ordres sur 296, sans écart de date, de symbole ni de quantité ;
- 27 statistiques QC sur 27.

Les ordres de la stratégie sont horodatés 16:00 New York, à la clôture de la séance, sur les deux fenêtres ; aucun n'est passé à minuit. La stratégie reste en liquidités pendant ses 30 premiers jours, car le compteur de rééquilibrage part de la date de début ; ces séances comptent dans sa série.

| Fenêtre | Séances | Sharpe stratégie (taux nul) | SPY détenu (taux nul) | 60/40 (taux nul) | p Holm (Ledoit-Wolf, SPY / 60/40) | Verdict |
|---|---|---|---|---|---|---|
| Codée, 2018-01-02 → 2024-12-31 | 1761 | 0,350 | 0,758 | 0,751 | 1,0 / 1,0 | **NO BEATS** |
| Hors échantillon, 2025-01-02 → 2026-07-22 | 388 | 1,500 | 1,063 | 1,180 | 1,0 / 1,0 | **INCONCLUSIVE** |

Statistiques QC (calculées par QC avec son propre taux sans risque). Leurs Sharpe ne se comparent pas à ceux de la table du dessus : QC retranche un taux sans risque non nul et part de ses propres séries quotidiennes, alors que le protocole prend un taux nul sur la valeur du portefeuille à l'ouverture. Le classement des portefeuilles peut donc changer d'une table à l'autre, et le verdict se lit sur la table du dessus.

| Fenêtre | Mode | Sharpe QC (taux de QC, autre échelle) | CAGR | Pire baisse | Ordres | Backtest |
|---|---|---|---|---|---|---|
| Codée | stratégie | 0,035 | 3,58 % | 24,4 % | 296 | `612dcc9e67a272b2dafe85a6dc982e8b` |
| Codée | SPY détenu | 0,496 | 13,58 % | 33,7 % | 3 | `be5102e822d65d785a742dc384db68ab` |
| Codée | 60/40 | 0,378 | 8,66 % | 21,7 % | 147 | `d82b8a947cadca01d14cb0714f916811` |
| Hors échantillon | stratégie | 0,989 | 22,47 % | 12,1 % | 76 | `fe725f78b216a529e3dbd78c29772ba2` |
| Hors échantillon | SPY détenu | 0,647 | 18,40 % | 18,7 % | 2 | `6cd30dea278e0861f1fe727231f53780` |
| Hors échantillon | 60/40 | 0,548 | 12,71 % | 11,2 % | 30 | `5f210726035d1da458622076e2d9d102` |

Le backtest hors échantillon a été demandé jusqu'au 2026-10-20, mais il s'arrête le 2026-07-22 : les nœuds QC utilisés coupent les backtests environ 90 jours avant la date du jour. Aucun paramètre n'a été réglé sur cette période.

**Lecture.** Sur la fenêtre codée, la stratégie est sous les deux références en Sharpe, sans que l'écart soit significatif : les p brutes de Ledoit-Wolf valent 0,23 contre SPY détenu et 0,25 contre le 60/40. Face au 60/40, à volatilité annuelle presque égale selon QC (10,2 % contre 10,1 %), elle rend 3,6 % par an contre 8,7 %, pour une pire baisse plus forte. Hors échantillon, son Sharpe est le plus haut des trois, sans écart significatif : sur 388 séances, l'intervalle bootstrap à 95 % de l'écart contre SPY détenu va de −0,90 à +1,67. Son rendement quotidien moyen y dépasse à peine celui de SPY détenu (Newey-West, p brute 0,80), avec une volatilité plus basse (11,8 % contre 14,6 %). Le code actuel ne bat donc aucune des deux références de façon mesurable, et passe sous SPY détenu sur sa propre fenêtre.

## Fichiers

| Fichier | Description |
|---------|-------------|
| `main.py` | Rotation à double filtre SMA200 + momentum sur 6 ETF multi-actifs ; paramètres `mode`, `start_date` et `end_date`, trace `shadow` (#21534) |

## Références

- Hurst, B., Ooi, Y.H., Pedersen, L.h. (2014). *A Century of Evidence on Trend-Following Investing*. AQR.
- [Documentation QuantConnect](https://www.quantconnect.com/docs/)
