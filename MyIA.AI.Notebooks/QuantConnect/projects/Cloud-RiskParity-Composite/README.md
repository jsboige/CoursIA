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
Projet 30820857. Téléverser `main.py`, compiler et lancer un backtest. Période codée en dur : **2018-01-01 → 2025-01-01** (alignée sur la baseline cross-stratégie #1630). Paramètre optionnel `rebalance_days` (défaut 30).

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

**Verdict : NO-BEATS.** Sharpe 0,027, CAGR ~3,5 % : la rotation à double filtre sur cette fenêtre ne bat pas le buy-and-hold SPY (CAGR à deux chiffres 2018-2025). Le plafond structurel du trend-following égal-pondéré sans levier est confirmé (cf catalogue `qc-strategies-status.md` : « contre-exemple pédagogique »).

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

## Fichiers

| Fichier | Description |
|---------|-------------|
| `main.py` | Rotation parité de risque avec double filtre SMA200 + momentum sur 6 ETF multi-actifs |

## Références

- Hurst, B., Ooi, Y.H., Pedersen, L.h. (2014). *A Century of Evidence on Trend-Following Investing*. AQR.
- [Documentation QuantConnect](https://www.quantconnect.com/docs/)
