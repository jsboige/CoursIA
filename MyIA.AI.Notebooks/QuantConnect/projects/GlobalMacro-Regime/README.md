# GlobalMacro-Regime

**Asset class:** Multi-asset (Equities, Bonds, Commodities)

**Cloud project ID:** N/A

## Description

Rank-based Risk Parity with Regime Switching (v3). Uses SMA200 + 6-month momentum for regime classification. In bull markets, allocates to trending risky assets (SPY, EFA, EEM, TLT, GLD, DBC) with rank-weighted inverse-volatility positioning. In bear markets, shifts to risk parity on defensive assets (BND, TLT, GLD). Monthly rebalance.

Les chiffres de la docstring de `main.py` (v3 : Sharpe 0,607, CAGR 11,62 %, pire baisse 23,6 %) ne disent pas sur quelle fenêtre ils ont été mesurés. **Mesure du 2026-10-27 (#22869) :** sur la fenêtre codée (2018-01-01 → 2025-01-01), le code donne un Sharpe QC de 0,456, un CAGR de 9,79 % et une pire baisse de 22,8 % ; voir la section « Verdict contre références détenues (#22869) ».

## How to Run

### Lean CLI
```bash
lean backtest --algorithm GlobalMacro-Regime/main.py
```

### QC Cloud
Créer un projet, y envoyer `main.py`, compiler et lancer un backtest. La fenêtre par défaut est celle du code, 2018-01-01 → 2025-01-01 ; les paramètres `start_date` et `end_date` (format `%Y-%m-%d`) la changent, et le paramètre `mode` choisit le portefeuille (voir la section du verdict).

## Backtest Metrics

| Method | Rebalance | Key Parameters |
|--------|-----------|----------------|
| Regime-switching Risk Parity (v3) | Monthly | SMA200 + 6m momentum regime, rank-based inverse-vol weighting |

## Verdict contre références détenues (#22869)

Le protocole a été écrit dans #22869 avant le premier backtest, sur le modèle de #21594 et de #22828. Les deux références du verdict, SPY détenu et le 60/40 (SPY 60 %, BND 40 %), tournent dans le même algorithme que la stratégie, sous le même modèle de courtage. Deux diagnostics ne comptent pas dans le verdict :

- `ew7`, les sept ETF du code à poids égal, rééquilibrés chaque mois : la sélection et la pondération ajoutent-elles quelque chose à la détention des sept ETF ?
- `noregime`, la même règle, toujours dans la branche haussière, repli défensif compris : le filtre de régime sur SPY ajoute-t-il quelque chose ?

Le paramètre `mode` choisit le portefeuille (`strategy`, `spy`, `6040`, `ew7`, `noregime`). En mode `strategy`, la décision du code ne change pas. Les sept ETF sont déjà abonnés par le code, BND compris : aucun mode n'ajoute d'abonnement.

Propriétés du code, gardées telles quelles :

- le compte est déclaré sur marge, et les ordres partent ETF par ETF dans un ordre fixe : un achat peut précéder la vente qui le finance. L'exposition brute reste proche de 1, sans aucune position courte : au plus 1,009 sur la fenêtre 1 (mi-janvier 2021) et 1,004 sur la fenêtre 2 (début janvier 2025) ;
- les ordres de la stratégie sont soumis à 10 h, heure de New York, 30 minutes après l'ouverture, et remplis à la clôture du jour (`MarketOnClose`). Ceux des références partent à 9 h 31 et sont aussi remplis à la clôture ;
- le régime et le filtre de tendance lisent la clôture de la veille. Le préchauffage de 300 jours calendaires couvre la moyenne de 200 séances, et le premier ordre part à la première séance de chaque fenêtre (2018-01-02 et 2025-01-02).

Les fenêtres sont coupées au 1er janvier 2025, date de fin du code. La docstring classe les versions v1 à v6 (« v4-v6: no improvement ») sans dire sur quelle fenêtre ; un commentaire du code indique un début en 2015, aligné sur 2018 par #1630. La fenêtre 1 recouvre donc, au moins en partie, l'échantillon sur lequel la v3 a été retenue ; la fenêtre 2 commence à la date de fin codée.

Les séries comparées sont la valeur du portefeuille à chaque ouverture de SPY. Les tests passent par `Paradox46Benchmarks/significance.py`, avec un taux sans risque nul :

- écart de Sharpe de Ledoit-Wolf ;
- bootstrap stationnaire ;
- écart de moyennes de Newey-West.

Sur chaque fenêtre, la correction de Holm porte sur les six p-valeurs du verdict. Les diagnostics sont une exécution séparée, avec leur propre correction de Holm sur six p-valeurs.

Règle de verdict, écrite avant la mesure :

- `BEATS` : écart de Sharpe positif et significatif (Holm < 0,05, Ledoit-Wolf) contre les deux références ;
- `NO BEATS` : Sharpe de la stratégie inférieur à celui de SPY détenu ;
- `INCONCLUSIVE` : tous les autres cas.

**Contrôle d'innocuité : tenu.** En mode `strategy`, sur la fenêtre codée (2018-01-01 → 2025-01-01), le code instrumenté (backtest `f055fc0faf4a3d6fed4e95aff94bcbc6`, projet 38513084) reproduit le backtest du code d'origine (`5914828ce44d6e8ce1454998e55d2e26`, projet 38513082), lancé le même jour :

- 376 ordres sur 376, sans écart de date, de symbole ni de quantité ;
- 27 statistiques QC sur 27, et 8 statistiques d'exécution sur 8.

Ces statistiques diffèrent peu de l'ancienne ligne du registre `docs/qc/qc-strategies-status.md` (Sharpe QC 0,454, CAGR 9,80 %, pire baisse 22,8 %), sauf la PSR de QC : 3,5 % ici, 16,7 % au registre. L'origine de cet écart n'a pas été recherchée.

| Fenêtre | Séances | Sharpe stratégie (taux nul) | SPY détenu (taux nul) | 60/40 (taux nul) | p Holm (Ledoit-Wolf, SPY / 60/40) | Verdict |
|---|---|---|---|---|---|---|
| 1, 2018-01-02 → 2024-12-31 | 1761 | 0,838 | 0,758 | 0,751 | 1,0 / 1,0 | **INCONCLUSIVE** |
| 2, 2025-01-02 → 2026-07-01 | 374 | 1,232 | 1,080 | 1,224 | 1,0 / 1,0 | **INCONCLUSIVE** |

Statistiques QC (calculées par QC avec son propre taux sans risque). Leurs Sharpe ne se comparent pas à ceux de la table du dessus : QC retranche un taux sans risque non nul et part de ses propres séries quotidiennes, alors que le protocole prend un taux nul sur la valeur du portefeuille à l'ouverture. Le verdict se lit sur la table du dessus.

| Fenêtre | Mode | Sharpe QC (taux de QC, autre échelle) | CAGR | Pire baisse | Ordres | Backtest |
|---|---|---|---|---|---|---|
| 1 | stratégie | 0,456 | 9,79 % | 22,8 % | 376 | `35eebe866e191efdb2fac677afad214f` |
| 1 | SPY détenu | 0,496 | 13,58 % | 33,7 % | 3 | `aef77e08fae01f3d24dadf96a826b467` |
| 1 | 60/40 | 0,378 | 8,66 % | 21,7 % | 147 | `ad4a11a7874adbb7ef00567ab5bfa27c` |
| 1 | 7 ETF à poids égal | 0,141 | 5,04 % | 19,3 % | 380 | `2c90ed70e254e157a3458d356844ba3b` |
| 1 | sans filtre de régime | 0,497 | 10,64 % | 22,2 % | 356 | `20fd45cb9a9461b6a6162f98b0f2f0e8` |
| 2 | stratégie | 0,617 | 14,70 % | 9,6 % | 95 | `b05c630ffcd258d3e96f671228d5257f` |
| 2 | SPY détenu | 0,665 | 18,96 % | 18,7 % | 2 | `a42c89652281ac130c15e4773762a172` |
| 2 | 60/40 | 0,590 | 13,37 % | 11,2 % | 30 | `19a938c38eabd38e50655a0dcae97fb7` |
| 2 | 7 ETF à poids égal | 1,127 | 20,34 % | 8,0 % | 83 | `11a2aaebece6737088a24b19fe696cd3` |
| 2 | sans filtre de régime | 0,964 | 21,58 % | 10,2 % | 91 | `1d7182c45d740da71f47a13b517f6d23` |

Le backtest de la fenêtre 2 va jusqu'à sa date codée : sa dernière séance est le 2026-07-01, et la coupure d'environ 90 jours que les nœuds QC utilisés appliquent à la fin des backtests ne l'a pas atteint. Sur ses 374 séances, la fenêtre a peu de puissance. Ses deux références reproduisent celles de la mesure #22828 sur la même fenêtre, lancées dans un autre algorithme : mêmes Sharpe à taux nul (1,080 et 1,224) et mêmes statistiques QC.

**Lecture.** Sur les deux fenêtres, la stratégie a un Sharpe ponctuel supérieur à celui de SPY détenu et à celui du 60/40, sans qu'aucun écart soit significatif : la p de Holm vaut 1,0 pour les six tests de chaque fenêtre. Selon la règle écrite avant la mesure, le verdict est `INCONCLUSIVE`. Sur la fenêtre 1, l'intervalle bootstrap à 95 % de l'écart contre SPY détenu va de −0,66 à +0,77. La stratégie y gagne moins que SPY détenu (rendement quotidien moyen annualisé de 10,1 % contre 14,7 %), et son Sharpe le dépasse parce que sa volatilité est plus basse (12,1 % contre 19,4 % par an), comme sa pire baisse (22,8 % contre 33,7 %). Le Sharpe de QC classe la stratégie sous SPY détenu sur les deux fenêtres (0,456 contre 0,496, puis 0,617 contre 0,665) : retrancher un taux sans risque pèse davantage sur la série la moins volatile. Le protocole fixe un taux nul.

**Diagnostic : le filtre de régime n'ajoute rien de mesurable ; l'apport de la sélection reste ouvert sur la fenêtre 1 et manque sur la fenêtre 2.**

| Fenêtre | Diagnostic | Sharpe du diagnostic (taux nul) | Écart stratégie − diagnostic | Intervalle bootstrap 95 % | p Holm (Ledoit-Wolf) | Corrélation | Lecture |
|---|---|---|---|---|---|---|---|
| 1 | 7 ETF à poids égal | 0,535 | +0,303 | −0,24 à +0,83 | 1,0 | 0,64 | question ouverte |
| 1 | sans filtre de régime | 0,871 | −0,032 | −0,20 à +0,12 | 1,0 | 0,95 | rien de mesurable |
| 2 | 7 ETF à poids égal | 1,865 | −0,633 | −1,69 à +0,33 | 1,0 | 0,83 | rien de mesurable |
| 2 | sans filtre de régime | 1,550 | −0,318 | −1,02 à +0,38 | 1,0 | 0,88 | rien de mesurable |

Sur les deux fenêtres, la même règle sans filtre de régime a un Sharpe ponctuel supérieur à celui de la stratégie (0,871 contre 0,838, puis 1,550 contre 1,232), avec des écarts non significatifs : le filtre de régime sur SPY n'ajoute rien de mesurable. Sur la fenêtre 1, la stratégie dépasse les sept ETF détenus à poids égal (0,838 contre 0,535) sans que l'écart soit significatif : selon la règle écrite avant la mesure, la question reste ouverte. Sur la fenêtre 2, elle fait moins bien qu'eux (1,232 contre 1,865), sans écart significatif non plus.

**Prédictions écrites avant la mesure :**

- contrôle d'innocuité tenu : juste ;
- fenêtre 1, `NO BEATS` contre SPY détenu : faux. La prédiction s'appuyait sur le Sharpe de l'ancienne ligne du registre (0,454), qui est un Sharpe QC ; à taux nul, la stratégie dépasse SPY détenu (0,838 contre 0,758) et le verdict est `INCONCLUSIVE` ;
- diagnostic `ew7` sur la fenêtre 1, Sharpe de la stratégie supérieur sans écart significatif : juste ;
- diagnostic `noregime` sur la fenêtre 1, écart non significatif : juste. Son signe, non prédit, est négatif ;
- fenêtre 2 : pas de prédiction.

## Files

| File | Description |
|------|-------------|
| `main.py` | Stratégie v3 (parité de risque pondérée par le rang, bascule de régime), avec le paramètre `mode` et la trace `shadow` de la mesure #22869 |

## References

- Hurst, B., Ooi, Y.H., Pedersen, L.H. (2014). *A Century of Evidence on Trend-Following Investing*. AQR.
- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
