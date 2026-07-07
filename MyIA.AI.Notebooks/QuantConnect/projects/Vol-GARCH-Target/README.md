# Vol-GARCH-Target

**Classe d'actifs :** Multi-actifs (Actions, Obligations, Matières premières)

**Cloud project ID :** `33245149` (voir `config.json`, local-id : `818573377`)

## Description

Stratégie de vol-targeting GARCH(1,1) sur six actifs (SPY, EFA, EEM, TLT, GLD, DBC). Chaque actif cible 10 % de volatilité annualisée avec des tailles de position ajustées par la prévision GARCH. Utilise une SMA200 pour la direction de la tendance (long en tendance haussière, réduction en tendance baissière). Le modèle est ré-estimé tous les 22 jours de bourse sur une fenêtre d'apprentissage de 500 jours. Rebalance hebdomadaire le lundi.

## Comment exécuter

### Lean CLI
```bash
lean backtest --algorithm Vol-GARCH-Target/main.py
```

### QC Cloud
Ouvrir le projet cloud (project-id : `33245149`), compiler et lancer un backtest.

## Métriques de backtest

| Méthode | Rebalance | Paramètres clés |
|---------|-----------|-----------------|
| Vol-targeting GARCH(1,1) | Hebdomadaire (lundi) | Vol target 10 %, tendance SMA200, fenêtre 500 jours, ré-estimation tous les 22 jours |

### Baseline alignée (2018-2025)

Vérifiée sur QC Cloud (projet 33245149, backtest `a0f7a5b59e878becd574612b85791d51`).

| Période | Sharpe | CAGR | MaxDD | PSR |
|---------|--------|------|-------|-----|
| 2018-2025 (alignée) | 0.325 | 6.97 % | 10.80 % | 14.9 % |

La force de la stratégie est le contrôle du risque, pas le rendement. Un MaxDD de 10.80 % est le plus serré des baselines dorsales à ce jour (cf GlobalMacro-Regime 22.8 %, HAR-RV-J-Kelly 37.1 %, Cloud-VolTargeting mono-actif 38.2 %) — la prévision de variance GARCH(1,1), le plafond de 30 % par actif et le filtre de tendance SMA200 se combinent en un véritable budget de risque qui contient les drawdowns. Le Sharpe de 0.325 est positif mais modeste, et le PSR de 14.9 % est non significatif. Notablement, elle bat Cloud-VolTargeting (mono-actif SPY, vol réalisée, clamp 150 %) à la fois sur le Sharpe (0.325 vs 0.207) et le MaxDD (10.8 % vs 38.2 %) : la prévision GARCH plus la diversification multi-actifs surperforme une naïve vol réalisée mono-actif avec clamp de levier. Promue Tier 4 (Untested) vers Tier 2 (Historique). Voir le doc comparative-backtests pour la table cross-strategy.

## Fichiers

| Fichier | Description |
|---------|-------------|
| `main.py` | Vol-targeting GARCH(1,1) avec filtre de tendance SMA200 sur 6 ETF multi-actifs |
| `config.json` | Configuration du projet (local-id) |
| `research.ipynb` | Notebook de recherche avec analyse du modèle GARCH et exploration des paramètres |

## Références

- Bollerslev, T. (1986). *Generalized Autoregressive Conditional Heteroskedasticity*. Journal of Econometrics.
- [Documentation QuantConnect](https://www.quantconnect.com/docs/)
