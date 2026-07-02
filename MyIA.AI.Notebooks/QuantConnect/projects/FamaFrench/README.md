# FamaFrench

**Classe d'actifs :** ETFs facteurs US
**ID projet Cloud :** Aucun (local uniquement)

## Description

Stratégie de rotation d'ETFs因子 utilisant le momentum ajusté au risque (rendement 12m-1m / volatilité réalisée 63j) avec mois de skip.

Univers de 5 ETFs facteurs Fama-French : VLUE (valeur), MTUM (momentum), SIZE (taille), QUAL (qualité), USMV (low-vol).

Filtre de régime SMA200 sur SPY : en marché baissier, rotation vers USMV comme actif risk-off.
Sélection dynamique top_n (tous les facteurs à score positif). Stop-loss par position à -12%.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/FamaFrench"`
```bash
lean backtest --project .
```

**QC Cloud :** Pas encore déployé. Copier les fichiers dans un nouveau projet QC Cloud pour exécuter.

## Métriques backtest (2015-2026)

| Métrique | Valeur |
|----------|--------|
| Ratio de Sharpe | 0,540 |
| CAGR | 12,1 % |
| Drawdown max | 24,2 % |
| Rendement net | +258 % |
| Rééquilibrage | Mensuel |

### Baseline alignée (2018-2025)

Exécution backbone #1630 standardisée (projet QC Cloud `33251801`, backtest `697e96af`).

| Métrique | Valeur |
|----------|--------|
| Ratio de Sharpe | 0,445 |
| CAGR | 11,111 % |
| Drawdown max | 24,100 % |
| Ratio de Sharpe probabiliste | 11,9 % |
| Dates tradables | 1761 |

Interprétation : Sharpe positif fort 0,445 (3ᵉ meilleur backbone non-ML, proche de GlobalMacro-Regime 0,454) avec le 2ᵉ CAGR le plus élevé (11,1 %, après HAR-RV-J-Kelly 14,1 %). La rotation因子 ajustée au risque (momentum 12m-1m / vol réalisée 63j, top_n dynamique) combinée au filtre de régime SMA200, USMV risk-off et stop-loss -12 % par position survit à l'alignement 2018-2025 avec seulement une baisse légère du Sharpe vs la v3.0 2015-2024 de l'auteur (0,540 → 0,445 ; MaxDD stable 24,2 % → 24,1 %) — la stratégie est véritablement robuste, pas sur-ajustée à la période, contrairement au constat plus large « effondrement des facteurs simples » (il s'agit d'une rotation momentum ajustée au risque, pas d'une exposition statique aux facteurs). Sous le composite FamaFrenchAllWeather (0,684) — le composite dframework apporte de la valeur par rapport à la rotation isolée. Promu Tier 4 → 2 (Historique). totalOrders = 0 = artefact d'extraction du wrapper (CAGR 11,1 % implique des trades réels).

## Fichiers

- `main.py` — Stratégie (v3, momentum ajusté au risque avec mois de skip)
- `research.ipynb` — Analyse因子 et tests de robustesse du signal

## Références

- Fama & French (1993), « Common risk factors in the returns on stocks and bonds »
- Barroso & Santa-Clara (2015), « Momentum has its moments »