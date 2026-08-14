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

## Fichiers

| Fichier | Description |
|---------|-------------|
| `main.py` | Rotation parité de risque avec double filtre SMA200 + momentum sur 6 ETF multi-actifs |

## Références

- Hurst, B., Ooi, Y.H., Pedersen, L.h. (2014). *A Century of Evidence on Trend-Following Investing*. AQR.
- [Documentation QuantConnect](https://www.quantconnect.com/docs/)
