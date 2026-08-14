# Cloud-MeanReversion-Sectors

**Classe d'actifs :** Actions (ETF sectoriels GICS)

**ID projet Cloud :** 30822855

## Description

Stratégie de retour à la moyenne basée sur le RSI(14) sur 11 ETF sectoriels GICS (XLK, XLF, XLE, XLV, XLI, XLY, XLP, XLU, XLB, XLRE, XLC). Trois variantes de sophistication croissante : v1 utilise des signaux bruts de survente/surachat du RSI ; v2 ajoute un filtre de régime SMA200 (ne trader qu'en marché haussier) ; v3 incorpore une règle de stop-loss à 8 %. Scan quotidien 30 minutes après l'ouverture du marché. Brokerage Interactive Brokers (frais réels), benchmark SPY.

## Comment exécuter

### Lean CLI
```bash
lean backtest --algorithm Cloud-MeanReversion-Sectors/main.py
```

### QC Cloud
Projet 30822855. Téléverser `main.py`, compiler et lancer un backtest en passant le paramètre `version` (`v1`/`v2`/`v3`). Période codée en dur : **2018-01-01 → 2025-01-01** (alignée sur la baseline cross-stratégie #1630).

> **Note** : le paramètre `version` doit être passé explicitement (`v1`, `v2` ou `v3`). Le défaut du code (`"1"`) ne correspond à aucune branche et lèverait une `AttributeError` au premier scan ; le paramètre explicite est obligatoire pour toute exécution.

## Métriques de backtest

Backtest frais via QC Cloud MCP, 2026-08-14 (`MeanReversion-v1-2018-2025-aligned-status-2026-08`, projet 30822855, compile `BuildSuccess`, paramètre `version=v1`, **1761 dates négociables — baseline #1630 alignée 2018-2025**, 273 ordres) :

| Indicateur | Valeur | Lecture |
|---|---|---|
| Ratio de Sharpe | **0,067** | quasi nul |
| CAGR | **3,793 %** | sous le buy-hold SPY sur la période |
| Drawdown max | **41,700 %** | catastrophique (> 2× SPY) |
| Profit net total | **29,789 %** (+35 082 $) | sur la période |
| PSR (Probabilistic Sharpe Ratio) | **0,147 %** | non distinguable du bruit |
| Ordres | 273 | backtest réel |

**Verdict : NO-BEATS.** Sharpe 0,067, CAGR ~3,8 % pour un drawdown de 41,7 %, PSR ≈ 0 : la stratégie sous-performe le buy-and-hold SPY (CAGR à deux chiffres sur 2018-2025) avec un risque bien supérieur.

> **Historique des mesures (traçabilité)** : (1) run du 2026-04-28 sur code pré-#1630 (2014-2025, 2768 j.) : v1 Sharpe 0,288 / DD 42,4 %, v2 0,214, **v3 0,278 / DD 14,7 %** ; (2) run du 2026-08-07 même code stale : v1 0,176 / DD 41,7 % ; (3) **run 2026-08-14 ci-dessus, premier sur le code aligné 2018-2025 (#1630)** : v1 0,067. L'alignement retire les années fastes 2014-2017 et dégrade le v1 ; les chiffres d'avant août 2024 cités dans d'anciens catalogues (0,278 / 14,7 %) sont ceux du **v3** sur période 2014-2025 — toujours NO-BEATS sur toutes les fenêtres et variantes, mais incomparables entre eux sans étiquette variante + période.

## Lecture honnête (variante v1)

Le v1 est le mean reversion RSI pur : acheter les 3 ETF sectoriels les plus survendus (RSI < 35), sortir au surachat (RSI > 55) ou après 20 jours de détention. Les faiblesses structurelles observées sur 2018-2025 :

- **Value trap en tendance baissière.** Le RSI reste oversold tant que la baisse se poursuit ; le signal « acheter la survente » accumule des perdants dans les bear markets (Q4 2018, COVID 2020, bear 2022). Sans filtre de régime, le v1 reste pleinement exposé, d'où le drawdown de 41,7 %.
- **Allocation equal-weight des 3 plus oversold.** Les 3 ETF les plus survendus sont souvent les mêmes en chute libre ; concentrer dessus amplifie la queue de perte.
- **PSR ≈ 0.** Le Sharpe 0,176 n'est pas statistiquement significatif : indistinguable du bruit. Tout claim de bord serait trompeur (règle C, PR-review-discipline §C).

Les variants v2 (+ filtre SMA200) et v3 (+ stop-loss 8 %) sont conçus pour adresser ces faiblesses mais ne sont pas backtestés ici : un honest-read documente le variant baseline et son verdict honnête, sans re-tuning. Re-optimiser les seuils RSI, le nombre de positions ou la période de détention pour récupérer un Sharpe positif sur cette seule fenêtre serait du surapprentissage jusqu'à preuve du contraire (EPIC #9768, D2 « fenêtre non figée »). La stratégie est livrée avec ses paramètres codés tels quels, verdict honnête rendu.

## Fichiers

| Fichier | Description |
|---------|-------------|
| `main.py` | Mean reversion RSI(14) avec 3 variantes (v1 RSI pur, v2 +régime SMA200, v3 +stop-loss 8 %) sur 11 ETF sectoriels GICS |

## Références

- [Documentation QuantConnect](https://www.quantconnect.com/docs/)
- EPIC de consolidation QC / Trading : #1621
- Discipliné par l'EPIC #9768 (dérive des métriques de backtest à travers les révisions)

See #1621 (contribution partielle : honest-read d'une stratégie non auditée).
