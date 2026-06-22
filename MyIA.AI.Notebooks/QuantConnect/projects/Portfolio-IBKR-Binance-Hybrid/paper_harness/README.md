# paper_harness — exécution paper-trading Phase 4

Harness local d'**exécution paper** du portefeuille hybride IBKR + Binance décrit
dans le [README parent](../README.md) (Phase 4). Distinct de `../main.py` (algorithme
de backtest QC Cloud) : ce package parle aux **venues paper réelles** (Binance Spot
Testnet, IB Gateway paper) au lieu du backtester QC.

Architecture conforme à la décision Phase 4 du README parent (leçon Phase 2 :
`set_brokerage_model(IBKR)` rejette le type Crypto → un backtest unifié 2-broker
n'est pas transposable en live unifié) : approche **Binance-first** — paper-trader
le sleeve crypto seul sur Binance testnet, sleeve IBKR en backtest parallèle.

## État (2026-06-22)

| Composant | Statut |
|-----------|--------|
| `config.py` (loader `.env` typé) | livré |
| `risk.py` (circuit-breakers) | livré, dry-run validé |
| `binance_sleeve.py` (wrapper python-binance testnet) | livré, **SOTA-OK** (validé live) |
| `smoke_test_binance.py` (validation read-only live) | livré |
| `ibkr_sleeve.py` (wrapper ib_insync) | livré, **SOTA-OK** (validé live, surface read-only) |
| `smoke_test_ibkr.py` (validation read-only live) | livré |
| `orchestrator.py` (boucle principale + routing) | **TODO** (cycle suivant) |

## Sécurité

- **Testnet uniquement** en paper (`BINANCE_TESTNET=true`). Les soldes sont fictifs.
- Le smoke test est **read-only** (connexion, soldes, prix, dry-run breakers) — il ne
  place **aucun ordre**. Le chemin ordre (`market_buy`/`market_sell`) est implémenté
  mais activé uniquement par l'orchestrator, après relecture des circuit-breakers.
- Circuit-breakers (`risk.py`) : drawdown max (`RISK_MAX_DD_PCT`), perte journalière
  (`RISK_DAILY_VAR_PCT`), taille de position unitaire (`RISK_MAX_POSITION_PCT`),
  exposition brute (`RISK_MAX_GROSS_EXPOSURE`). Tout ordre passe par `RiskGate.check_order`.
- Aucun secret n'est imprimé ; les credentials vivent uniquement dans le `.env` gitigné.

## SOTA-OK (Prong A)

Les deux sleeves pilotent la **vraie lib** contre la **vraie venue paper** — aucune
sortie de substitution (ASCII, réimplémentation jouet, stub).

- **Binance** : `python-binance` contre le Spot Testnet (clé HMAC, perms
  TRADE+USER_DATA+USER_STREAM, commissions 0.1%). Validation live : `can_trade=True`,
  `maker_fee=10bps`, soldes fictifs présents (BTC/ETH/USDT…).
- **IBKR** : `ib_insync` contre IB Gateway en mode paper/simulated (port 4002). Validation
  live : compte paper connecté, `accountSummary()` lu (NetLiq, cash, buying power),
  `positions()` lu. Le chemin ordre est implémenté mais **gated** sur deux conditions :
  (1) "Read-Only API" OFF côté gateway (sinon IB rejette l'ordre, Error 321), (2) passage
  derrière l'orchestrator + circuit-breakers relus. Aucun ordre placé à ce stade.

## Installation

```bash
python -m pip install -r paper_harness/requirements.txt
```

## Smoke test (read-only, depuis la racine du projet)

```bash
# Binance Spot Testnet
python -m paper_harness.smoke_test_binance

# IB Gateway paper (doit tourner en mode simulated/paper sur IBKR_PORT)
python -m paper_harness.smoke_test_ibkr
```

Sortie attendue (IBKR) : `managed acct`, `net_liq`, `total_cash`, `buying_power`,
`positions: N`, puis dry-run des 3 cas breakers (sane → ALLOW, oversized → BLOCK,
gross → BLOCK). Exit code 0 = SOTA-OK.

## Suite (cycles suivants)

1. `orchestrator.py` : boucle de rebalancement, routing des target par sleeve,
   appel systématique à `RiskGate` avant chaque ordre, logging fills vs backtest.
2. Premier ordre paper (BTC spot sur Binance testnet ; équity IBKR derrière
   "Read-Only API" OFF côté gateway) derrière circuit-breakers relus.

## Liens

- [README parent](../README.md) — Phase 1-3 + roadmap 5 phases + discipline de validation
- Issue [#1027](https://github.com/jsboige/CoursIA/issues/1027)
- [`.env.template`](../.env.template) — clés de configuration (`.env` local gitigné)
