# paper_harness — exécution paper-trading Phase 4

Harness local d'**exécution paper** du portefeuille hybride IBKR + Coinbase (MiCA) décrit
dans le [README parent](../README.md) (Phase 4). Distinct de `../main.py` (algorithme
de backtest QC Cloud) : ce package parle aux **venues paper réelles** (Coinbase Advanced
Trade API, IB Gateway paper) au lieu du backtester QC.

## Migration MiCA : sleeve crypto Binance → Coinbase (2026-06-28)

Le sleeve crypto ACTIF est désormais **Coinbase** (Binance France cesse le 2026-07-01,
pas de licence CASP MiCA ; Coinbase détient la CASP MiCA France + est nativement supporté
par QC, `Market.COINBASE` dans `../main.py`). Le `binance_sleeve.py` est conservé comme
**fallback legacy** mais n'est plus le chemin actif. Voir la section [Migration MiCA](../README.md#migration-mica-sleeve-crypto-binance--coinbase-2026-06-28)
du README parent.

Architecture conforme à la décision Phase 4 du README parent (leçon Phase 2 :
`set_brokerage_model(IBKR)` rejette le type Crypto → un backtest unifié 2-broker
n'est pas transposable en live unifié) : approche **crypto-first** — paper-trader
le sleeve crypto seul sur Coinbase, sleeve IBKR en backtest parallèle.

## État (2026-06-28)

| Composant | Statut |
|-----------|--------|
| `config.py` (loader `.env` typé) | livré (ajout `CoinbaseConfig`) |
| `risk.py` (circuit-breakers) | livré, dry-run validé |
| `coinbase_sleeve.py` (wrapper coinbase-advanced-py, **MiCA**) | livré, **SOTA-OK code** (API vérifiée firsthand) |
| `smoke_test_coinbase.py` (validation read-only) | livré, exit 2 = USER-HAND sans creds |
| `binance_sleeve.py` (wrapper python-binance testnet, **legacy**) | livré, SOTA-OK (pré-MiCA) |
| `smoke_test_binance.py` (validation read-only live) | livré (legacy) |
| `ibkr_sleeve.py` (wrapper ib_insync) | livré, **SOTA-OK** (validé live, surface read-only) |
| `smoke_test_ibkr.py` (validation read-only live) | livré |
| `orchestrator.py` (boucle principale + routing) | **TODO** (cycle suivant) |

## Sécurité

- **Sandbox / paper uniquement** tant que `COINBASE_SANDBOX=true`. Coinbase Advanced
  Trade n'a pas de testnet public distinct de Binance : le « sandbox » est un **compte
  Coinbase paper** dont la clé API frappe le même endpoint (documenté honnêtement, pas
  contourné). Les soldes d'un compte paper sont fictifs.
- Le smoke test est **read-only** (connexion, soldes, prix, dry-run breakers) — il ne
  place **aucun ordre**. Le chemin ordre (`market_buy`/`market_sell`) est implémenté
  mais activé uniquement par l'orchestrator, après relecture des circuit-breakers.
- Circuit-breakers (`risk.py`) : drawdown max (`RISK_MAX_DD_PCT`), perte journalière
  (`RISK_DAILY_VAR_PCT`), taille de position unitaire (`RISK_MAX_POSITION_PCT`),
  exposition brute (`RISK_MAX_GROSS_EXPOSURE`). Tout ordre passe par `RiskGate.check_order`.
- Aucun secret n'est imprimé ; les credentials vivent uniquement dans le `.env` gitigné.

## SOTA-OK (Prong A)

Les sleeves pilotent la **vraie lib** contre la **vraie venue paper** — aucune
sortie de substitution (ASCII, réimplémentation jouet, stub).

- **Coinbase (ACTIF, MiCA)** : `coinbase-advanced-py` contre l'Advanced Trade API (clé
  CDP Ed25519/ECDSA). API surface vérifiée firsthand sur la lib installée (1.8.4) :
  `RESTClient(api_key, api_secret)`, `get_accounts()`, `get_product()`,
  `market_order_buy(client_order_id, product_id, quote_size)`,
  `market_order_sell(client_order_id, product_id, base_size)`, `cancel_orders(order_ids=[...])`.
  Le code sleeve est SOTA-OK ; le **run live** est gated **USER-HAND** : ouverture de
  compte Coinbase + création de clé CDP côté user (#1027 Phase-B). Le smoke test
  rapporte `RECOVERABLE-USER-HAND` (exit 2) en attendant.
- **Binance (LEGACY)** : `python-binance` contre le Spot Testnet (pré-MiCA). Conservé
  comme fallback.
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
# Coinbase (MiCA) — sans creds : exit 2 RECOVERABLE-USER-HAND (attendu)
python -m paper_harness.smoke_test_coinbase

# IB Gateway paper (doit tourner en mode simulated/paper sur IBKR_PORT)
python -m paper_harness.smoke_test_ibkr
```

Sortie attendue (IBKR) : `managed acct`, `net_liq`, `total_cash`, `buying_power`,
`positions: N`, puis dry-run des 3 cas breakers (sane → ALLOW, oversized → BLOCK,
gross → BLOCK). Exit code 0 = SOTA-OK.

## Suite (cycles suivants)

1. `orchestrator.py` : boucle de rebalancement, routing des target par sleeve,
   appel systématique à `RiskGate` avant chaque ordre, logging fills vs backtest.
2. Premier ordre paper (BTC spot sur Coinbase sandbox ; équity IBKR derrière
   "Read-Only API" OFF côté gateway) derrière circuit-breakers relus — **après**
   obtention des creds Coinbase USER-HAND.

## Liens

- [README parent](../README.md) — Phase 1-3 + roadmap 5 phases + migration MiCA
- Issue [#1027](https://github.com/jsboige/CoursIA/issues/1027)
- [`.env.template`](../.env.template) — clés de configuration (`.env` local gitigné)
