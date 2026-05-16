# QC-IBKR Integration Guide

Documentation compilee depuis les sources officielles QuantConnect + IBKR Campus.
Derniere mise a jour : 2026-05-16.

---

## 1. Configuration requise

### 1.1 Compte IBKR

| Prerequis | Detail |
|-----------|--------|
| Plan IBKR | **PRO requis** (pas LITE). Le plan LITE ne supporte pas l'API programmatique. |
| Type de compte | Individuel ou Financial Advisor (FA). Les comptes FA supportent le filtrage par groupe. |
| IB Key | Obligatoire pour l'authentification 2FA. **SMS 2FA non supporte** par QC. |
| Abonnement donnees | Market data subscriptions necessaires pour les instruments tradés (ex: US Equities Bundle). |

### 1.2 Logiciel IB Gateway / TWS

- **IB Gateway** (recommande pour trading automatisé) : tourne en headless, port paper=4002, live=4001
- **TWS** (Trader Workstation) : alternative avec GUI, port paper=7497, live=7496
- Version testee : IB Gateway 10.46.1g, server version 176

#### Configuration IB Gateway

```
Edit > Global Configuration > API > Settings:
  - Enable ActiveX and Socket Clients = YES
  - Socket port: 4002 (paper) / 4001 (live)
  - Allow connections from: 127.0.0.1
  - Read-only API: NO (pour passer des ordres)
  - Download open orders on connection: YES
```

Le fichier `jts.ini` (ex: `C:\Jts\ibgateway\1046\jts.ini`) contient :
```ini
[IBGateway]
ApiOnly=true
LocalServerPort=4002
TrustedIPs=127.0.0.1

[Logon]
tradingMode=p          # p = paper, u = unified (live)
UseSSL=true
```

### 1.3 Authentification hebdomadaire

**Re-auth Sunday obligatoire** : IBKR exige une re-authentification chaque dimanche via IB Key.
- QC Cloud redemarre automatiquement l'algorithme apres re-auth
- Pour IB Gateway local : intervention manuelle requise le dimanche
- Parametre QC : `ib-weekly-restart-utc-time` (format HH:MM:SS UTC)

### 1.4 IP Whitelist (QC Cloud)

Si vous utilisez QC Cloud pour live trading avec IBKR, ajoutez l'IP QC a votre liste blanche IBKR :
- **IP QC : 207.182.16.137**
- Configuration : IB Gateway/TWS > Global Configuration > API > Settings > Trusted IPs

---

## 2. Classes d'actifs supportees

| Classe | Support QC-IBKR | Notes |
|--------|----------------|-------|
| US Equities | Oui | NYSE, NASDAQ, ARCA, AMEX |
| Equity Options | Oui | Chains completes, greeks |
| Forex | Oui | Paires majeures/mineures |
| Futures | Oui | CME, CBOT, NYMEX, COMEX, ICE |
| Future Options | Oui | Options sur futures |
| Indices | Oui | Data only, pas de trading direct |
| Index Options | Oui | SPX, NDX, etc. |
| CFD | Oui | Contracts for Difference |

**Non supporte** : Fractional shares, crypto direct (utiliser Binance sleeve).

---

## 3. Types d'ordres

| Type | QC Enum | Notes |
|------|---------|-------|
| Market | `OrderType.Market` | Execution immediate |
| Limit | `OrderType.Limit` | Prix limite specifie |
| LimitIfTouched | `OrderType.LimitIfTouched` | Trigger + limit |
| StopMarket | `OrderType.StopMarket` | Stop-loss style |
| StopLimit | `OrderType.StopLimit` | Stop + limit price |
| TrailingStop | `OrderType.TrailingStop` | Trail amount ou percentage |
| MarketOnOpen (MOO) | `OrderType.MarketOnOpen` | Ouverture session |
| MarketOnClose (MOC) | `OrderType.MarketOnClose` | Fermeture session |
| Combo | Combo orders | Multi-leg (options spreads) |

### Proprietes d'ordre

```python
from AlgorithmImports import *

# Time in Force
order_properties = OrderProperties()
order_properties.TimeInForce = TimeInForce.Day           # Journee
order_properties.TimeInForce = TimeInForce.GoodTilDate(datetime(2026, 6, 1))  # GTD
order_properties.TimeInForce = TimeInForce.GoodTilCanceled  # GTC

# Outside Regular Trading Hours
order_properties.Exchange = Exchange.EXTENDED  # Pre/after-hours
```

### Fill simulation

- **Temps de fill moyen** : 400ms (paper et live)
- **Slippage modele** : configurable via `self.SlippageModel`
- **Transaction costs** : 5bps recommande pour equities US

---

## 4. Deployment QC Cloud

### 4.1 Configuration via MCP qc-mcp

```python
# Parametres de connexion IBKR pour create_live_algorithm
{
    "brokerage": {
        "id": "InteractiveBrokersBrokerage",
        "ib-user-name": "<username>",
        "ib-account": "<account_id>",
        "ib-password": "<password>",
        "ib-weekly-restart-utc-time": "04:00:00",
        "ib-financial-advisors-group-filter": ""  # Optionnel, pour comptes FA
    },
    "dataProviders": {
        "InteractiveBrokersBrokerage": {
            "id": "InteractiveBrokersBrokerage",
            "ib-user-name": "<username>",
            "ib-account": "<account_id>",
            "ib-password": "<password>",
            "ib-weekly-restart-utc-time": "04:00:00"
        }
    }
}
```

### 4.2 Deploiement local via lean-cli

Alternative economique au QC Cloud :

```bash
# Backtest avec donnees IBKR
lean backtest --data-provider-historical "Interactive Brokers"

# Live trading avec IBKR
lean live deploy \
    --brokerage "Interactive Brokers" \
    --data-provider-live "Interactive Brokers" \
    --environment paper

# Necessite Docker + lean-cli installe
pip install lean-cli
lean init
```

### 4.3 Prix QC Cloud

| Composant | Cout mensuel |
|-----------|-------------|
| IBKR Live Trading Subscription | $10/mo minimum |
| Live Trading Node (N1-4) | ~$20-40/mo |
| Backtest Node | ~$8-16/mo |
| **Total estimé** | **~$38-66/mo** |

Le plan Researcher Pack ($60/mo) inclut backtesting + research nodes mais pas le live node.

---

## 5. Connexion IB Gateway locale

### 5.1 Test de connexion

Le script `ibkr_connection_test.py` dans ce dossier teste la connexion :

```bash
# Paper trading (defaut, port 4002)
python ibkr_connection_test.py

# Live trading (port 4001)
python ibkr_connection_test.py --live

# Override host/port
python ibkr_connection_test.py --host 127.0.0.1 --port 4002
```

**Prerequis** : `pip install ib_insync python-dotenv`

### 5.2 Identification du probleme "API en lecture seule"

Si le test retourne `"L'interface API est actuellement en lecture seule"` :

1. **Verifier** IB Gateway > Global Configuration > API > Settings > **Read-only API = NO**
2. **Attendre** la synchronisation initiale (2-3 minutes apres login)
3. **Verifier** que le compte paper est actif dans IB Gateway
4. **Redemarrer** IB Gateway si necessaire

### 5.3 Utilisation avec `ib_insync`

```python
from ib_insync import IB, Stock, util

ib = IB()
ib.connect('127.0.0.1', 4002, clientId=1)

# Exemple : requeter SPY
spy = Stock('SPY', 'SMART', 'USD')
ib.qualifyContracts(spy)
ticker = ib.reqMktData(spy, '', True, False)
ib.sleep(2)
print(f'SPY: {ticker.last} (bid={ticker.bid}, ask={ticker.ask})')

ib.disconnect()
```

---

## 6. Integration FIX (avance)

Pour les institutions necessitant FIX protocol :
- Disponible via IBKR Client Portal (abonnement supplementaire)
- QC supporte les ordres FIX via `FIXConfiguration`
- Latence sub-millisecond possible
- Non necessaire pour le portfolio hybride (ordres market/limit suffisent)

---

## 7. Troubleshooting

| Probleme | Cause probable | Solution |
|----------|---------------|----------|
| Connection refused | IB Gateway non lance | Demarrer IB Gateway, verifier port |
| "API read-only" | Setting Read-only API = YES | Desactiver dans Global Configuration > API |
| 2FA timeout | IB Key non configure | Installer IB Key sur mobile |
| Market data refused | Pas de subscription data | Souscrire aux data feeds IBKR |
| Disconnect Sunday | Re-auth hebdomadaire | Re-authentifier, redemarrer algo QC |
| Order rejected | Pas assez de marge / restriction | Verifier pouvoir d'achat et permissions |
| "L'interface API est en lecture seule" | IB Gateway en mode lecture seule | Desactiver Read-only API + attendre sync |

---

## 8. Workflow papier -> live

```
1. Research notebook (QuantBook QC Cloud ou local)
   |
2. Backtest QC Cloud (compile + create_backtest)
   |  Verifier: Sharpe > 0.5, MaxDD < 25%, CAGR > 8%
   |
3. Paper trading IBKR (30 jours minimum)
   |  - Deployer sur QC Cloud node paper
   |  - Logger fills quotidiens vs backtest
   |  - Mesurer slippage reel vs modele
   |
4. Review papier (apres 30j)
   |  - Sharpe reel vs backtest (delta < 30% acceptable)
   |  - MaxDD observe < seuil circuit-breaker
   |  - Aucun bug d'execution
   |
5. Live trading IBKR
   |  - Deployer sur QC Cloud node live
   |  - IBKR plan PRO requis
   |  - Monitoring rolling 30j + circuit-breaker
   |
6. Monitoring continu
      - Sharpe rolling 30j
      - MaxDD circuit-breaker -10% (config RISK_MAX_DD_PCT)
      - Vol spike alerte (RISK_VOL_SPIKE_THRESHOLD = 2.0)
```

---

## 9. References

- [QC IBKR Brokerage Docs](https://www.quantconnect.com/docs/v2/cloud-platform/live-trading/brokerages/interactive-brokers)
- [QC IBKR Brokerage Page](https://www.quantconnect.com/brokerages/interactive)
- [IBKR Campus - Live Algo Trading with QC](https://www.interactivebrokers.com/campus/ibkr-quant-news/interactive-brokers-live-algo-trading-with-quantconnect/)
- [IB Gateway Installation Guide](https://www.interactivebrokers.com/campus/ibkr-authentication/ibgateway/)
- [ib_insync Library](https://github.com/erdewit/ib_insync)

---

## 10. Notes specifiques au projet

- **Compte paper** : `DUA330080` (username: voir `.env`)
- **Compte live** : `U15347277`
- **IB Gateway** : v10.46.1g, paper mode, port 4002
- **Issue #1199** : Changer le mot de passe paper trading pour un mot de passe dedie (KeePass)
- **.env** : Credentials dans `.env` local uniquement, JAMAIS committe (`.gitignore`)
