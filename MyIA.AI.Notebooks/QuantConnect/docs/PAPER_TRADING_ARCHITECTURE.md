# Paper Trading Architecture

Module pedagogique illustrant le passage backtest -> paper trading -> live trading via QuantConnect, avec deux brokers : Binance (crypto) et Interactive Brokers (multi-asset).

---

## 1. Concepts fondamentaux

### Paper Trading vs Live Trading

Le meme algorithme LEAN s'execute en mode paper ou live. La difference est au niveau de l'execution bridge :

| Aspect | Paper Trading | Live Trading |
|--------|---------------|--------------|
| Donnees de marche | Reelles (temps reel) | Reelles (temps reel) |
| Execution des ordres | Simulee (fills fictifs) | Reelle (envoyee au broker) |
| Capital | Fictif | Reel |
| Slippage | Aucun | Variable selon liquidite |
| Commissions | Simulees selon broker model | Reelles |
| Credentials broker | Non requis | Requis |

Le paper trading teste la logique algorithmique en conditions reelles de donnees, sans risque financier.

### Tiers QuantConnect

| Tier | Paper Trading | IBKR | Binance | Live Nodes | Prix |
|------|:---:|:---:|:---:|:---:|------|
| Free | - | - | - | 0 | Gratuit |
| Quant Researcher | OK | OK | OK | 2 | $20/mois |
| Team | OK | OK | OK | 10 | $80/mois |
| Trading Firm | OK | OK | OK | Illimite | Sur devis |

Le tier **Quant Researcher** ($20/mois) suffit pour le paper trading pedagogique avec 2 nodes live simultanes.

---

## 2. Nodes QuantConnect

### Types de nodes

| Node | CPU | RAM | Usage | Prix indicatif |
|------|-----|-----|-------|----------------|
| B2-8 (Backtest) | 2 @ 4.9GHz | 8 GB | Backtests | Inclus |
| L-MICRO (Live) | 1 @ 2.4GHz | 0.5 GB | Paper/Live trading | $24/mois |
| R1-4 (Research) | 1 @ 2.4GHz | 4 GB | Notebooks research | $12/mois |
| O2-8 (Optimization) | 2 CPUs | 8 GB | Parameter sweep | $40/mois |

**Pour le paper trading** : un node **L-MICRO** (1 CPU, 0.5 GB RAM) suffit pour une strategie simple sur 1-10 actifs. L'algorithme tourne sur les serveurs co-locates de QC.

### Limites par node live

- **L-MICRO** : 10 actifs max, 0.5 GB RAM
- Uptime typique : 6+ mois sans interruption
- Latence : < 100ms pour l'execution simulee

### Selection du node via MCP

```python
# Via l'API MCP QC
read_project_nodes(project_id=PROJECT_ID)
update_project_nodes(project_id=PROJECT_ID, nodes=["LN-xxxxx"])
```

---

## 3. Brokerage : Binance (Crypto)

### Configuration

| Parametre | Paper Trading | Live Trading |
|-----------|---------------|--------------|
| Brokerage | `BinanceBrokerage` | `BinanceBrokerage` |
| Environnement | `paper` (Spot Test Network) | `live` |
| Credentials | API key Testnet (gratuite, pas de compte requis) | API key reelle |
| Account type | Cash ou Margin | Cash ou Margin |

### Code d'initialisation

```python
def initialize(self):
    self.set_brokerage_model(BrokerageName.BINANCE, AccountType.CASH)
    self.add_crypto("BTCUSDT", Resolution.MINUTE, Market.BINANCE)
    self.add_crypto("ETHUSDT", Resolution.MINUTE, Market.BINANCE)
```

### Obtention des credentials Testnet

1. Se connecter au **Binance Spot Test Network** avec un compte GitHub
2. Section API Keys > Generate HMAC_SHA256 Key
3. Sauvegarder la cle API et le secret (pas de compte Binance requis)

### Ordres supportes

| Type | Support |
|------|---------|
| MarketOrder | OK |
| LimitOrder | OK |
| StopLimitOrder | OK |
| Order Updates | **Non** (annuler + recreer) |

### Fees simulees

- 0.1% maker/taker (VIP Level 0)
- Le Testnet ne facture pas de frais reels

### Leverage

- Compte Cash : 1x
- Compte Margin : jusqu'a 3x
- Binance US : Cash uniquement

### Assets disponibles

- Spot crypto : BTC, ETH, et 300+ paires sur Binance
- Donnees : minute, hour, daily (via QC data cloud)

---

## 4. Brokerage : Interactive Brokers (Multi-Asset)

### Configuration

| Parametre | Paper Trading | Live Trading |
|-----------|---------------|--------------|
| Brokerage | `InteractiveBrokersBrokerage` | `InteractiveBrokersBrokerage` |
| Environnement | Paper TWS (port 7497) | Live TWS/Gateway (port 7496) |
| Credentials | Compte paper IBKR | Compte reel IBKR |
| Prerequis | TWS ou IB Gateway en cours d'execution | Idem + 2FA |

### Code d'initialisation

```python
def initialize(self):
    self.set_brokerage_model(
        BrokerageName.INTERACTIVE_BROKERS_BROKERAGE,
        AccountType.MARGIN
    )
    self.add_equity("SPY", Resolution.MINUTE, Market.USA)
    self.add_equity("QQQ", Resolution.MINUTE, Market.USA)
```

### Prerequis specifiques

1. **Compte IBKR** : ouverture en ligne (processus KYC, delai 1-3 jours)
2. **TWS (Trader Workstation)** ou **IB Gateway** installe et en cours d'execution
3. **Parametres TWS** :
   - Activer ActiveX and Socket Clients
   - Configurer le port (7497 paper / 7496 live)
   - Desactiver Read-Only API
4. **Weekly restart** : IBKR requiert un redemarrage hebdomadaire avec verification 2FA

### Deploy via MCP QC

```python
create_live_algorithm(
    model={
        "projectId": PROJECT_ID,
        "compileId": compile_id,
        "nodeId": "LN-xxxxx",
        "versionId": "-1",
        "brokerage": {
            "id": "InteractiveBrokersBrokerage",
            "ib-user-name": "...",
            "ib-account": "...",
            "ib-password": "...",
            "ib-weekly-restart-utc-time": "04:00:00"
        }
    }
)
```

### Ordres supportes

| Type | Support |
|------|---------|
| MarketOrder | OK |
| LimitOrder | OK |
| StopMarketOrder | OK |
| StopLimitOrder | OK |
| MarketOnOpen/Close | OK |
| Order Updates | OK |

### Asset classes

- US Equities, Equity Options, Forex, Futures, Future Options
- Donnees : tick, second, minute, hour, daily

---

## 5. Flux de donnees en live

### Data Providers

QuantConnect supporte plusieurs sources de donnees en live, configurees separement du brokerage :

| Provider | Assets | Resolution | Notes |
|----------|--------|------------|-------|
| QuantConnectBrokerage | Tous | Minute+ | Par defaut, data cloud QC |
| BinanceBrokerage | Crypto | Tick+ | Direct depuis Binance |
| InteractiveBrokersBrokerage | Equities, Options, Forex, Futures | Tick+ | Via TWS |
| PolygonDataFeed | US Equities, Options | Tick+ | Add-on payant |

### Configuration via MCP

```python
create_live_algorithm(
    model={
        # ... brokerage config ...
        "dataProviders": {
            "QuantConnectBrokerage": {"id": "QuantConnectBrokerage"},
            "BinanceBrokerage": {
                "id": "BinanceBrokerage",
                "binance-api-key": "...",
                "binance-api-secret": "...",
                "binance-exchange-name": "Binance",
                "binance-use-testnet": "paper"
            }
        }
    }
)
```

### Ordre de precedence

Les providers sont consultes dans l'ordre de la configuration. Si le premier n'a pas la donnee, le suivant est interroge.

---

## 6. Workflow pedagogique : Backtest -> Paper -> Live

### Etape 1 : Backtest

```
1. Ecrire l'algorithme (Initialize + OnData)
2. Lancer un backtest historique (2-5 ans)
3. Analyser : Sharpe, MaxDD, CAGR, win rate
4. Optimiser les parametres (si necessaire)
```

### Etape 2 : Paper Trading (1-2 semaines)

```
1. Compiler le projet : create_compile()
2. Deployer en paper trading : create_live_algorithm() avec broker paper
3. Monitorer quotidiennement :
   - read_live_algorithm() : stats, portfolio
   - read_live_orders() : ordres executes
   - read_live_logs() : erreurs eventuelles
4. Comparer les resultats paper avec le backtest sur la meme periode
```

### Etape 3 : Analyse des ecarts backtest/paper

| Source d'ecart | Description |
|----------------|-------------|
| Slippage | Le paper trading simule sans slippage (sauf si configure) |
| Timing | Les donnees live peuvent avoir des latences differentes |
| Liquidite | Les ordres paper sont fills immediatement, pas toujours le cas en live |
| Market impact | Non modelise en paper trading |

### Etape 4 : Transition vers le live (hors scope pedagogique)

Voir `PAPER_TO_LIVE_TRANSITION.md` pour les prerequis.

---

## 7. Architecture des notebooks

### QC-Py-40 : Paper Trading Binance (Mean-Reversion Crypto)

**Objectif** : Demontrer le workflow complet backtest -> paper deploy sur crypto.

```
Notebook structure:
1. Introduction : concepts paper trading, architecture QC
2. Strategie mean-reversion Bollinger Bands (BTC/ETH)
3. Backtest historique 2020-2024
4. Analyse des resultats
5. Deploy en paper trading via MCP QC
6. Monitoring : lire les stats live
7. Exercice : adapter les parametres BB
```

### QC-Py-41 : Paper Trading IBKR (SP500 Momentum)

**Objectif** : Workflow identique sur equities via IBKR.

```
Notebook structure:
1. Introduction : IBKR comme broker multi-asset
2. Strategie momentum (cross-section SP500)
3. Backtest historique
4. Configuration IBKR (prerequis TWS)
5. Deploy en paper trading
6. Monitoring
7. Exercice : ajouter un filtre de volatilite
```

### Dependencies

- QC-Py-27 (Production Deployment) : prerequis pour comprendre le workflow live
- QC-Py-09 (Order Types) : prerequis pour les ordres
- QC-Py-12 (Backtesting Analysis) : prerequis pour l'analyse de backtest

---

## 8. Limites et considerations

### Paper Trading n'est pas un backtest

- Le paper trading utilise les memes donnees que le live, mais simule les fills
- Il peut masquer des problemes de liquidite qui apparaitront en live
- La latence d'execution est differente de celle d'un backtest

### Limites specifiques Binance

- Pas de support des order updates (annuler + recreer)
- Pas de Futures support via QC (spot uniquement a ce jour)
- Testnet : les liquidites reflettent le mainnet mais avec moins de volume

### Limites specifiques IBKR

- Requiert TWS/Gateway en cours d'execution (pas 100% cloud)
- Redemarrage hebdomadaire obligatoire avec 2FA
- Paper TWS peut avoir des comportements legerement differents du live

### Ressources

- [QC Live Trading Docs](https://www.quantconnect.com/docs/v2/our-platform/live-trading)
- [QC Binance Brokerage](https://www.quantconnect.com/docs/v2/our-platform/live-trading/brokerages/binance)
- [QC IBKR Brokerage](https://www.quantconnect.com/docs/v2/our-platform/live-trading/brokerages/interactive-brokers)
- [QC Paper Trading](https://www.quantconnect.com/docs/v2/our-platform/live-trading/brokerages/quantconnect-paper-trading)
- [Binance Spot Test Network](https://testnet.binance.vision/)
- [Hands-On AI Trading](https://www.hands-on-ai-trading.com/) (Jared Broad, chapitre 27)
