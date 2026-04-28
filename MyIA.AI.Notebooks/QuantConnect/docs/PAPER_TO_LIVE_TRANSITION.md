# Paper to Live Transition Guide

Ce document decrit les prerequis et etapes pour passer du paper trading au live trading sur QuantConnect. Il s'agit d'un guide pedagogique, **pas d'une recommandation d'investissement**.

---

## 1. Checklist pre-live

Avant de passer en live, **toutes** les conditions suivantes doivent etre remplies :

### Performance
- [ ] Sharpe Ratio > 0.5 sur le backtest (minimum 3 ans)
- [ ] Max Drawdown acceptable (< 30% pour du momentum, < 20% pour du mean-reversion)
- [ ] Paper trading profitable sur >= 2 semaines avec comportement coherent vs backtest
- [ ] Win rate coherent entre backtest et paper trading (+/- 5%)

### Technique
- [ ] Aucune erreur dans les logs live pendant la periode paper
- [ ] Ordres executes correctement (pas de rejects, pas de timeouts)
- [ ] Fills a des prix realistes (pas de fills impossibles)
- [ ] Algorithme stable (pas de crash, pas de memory leak)

### Infrastructure
- [ ] Brokerage credentials valides et actifs
- [ ] Node live suffisamment dimensionne (L-MICRO pour 1-10 actifs)
- [ ] TWS/Gateway operationnel (IBKR uniquement)
- [ ] Monitoring en place (alerts sur erreurs, drawdown, deconnexion)

---

## 2. Ecarts backtest -> paper -> live

### Sources d'ecart cumulatives

```
Backtest (historique)
  -> Paper Trading (donnees reelles, fills simules)
    -> Live Trading (donnees reelles, fills reels)
```

| Source | Backtest | Paper | Live |
|--------|:--------:|:-----:|:----:|
| Slippage | Modelise | Aucun | Reel |
| Latence | N/A | Faible | Variable |
| Liquidite | Illimitee | Simulee | Reelle |
| Market impact | Aucun | Aucun | Proportionnel |
| Commissions | Simulees | Simulees | Reelles |
| Connection | N/A | QC cloud | QC + Broker |

### Red flags en paper trading

Si vous observez l'un de ces comportements en paper trading, **ne pas passer en live** :

- Fills systematiquement meilleurs que le backtest
- Nombre de trades significativement different
- Drawdown live > 2x le drawdown backtest
- Erreurs de connection regulieres
- Algorithme qui ne trade pas quand il devrait

---

## 3. Transition Binance (Crypto)

### Paper -> Live

| Parametre | Paper | Live |
|-----------|-------|------|
| Environnement | `paper` (Testnet) | `live` |
| Credentials | Testnet API key | API key reelle |
| Capital | Fictif (10 000 USD) | Reel |
| Slippage | Aucun | Variable selon liquidite BTC/ETH |

### Configuration live

```python
brokerage = {
    "id": "BinanceBrokerage",
    "binance-api-key": "<real-api-key>",
    "binance-api-secret": "<real-api-secret>",
    "binance-exchange-name": "Binance",
    "binance-use-testnet": "live"  # <- changer ici
}
```

### Risques specifiques crypto

- **Volatilite** : les crypto peuvent bouger de 10-20% en une journee
- **Liquidite** : les petits altcoins peuvent avoir des spreads enormes
- **Hacks** : risque de piratage du compte (utiliser 2FA, IP whitelist)
- **Regulation** : le cadre legal evolue rapidement

---

## 4. Transition IBKR (Equities)

### Paper -> Live

| Parametre | Paper | Live |
|-----------|-------|------|
| Port TWS | 7497 | 7496 |
| Account | DU... (paper) | U... (live) |
| Slippage | Minimal | Reel (surtout small caps) |
| 2FA | Optionnel | Obligatoire |

### Configuration live

```python
brokerage = {
    "id": "InteractiveBrokersBrokerage",
    "ib-user-name": "<username>",
    "ib-account": "U12345",  # <- compte reel (pas DU...)
    "ib-password": "<password>",
    "ib-weekly-restart-utc-time": "04:00:00"
}
```

### Risques specifiques equities

- **Gap risk** : le marche ouvre avec un gap par rapport a la cloture precedente
- **Short selling** : les actions peuvent etre "hard to borrow"
- **Regulation T** : regles de marge specifiques (pattern day trader aux US)
- **Corporate actions** : splits, dividendes, mergers affectent les positions

---

## 5. Risk Management en Live

### Position sizing

La reggle fondamentale : **ne jamais risquer plus de 1-2% du capital par trade**.

```python
# Calcul de la taille de position
capital = 100000  # USD
risk_per_trade = 0.02  # 2%
stop_loss_distance = 0.05  # 5% sous le prix d'entree

position_size = (capital * risk_per_trade) / stop_loss_distance
# = (100000 * 0.02) / 0.05 = 40 000 USD
# Soit 40% du capital -> trop concentre, ajuster
```

### Stop-loss obligatoire

Chaque position live doit avoir un stop-loss. Options :

| Methode | Description | Avantage |
|---------|-------------|----------|
| Fixe (%) | -5% du prix d'entree | Simple |
| ATR-based | k * ATR(14) sous l'entree | S'adapte a la volatilite |
| Trailing | Monte avec le prix | Protege les gains |
| Time-based | Sortie apres N jours | Evite les positions stagnantes |

### Diversification minimum

- Au moins 3 positions simultanees
- Pas plus de 20% dans un seul actif
- Preferer des actifs non-correles (ex: equity + crypto, pas BTC + ETH uniquement)

---

## 6. Monitoring en Live

### Metriques quotidiennes

| Metrique | Alerte si... |
|----------|-------------|
| Portfolio value | < 95% du capital initial |
| Drawdown | > 10% |
| Daily loss | > 3% |
| Open positions | > 20 ou < 0 (incoherence) |
| Errors in logs | > 0 erreurs critiques |

### Arret d'urgence

Si une anomalie est detectee :

1. **Stop live algorithm** via MCP QC : `stop_live_algorithm(projectId=...)`
2. **Liquidier les positions** si necessaire : `liquidate_live_algorithm(projectId=...)`
3. **Analyser les logs** : `read_live_logs(projectId=..., algorithmId=..., startLine=0, endLine=250)`
4. **Corriger l'algorithme** et re-backtester avant de re-deployer

---

## 7. Avertissement pedagogique

Ce document est un **guide pedagogique**, pas un conseil financier. Le trading algorithmique en live comporte des risques reels de perte de capital.

> "Past performance is not indicative of future results."

Les strategies presentees dans les notebooks QC-Py-40 et QC-Py-41 sont des exemples educatifs. Leur performance en backtest ou paper trading ne garantit pas de performance en live.

### Ressources
- [QC Live Trading Docs](https://www.quantconnect.com/docs/v2/our-platform/live-trading)
- [QC Risk Management](https://www.quantconnect.com/docs/v2/writing-algorithms/risk-management)
- [Hands-On AI Trading](https://www.hands-on-ai-trading.com/) (Jared Broad, chapitre 28)
