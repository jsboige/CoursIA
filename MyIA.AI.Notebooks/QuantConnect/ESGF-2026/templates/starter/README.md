# Template Starter : Croisement EMA sur BTCUSDT

## Description

Ce template implemente une strategie de **croisement de moyennes mobiles exponentielles (EMA)** sur le Bitcoin (BTCUSDT) via Binance.

**Principe :**
- Quand l'EMA rapide (12 periodes) passe **au-dessus** de l'EMA lente (26 periodes), c'est un **golden cross** : on achete.
- Quand l'EMA rapide passe **en dessous** de l'EMA lente, c'est un **death cross** : on vend.

Le backtest couvre la periode du 1er janvier 2023 au 31 decembre 2024, avec un capital initial de 10 000 USDT et des donnees horaires.

## Utilisation

1. Connectez-vous a [QuantConnect](https://www.quantconnect.com/)
2. Creez un nouveau projet Python dans l'organisation **Trading Firm ESGF**
3. Copiez le contenu de `main.py` dans le fichier principal du projet
4. Lancez un backtest pour observer les resultats
5. Analysez les metriques : Sharpe Ratio, drawdown, nombre de trades

## Concepts QC couverts

| Concept | Description | Ligne(s) |
|---------|-------------|----------|
| `AddCrypto` | Ajouter un actif crypto avec marche et resolution | `Initialize` |
| `Resolution.Hour` | Granularite des donnees (ici bougies horaires) | `Initialize` |
| `self.EMA(...)` | Creer un indicateur Moyenne Mobile Exponentielle | `Initialize` |
| `SetWarmUp` | Prechauffer les indicateurs avant de trader | `Initialize` |
| `SetHoldings` | Allouer un pourcentage du portefeuille a un actif | `OnData` |
| `Liquidate` | Vendre toute la position sur un actif | `OnData` |
| `Portfolio[symbol].Invested` | Verifier si on detient une position | `OnData` |
| `SetBenchmark` | Definir un indice de reference pour comparer la performance | `Initialize` |
| `OnOrderEvent` | Recevoir les notifications d'execution des ordres | `OnOrderEvent` |

## Modifications suggerees

Voici des pistes pour ameliorer et personnaliser cette strategie :

### Niveau 1 - Parametrage
- Changer les periodes EMA : essayer (5, 20), (20, 50) ou (50, 200)
- Modifier la resolution : `Resolution.Daily` au lieu de `Resolution.Hour`
- Tester un autre actif : remplacer `"BTCUSDT"` par `"ETHUSDT"` ou `"SOLUSDT"`

### Niveau 2 - Filtres supplementaires
- Ajouter un **filtre RSI** : ne pas acheter si RSI > 70 (suracheté), ne pas vendre si RSI < 30 (survendu)
  ```python
  self.rsi = self.RSI(self.btc, 14, Resolution.Hour)
  # Dans OnData : ajouter "and self.rsi.Current.Value < 70" a la condition d'achat
  ```
- Ajouter un **filtre de volume** : ne trader que si le volume est superieur a la moyenne
- Implementer un **stop-loss** a -5% pour limiter les pertes

### Niveau 3 - Gestion de position
- Utiliser `SetHoldings(self.btc, 0.5)` pour n'investir que 50% du capital
- Trader sur **plusieurs cryptos** en meme temps (BTC + ETH + SOL)
- Ajouter un **trailing stop** qui suit le prix a la hausse

### Niveau 4 - Evaluation
- Comparer les resultats avec differents parametres dans un tableau
- Analyser le **Sharpe Ratio** et le **Maximum Drawdown** de chaque variante
- Expliquer pourquoi certains parametres fonctionnent mieux que d'autres
