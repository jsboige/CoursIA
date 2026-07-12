# Template Starter : Croisement EMA sur BTCUSDT

## Description

Ce template implémente une stratégie de **croisement de moyennes mobiles exponentielles (EMA)** sur le Bitcoin (BTCUSDT) via Binance.

**Principe :**
- Quand l'EMA rapide (12 périodes) passe **au-dessus** de l'EMA lente (26 périodes), c'est un **golden cross** : on achète.
- Quand l'EMA rapide passe **en dessous** de l'EMA lente, c'est un **death cross** : on vend.

Le backtest couvre la période du 1er janvier 2023 au 31 décembre 2024, avec un capital initial de 10 000 USDT et des données horaires.

## Utilisation

1. Connectez-vous à [QuantConnect](https://www.quantconnect.com/)
2. Create a new Python project in your course organization
3. Copiez le contenu de `main.py` dans le fichier principal du projet
4. Lancez un backtest pour observer les résultats
5. Analysez les métriques : Sharpe Ratio, drawdown, nombre de trades

## Concepts QC couverts

| Concept | Description | Ligne(s) |
|---------|-------------|----------|
| `AddCrypto` | Ajouter un actif crypto avec marché et résolution | `Initialize` |
| `Resolution.Hour` | Granularité des données (ici bougies horaires) | `Initialize` |
| `self.EMA(...)` | Créer un indicateur Moyenne Mobile Exponentielle | `Initialize` |
| `SetWarmUp` | Préchauffer les indicateurs avant de trader | `Initialize` |
| `SetHoldings` | Allouer un pourcentage du portefeuille à un actif | `OnData` |
| `Liquidate` | Vendre toute la position sur un actif | `OnData` |
| `Portfolio[symbol].Invested` | Vérifier si on détient une position | `OnData` |
| `SetBenchmark` | Définir un indice de référence pour comparer la performance | `Initialize` |
| `OnOrderEvent` | Recevoir les notifications d'exécution des ordres | `OnOrderEvent` |

## Modifications suggérées

Voici des pistes pour améliorer et personnaliser cette stratégie :

### Niveau 1 - Paramétrage
- Changer les périodes EMA : essayer (5, 20), (20, 50) ou (50, 200)
- Modifier la résolution : `Resolution.Daily` au lieu de `Resolution.Hour`
- Tester un autre actif : remplacer `"BTCUSDT"` par `"ETHUSDT"` ou `"SOLUSDT"`

### Niveau 2 - Filtres supplementaires
- Ajouter un **filtre RSI** : ne pas acheter si RSI > 70 (suracheté), ne pas vendre si RSI < 30 (survendu)
  ```python
  self.rsi = self.RSI(self.btc, 14, Resolution.Hour)
  # Dans OnData : ajouter "and self.rsi.Current.Value < 70" a la condition d'achat
  ```
- Ajouter un **filtre de volume** : ne trader que si le volume est supérieur à la moyenne
- Implémenter un **stop-loss** à -5% pour limiter les pertes

### Niveau 3 - Gestion de position
- Utiliser `SetHoldings(self.btc, 0.5)` pour n'investir que 50% du capital
- Trader sur **plusieurs cryptos** en même temps (BTC + ETH + SOL)
- Ajouter un **trailing stop** qui suit le prix à la hausse

### Niveau 4 - Evaluation
- Comparer les résultats avec différents paramètres dans un tableau
- Analyser le **Sharpe Ratio** et le **Maximum Drawdown** de chaque variante
- Expliquer pourquoi certains paramètres fonctionnent mieux que d'autres
