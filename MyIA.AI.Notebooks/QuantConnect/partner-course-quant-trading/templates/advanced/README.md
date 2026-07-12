# Template Avancé - Machine Learning sur BTC

## Description

Ce template implémente une stratégie de trading algorithmique sur BTCUSDT utilisant un modèle de Machine Learning (RandomForestClassifier) pour prédire la direction du prix. Le modèle est entraîné directement dans l'algorithme et ré-entraîne mensuellement pour s'adapter aux conditions de marché.

## Pipeline ML

```
Donnees de marche (BTCUSDT Daily)
        |
        v
Feature Engineering
  - SMA(20) ratio : prix / SMA (tendance)
  - RSI(14) normalise : 0-1 (momentum)
  - EMA(10)/EMA(50) ratio : croisement (signal)
  - DailyReturn : rendement journalier (volatilite)
        |
        v
Entrainement (RandomForestClassifier)
  - 100 arbres, profondeur max 5
  - Fenetre glissante de 252 jours (~1 an)
  - Re-entrainement automatique chaque mois
        |
        v
Prediction quotidienne
  - 1 = hausse prevue -> Position longue (100%)
  - 0 = baisse prevue -> Cash (flat)
        |
        v
Execution sur Binance Cash
```

## Persistance du modèle (ObjectStore)

Le modèle entraîné est sauvegardé dans l'ObjectStore de QuantConnect via `pickle`. Cela permet de :

- **Reprendre** un backtest sans ré-entraîner depuis zéro
- **Deployer** un modèle entraîné en backtest vers le live trading
- **Sauvegarder automatiquement** à la fin du backtest et à chaque ré-entraînement

## Concepts clés abordés

| Concept | Description |
|---------|-------------|
| **Feature engineering** | Transformation d'indicateurs techniques en features ML normalisées |
| **sklearn dans QC** | Utilisation de RandomForestClassifier dans l'environnement QuantConnect |
| **ObjectStore** | Persistance de modèles sérialisés entre exécutions |
| **Ré-entraînement programmé** | `Schedule.On` pour adapter le modèle au régime de marché |
| **Warmup** | Période d'initialisation des indicateurs avant le trading |

## Modifications suggérées

Pour aller plus loin, les étudiants peuvent :

1. **Ajouter des features** : ADX, ATR, Bollinger Bands, volume, volatilité historique
2. **Essayer d'autres modèles** : `XGBClassifier` (xgboost), `SVC` (sklearn), ou un ensemble de modèles
3. **Ajouter des positions short** : Vendre à découvert quand la prédiction est baissière (nécessite Margin account)
4. **Walk-forward optimization** : Entraîner sur les N derniers mois, tester sur le mois suivant, puis avancer la fenêtre
5. **Gestion du risque** : Stop-loss, take-profit, taille de position variable selon la confiance du modèle
6. **Décalage temporel** : Predire le label de J+1 avec les features de J (voir avertissement ci-dessous)

## Avertissements importants

**Overfitting** : Un modèle trop complexe (trop d'arbres, profondeur illimitée) apprendra le bruit du marché plutôt que les vrais signaux. La performance en backtest sera excellente mais catastrophique en live. Toujours valider sur des données hors échantillon.

**Lookahead bias** : Dans ce template simplifié, les features et le label sont calculés à partir des mêmes données du jour J. En production, il faut s'assurer que la prédiction utilise uniquement des données disponibles AVANT la prise de decision. Décaler les labels d'un jour (prédire J+1 avec les features de J) est la correction standard.

**Data snooping** : Tester de nombreuses combinaisons de features/hyperparamètres sur le même jeu de données augmente le risque de trouver des patterns aléatoires. Utiliser un jeu de validation séparé.
