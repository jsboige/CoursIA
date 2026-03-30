# Template Avance - Machine Learning sur BTC

## Description

Ce template implemente une strategie de trading algorithmique sur BTCUSDT utilisant un modele de Machine Learning (RandomForestClassifier) pour predire la direction du prix. Le modele est entraine directement dans l'algorithme et re-entraine mensuellement pour s'adapter aux conditions de marche.

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

## Persistance du modele (ObjectStore)

Le modele entraine est sauvegarde dans l'ObjectStore de QuantConnect via `pickle`. Cela permet de :

- **Reprendre** un backtest sans re-entrainer depuis zero
- **Deployer** un modele entraine en backtest vers le live trading
- **Sauvegarder automatiquement** a la fin du backtest et a chaque re-entrainement

## Concepts cles abordes

| Concept | Description |
|---------|-------------|
| **Feature engineering** | Transformation d'indicateurs techniques en features ML normalisees |
| **sklearn dans QC** | Utilisation de RandomForestClassifier dans l'environnement QuantConnect |
| **ObjectStore** | Persistance de modeles serialises entre executions |
| **Re-entrainement programme** | `Schedule.On` pour adapter le modele au regime de marche |
| **Warmup** | Periode d'initialisation des indicateurs avant le trading |

## Modifications suggerees

Pour aller plus loin, les etudiants peuvent :

1. **Ajouter des features** : ADX, ATR, Bollinger Bands, volume, volatilite historique
2. **Essayer d'autres modeles** : `XGBClassifier` (xgboost), `SVC` (sklearn), ou un ensemble de modeles
3. **Ajouter des positions short** : Vendre a decouvert quand la prediction est baissiere (necessite Margin account)
4. **Walk-forward optimization** : Entrainer sur les N derniers mois, tester sur le mois suivant, puis avancer la fenetre
5. **Gestion du risque** : Stop-loss, take-profit, taille de position variable selon la confiance du modele
6. **Decalage temporel** : Predire le label de J+1 avec les features de J (voir avertissement ci-dessous)

## Avertissements importants

**Overfitting** : Un modele trop complexe (trop d'arbres, profondeur illimitee) apprendra le bruit du marche plutot que les vrais signaux. La performance en backtest sera excellente mais catastrophique en live. Toujours valider sur des donnees hors echantillon.

**Lookahead bias** : Dans ce template simplifie, les features et le label sont calcules a partir des memes donnees du jour J. En production, il faut s'assurer que la prediction utilise uniquement des donnees disponibles AVANT la prise de decision. Decaler les labels d'un jour (predire J+1 avec les features de J) est la correction standard.

**Data snooping** : Tester de nombreuses combinaisons de features/hyperparametres sur le meme jeu de donnees augmente le risque de trouver des patterns aleatoires. Utiliser un jeu de validation separe.
