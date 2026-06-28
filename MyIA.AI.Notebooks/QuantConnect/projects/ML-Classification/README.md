# ML-Classification

Stratégie de classification ML utilisant un modèle pré-entraîné chargé depuis le QuantConnect ObjectStore.

## Prérequis

Cette stratégie **nécessite un modèle pré-entraîné** stocké dans le QC ObjectStore. Elle ne peut pas s'exécuter comme un backtest autonome sans l'artefact du modèle.

### Étapes de configuration

1. Ouvrir l'environnement de recherche QC
2. Exécuter `research_classification.ipynb` pour entraîner le modèle
3. Sauvegarder le modèle dans l'ObjectStore via `qb.object_store.save_bytes()`
4. Puis lancer cet algorithme en backtest

### Clés ObjectStore

- `classification_model` — classifieur sklearn sérialisé (format joblib)
- `classification_config` — configuration JSON du modèle (colonnes de features, seuils)

## Logique de stratégie

- Prédit la direction du marché (hausse/baisse) à T+1 via un classifieur RandomForest
- Prend position long lorsque la probabilité prédite > 0.55
- Liquide la position lorsque la probabilité prédite < 0.45
- Trade SPY en quotidien

## Conformité PEP8

Toutes les méthodes personnalisées utilisent le naming `snake_case` selon les conventions PEP8. Les méthodes du QC Framework (`Initialize`, `OnData`, etc.) conservent leur naming PascalCase comme l'exige l'API.
