# Template Intermédiaire - Stratégie Momentum avec Alpha Framework

## Description

Ce template implémente une **stratégie de momentum ranking** sur les actions du S&P 500.
L'algorithme sélectionne les 100 plus gros composants du SPY par pondération,
calcule leur momentum sur 90 jours, et investit de maniere égale dans ceux
dont le momentum est positif. Un trailing stop à 5 % protège chaque position.

**Période de backtest** : Janvier 2021 - Décembre 2024
**Capital initial** : 100 000 USD (compte marge Interactive Brokers)
**Rebalancement** : Mensuel (premier jour de bourse du mois)

---

## Concepts de l'Alpha Framework

QuantConnect décompose une stratégie en 4 modules indépendants,
ce qui permet de modifier un composant sans toucher aux autres :

| Module | Role | Classe utilisée |
|--------|------|-----------------|
| **AlphaModel** | Generer des signaux (Insights) haussiers/baissiers | `MomentumAlphaModel` (custom, MomentumPercent 90j) |
| **PortfolioConstructionModel** | Convertir les Insights en allocations cibles | `EqualWeightingPortfolioConstructionModel` |
| **RiskManagementModel** | Ajuster ou liquider des positions selon le risque | `TrailingStopRiskManagementModel(0.05)` |
| **ExecutionModel** | Envoyer les ordres au marché | `ImmediateExecutionModel` |

### Flux de données

```
Donnees de marche
    |
    v
AlphaModel.update()  -->  Liste d'Insights (direction, duree, magnitude)
    |
    v
PortfolioConstructionModel  -->  Allocations cibles (% du portefeuille)
    |
    v
RiskManagementModel  -->  Ajustements (trailing stop, max drawdown)
    |
    v
ExecutionModel  -->  Ordres envoyes au courtier
```

---

## Fichiers

| Fichier | Description |
|---------|-------------|
| `main.py` | Algorithme complet : classe `MomentumAlphaModel` + `IntermediateMomentumAlgorithm` |

---

## Modifications suggérées

Voici des pistes pour personnaliser et améliorer la stratégie :

### 1. Modifier la période de lookback
Changer `lookback=90` dans `MomentumAlphaModel` (ex: 60, 120 ou 252 jours).
Un lookback plus court réagit plus vite mais génère plus de turnover.

### 2. Ajouter un filtre RSI
Combiner le momentum avec un filtre RSI pour éviter d'acheter des titres
en zone de surachat :

```python
# Dans on_securities_changed :
self.rsi[sym] = algorithm.RSI(sym, 14, Resolution.DAILY)

# Dans update, ajouter la condition :
if indicator.current.value > 0 and self.rsi[symbol].current.value < 70:
    insights.append(...)
```

### 3. Filtrage sectoriel
Utiliser `security.Fundamentals.AssetClassification.MorningstarSectorCode`
pour concentrer la stratégie sur certains secteurs (technologie, santé, etc.)
ou pour diversifier en limitant le nombre de titres par secteur.

### 4. Changer le modèle de construction de portefeuille
Remplacer `EqualWeightingPortfolioConstructionModel` par :
- `InsightWeightingPortfolioConstructionModel` : pondère par la magnitude des Insights
- `MeanVarianceOptimizationPortfolioConstructionModel` : optimisation Markowitz
- `RiskParityPortfolioConstructionModel` : parité de risque (voir exemple Sector-Momentum)

### 5. Ajuster le trailing stop
Modifier le seuil de 5 % ou combiner avec `MaximumDrawdownPercentPerSecurity(0.10)`
pour une gestion du risque en couches.

---

## Concepts QC couverts par ce template

- **Universe Selection** : filtrage dynamique via `universe.etf()` et callback de filtre
- **Alpha Framework** : les 4 modules (Alpha, PCM, Risk, Exécution)
- **Indicateurs intégrés** : `MomentumPercent` (MOMP) avec enregistrement automatique
- **Insights** : signaux avec direction, durée (`Expiry.END_OF_MONTH`) et confiance
- **ScheduledEvent** : déclenchement périodique (`date_rules.month_start`)
- **Warm-up** : période de chauffe pour initialiser les indicateurs avant le trading
- **BrokerageModel** : simulation réaliste Interactive Brokers avec frais et marge

---

## Pour aller plus loin

- Consulter les notebooks `QC-Py-17` (Alpha Framework) et `QC-Py-19` (Risk Management)
- Etudier l'exemple `Sector-Momentum` pour le momentum dual avec parité de risque
- Etudier l'exemple `Trend-Following` pour combiner plusieurs indicateurs
- Documentation officielle : https://www.quantconnect.com/docs/v2/writing-algorithms/algorithm-framework
