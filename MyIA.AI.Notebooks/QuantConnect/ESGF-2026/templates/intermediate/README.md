# Template Intermediaire - Strategie Momentum avec Alpha Framework

## Description

Ce template implemente une **strategie de momentum ranking** sur les actions du S&P 500.
L'algorithme selectionne les 100 plus gros composants du SPY par ponderation,
calcule leur momentum sur 90 jours, et investit de maniere egale dans ceux
dont le momentum est positif. Un trailing stop a 5 % protege chaque position.

**Periode de backtest** : Janvier 2021 - Decembre 2024
**Capital initial** : 100 000 USD (compte marge Interactive Brokers)
**Rebalancement** : Mensuel (premier jour de bourse du mois)

---

## Concepts de l'Alpha Framework

QuantConnect decompose une strategie en 4 modules independants,
ce qui permet de modifier un composant sans toucher aux autres :

| Module | Role | Classe utilisee |
|--------|------|-----------------|
| **AlphaModel** | Generer des signaux (Insights) haussiers/baissiers | `MomentumAlphaModel` (custom, MomentumPercent 90j) |
| **PortfolioConstructionModel** | Convertir les Insights en allocations cibles | `EqualWeightingPortfolioConstructionModel` |
| **RiskManagementModel** | Ajuster ou liquider des positions selon le risque | `TrailingStopRiskManagementModel(0.05)` |
| **ExecutionModel** | Envoyer les ordres au marche | `ImmediateExecutionModel` |

### Flux de donnees

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

## Modifications suggerees

Voici des pistes pour personnaliser et ameliorer la strategie :

### 1. Modifier la periode de lookback
Changer `lookback=90` dans `MomentumAlphaModel` (ex: 60, 120 ou 252 jours).
Un lookback plus court reagit plus vite mais genere plus de turnover.

### 2. Ajouter un filtre RSI
Combiner le momentum avec un filtre RSI pour eviter d'acheter des titres
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
pour concentrer la strategie sur certains secteurs (technologie, sante, etc.)
ou pour diversifier en limitant le nombre de titres par secteur.

### 4. Changer le modele de construction de portefeuille
Remplacer `EqualWeightingPortfolioConstructionModel` par :
- `InsightWeightingPortfolioConstructionModel` : pondere par la magnitude des Insights
- `MeanVarianceOptimizationPortfolioConstructionModel` : optimisation Markowitz
- `RiskParityPortfolioConstructionModel` : parite de risque (voir exemple Sector-Momentum)

### 5. Ajuster le trailing stop
Modifier le seuil de 5 % ou combiner avec `MaximumDrawdownPercentPerSecurity(0.10)`
pour une gestion du risque en couches.

---

## Concepts QC couverts par ce template

- **Universe Selection** : filtrage dynamique via `universe.etf()` et callback de filtre
- **Alpha Framework** : les 4 modules (Alpha, PCM, Risk, Execution)
- **Indicateurs integres** : `MomentumPercent` (MOMP) avec enregistrement automatique
- **Insights** : signaux avec direction, duree (`Expiry.END_OF_MONTH`) et confiance
- **ScheduledEvent** : declenchement periodique (`date_rules.month_start`)
- **Warm-up** : periode de chauffe pour initialiser les indicateurs avant le trading
- **BrokerageModel** : simulation realiste Interactive Brokers avec frais et marge

---

## Pour aller plus loin

- Consulter les notebooks `QC-Py-17` (Alpha Framework) et `QC-Py-19` (Risk Management)
- Etudier l'exemple `Sector-Momentum` pour le momentum dual avec parite de risque
- Etudier l'exemple `Trend-Following` pour combiner plusieurs indicateurs
- Documentation officielle : https://www.quantconnect.com/docs/v2/writing-algorithms/algorithm-framework
