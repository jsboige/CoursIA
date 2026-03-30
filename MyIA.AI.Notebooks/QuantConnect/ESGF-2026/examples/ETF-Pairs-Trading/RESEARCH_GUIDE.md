# ETF Pairs Trading - Research Guide

## Objectif

Diagnostiquer et corriger le **Sharpe négatif (-0.759)** de la stratégie ETF-Pairs-Trading.

## Stratégie actuelle

- **Univers** : Sector ETFs (XLB, XLE, XLF, XLI, XLK, XLP, XLU, XLV, XLY)
- **Résolution** : Hourly
- **Période** : 2020-01-01 → 2024-03-01
- **Logique** : Statistical arbitrage sur paires cointégrées
  - Sélection hebdomadaire des 3 meilleures paires (p-value < 0.05)
  - Entrée à z-score ± 1.5
  - **Sortie à z-score ± 0.5** ← PROBLÈME IDENTIFIÉ
  - Stop-loss trailing 8% par jambe ← BRISE LA NEUTRALITÉ
  - Insight duration fixe 6h ← INADAPTÉ

## Problèmes identifiés

### 1. Sortie prématurée (CRITIQUE)

**Code actuel** :
```python
if abs(z_score) < 0.5:  # Sortie trop tôt !
    return Insight.Price(...)
```

**Problème** : On sort à z=0.5 au lieu de z=0.0 (mean). Cela signifie qu'on **quitte la position avant que la convergence attendue ne se réalise**.

**Impact estimé** : +0.3 à +0.5 points de Sharpe

**Fix** :
```python
if abs(z_score) < 0.0:  # Attendre le retour à la moyenne
    return Insight.Price(...)
```

### 2. Stop-loss per-leg (CRITIQUE)

**Code actuel** :
```python
self.SetRiskManagement(TrailingStopRiskManagementModel(0.08))
```

**Problème** : Le stop s'applique à **chaque jambe indépendamment**. Si XLI baisse de 8%, on coupe la position XLI mais on garde XLK → on n'est plus market-neutral !

**Impact** : Transforme une stratégie pairs-trading en stratégie directionnelle non intentionnelle.

**Fix** : Implémenter un stop au niveau du **spread** (ex: 2.5σ du spread).

### 3. Half-life ignoré (ÉLEVÉ)

**Problème** : L'insight duration est fixe (6h) alors que le half-life de mean-reversion peut varier de 5 jours à 90 jours selon la paire.

**Impact** : On peut sortir trop tôt (HL=30j) ou trop tard (HL=3j).

**Fix** : Calculer le half-life de chaque paire et adapter :
```python
insight_duration = timedelta(days=min(2 * half_life, 30))
```

### 4. Pas de filtre de stabilité (MODÉRÉ)

**Problème** : Une paire peut être cointégrée sur le lookback (1638h = 68 jours) mais perdre cette propriété pendant la position.

**Impact** : Positions qui divergent au lieu de converger.

**Fix** : Filtrer les paires avec half-life > 30 jours (trop lent pour hourly).

## Plan de correction

### Phase 1 : Corrections critiques (priorité 1)

1. **Corriger z-exit** : `0.5 → 0.0` dans `alpha.py`
2. **Remplacer stop per-leg** : Implémenter spread-level stop dans `risk.py`

### Phase 2 : Améliorations (priorité 2)

3. **Calculer half-life** : Ajouter fonction de calcul dans `universe.py`
4. **Filtre half-life** : Exclure paires avec HL > 30 jours
5. **Insight duration adaptatif** : Baser sur 2× half-life

### Phase 3 : Extension temporelle (priorité 3)

6. **Étendre période** : 2020-2024 → 2015-2026
   - Objectif : Tester sur différents régimes (sideways 2015-2019, volatil 2020-2021)

## Notebooks de recherche

### Option 1 : Notebook Jupyter (recherche exploratoire)

**Fichier** : `research_robustness.ipynb`

**Utilisation** :
1. Ouvrir dans QuantConnect Research Lab
2. Exécuter cellule par cellule
3. Analyser les résultats de chaque hypothèse

**Avantages** : Visualisations, exploration interactive

### Option 2 : Script Python (analyse rapide)

**Fichier** : `research_robustness_standalone.py`

**Utilisation** :
```python
# Dans QC Research
from research_robustness_standalone import run_diagnostic_analysis

qb = QuantBook()
results = run_diagnostic_analysis(qb)
```

**Avantages** : Rapport JSON automatique, plus rapide

## Hypothèses à valider

| ID | Hypothèse | Métrique | Statut attendu |
|----|-----------|----------|----------------|
| H1 | z-exit 0.5→0.0 améliore Sharpe >0.3 | Δ Sharpe | CONFIRMÉE |
| H2 | Paires restent cointégrées <50% du temps | % stabilité | CONFIRMÉE |
| H3 | Half-life médian > 10 jours | HL médian | CONFIRMÉE |
| H4 | Filtre HL<30j élimine 30%+ des paires | % filtré | À TESTER |
| H5 | Walk-forward Sharpe < 0.3 | Sharpe WF | À TESTER |

## Métriques de succès

- **Sharpe target** : > 0.3 (au minimum neutre, idéalement 0.5+)
- **Max Drawdown** : < 15%
- **Win rate** : > 45%
- **Stabilité walk-forward** : σ(Sharpe) < 0.5

## Prochaines étapes

1. ✅ Créer notebooks de recherche
2. ⏳ Exécuter dans QC Research Lab
3. ⏳ Analyser résultats et valider hypothèses
4. ⏳ Implémenter corrections dans main.py, alpha.py, risk.py
5. ⏳ Compiler sur cloud
6. ⏳ Backtester via UI web
7. ⏳ Vérifier Sharpe > 0.3 avant live

## Références

- **Projet QC** : ETF-Pairs-Trading (ID: 19865767)
- **Org** : ESGF (94aa4bcb...)
- **Dossier local** : `ESGF-2026/examples/ETF-Pairs-Trading/`

## Notes pédagogiques

### Pourquoi le pairs trading échoue-t-il souvent ?

1. **Cointégration non-stationnaire** : Deux ETFs cointégrés hier ne le sont pas forcément aujourd'hui
2. **Coûts de transaction** : Sur-trading (HL court) peut tuer la stratégie
3. **Spread divergence** : La paire peut "casser" pendant qu'on est en position
4. **Mauvais timing** : Sortie avant convergence = laisser le profit sur la table

### Leçons clés

- **Le z-score = 0 est la vraie cible** : C'est la définition du retour à la moyenne
- **La neutralité est fragile** : Un stop per-leg brise instantanément l'équilibre
- **Le half-life est un signal** : Plus il est court, plus la mean-reversion est fiable
- **Walk-forward est crucial** : Le pairs trading overfit facilement sur les paramètres
