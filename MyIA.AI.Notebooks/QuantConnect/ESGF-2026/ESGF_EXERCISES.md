# ESGF QC Trading - Exercices Progressifs

**Cours** : Trading Algorithmique avec QuantConnect
**Mastere** : ESGF Big Data & Data Science en Finance
**Prerequis** : Compte QuantConnect gratuit, notebooks QC-Py-01 a QC-Py-04 completes
**Code education** : `education2025` (sponsoring Jared Broad)

---

## Module 1 : Bases du Trading Algorithmique

### Exercice 1.1 : Mon premier backtest EMA Crossover

**Niveau** : Debutant | **Duree** : 45 min | **Ref** : QC-Py-02, EMA-Cross-Stocks

**Objectif** : Creer un algorithme de trading base sur le croisement de deux moyennes mobiles exponentielles (EMA).

**Enonce** :

1. Creer un nouveau projet Python dans QuantConnect Lab
2. Implementer un algorithme avec :
   - Actif : SPY (S&P 500 ETF)
   - Resolution : Daily
   - EMA rapide : 12 periodes
   - EMA lente : 26 periodes
   - Signal achat : EMA rapide croise au-dessus de l'EMA lente
   - Signal vente : EMA rapide croise en-dessous de l'EMA lente
3. Backtester sur la periode 2018-01-01 a 2024-12-31
4. Comparer avec un Buy & Hold sur SPY

**Questions** :

- Quel est le Sharpe ratio obtenu ? Est-il superieur a SPY Buy & Hold ?
- Combien de trades ont ete executes ? Quel est le win rate ?
- Modifier les periodes EMA (essayer 20/50 et 50/200). Quel impact sur les resultats ?

**Indices** :
- Utiliser `self.ema(symbol, period, Resolution.DAILY)` pour creer les indicateurs
- Le crossover se detecte en comparant `ema_fast.current.value` et `ema_slow.current.value`
- Ne pas oublier `self.set_warm_up(period_lente, Resolution.DAILY)`

---

### Exercice 1.2 : Portfolio All-Weather simplifie

**Niveau** : Debutant | **Duree** : 60 min | **Ref** : QC-Py-08, AllWeather

**Objectif** : Construire un portfolio multi-actifs inspire de Ray Dalio avec rebalancement periodique.

**Enonce** :

1. Creer un algorithme avec l'allocation "All-Weather" classique de Ray Dalio :
   - SPY (actions) : 30%
   - TLT (obligations long terme) : 40%
   - IEF (obligations intermediaires) : 15%
   - GLD (or) : 7.5%
   - DBC (matieres premieres) : 7.5%

   *Note : cette allocation classique differe de la version optimisee v5.0 dans `projects/AllWeather/` qui utilise SPY/IEF/GLD/XLP. L'exercice utilise intentionnellement l'allocation originale Dalio pour sa valeur pedagogique.*
2. Implementer un rebalancement trimestriel (tous les 3 mois)
3. Backtester sur 2015-01-01 a 2024-12-31
4. Calculer et afficher les metriques de performance

**Questions** :

- Quel est le MaxDD du portfolio ? Comment se compare-t-il a SPY seul pendant COVID (mars 2020) ?
- Le portfolio est-il plus stable que SPY en termes de volatilite annualisee ?
- Tester un rebalancement mensuel vs trimestriel. Quelle difference ?

**Indices** :
- Utiliser `self.schedule.on()` avec `self.date_rules.month_start()` pour le rebalancement
- `self.set_holdings(symbol, weight)` gere automatiquement les ordres

---

## Module 2 : Strategies Momentum

### Exercice 2.1 : Rotation sectorielle par momentum

**Niveau** : Intermediaire | **Duree** : 75 min | **Ref** : QC-Py-05, QC-Py-13, SectorMomentum

**Objectif** : Implementer une strategie de rotation sectorielle basee sur le momentum (rendement passe).

**Enonce** :

1. Definir un univers de 11 ETFs sectoriels :
   ```
   XLK, XLV, XLF, XLE, XLI, XLY, XLP, XLU, XLB, XLRE, XLC
   ```
2. A chaque rebalancement mensuel :
   - Calculer le rendement sur 3 mois (momentum lookback) de chaque ETF
   - Selectionner les 3 meilleurs (top-N)
   - Allouer en equal-weight parmi les selectionnes
   - Ajouter un filtre regime : SPY doit etre au-dessus de sa SMA200 pour investir
3. Si SPY < SMA200 : aller en cash (liquidation)
4. Backtester sur 2015-01-01 a 2024-12-31

**Questions** :

- Quel impact a le filtre SMA200 sur le MaxDD en 2022 (bear market) ?
- Tester top-2, top-3, top-5. Quel est le meilleur compromis rendement/risque ?
- Tester des lookback de 1, 3, 6, 12 mois. Lequel donne le meilleur Sharpe ?

**Indices** :
- `self.history(symbols, lookback_days, Resolution.DAILY)` pour les donnees historiques
- Calculer le rendement comme `(prix_actuel / prix_debut) - 1`
- Utiliser `sorted(zip(returns, symbols), reverse=True)[:top_n]` pour le classement

---

### Exercice 2.2 : Trend-following multi-sectoriel

**Niveau** : Intermediaire | **Duree** : 60 min | **Ref** : QC-Py-11, TrendStocksLite

**Objectif** : Implementer une strategie trend-following avec filtre de tendance double (SMA + EMA crossover).

**Enonce** :

1. Univers : 15 large-caps diversifiees (voir `projects/TrendStocksLite/main.py`)
2. Signal bullish par action :
   - Prix > SMA(200)
   - EMA(20) > EMA(50)
3. Allocation equal-weight parmi les actions bullish uniquement
4. Rebalancement hebdomadaire (chaque lundi)
5. Comparer avec la version tech-only (5 actions AAPL, MSFT, GOOGL, AMZN, NVDA)

**Questions** :

- Combien d'actions sont en "uptrend" en moyenne ? Ce nombre varie-t-il entre bull et bear market ?
- La diversification (15 vs 5 stocks) reduit-elle le drawdown ?
- Quel serait l'impact d'un ATR trailing stop sur chaque position ?

---

## Module 3 : Algorithm Framework QC

### Exercice 3.1 : Alpha Model personnalise

**Niveau** : Intermediaire-Avance | **Duree** : 90 min | **Ref** : QC-Py-13, QC-Py-14, EMA-Cross-Alpha

**Objectif** : Refactorer la strategie EMA crossover en utilisant l'Algorithm Framework QC (Alpha + PCM + Execution + Risk models).

**Enonce** :

1. Creer une classe `EmaCrossAlphaModel(AlphaModel)` :
   - `update(self, algorithm, data)` : generer des `Insight` Up/Down/Flat
   - Signal Up quand EMA(20) croise au-dessus d'EMA(50)
   - Signal Down quand EMA(20) croise en-dessous
   - Duree d'insight : `timedelta(days=5)` (valide 5 jours)
2. Utiliser les modeles standard QC :
   - `EqualWeightingPortfolioConstructionModel()` pour l'allocation
   - `ImmediateExecutionModel()` pour l'execution
   - `MaximumDrawdownPercentPerSecurity(0.10)` pour le risk
3. Univers : SPY, QQQ, IWM (3 ETFs indices)
4. Backtester sur 2020-01-01 a 2024-12-31

**Questions** :

- Quel avantage offre l'Architecture Framework par rapport a une strategie monolithique ?
- Remplacer `EqualWeightingPCM` par `MeanVarianceOptimizationPCM`. Impact ?
- Ajouter un deuxieme Alpha Model (ex: RSI mean-reversion). Comment QC combine-t-il deux alphas ?

**Indices** :
- Heriter de `AlphaModel` et implementer `update()` et `on_securities_changed()`
- Les Insights sont crees avec `Insight.price(symbol, timedelta, InsightDirection.Up)`
- Le Framework combine automatiquement les insights de multiples Alpha Models

---

## Module 4 : Strategies Avancees

### Exercice 4.1 : Strategie composite multi-alpha

**Niveau** : Avance | **Duree** : 120 min | **Ref** : QC-Py-15, Framework_Composite_EMATrend

**Objectif** : Construire une strategie composite combinant plusieurs Alpha Models avec un Portfolio Construction Model personnalise.

**Enonce** :

1. Creer 3 Alpha Models :
   - `TrendAlpha` : EMA crossover (signal directionnel)
   - `MomentumAlpha` : Rendement 3 mois > 0 (filtre momentum)
   - `RegimeAlpha` : SPY > SMA200 (filtre macro)
2. Creer un `CompositeWeightingPCM(PortfolioConstructionModel)` :
   - Assigner un poids a chaque alpha (ex: 40% trend, 40% momentum, 20% regime)
   - Combiner les insights en un signal unique [-1, +1] par actif
   - Normaliser les poids du portfolio pour que la somme = 1
3. Univers : 5 ETFs sectoriels (XLK, XLV, XLF, XLE, XLI)
4. Backtester sur 2015-01-01 a 2024-12-31 et comparer avec chaque alpha seul

**Questions** :

- La combinaison multi-alpha surpasse-t-elle chaque alpha individuel ?
- Quel jeu de poids (40/40/20 vs 60/20/20 vs 33/33/33) donne le meilleur Sharpe ?
- Ajouter une optimisation walk-forward des poids (re-optimiser chaque annee)

**Indices** :
- Heriter de `PortfolioConstructionModel` et implementer `create_targets()`
- `insight.direction` vaut `InsightDirection.Up`, `Down` ou `Flat`
- `PortfolioTarget(symbol, weight)` definit le poids cible

---

### Exercice 4.2 : Detection de regime et adaptation

**Niveau** : Avance | **Duree** : 90 min | **Ref** : RegimeSwitching, AdaptiveAssetAllocation

**Objectif** : Implementer un detecteur de regime de marche qui adapte l'allocation dynamiquement.

**Enonce** :

1. Definir 3 regimes de marche bases sur la volatilite realisee de SPY :
   - **Bull** : Vol 30j < 15% annualisee → allocation agressive (80% actions)
   - **Normal** : Vol 30j entre 15-25% → allocation equilibree (50% actions, 50% bonds)
   - **Bear** : Vol 30j > 25% → allocation defensive (20% actions, 80% bonds)
2. Actifs : SPY (actions), TLT (obligations)
3. Rebalancement : a chaque changement de regime (pas periodique)
4. Backtester sur 2015-01-01 a 2024-12-31

**Questions** :

- Combien de changements de regime se produisent sur la periode ?
- Le regime "Bear" detecte-t-il correctement COVID-2020 et l'inflation-2022 ?
- Tester des seuils de volatilite differents (12/20, 15/25, 18/30). Impact ?
- Ajouter un delai (confirmation 3 jours) avant de changer de regime. Effet sur les faux signaux ?

**Indices** :
- `self.history(spy, 30, Resolution.DAILY)['close'].pct_change().std() * np.sqrt(252)` pour la vol realisee
- Stocker le regime courant dans `self.current_regime` pour detecter les changements
- Ne rebalancer que quand `new_regime != self.current_regime`

---

## Evaluation

### Bareme suggere

| Module | Exercice | Points | Competence evaluee |
|--------|----------|--------|--------------------|
| M1 | 1.1 EMA Crossover | 15 | Fondamentaux QC, backtesting |
| M1 | 1.2 All-Weather | 15 | Multi-actifs, rebalancement |
| M2 | 2.1 Rotation sectorielle | 20 | Universe selection, momentum |
| M2 | 2.2 Trend-following | 15 | Indicateurs, filtres |
| M3 | 3.1 Alpha Model | 20 | Algorithm Framework |
| M4 | 4.1 ou 4.2 (au choix) | 15 | Strategie avancee |
| **Total** | | **100** | |

### Criteres de notation

- **Code fonctionnel** (40%) : Le backtest s'execute sans erreur
- **Analyse des resultats** (30%) : Reponses aux questions, interpretation des metriques
- **Exploration** (20%) : Tests de variantes, optimisation des parametres
- **Qualite du code** (10%) : Lisibilite, commentaires, structure

---

## Ressources

- **Notebooks de reference** : QC-Py-01 a QC-Py-15 (phases 1-4 du cours)
- **Projets exemples** : `projects/` (56 projets avec research notebooks)
- **Templates** : `ESGF-2026/templates/` (starter, intermediate, advanced)
- **Documentation QC** : https://www.quantconnect.com/docs
- **Code education** : `education2025` pour acces Team tier
