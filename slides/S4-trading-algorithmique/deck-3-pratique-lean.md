---
theme: ../theme-ia101
title: "S4 Trading Algorithmique - Partie 3 : Pratique Lean/QuantConnect"
info: Cours Intelligence Artificielle - Pratique avec Lean/QuantConnect
paginate: true
drawings:
  persist: false
transition: slide-left
mdc: true
layout: cover
---

# Pratique avec Lean/QuantConnect

Intelligence Artificielle -- S4 -- Partie 3

**De la theorie a la pratique : codez votre premier algorithme de trading**

- Setup de l'environnement QC Cloud
- Structure d'un algorithme Python (evenementiel)
- Framework Alpha haut niveau (5 composants modulaires)
- 67 projets prets a backtester et a modifier

---

# Du Concept au Code : le Workflow du Trader Quant

- **1. Hypothese** : Identifier une anomalie ou un pattern exploitable
  - "Les actions qui baissent de plus de 5% en 3 jours tendent a rebondir"
<div v-click="1">

- **2. Recherche** : Valider l'hypothese sur les donnees (notebooks Jupyter)
  - Statistiques, visualisations, tests de significativite
</div>
<div v-click="2">

- **3. Implementation** : Coder la strategie dans Lean (Python)
  - Initialize, OnData, gestion des ordres
</div>
<div v-click="3">

- **4. Backtest** : Simuler sur donnees historiques
  - Sharpe, drawdown, nombre de trades, couts
</div>
<div v-click="4">

- **5. Paper Trading** : Tester en temps reel sans capital
  - Derniere validation avant engagement de capital
</div>
<div v-click="5">

- **6. Live Trading** : Deployer avec capital reel, monitorer en continu

</div>

> Ref: *Hands-On AI Trading* Ch2 "Research Process" p.25-26, "Coding Process" p.28

---

# Lean/QuantConnect

- **Qu'est-ce que c'est?**
  - Plateforme de trading algorithmique open-source
<div v-click="1">

- **Langage de Programmation**
  - Python (notre focus dans ce cours)

</div>
<div v-click="2">

- **Fonctionnalites Principales**
  - Notebooks d'analyse, Backtesting, optimisation, paper et live trading
</div>
<div v-click="3">

- **Data Library**
  - Donnees historiques de plusieurs marches (actions, forex, crypto, options, futures)
</div>
<div v-click="4">

- **Ressources du depot**
  - 28 notebooks progressifs + 67 projets prets a backtester
  - Communaute, forums, tutoriels, documentation

</div>

> Notebook: QC-Py-01-Setup.ipynb

---

# Installation de l'Environnement (1/2)

- **QuantConnect Cloud** (recommande pour demarrer)
  - Creer un compte sur quantconnect.com
  - Organisations : regroupez vos projets et collaborateurs
  - Noeuds de ressources : backtesting et live trading

<div v-click="1">

- **Lean-cli + VS Code** (pour le developpement local)
  - Synchronisation bidirectionnelle avec le Cloud
  - Execution locale via containers Docker
</div>
<div v-click="2">

- **Pourquoi le Cloud d'abord ?**
  - Zero configuration, donnees incluses
  - Backtests rapides sans installation locale
  - Creez un compte gratuit sur quantconnect.com

</div>

> Ref: *Hands-On AI Trading* Ch2 "Testing and Debugging Tools" p.27-28

---

# Installation de l'Environnement (2/2)

- **VS Code + Extension QuantConnect**
  - Extensions recommandees : Python, Git Extension Pack, Python Extension Pack, QuantConnect
<div v-click="1">

- **Configuration minimale**
  - Python 3.8+ installe localement
  - Compte QuantConnect actif avec token API
</div>
<div v-click="2">

- **Extension QuantConnect pour VS Code**
  - Synchronisation des projets Cloud
  - Lancement de backtests depuis l'editeur
  - Autocompletion sur l'API QC

</div>

---

# Mise en Route Lean-cli / VS Code

- **Installation pip**
  - `pip install --upgrade lean`
  - `lean --version`
<div v-click="1">

- **Sur QuantConnect**
  - My Account -- Request Token Information
  - Creez un compte gratuit sur quantconnect.com

</div>
<div v-click="2">

- **Lean init**
  - Choix de l'"Organisation"
</div>
<div v-click="3">

- **Synchronisation**
  - `lean cloud pull` (recuperer les projets du Cloud)
  - `lean cloud push` (envoyer vos modifications)

</div>

---

# Environnement d'Algorithme (1/2)

- **QCAlgorithm** : la classe de base de tout algorithme Lean
  - Modele **evenementiel** : votre code reagit aux donnees de marche, pas de lookahead possible
  - Le moteur garantit que vous ne voyez jamais le futur -- elimine le look-ahead bias par design
  - Strategic Development Framework integre (5 composants modulaires)

<div v-click="1">

- **Objets fondamentaux**
  - `self.time` : horloge du backtest (pas le temps reel)
  - `self.symbol` / `self.symbols` : identifiants des actifs
  - `self.portfolio` : etat courant du portefeuille
  - `self.securities` : donnees des actifs souscrits
  - Brokerage : modele de frais et de marche

</div>

> Notebook: QC-Py-02-Platform-Fundamentals.ipynb

---

# Environnement d'Algorithme (2/2)

- **Objets fondamentaux (suite)**
  - Indicateurs techniques (EMA, RSI, MACD, Bollinger...)
  - `self.history(symbol, period, resolution)` : donnees historiques sous forme DataFrame
<div v-click="1">

- **Membres locaux de l'algorithme**
  - Declares dans `initialize`, manipules par les methodes
  - Possibilite de les parametrer via `self.get_parameter("nom", default)`
  - Herites de QCAlgorithm ou ajoutes par le developpeur

</div>

---

# Evenements (1/2)

- **initialize** : point d'entree de configuration
  - `set_start_date`, `set_end_date`, `set_cash`
  - `add_equity`, `add_crypto`, `add_forex` (+ resolution)
  - `set_brokerage_model`, `set_portfolio_construction`
  - Consolidateurs, indicateurs, handlers

<div v-click="1">

- **on_data** : traitement des donnees a chaque pas de temps
  - `slice` contient des Ticks, TradeBars, QuoteBars
  - Acces par symbole : `data[self.symbol]`
  - Prix de cloture : `self.securities[symbol].price`

</div>

> Ref: *Hands-On AI Trading* Ch2 "Strategy Styles" p.30-31

---

# Evenements (2/2)

- **on_data (suite)** : logique de decision
  - Verification : `self.portfolio.invested`, seuils de temps
  - Ordres : `self.market_order(symbol, quantity)`, `self.set_holdings(symbol, weight)`
  - Journalisation : `self.log("message")`
  - Sortie de position : `self.liquidate(symbol)`

<div v-click="1">

- **on_order_event** : suivi des ordres
  - Statuts : Filled, Submitted, Canceled, Invalid...
</div>
<div v-click="2">

- **Autres points d'entree**
  - `on_securities_changed`, `on_end_of_day`, `on_warmup_finished`
  - Evenements planifies via `self.schedule`

</div>

---

# Initialisation - Dates et Monnaies

- **Definition des dates de backtesting**
  ```python
  self.set_start_date(2018, 4, 1)
  self.set_end_date(datetime.now() - timedelta(7))
  ```
<div v-click="1">

- **Definition des monnaies et montants initiaux**
  ```python
  self.set_account_currency("EUR")
  self.set_cash("EUR", 10000)
  ```

</div>
<div v-click="2">

- **Bonnes pratiques**
  - Toujours laisser au moins 7 jours avant aujourd'hui (donnees non finalisees)
  - Definir la monnaie AVANT le cash initial
  - Pour les crypto : `self.set_account_currency("BTC")`

</div>

---

# Initialisation - Broker et Securites

- **Choix du Broker et souscription a des securites**
  ```python
  self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE,
                           AccountType.CASH)
  self.spy = self.add_equity("SPY", Resolution.HOUR)
  ```
<div v-click="1">

- **Ajout d'indicateurs**
  ```python
  self.fast = self.ema(symbol, 30, Resolution.MINUTE)
  self.slow = self.ema(symbol, 60, Resolution.MINUTE)
  ```

</div>
<div v-click="2">

- **Crypto**
  ```python
  self.set_brokerage_model(BrokerageName.BITSTAMP, AccountType.CASH)
  self.btc = self.add_crypto("BTCUSD", Resolution.DAILY)
  ```

</div>

> Ref: *Hands-On AI Trading* Ch1 "Brokerages and Transaction Costs" p.10-13

---

# Initialisation - Warmup

- **Warmup : prechauffer les indicateurs**
  ```python
  self.set_warm_up(200)  # nombre de barres
  ```
<div v-click="1">

- **Warmup par duree**
  ```python
  self.set_warm_up(timedelta(days=150))
  ```
</div>
<div v-click="2">

- **Warmup automatique des indicateurs**
  ```python
  self.settings.automatic_indicator_warm_up = True
  ```
  - Chaque indicateur est automatiquement prechauffe selon sa periode
  - Evite les signaux parasites au debut du backtest

</div>

---

# Initialisation - Evenements Planifies

- **Evenements planifies** : actions recurrentes hors on_data
  ```python
  self.schedule.on(
      self.date_rules.every_day(),
      self.time_rules.every(timedelta(minutes=10)),
      self.example_func
  )
  ```
<div v-click="1">

- **Cas d'usage typiques**
  - Rebalancement journalier ou hebdomadaire
  - Nettoyage de positions en fin de journee
  - Calcul de signaux a heure fixe (ouverture, cloture)
  - Journalisation periodique de metriques

</div>

---

# Initialisation - Consolidation et Graphiques

- **Consolidation de barres** : agreger vers une resolution superieure
  ```python
  self.consolidator = self.consolidate(
      self.symbol, timedelta(minutes=10), self.consolidation_handler
  )
  ```
<div v-click="1">

- **Creation de graphiques personnalises**
  ```python
  stock_plot = Chart("Trade Plot")
  stock_plot.add_series(Series("Price", SeriesType.LINE, 0))
  self.add_chart(stock_plot)
  ```
  - Affichage dans l'interface QC apres le backtest
  - Methode `self.plot("Trade Plot", "Price", value)` dans on_data

</div>

> Ref: *Hands-On AI Trading* Ch2 "Charting" p.27

---

# Evenements de Donnees

- **Temps decoupe en "slices"**
  - Peuvent contenir des Ticks (ponctuel) ou TradeBars, QuoteBars (periodes)
<div v-click="1">

- **Methode principale**
  ```python
  def on_data(self, slice: Slice) -> None:
      data = slice[self.symbol]
      price = data.close
  ```
</div>
<div v-click="2">

- **Alternative : current_slice**
  - Accessible dans un evenement planifie
  ```python
  def my_scheduled_action(self):
      current_price = self.current_slice[self.symbol].close
  ```

</div>

---

# Journalisation et Graphiques

- **Journalisation**
  - Methodes `self.log()` ou `self.debug()`
  - Exemple :
    ```python
    self.debug(f"Time: {self.time}, Price: {self.securities[self.symbol].price}")
    self.log(f"Portfolio Value: {self.portfolio.total_portfolio_value}")
    ```
  - Logs enregistres dans le backtest : eviter de les surcharger
<div v-click="1">

- **Export de graphiques**
  - Methode `self.plot("ChartName", "SeriesName", value)`
</div>
<div v-click="2">

- **Utilisation de donnees historiques**
  ```python
  self.df = self.history(self.symbol, start_time, end_time, Resolution.HOUR)
  # Plusieurs symboles
  self.dataframe = self.history([symbol_ibm, symbol_aapl], start_time, end_time)
  ```

</div>

---

# Gestion Explicite des Ordres (1/2)

- **Types d'ordres**
  - Market, Limit, StopMarket, StopLimit, MarketOnOpen, MarketOnClose
<div v-click="1">

- **Exemples**
  ```python
  ticket = self.market_order("SPY", 100)
  ticket = self.limit_order("SPY", 100, 21.67)
  ticket = self.stop_market_order("IBM", 10, price * 0.9)
  ```

</div>
<div v-click="2">

- **Type de retour : OrderTicket**
  - Permet de suivre l'ordre (Status, QuantityFilled, etc.)
  - Possibilite de mise a jour chez certains Brokers
  - Methode `ticket.update(UpdateOrderFields(...))`

</div>

> Notebook: QC-Py-09-Order-Types.ipynb

---

# Gestion Explicite des Ordres (2/2)

- **Evenement de suivi**
  ```python
  def on_order_event(self, order_event: OrderEvent) -> None:
      if order_event.status == OrderStatus.FILLED:
          self.log(f"Ordre rempli: {order_event.symbol} x {order_event.fill_quantity}")
  ```
<div v-click="1">

- **Annulation**
  - `ticket.cancel("raison de l'annulation")`
</div>
<div v-click="2">

- **Dimensionnement de position**
  ```python
  self.set_holdings("SPY", 0.5)   # 50% du portefeuille
  self.set_holdings([
      PortfolioTarget("SPY", 0.8),
      PortfolioTarget("IBM", 0.2)
  ], True)  # True = liquider les positions existantes
  ```
</div>
<div v-click="3">

- **Buffer de slippage** : 2.5% par defaut
  - `self.settings.free_portfolio_value_percentage = 0.05`
- **Liquidation** : `self.liquidate()` (toutes les positions)

</div>

---

# Notebooks de Recherche

- **Research Environment** -- l'etape ou vous passez le plus de temps (et c'est normal)
  - Environnement d'exploration Jupyter pour iterer rapidement sur vos hypotheses
  - Disponible dans QC Cloud (zero install) ou en local via lean-cli

<div v-click="1">

- **Workflow**
  - Hypothese / Edge -> Research -> Strategy -> Backtests/Optimisation -> Paper/Live trading
</div>
<div v-click="2">

- **Kernel dedie**
  - Execution QC en ligne (Cloud)
  - Execution sous container Docker via lean-cli
</div>
<div v-click="3">

- **QuantBook**
  - Classe heritant de QCAlgorithm pour la recherche
  - Acces aux donnees historiques sous forme de DataFrames
  - Ideal pour le prototypage et la visualisation

</div>

> Ref: *Hands-On AI Trading* Ch2 "Research" p.25-26 | Notebook: QC-Py-04-Research-Workflow

---

# Framework de Haut Niveau

- **Architecture modulaire en 5 etapes** -- la force de Lean est cette separation des responsabilites
  - **Universe Selection** : *Quels actifs surveiller ?* (filtrage dynamique, screening)
  - **Alpha Creation** : *Quels signaux generer ?* (insights : direction, magnitude, confiance)
  - **Portfolio Construction** : *Comment allouer le capital ?* (equal weight, optimisation Markowitz, risk parity)
  - **Risk Management** : *Comment limiter les pertes ?* (drawdown max, trailing stop, exposure sectorielle)
  - **Execution** : *Comment passer les ordres ?* (immediat, VWAP, spread-based)

<div v-click="1">

- **Avantage du framework**
  - Chaque module est interchangeable et testable independamment
  - Possible de mixer primitives bas niveau et modules haut niveau
  - Facilite la composition : plusieurs Alphas contribuent au meme portefeuille
  - Exemples complets : `projects/Framework_Composite_*` (4 strategies composites)

</div>

> Notebooks: QC-Py-13-Alpha-Models, QC-Py-14-Portfolio-Construction-Execution

---

# Selection d'Univers

- **Un univers definit les actifs disponibles pour le portefeuille**
<div v-click="1">

- **Selection manuelle**
  ```python
  self.add_universe_selection(ManualUniverseSelectionModel(symbols))
  ```
</div>
<div v-click="2">

- **Selection parametrique ou planifiee**
  - Ex: EmaCrossUniverseSelectionModel
  - Selectionne les actifs d'un ensemble en retournement haussier le plus fort
</div>
<div v-click="3">

- **Combinaisons d'univers possibles**
  - Union ou intersection de plusieurs criteres de selection
</div>
<div v-click="4">

- **Evenement de changement**
  ```python
  def on_securities_changed(self, changes: SecurityChanges) -> None:
      for security in changes.added_securities:
          self.log(f"Ajout: {security.symbol}")
  ```

</div>

> Notebook: QC-Py-05-Universe-Selection | Ref: *Hands-On AI Trading* Ch2 "Diversification and Asset Selection" p.37-40

---

# Alphas (1/2)

- **Classes chargees de generer des signaux**
  - Insights : direction, amplitude et confiance
  - Bases sur des indicateurs, des modeles ML, ou des regles metier
<div v-click="1">

- **Ajout a l'initialisation**
  ```python
  self.add_alpha(RsiAlphaModel())
  ```

</div>
<div v-click="2">

- **Alphas par defaut**
  - EmaCrossAlphaModel, MacdAlphaModel, RsiAlphaModel
  - PearsonCorrelationPairsTradingAlphaModel
  - Exemple custom : `projects/EMA-Cross-Alpha` (Alpha standalone)

</div>

> Projet: EMA-Cross-Alpha (Sharpe 0.98)

---

# Alphas (2/2) et Insights

- **Alpha personnalise**
  ```python
  class MyAlphaModel(AlphaModel):
      def on_securities_changed(self, algorithm: QCAlgorithm,
                                changes: SecurityChanges) -> None:
          pass

      def update(self, algorithm: QCAlgorithm,
                 data: Slice) -> List[Insight]:
          insights = []
          # Logique de generation de signaux
          return insights
  ```
<div v-click="1">

- **Insights : les signaux retournes par Update**
  ```python
  insight = Insight.price("IBM", timedelta(minutes=20), InsightDirection.UP)
  ```
  - Parametres : Direction, Period, Magnitude, Confidence, Weight
  - Regroupement : `Insight.group([insight1, insight2, insight3])`
  - Annulation : `self.insights.cancel(symbols)`

</div>

---

# Construction de Portefeuille

- **Le maillon entre les signaux et les ordres** : transforme les Insights en cibles de portefeuille
  ```python
  self.set_portfolio_construction(EqualWeightingPortfolioConstructionModel())
  ```
<div v-click="1">

- **Modeles fournis par defaut**
  - **EqualWeighting** : poids egal entre les actifs avec Insights
  - **ConfidenceWeighted** : ponderation par la confiance de l'insight
  - **InsightWeighting** : ponderation par poids de l'insight
  - **SectorWeighting** : ponderation par secteur industriel
  - **MeanVarianceOptimization** : minimise la volatilite
  - **BlackLittermanOptimization** : optimiseur bayesien
  - **RiskParity** : minimisation du risque equilibre

</div>
<div v-click="2">

- **Optimiseurs fournis**
  - MaximumSharpeRatioPortfolioOptimizer, MinimumVariancePortfolioOptimizer
  - RiskParityPortfolioOptimizer, UnconstrainedMeanVariancePortfolioOptimizer

</div>

> Ref: *Hands-On AI Trading* Ch8 "Conditional Portfolio Optimization" p.319

---

# Gestion du Risque (Framework)

- **Objectif : gestion du risque des cibles**
  - Renvoyees par le gestionnaire de portefeuille
  - Idealement, integre des la conception, pas apres optimisation
  - Sinon, souvent performances degradees
<div v-click="1">

- **Definition**
  ```python
  self.add_risk_management(MaximumSectorExposureRiskManagementModel())
  ```

</div>
<div v-click="2">

- **Modeles fournis par defaut**
  - MaximumDrawdownPercentPerSecurity, MaximumDrawdownPercentPortfolio
  - MaximumUnrealizedProfitPercentPerSecurity
  - MaximumSectorExposureRiskManagementModel
  - TrailingStopRiskManagementModel

</div>

> Notebook: QC-Py-10-Risk-Portfolio-Management

---

# Modeles d'Execution

- **Determine comment les ordres sont executes**
<div v-click="1">

- **Definition**
  ```python
  self.set_execution(ImmediateExecutionModel())
  ```
</div>
<div v-click="2">

- **Modeles fournis**
  - **ImmediateExecutionModel** : execution immediate au prix courant
  - **SpreadExecutionModel** : attend un spread acceptable (necessite QuoteBars)
  - **StandardDeviationExecutionModel** : execute quand le prix est dans une fourchette
  - **VolumeWeightedAveragePriceExecutionModel** : decoupe l'ordre pour minimiser l'impact

</div>

---

# Optimisation de Parametres (1/2)

- **Definition de parametres d'algorithmes**
  ```python
  fast_period = self.get_parameter("ema-fast", 100)
  self.fast = self.ema("SPY", fast_period)
  ```
<div v-click="1">

- **Configuration dynamique**
  - Fichier config.json ou interface QC en ligne
  - Extension VS Code avec formulaire de parametrage

</div>
<div v-click="2">

- **Lanceur d'optimisation**
  - Execute une serie de backtests pour trouver la meilleure combinaison
  - Objectif : maximiser une metrique (ex: ratio de Sharpe)
  - Environnement Cloud (bouton + formulaire) ou `lean optimize` en local

</div>

> Notebook: QC-Py-15-Parameter-Optimization | Ref: *Hands-On AI Trading* Ch2 "Parameter Sensitivity Testing" p.33-34

---

# Optimisation de Parametres (2/2)

- **Strategies d'exploration**
  - **GridSearch** : teste toutes les combinaisons (min, max, step)
  - **EulerSearch** : GridSearch puis raffinement autour du meilleur resultat
<div v-click="1">

- **Definition des objectifs**
  - Parametre a optimiser (ex: Sharpe, CAGR, MaxDrawdown)
  - Maximiser ou minimiser (extremum)
  - Arret premature possible avec `target-value`
</div>
<div v-click="2">

- **Contraintes et bonnes pratiques**
  - Ajout de contraintes : disqualifier les configurations trop risquees
  - Attention a la combinatoire (produit cartesien des possibilites)
  - Version d'algo "rapide" pour tester la sensibilite
  - Validation finale sur une periode **hors-echantillon**

</div>

---
layout: image-overlay
image: ./images/book_cover_handson.png
imageClass: mid-right visible
---

# Hands-On AI Trading : votre livre

- **3 parties, 9 chapitres, 20+ exemples**
<div v-click="1">

- **Part I** : Fondations (Ch1-2)
  - Marches, brokers, workflow de recherche
</div>
<div v-click="2">

- **Part II** : ML step-by-step (Ch3-5)
  - Features, classification, regression
</div>
<div v-click="3">

- **Part III** : Applications avancees (Ch6-9)
  - NLP, RL, portfolio optimization, production
</div>
<div v-click="4">

- **Repo** : `github.com/QuantConnect/HandsOnAITradingBook`
- **Mapping complet** : `docs/HANDSON_AI_TRADING_MAPPING.md`

</div>

---
layout: dense
---

# Vos 28 notebooks progressifs

| Phase | Notebooks | Titre |
|-------|-----------|-------|
| **1 - Fondations LEAN** | QC-Py-01 a 04 | Setup, Platform, Data, Research |
| **2 - Univers et Assets** | QC-Py-05 a 08 | Universe, Options, Futures, Multi-Asset |
| **3 - Trading avance** | QC-Py-09 a 12 | Orders, Risk, Indicators, Backtesting |
| **4 - Algorithm Framework** | QC-Py-13 a 15 | Alpha, Portfolio, Optimization |
| **5 - Donnees alternatives** | QC-Py-16 a 17 | Alternative Data, Sentiment |
| **6 - ML classique** | QC-Py-18 a 21 | Features, Classification, Regression, Portfolio-ML |
| **7 - Deep Learning** | QC-Py-22 a 25 | LSTM, Unsupervised, NLP, RL |
| **8 - Production** | QC-Py-26 a 28 | LLM-Signals, Deployment, Regime Detection |

<div v-click="1">

- **Progression** : chaque phase suppose la maitrise des precedentes
- **Autonomie** : chaque notebook contient theorie, code commente, et exercices
- **Chemin rapide** : Phases 1-3 pour les fondamentaux (~8h), Phase 4 pour le framework (~3h)

</div>

---
layout: dense
---

# 67 projets prets a backtester

| Categorie | Nombre | Exemples | Meilleur Sharpe |
|-----------|--------|----------|-----------------|
| **Classiques** | 15 | EMA, Momentum, AllWeather, RegimeSwitching | 1.16 |
| **ML/AI** | 18 | RF, XGBoost, LSTM, RL-DQN, Gaussian, Chronos | 0.90 |
| **Livre HandsOn** | 14 (sur 20) | Mapping chapitre par chapitre | -- |
| **Options** | 3 | Wheel, CoveredCall, VGT Options | -- |
| **Crypto** | 4 | BTC-MACD-ADX, EMA-Cross-Crypto, MultiCanal | -- |
| **Composites** | 4 | TrendWeather, FamaFrench, EMATrend, MomentumRegime | -- |

<div v-click="1">

- **Tous les projets** sont dans `QuantConnect/projects/` avec un `main.py` pret a backtester
- **Metriques documentees** : Sharpe, CAGR, MaxDrawdown pour chaque strategie
- **Difficulte progressive** : des EMA Crossovers aux composites multi-Alpha

</div>

---
layout: dense
---

# Mapping Exercices ESGF

| Exercice | Sujet | Notebooks | Projet |
|----------|-------|-----------|--------|
| **Ex01** | Setup + EMA Crossover | QC-Py-01, 02 | EMA-Cross-Stocks |
| **Ex02** | All-Weather Portfolio | QC-Py-08 | AllWeather |
| **Ex03** | Sector Momentum | QC-Py-05, 13 | SectorMomentum |
| **Ex04** | Trend-Following Multi-Sector | QC-Py-11 | TrendStocksLite |
| **Ex05** | Custom Alpha Model | QC-Py-13, 14 | EMA-Cross-Alpha |
| **Ex06** | Multi-Alpha Composite | QC-Py-15 | Framework_Composite_TrendWeather |

<div v-click="1">

- **Ex01-Ex02** : niveau debutant, ~2h chacun
- **Ex03-Ex04** : niveau intermediaire, necessite la maitrise des univers et indicateurs
- **Ex05-Ex06** : niveau avance, utilisation du framework Alpha complet
- **Objectif** : presenter votre strategie avec ses metriques de backtest

</div>

---

# Demo : un backtest en 5 minutes

```python
class EMACrossStocksAlgorithm(QCAlgorithm):
    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_cash(100000)
        self.tickers = ["AAPL", "MSFT", "GOOGL", "AMZN", "NVDA"]
        self.symbols = {}
        self.ema_fast = {}
        self.ema_slow = {}
        for ticker in self.tickers:
            sym = self.add_equity(ticker, Resolution.DAILY).symbol
            self.symbols[ticker] = sym
            self.ema_fast[ticker] = self.ema(sym, 20, Resolution.DAILY)
            self.ema_slow[ticker] = self.ema(sym, 50, Resolution.DAILY)

    def on_data(self, data):
        for ticker in self.tickers:
            if self.ema_fast[ticker].current.value > self.ema_slow[ticker].current.value:
                self.set_holdings(self.symbols[ticker], 0.19)
            elif self.portfolio[self.symbols[ticker]].invested:
                self.liquidate(self.symbols[ticker])
```

**15 lignes de code, 5 actions, 11 ans de backtest.** Copiez dans QC Cloud, lancez : Sharpe ~0.87, soit +74% de mieux que le buy-and-hold.

---

# Synthese et prochaines etapes

Vous avez maintenant les outils pour passer de l'idee au backtest. Voici votre feuille de route :

**1. Creez votre compte QC Cloud** (gratuit sur quantconnect.com)
<div v-click="1">

**2. Completez Ex01 et Ex02** (debutant, ~2h chacun)
  - Ex01 : Setup + votre premier EMA Crossover
  - Ex02 : All-Weather Portfolio multi-actifs
</div>
<div v-click="2">

**3. Explorez les notebooks QC-Py-01 a 04**
  - Maitrisez les fondamentaux de la plateforme
</div>
<div v-click="3">

**4. Choisissez une strategie du depot a modifier**
  - 67 projets disponibles, de debutant a avance
  - Modifiez les parametres, ajoutez des actifs, testez des variantes
</div>
<div v-click="4">

**5. Objectif final** : presenter votre strategie avec metriques de backtest
  - Sharpe, CAGR, MaxDrawdown, nombre de trades
  - Justifiez vos choix de conception

</div>

---
layout: cover
---

# Merci et Ressources

Jean-Sylvain Boige -- jsboige@myia.org

**Tout est dans le depot pour demarrer des aujourd'hui :**

- **QC Cloud** : quantconnect.com (compte gratuit)
- **Repo GitHub** : github.com/jsboige/CoursIA (28 notebooks + 67 projets)
- **Livre** : *Hands-On AI Trading* (Pik, Chan, Broad, Sun, Singh -- Wiley 2025)
- **Documentation QC** : quantconnect.com/docs

> Le trading algorithmique est un domaine ou la pratique precede la theorie.
> Le meilleur apprentissage : modifiez une strategie existante, backtestez, analysez les resultats, iterez.
