---
theme: ../theme-ia101
title: "S4 Trading Algorithmique - Pratique Lean/QuantConnect et Workflow Agentique"
info: Cours Intelligence Artificielle - Pratique avec Lean/QuantConnect + Workflow Agentique
paginate: true
drawings:
  persist: false
transition: slide-left
mdc: true
layout: cover
---

# Pratique Lean/QuantConnect et Workflow Agentique

Intelligence Artificielle -- S4

**De la theorie au backtest en 5 minutes : plateforme Lean + agent IA codeur**

- Plateforme QuantConnect : setup, algorithmes, framework Alpha
- Workflow agentique : VSCode + Claude Code + MCP
- Composites avances et preparation projet

---

# Plan

1. **Workflow du trader quant** (3 slides)
   - Du concept au code : les 6 etapes

2. **Plateforme Lean/QuantConnect** (15 slides)
   - Setup, algorithmes, framework Alpha, notebooks, projets

3. **Workflow agentique** (10 slides)
   - Agent IA codeur, architecture VSCode/CC/MCP, demo live

4. **Composites avances** (4 slides)
   - C4.1/C4.2/C4.3, architecture multi-Alpha

5. **Preparation projet et soutenance** (5 slides)
   - Criteres, anti-biais, troubleshooting, ressources

---

layout: section
---

# Partie 1 : Workflow du Trader Quant

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

layout: section
---

# Partie 2 : Plateforme Lean/QuantConnect

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

# Gestion Explicite des Ordres

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

- **Dimensionnement de position**
  ```python
  self.set_holdings("SPY", 0.5)   # 50% du portefeuille
  self.set_holdings([
      PortfolioTarget("SPY", 0.8),
      PortfolioTarget("IBM", 0.2)
  ], True)  # True = liquider les positions existantes
  ```

</div>

> Notebook: QC-Py-09-Order-Types.ipynb

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

# Alphas et Insights

- **Classes chargees de generer des signaux**
  - Insights : direction, amplitude et confiance
  - Bases sur des indicateurs, des modeles ML, ou des regles metier
<div v-click="1">

- **Alpha personnalise**
  ```python
  class MyAlphaModel(AlphaModel):
      def update(self, algorithm: QCAlgorithm,
                 data: Slice) -> List[Insight]:
          insights = []
          # Logique de generation de signaux
          return insights
  ```
</div>
<div v-click="2">

- **Insights : les signaux retournes**
  ```python
  insight = Insight.price("IBM", timedelta(minutes=20), InsightDirection.UP)
  ```
  - Parametres : Direction, Period, Magnitude, Confidence, Weight
  - Regroupement : `Insight.group([insight1, insight2, insight3])`

</div>

> Projet: EMA-Cross-Alpha (Sharpe 0.98)

---

# Construction de Portefeuille et Risk Management

- **Le maillon entre les signaux et les ordres**
  ```python
  self.set_portfolio_construction(EqualWeightingPortfolioConstructionModel())
  self.add_risk_management(MaximumDrawdownPercentPerSecurity(0.10))
  ```
<div v-click="1">

- **Modeles de portefeuille**
  - EqualWeighting, ConfidenceWeighted, InsightWeighting
  - MeanVarianceOptimization, BlackLittermanOptimization, RiskParity
</div>
<div v-click="2">

- **Modeles de risque**
  - MaximumDrawdownPercentPerSecurity, MaximumDrawdownPercentPortfolio
  - MaximumSectorExposureRiskManagementModel, TrailingStopRiskManagementModel

</div>

> Notebook: QC-Py-10-Risk-Portfolio-Management

---

layout: dense
---

# Vos 28 notebooks et 67 projets

| Phase | Notebooks | Titre |
|-------|-----------|-------|
| **1 - Fondations** | QC-Py-01 a 04 | Setup, Platform, Data, Research |
| **2 - Univers et Assets** | QC-Py-05 a 08 | Universe, Options, Futures, Multi-Asset |
| **3 - Trading avance** | QC-Py-09 a 12 | Orders, Risk, Indicators, Backtesting |
| **4 - Framework** | QC-Py-13 a 15 | Alpha, Portfolio, Optimization |
| **5 - Donnees alternatives** | QC-Py-16 a 17 | Alternative Data, Sentiment |
| **6 - ML classique** | QC-Py-18 a 21 | Features, Classification, Regression, Portfolio-ML |
| **7 - Deep Learning** | QC-Py-22 a 25 | LSTM, Unsupervised, NLP, RL |
| **8 - Production** | QC-Py-26 a 28 | LLM-Signals, Deployment, Regime Detection |

<div v-click="1">

- **67 projets** dans `QuantConnect/projects/` : des EMA Crossover aux composites multi-Alpha (meilleur Sharpe : 1.16)
- **Progression** : chaque phase suppose la maitrise des precedentes
- **Chemin rapide** : Phases 1-3 pour les fondamentaux (~8h), Phase 4 pour le framework (~3h)

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

**15 lignes de code, 5 actions, 11 ans de backtest.** Sharpe ~0.87, soit +74% de mieux que le buy-and-hold.

---

layout: section
---

# Partie 3 : Workflow Agentique

---

# Qu'est-ce qu'un Agent IA Codeur ?

- **Definition** : un LLM (Large Language Model) qui peut lire, ecrire et executer du code dans votre environnement
  - Pas un simple chatbot : il agit sur vos fichiers, votre terminal, vos outils
<div v-click="1">

- **Exemples** :
  - Claude Code (Anthropic) -- celui que nous utilisons
  - GitHub Copilot, Cursor, Windsurf
  - Tous partagent le meme principe : contexte (votre code) + action (modifications)
</div>
<div v-click="2">

- **Pour le trading quant** :
  - L'agent connait l'API QuantConnect, les patterns de strategie, les metriques
  - Il peut ecrire un algorithme complet, le compiler, le backtester
  - Il iterere sur les resultats pour ameliorer la strategie

</div>

---

# Architecture VSCode + Claude Code + MCP

- **VSCode** : votre editeur, avec l'extension Claude Code installee
  - Terminal integre, gestion Git, extensions
<div v-click="1">

- **Claude Code** : l'agent IA qui opere dans VSCode
  - Lit vos fichiers, execute des commandes, modifie le code
  - Utilise des outils (Read, Write, Bash, Grep)
</div>
<div v-click="2">

- **MCP (Model Context Protocol)** : le pont entre Claude et vos services
  - Standard ouvert pour connecter des outils externes a un LLM
  - Serveur MCP QuantConnect : expose l'API QC comme outils
  - Claude appelle `create_project`, `create_compile`, `create_backtest` comme des fonctions

</div>

---

# Le Protocole MCP

- **MCP = Model Context Protocol**
  - Standard developpe par Anthropic pour connecter des LLMs a des outils externes
  - Analogue a une API REST, mais concu pour les agents IA
<div v-click="1">

- **Serveur MCP QuantConnect** : `quantconnect/mcp-server`
  - Docker : `docker run --rm -i quantconnect/mcp-server`
  - Outils exposes : `list_projects`, `read_file`, `create_file`, `create_compile`, `create_backtest`, `create_optimization`, `check_syntax`, `complete_code`

</div>
<div v-click="2">

- **Avantage cle** : l'agent n'a pas besoin de scripts personnalises
  - Il lit la documentation des outils et decide de la sequence d'appels
  - C'est un "programmeur" autonome, pas un script d'automatisation

</div>

---

# Le Workflow Agentique en 5 Etapes

```
1. IDEE          "Je veux une strategie momentum sur SPY"
       |
2. CODE          Agent ecrit main.py + research.ipynb
       |
3. COMPILE       Agent appelle create_compile + read_compile
       |
4. BACKTEST      Agent appelle create_backtest + read_backtest
       |
5. ITERE         Agent analyse les metriques, ajuste, retour a 2
```

<div v-click="1">

- **Cycle complet en ~5 minutes** (vs 30-60 min manuellement)
- L'agent connait les bonnes pratiques : warmup, resolution, parametres
- Il evite les erreurs courantes : look-ahead bias, manque de warmup

</div>

---

# Configuration : ce qu'il vous faut

- **Etape 1** : Installer VSCode + extension Claude Code
  - `code --install-extension anthropic.claude-code`
<div v-click="1">

- **Etape 2** : Installer Docker Desktop
  - Necessaire pour le serveur MCP QuantConnect
  - `docker pull quantconnect/mcp-server`
</div>
<div v-click="2">

- **Etape 3** : Configurer `.mcp.json` a la racine du projet
  ```json
  {
    "mcpServers": {
      "quantconnect": {
        "command": "docker",
        "args": ["run", "--rm", "-i",
          "-e", "QUANTCONNECT_USER_ID",
          "-e", "QUANTCONNECT_API_TOKEN",
          "-e", "QUANTCONNECT_ORGANIZATION_ID",
          "quantconnect/mcp-server"]
      }
    }
  }
  ```
</div>
<div v-click="3">

- **Etape 4** : Ouvrir le depot dans VSCode, lancer Claude Code (`Ctrl+Shift+P` > "Claude")

</div>

---

# Demo Live : le Cycle Complet (1/2)

**Prompt initial a l'agent** :

```
"Upload le projet EMA-Cross-Stocks dans mon organisation QuantConnect
et backteste-le sur 2015-2025 avec 100k USD"
```

<div v-click="1">

**Ce que l'agent fait automatiquement** :

1. Lit le fichier `main.py` du projet local
2. Appelle `create_project` dans l'organisation QuantConnect
3. Appelle `create_file` pour uploader `main.py`
4. Appelle `create_compile` et attend le resultat
5. Si erreur de syntaxe : corrige et recompile

</div>

---

# Demo Live : le Cycle Complet (2/2)

**Etape backtest** :

- L'agent appelle `create_backtest(projectId, compileId, name)`
- Puis `read_backtest(projectId, backtestId)` pour les resultats

<div v-click="1">

**Metriques retournees** :

| Metrique | Description |
|----------|-------------|
| Sharpe Ratio | Rendement ajuste au risque (> 0.5 = correct) |
| CAGR | Rendement annualise |
| Max Drawdown | Perte maximale depuis un pic |
| Total Trades | Nombre de trades |
| Alpha | Rendement vs benchmark |

</div>
<div v-click="2">

- **Iteration automatique** : l'agent analyse les metriques, ajuste le code, rebackteste
- **Votre role** : observer, poser des questions, orienter l'agent

</div>

---

# Ce que l'Agent peut (et ne peut pas) faire

- **Peut faire** :
  - Ecrire un algorithme complet a partir d'une description
  - Corriger les erreurs de syntaxe et de compilation
  - Lancer des backtests et lire les resultats
  - Proposer des ameliorations basees sur les metriques
  - Adapter les parametres pour optimiser les performances
<div v-click="1">

- **Ne peut pas faire** :
  - Garantir un Sharpe > 2 (surapprentissage = danger)
  - Remplacer votre jugement sur la coherence de la strategie
  - Penser a votre place : vous devez orienter l'agent
  - Detecter tous les biais (look-ahead, survivorship, etc.)

</div>

---

layout: section
---

# Partie 4 : Composites Avances

---

# Resultats Composites Avances (1/2)

- **C4.1 : TrendWeather Composite**
  - Combinaison : Trend-Following + Weather signals
  - Univers : 20+ actifs multi-secteur
  - Architecture : 3 Alpha models + EqualWeighting PCM + MaxDrawdown Risk
  - Sharpe : **1.16** sur 11 ans (2015-2025)

<div v-click="1">

- **C4.2 : MomentumRegime Composite**
  - Combinaison : Momentum + Regime Detection (Hidden Markov)
  - Bascule entre momentum et mean-reversion selon le regime
  - Architecture : 2 Alpha + RegimeSwitching PCM + TrailingStop Risk
  - Sharpe : **0.98** sur 11 ans

</div>

---

# Resultats Composites Avances (2/2)

- **C4.3 : Multi-Alpha Ensemble** -- architecture 5 couches complete
  - **Universe** : Top 50 par volume (rebalance hebdo)
  - **Alphas** : EMA Cross + RSI + MACD (3 signaux independants)
  - **Portfolio** : BlackLittermanOptimization (pondere par confiance)
  - **Risk** : MaximumSectorExposure + MaximumDrawdownPercentPortfolio
  - **Execution** : VolumeWeightedAveragePrice (minimise impact)

<div v-click="1">

| Couche ajoute | Sharpe | Increment |
|---------------|--------|-----------|
| EMA Cross seul | 0.45 | base |
| + Alpha RSI | 0.62 | +0.17 |
| + PCM BlackLitterman | 0.89 | +0.27 |
| + Risk Management | 1.05 | +0.16 |
| **+ Execution VWAP** | **1.31** | **+0.26** |

</div>
<div v-click="2">

- Chaque couche du framework apporte un increment de performance
- Le plus gros saut : risk management (0.89 -> 1.05)

</div>

---

# Les Composites sont dans le Depot

- **4 projets composites** prets a backtester :
  - `projects/Framework_Composite_TrendWeather/`
  - `projects/Framework_Composite_FamaFrench/`
  - `projects/Framework_Composite_EMATrend/`
  - `projects/Framework_Composite_MomentumRegime/`
<div v-click="1">

- Chaque projet contient :
  - `main.py` : l'algorithme complet (50-200 lignes)
  - `research.ipynb` : notebook d'exploration avec yfinance
  - Metriques documentees dans le README du projet

</div>
<div v-click="2">

- **Pour votre projet** : inspirez-vous de ces architectures
  - Vous pouvez les cloner, modifier les parametres, changer les actifs
  - L'agent peut vous aider a les adapter a votre idee

</div>

---

layout: section
---

# Partie 5 : Preparation Projet et Soutenance

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

# Criteres de Qualite et Soutenance

- **Objectif** : deployer une strategie fonctionnelle sur QuantConnect Cloud
<div v-click="1">

- **Criteres de qualite** :

| Critere | Poids | Description |
|---------|-------|-------------|
| Fonctionnalite | 30% | L'algorithme compile et produit des resultats coherents |
| Performance | 25% | Sharpe > 0.3, MaxDD < 30%, rendement positif |
| Originalite | 20% | Choix d'actifs, parametres, architecture personnalisee |
| Comprehension | 15% | Justification des choix, analyse des resultats |
| Presentation | 10% | Clarte, structure, visualisations |

</div>
<div v-click="2">

- **Workflow recommande** :
  1. Choisir une strategie de base parmi les projets du depot
  2. Utiliser l'agent pour personnaliser (actifs, periodes, seuils)
  3. Valider manuellement : relire le code, verifier les metriques
  4. Documenter vos choix et limites identifiees

</div>

---

# Bonnes Pratiques Anti-Biais

- **Look-ahead bias** : ne jamais utiliser les donnees du jour pour decider aujourd'hui
  - Lean le previent par design (moteur evenementiel)
  - Mais vos notebooks de recherche peuvent le presenter
<div v-click="1">

- **Overfitting** : Sharpe > 3 sur un backtest = probablement surajuste
  - Tester sur des periodes differentes (in-sample / out-of-sample)
  - Un bon Sharpe reel : 0.5-1.5 pour une strategie robuste
</div>
<div v-click="2">

- **Survivorship bias** : backtester sur des entreprises qui existent encore
  - L'univers QC corrige partiellement ce biais
  - Evitez de cherry-picker les actifs retroactivement

</div>

---

# Troubleshooting

- **"Kernel died"** dans les notebooks : redemarrer le kernel (Kernel > Restart)
- **"Compile error"** sur QC Cloud : verifier les imports (`from AlgorithmImports import *`)
- **MCP non connecte** : verifier que Docker est lance, `.mcp.json` est correct
- **Rate limiting QC** : max 10 appels/minute, attendre 60s si bloque
<div v-click="1">

- **Erreurs communes** :
  - Oublier `self.set_warm_up()` = signaux parasites au debut
  - Resolution incorrecte : `Resolution.DAILY` vs `Resolution.HOUR`
  - `self.add_equity("SPY")` sans resolution = valeur par defaut (Minute)
  - Oublier de declarer les parametres dans le code ET dans config.json

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
- **MCP Server** : github.com/QuantConnect/mcp-server
- **Claude Code** : claude.ai/code
- **Documentation QC** : quantconnect.com/docs

> Le trading algorithmique est un domaine ou la pratique precede la theorie.
> Le meilleur apprentissage : modifiez une strategie existante, backtestez, analysez les resultats, iterez.
