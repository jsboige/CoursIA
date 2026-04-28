---
theme: ../theme-ia101
title: "Trading Algorithmique - Workflow Agentique"
info: Cours Intelligence Artificielle - Workflow Agentique VSCode + MCP QuantConnect
paginate: true
drawings:
  persist: false
transition: slide-left
mdc: true
layout: cover
---

# Workflow Agentique pour le Trading

Intelligence Artificielle -- Trading Algorithmique

**De l'idee au backtest en 5 minutes avec VSCode + Claude Code + MCP QuantConnect**

- Comprendre le concept d'agent IA codeur
- Installer et configurer le workflow agentique
- Demonstrer le cycle complet : idee, code, backtest, analyse
- Preparer un projet de strategie algorithmique

---

# Ou en sommes-nous ?

- **Seance 1** : Fondamentaux du trading algorithmique
  - Marches, ordres, metriques de performance
- **Seance 2** : Strategies et framework Lean
  - Alpha models, portfolio construction, risk management
  - Notebooks progressifs, projets prets a backtester

<div v-click="1">

- **Maintenant** : Workflow agentique
  - Comment un agent IA peut ecrire, tester et deployer votre strategie
  - Demonstration live avec VSCode + Claude Code

</div>

---

# Plan de la Seance

1. **Le workflow agentique** (8 slides)
   - Qu'est-ce qu'un agent IA codeur ?
   - Architecture VSCode + Claude Code + MCP
   - Le protocole MCP (Model Context Protocol)

2. **Demo live MCP QuantConnect** (8 slides)
   - Creation de projet, upload, compilation, backtest
   - Lecture des resultats, iteration

3. **Composites avances** (5 slides)
   - Resultats C4.1, C4.2, C4.3
   - Architecture multi-Alpha

4. **Preparation projet** (3 slides)
   - Criteres de qualite, rendu

5. **Q&A et ressources** (3 slides)

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

# Le Protocole MCP (1/2)

- **MCP = Model Context Protocol**
  - Standard developpe par Anthropic pour connecter des LLMs a des outils externes
  - Analogue a une API REST, mais concu pour les agents IA
<div v-click="1">

- **Comment ca marche** :
  1. Un serveur MCP expose des "outils" (functions) avec leurs schemas
  2. L'agent decouvre les outils disponibles
  3. L'agent decide quand et comment les appeler
  4. Les resultats retournent dans le contexte de la conversation

</div>
<div v-click="2">

- **Avantage cle** : l'agent n'a pas besoin de scripts personnalises
  - Il lit la documentation des outils et decide de la sequence d'appels
  - C'est un "programmeur" autonome, pas un script d'automatisation

</div>

---

# Le Protocole MCP (2/2)

- **Serveur MCP QuantConnect** : `quantconnect/mcp-server`
  - Docker : `docker run --rm -i quantconnect/mcp-server`
  - Authentification via variables d'environnement
  - Rate limiting : 10 appels/minute max
<div v-click="1">

- **Outils exposes** :
  - `list_projects`, `read_project`, `create_project`
  - `read_file`, `create_file`, `update_file_contents`
  - `create_compile`, `read_compile`
  - `create_backtest`, `read_backtest`
  - `create_optimization`, `read_optimization`
  - `check_syntax`, `complete_code`

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

# Demo Live : le Cycle Complet (1/4)

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

# Demo Live : le Cycle Complet (2/4)

**Etape compilation** :

- L'agent appelle `create_compile(projectId)` puis `read_compile(projectId, compileId)`
- Si le compile est en cours : il attend et relance
- Si erreur : il lit le message, identifie la ligne, corrige le code

<div v-click="1">

**Erreurs typiques detectees automatiquement** :
- `self.add_equity` sans `Resolution`
- Import manquant (`from AlgorithmImports import *`)
- Parametres non declares dans `config.json`
- Indentation incorrecte (Python)

</div>

---

# Demo Live : le Cycle Complet (3/4)

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
| Win Rate | % de trades gagnants |
| Alpha | Rendement vs benchmark |
| Beta | Correlation avec le marche |

</div>

---

# Demo Live : le Cycle Complet (4/4)

**Iteration automatique** :

```
Agent : "Le backtest donne Sharpe 0.45, MaxDD -22%.
         Je vais ajouter un stop-loss a 5% et
         reduire la position a 15% par actif."
```

<div v-click="1">

- L'agent modifie `main.py` : ajoute `self.add_risk_management(...)`
- Recompile, relance le backtest
- Compare les metriques avant/apres
- Itere jusqu'a converger vers un Sharpe acceptable

</div>
<div v-click="2">

- **Ce que vous faites pendant ce temps** : observer, poser des questions, orienter
- L'agent est un assistant, pas un oracle : votre jugement reste essentiel

</div>

---

# MCP QC : les Outils en Detail (1/2)

- **Gestion de projets**
  - `list_projects()` : lister tous les projets de l'organisation
  - `read_project(projectId)` : lire les fichiers d'un projet
  - `create_project(name, language)` : creer un nouveau projet
<div v-click="1">

- **Gestion de fichiers**
  - `read_file(projectId, name)` : lire le contenu d'un fichier
  - `create_file(projectId, name, content)` : ajouter un fichier
  - `update_file_contents(projectId, name, content)` : modifier un fichier
  - `patch_file(projectId, patch)` : appliquer un diff unifie

</div>

---

# MCP QC : les Outils en Detail (2/2)

- **Compilation et Backtest**
  - `create_compile(projectId)` -> `read_compile(projectId, compileId)`
  - `create_backtest(projectId, compileId, name)` -> `read_backtest(projectId, backtestId)`
<div v-click="1">

- **Optimisation**
  - `create_optimization(...)` : lancer une recherche de parametres
  - `read_optimization(optimizationId)` : lire les resultats
  - `estimate_optimization_time(...)` : estimer le cout

</div>
<div v-click="2">

- **Assistance**
  - `check_syntax(language, files)` : verification syntaxique hors ligne
  - `complete_code(language, sentence)` : autocompletion API QC
  - `enhance_error_message(language, error)` : diagnostic d'erreur

</div>

---

# Resultats Composites Avances (1/3)

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

# Resultats Composites Avances (2/3)

- **C4.3 : Multi-Alpha Ensemble**
  - Architecture 5 couches complete :
    1. **Universe** : Top 50 par volume (rebalance hebdo)
    2. **Alphas** : EMA Cross + RSI + MACD (3 signaux independants)
    3. **Portfolio** : BlackLittermanOptimization (pondere par confiance)
    4. **Risk** : MaximumSectorExposure + MaximumDrawdownPercentPortfolio
    5. **Execution** : VolumeWeightedAveragePrice (minimise impact)

<div v-click="1">

- **Resultats** : Sharpe **1.3+**, MaxDD -15%, 300+ trades/an
- **Cle** : la diversification des signaux Alpha reduit la variance
- Chaque Alpha seul aurait Sharpe 0.4-0.6, l'ensemble atteint 1.3+

</div>

---

# Resultats Composites Avances (3/3)

| Strategie | Sharpe | CAGR | Max DD | Trades/an |
|-----------|--------|------|--------|-----------|
| EMA Cross seul | 0.45 | 8.2% | -25% | 50 |
| + Alpha RSI | 0.62 | 10.1% | -22% | 80 |
| + PCM BlackLitterman | 0.89 | 12.5% | -18% | 95 |
| + Risk Management | 1.05 | 11.8% | -15% | 90 |
| **+ Execution VWAP** | **1.31** | **13.2%** | **-14%** | **110** |

<div v-click="1">

- Chaque couche du framework apporte un increment de performance
- Le plus gros saut : de 0.89 a 1.05 avec le risk management
- Conclusion : la gestion du risque est plus importante que le signal seul

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

# Preparation Projet (1/2)

- **Objectif** : deployer une strategie fonctionnelle sur QuantConnect Cloud
  - Upload dans une organisation QuantConnect (fournie par le formateur)

<div v-click="1">

- **Format attendu** :
  - Un projet QuantConnect avec votre strategie
  - Un notebook de recherche (`research.ipynb`) avec vos analyses
  - Metriques de backtest : Sharpe, CAGR, MaxDD, nombre de trades
  - Justification de vos choix de conception

</div>

---

# Preparation Projet (2/2)

- **Criteres de qualite** :

| Critere | Poids | Description |
|---------|-------|-------------|
| Fonctionnalite | 30% | L'algorithme compile et produit des resultats coherents |
| Performance | 25% | Sharpe > 0.3, MaxDD < 30%, rendement positif |
| Originalite | 20% | Choix d'actifs, parametres, architecture personnalisee |
| Comprehension | 15% | Justification des choix, analyse des resultats |
| Presentation | 10% | Clarte, structure, visualisations |

<div v-click="1">

- **Conseil** : commencez par modifier une strategie existante
- Le workflow agentique accelere l'iteration, mais la comprehension reste votre responsabilite

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

# Workflow Recommande pour la Soutenance

1. **Choisir une strategie de base** parmi les projets du depot
   - Projects simples pour debuter, composites pour les plus ambitieux

<div v-click="1">

2. **Utiliser l'agent pour personnaliser** :
   - Changer les actifs, les periodes, les seuils
   - Ajouter un module de risque ou de gestion de position
</div>
<div v-click="2">

3. **Valider manuellement** :
   - Relire le code produit par l'agent
   - Verifier les metriques : sont-elles realistes ?
   - Tester sur une periode hors-echantillon (out-of-sample)
</div>
<div v-click="3">

4. **Documenter vos choix** :
   - Pourquoi cette strategie ? Quels actifs ? Quels parametres ?
   - Quelles limites avez-vous identifiees ?

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

# Ressources

- **QuantConnect Cloud** : quantconnect.com (compte gratuit)
- **Depot GitHub** : github.com/jsboige/CoursIA
  - Notebooks progressifs et projets prets a backtester
  - Documentation : `QuantConnect/docs/HANDSON_AI_TRADING_MAPPING.md`
<div v-click="1">

- **Livre de reference** : *Hands-On AI Trading* (Pik, Chan, Broad, Sun, Singh -- Wiley 2025)
- **MCP Server** : github.com/QuantConnect/mcp-server
- **Claude Code** : claude.ai/code

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

# Merci et Questions

Jean-Sylvain Boige -- jsboige@myia.org

**Votre mission** :

1. Choisissez une strategie (ou creez la votre)
2. Utilisez le workflow agentique pour iterer rapidement
3. Deployez sur QuantConnect Cloud
4. Preparez votre presentation

> Le meilleur apprentissage : modifiez, backtestez, analysez, iterez.
> L'agent accelere le cycle, mais la comprehension vous appartient.
