# CoursIA

**Apprendre l'intelligence artificielle par la pratique, des fondements theoriques aux applications avancees.**

CoursIA est une collection de notebooks Jupyter interactifs couvrant l'ensemble du spectre de l'IA : algorithmes de recherche, resolution par contraintes, raisonnement formel, theorie des jeux, programmation probabiliste, machine learning, IA generative multimodale et trading algorithmique.

Les notebooks sont disponibles en Python, C# (.NET Interactive) et Lean 4. Chaque serie suit une progression pedagogique, des concepts fondamentaux vers les applications avancees. La plupart fonctionnent en local sans configuration ; seules les series GenAI et QuantConnect necessitent des cles API.

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

---

> **Catalogue vivant** -- Pour l'inventaire exhaustif et a jour (comptes exacts par serie, statut READY/DEMO, maturite PRODUCTION/BETA), consultez **[`COURSE_CATALOG.generated.md`](COURSE_CATALOG.generated.md)**. Ce catalogue est regenere automatiquement chaque jour : il fait foi sur les chiffres et les statuts, ce README en donne la vue d'ensemble pedagogique. Le depot couvre une douzaine de grandes series, de l'IA symbolique au trading algorithmique en passant par l'IA generative et l'apprentissage automatique.

## Commencer ici

Vous avez clone le depot et vous ne savez pas par ou commencer ?

1. **Choisissez votre niveau** : voyez les parcours recommandes plus bas pour un plan d'apprentissage guide
2. **Explorez par serie** : chaque serie a son propre README detaille avec une vue d'ensemble, la liste des notebooks, les prerequis et la duree estimee
3. **Documentation projet** : le repertoire [docs/](docs/README.md) centralise les regles de travail, l'infrastructure, les procedes recurrents et les guides d'apprentissage

## Cartographie rapide du depot

```
MyIA.AI.Notebooks/
  Search/          -> Algorithmes de recherche (BFS, A*, CSP) -- point d'entree ideal pour debutants
  Sudoku/          -> Resolution multi-paradigme -- 10 approches pour 1 probleme
  ML/              -> Machine Learning (ML.NET, agents ADK)
  RL/              -> Reinforcement Learning (PPO, DQN, Stable Baselines3)
  Probas/          -> Programmation probabiliste (Infer.NET, Pyro)
  GameTheory/      -> Theorie des jeux, equilibres de Nash, mechanism design
  IIT/             -> Theorie de l'information integree (Tononi, PyPhi)
  CaseStudies/     -> Etudes de cas interdisciplinaires
  SymbolicAI/      -> Raisonnement formel (Lean 4, Tweety, Semantic Web, Smart Contracts, Planners, Symbolic Learning)
  GenAI/           -> IA generative (Image, Audio, Video, Texte, Semantic Kernel) -- la plus grande serie
  QuantConnect/    -> Trading algorithmique (notebooks pedagogiques + strategies backtestees + pipeline ML)
  cross-series/    -> Applications transverses (matching-cv : data science multi-domaines)
```

Pour un guide complet des parcours d'apprentissage, voir [docs/parcours/](docs/parcours/).

---

## Parcours recommandes

**Debutant** -- Commencer par Search (Part 1), Sudoku, puis ML.Net. Ces series ne necessitent aucune cle API et introduisent les concepts fondamentaux.

**Intermediaire** -- Explorer GameTheory, Probas, puis la partie Foundations de GenAI (Image, Texte). Ajoutez les techniques probabilistes et generatives a votre boite a outils.

**Avance** -- SymbolicAI (Lean, SmartContracts), QuantConnect (strategies ML/DL), GenAI Video/Audio. Pour les etudiants a l'aise avec les fondamentaux qui veulent aller plus loin.

**Recherche** -- ML Training Pipeline (forecasting, GNN), SymbolicAI (preuves formelles Lean 4), Infer.NET (programmation probabiliste avancee).

---

## Ce qu'on y trouve

Le depot couvre un spectre large de l'IA, des algorithmes classiques aux modeles generatifs les plus recents, avec un parti pris constant : confronter plusieurs paradigmes sur les memes problemes plutot que d'en privilegier un seul. Quelques points notables :

- **Multi-langages, multi-ecosystemes** : Python pour le machine learning et l'IA generative, C# pour l'ecosysteme Microsoft (ML.NET, Infer.NET, Semantic Kernel), Lean 4 pour la verification formelle. Chaque langage est employe la ou il excelle, pas par defaut.
- **Du fondamental a la recherche** : les series partent des algorithmes de base (BFS, A*, backtracking) et vont jusqu'a des sujets de pointe -- transformers pour le forecasting financier, agents de preuve autonomes, integration neuro-symbolique, deep learning multimodal.
- **Preuves formelles ambitieuses** : au-dela des exercices, les series Lean et GameTheory mecanisent des theoremes phares en Lean 4 -- theoreme de sensibilite, theoreme de Kochen-Specker, theoreme du libre arbitre de Conway-Kochen, formalisations des theoremes d'Arrow et de Sen -- avec des hommages aux mathematiques de Grothendieck et de Conway.
- **Donnees et marches reels** : les notebooks QuantConnect s'appuient sur des donnees de marche reelles (yfinance, framework LEAN) ; le pipeline d'entrainement ML valide ses modeles par walk-forward strict et multi-seed sur un panier de cryptomonnaies.
- **IA generative deployable** : les notebooks GenAI fonctionnent au choix sur des APIs cloud (OpenAI, Anthropic) ou sur des modeles locaux servis par une infrastructure Docker GPU (Qwen, FLUX, ComfyUI, Whisper, MusicGen).
- **Agents et LLMs transverses** : assistants de preuve, agents de data science autonomes, planification pilotee par LLM, GraphRAG et boucles LLM-verification symbolique tissent un fil rouge entre les series.
- **Etudes de cas integratrices** : des projets interdisciplinaires (diagnostic medical, planification oncologique) et des applications transverses combinent les techniques apprises en silos en livrables complets.

---

## Philosophie pedagogique

Chaque serie est concue pour etre **self-contained** : un etudiant peut ouvrir n'importe quel notebook et suivre la progression sans prerequis externes, les explications etant integrees au fil des cellules.

Les approches **multi-paradigmes** sont privilegiees : le Sudoku est resolu par backtracking, CSP, metaheuristiques et reseaux de neurones pour comparer les compromis. Les jeux sont formalises en Python et en Lean 4. Cette diversite d'approches sur un meme probleme est au coeur de la demarche.

Les notebooks combinent **theorie et implementation** : les concepts sont introduits progressivement, puis mis en pratique dans des cellules executables. La structure **exemple puis exercice** est systematique -- chaque notion est d'abord demontree par un exemple resolu, puis reprise dans un exercice a completer ; corriges et squelettes cohabitent, et le notebook s'execute de bout en bout meme lorsque les exercices ne sont pas faits.

Enfin, **la priorite au local** : la majorite des series tournent apres un simple clone, sans cle API ni GPU. Seules GenAI (modeles generatifs) et QuantConnect (donnees de marche) demandent une configuration -- de sorte que rien ne fasse barrage a la prise en main.

---

## Series de notebooks

### Search -- Algorithmes de recherche et optimisation

Comment un ordinateur trouve-t-il son chemin dans un labyrinthe, ordonne-t-il un atelier, ou bat-il un humain au Puissance 4 ? Tout probleme d'IA, du jeu de plateau a la planification logistique, se ramene a un meme defi : explorer un espace de solutions possibles pour trouver la meilleure. Le fil conducteur de la serie n'est pas l'accumulation d'algorithmes mais une seule competence -- savoir **quand explorer, quand contraindre, et quand combiner les deux** -- construite autour de l'idee de **reduction de l'espace de recherche** : comment passer d'une enumeration aveugle exponentielle a une resolution intelligemment guidee.

**Fondements** -- La progression part de la formalisation d'un probleme en espace d'etats (S, A, T, G), puis deroule les grands paradigmes : recherche non informee (BFS, DFS), recherche guidee par heuristique (A*, avec la garantie d'optimalite lorsque l'heuristique est admissible), optimisation locale (Hill Climbing, recuit simule, Tabu), evolution (algorithmes genetiques), recherche adversariale dans les jeux (Minimax, Alpha-Beta) et enfin Monte Carlo Tree Search jusqu'a l'architecture AlphaGo (MCTS couple a un DQN). S'y greffent des extensions de pointe : Dancing Links de Knuth pour la couverture exacte, programmation lineaire, automates symboliques a predicats Z3, et un banc d'essai de metaheuristiques (essaim particulaire, colonies, recuit).

**Programmation par contraintes** -- Un changement de paradigme : au lieu de concevoir un algorithme d'exploration, on declare les contraintes du probleme et le solveur trouve les solutions. On y apprend la propagation (AC-3, Forward Checking, MAC) qui elague l'espace avant meme de chercher, les contraintes globales d'OR-Tools CP-SAT (AllDifferent, Cumulative), puis les usages industriels -- ordonnancement d'atelier, planification de projet, optimisation combinatoire (sac a dos, bin packing) -- et les frontieres du domaine : contraintes souples, raisonnement temporel par algebre d'Allen, CSP distribues entre agents, et surtout l'hybridation (CP+SAT, CP+ML, et generation de contraintes par LLM). C'est le pont vers SymbolicAI.

**Applications** -- Chaque concept se mesure sur un probleme reel, la plupart adaptes de projets etudiants : N-Queens, coloration de cartes, planning d'infirmiers, emploi du temps, demineur (CSP, probabilites et LLM combines), solveur Wordle par theorie de l'information, nonogrammes, generation procedurale par Wave Function Collapse, Puissance 4 oppose a une batterie d'IA, voyageur de commerce et tournees de vehicules, optimisation de portefeuille et detection de bords par algorithmes genetiques (avec leurs pendants C# sur GeneticSharp), reglage d'hyperparametres pour le Machine Learning. C'est le terrain ou l'on compare, sur une meme instance, methode exacte et methode approchee.

Cette serie est aussi un carrefour : ses algorithmes irriguent Sudoku (DLX, automates), SymbolicAI (Z3, planification PDDL), GameTheory (Minimax, MCTS) et RL (MCTS et DQN), et ses metaheuristiques reviennent regler les hyperparametres du Machine Learning.

Python et C# | [README detaille](MyIA.AI.Notebooks/Search/README.md)

### Sudoku -- Resolution multi-paradigme

Un seul probleme -- la grille de Sudoku -- aborde par une dizaine de paradigmes differents. L'objectif n'est pas de resoudre des Sudokus, mais de comprendre les compromis entre performance, complexite d'implementation et expressivite de chaque approche.

On y decouvre le backtracking avec heuristiques MRV, la couverture exacte de Knuth (Dancing Links), les metaheuristiques (genetique, recuit simule), la programmation par contraintes (OR-Tools, Z3), et meme les reseaux de neurones. Chaque notebook est disponible en C# et Python.

C# et Python | [README detaille](MyIA.AI.Notebooks/Sudoku/README.md)

### SymbolicAI -- Raisonnement formel

L'IA symbolique s'interesse aux systemes de raisonnement automatique. Cette serie explore plusieurs sous-domaines complementaires :

**Tweety** -- Logiques formelles et argumentation computationnelle avec TweetyProject. Logiques propositionnelle, du premier ordre, modale et argumentatives, des extensions de Dung aux systemes ASPIC+ et DeLP, en passant par la revision de croyances AGM.

**Semantic Web** -- Du RDF/OWL aux graphes de connaissances integres aux LLMs. Fondations en .NET (dotNetRDF), standards modernes en Python (SHACL, JSON-LD, RDF-Star), puis GraphRAG et comparaison de raisonneurs.

**Lean** -- Verification formelle avec Lean 4, des fondations (types dependants, isomorphisme de Curry-Howard, tactiques Mathlib) a l'assistance par LLM (LeanCopilot, AlphaProof, agents de preuve autonomes), la verification de reseaux de neurones et le port de theoremes phares : theoreme de sensibilite, theoreme de Kochen-Specker, theoreme du libre arbitre de Conway-Kochen, ainsi que des hommages a Grothendieck et Conway. Necessite WSL sous Windows.

**Planners** -- Planification automatique : fondations PDDL, heuristiques avec Fast-Downward, planification temporelle, HTN, puis pont vers le neurosymbolique (LLM-planning).

**Smart Contracts** -- Des origines cypherpunk a Solidity avancee et aux blockchains multi-chain (Vyper, Move/Sui, Solana/Anchor). Tests Foundry, fuzz testing, verification formelle, zero-knowledge proofs, chiffrement homomorphe et DAO governance.

**Argument Analysis** -- Analyse argumentative multi-agents avec Semantic Kernel et LLMs.

**Symbolic Learning** -- Apprentissage symbolique dans la lignee du chapitre 19 d'AIMA : de l'induction pure (espaces de versions, elimination de candidats) a l'apprentissage guide par la connaissance (EBL, RBL) et a la programmation logique inductive (FOIL), jusqu'a l'integration neuro-symbolique (Logic Tensor Networks, DeepProbLog), l'extraction de regles sur graphes de connaissances et les boucles LLM-verification symbolique.

Python, Lean 4 et C# | [README detaille](MyIA.AI.Notebooks/SymbolicAI/README.md)

### GameTheory -- Theorie des jeux

Comment des agents rationnels interagissent-ils ? Des equilibres de Nash aux jeux evolutionnaires, du backward induction aux jeux bayesiens, cette serie couvre les fondamentaux de la theorie des jeux et leurs applications en IA.

Les aspects avances incluent le CFR (Counterfactual Regret Minimization, au coeur des IA de poker), les jeux cooperatifs, le mechanism design et le MARL. Des side tracks en Lean 4 proposent des formalisations et preuves des theoremes classiques (Arrow, Sen).

Python et Lean 4 | [README detaille](MyIA.AI.Notebooks/GameTheory/README.md)

### Probas -- Programmation probabiliste

Comment raisonner sous incertitude ? La programmation probabiliste permet de definir des modeles generatifs, propager l'incertitude et mettre a jour des croyances face a de nouvelles observations.

La serie utilise principalement Infer.NET de Microsoft (C#) : distributions fondamentales, reseaux bayesiens, modeles de melange et theorie de la decision bayesienne. Un notebook complementaire explore la pragmatique du langage avec Pyro (modele RSA -- Rational Speech Acts).

C# (Infer.NET) et Python (Pyro) | [README Probas](MyIA.AI.Notebooks/Probas/README.md)

### ML -- Machine Learning

Comment passe-t-on d'un tableur rempli de donnees a un modele qui predit, recommande ou anticipe ? Et ce savoir-faire change-t-il selon qu'on code en C# ou en Python ? La serie repond par la negative : les concepts du Machine Learning -- features, entrainement, evaluation, generalisation -- sont **invariants**, seuls les outils et le degre d'automatisation different. Le fil conducteur est justement ce deplacement : *qui* tient le pipeline ? Vous a la main, puis l'AutoML, puis un agent LLM autonome -- la constante etant, a chaque etage, une evaluation honnete qui distingue un modele qui marche d'un modele qu'on comprend.

**ML.NET -- le Machine Learning sans quitter l'ecosysteme .NET** -- Le premier volet construit le pipeline complet en C# : point d'entree `MLContext`, structure colonnaire `IDataView`, feature engineering (encodage, normalisation, concatenation), puis l'entrainement (SDCA, LightGBM, et l'AutoML qui cherche seul l'algorithme et ses hyperparametres). Vient ensuite l'etape la plus importante -- l'evaluation rigoureuse par validation croisee et l'explication des predictions (Permutation Feature Importance) -- avant les sujets de production : prevision de series temporelles par analyse spectrale (SSA), interoperabilite ONNX qui sert des modeles entraines ailleurs (scikit-learn, PyTorch, jusqu'a BERT ou Whisper) directement dans une application .NET, et systemes de recommandation par factorisation matricielle. Le TP capstone marie ML.NET et la regression bayesienne d'Infer.NET pour predire non plus seulement une valeur, mais sa plage de confiance -- pont direct vers Probas.

**Data Science avec agents (Python)** -- Le second volet part des fondations (NumPy, Pandas, scikit-learn) puis bascule vers un changement de paradigme : non plus *ecrire* le code d'analyse, mais *orchestrer* des agents LLM qui le produisent et l'executent. Le sous-track LangChain construit l'agent unique outille -- interroger un DataFrame, nettoyer un jeu de donnees, parser des appels d'offres, scorer des candidatures. Le sous-track Google ADK monte en puissance vers les systemes multi-agents : boucles planner-coder, framework DS-STAR pour une data science autonome, MLE-STAR jusqu'a concourir sur Kaggle, et le deploiement cloud (BigQuery, BQML). Tout est multi-provider -- Gemini, OpenAI ou un vLLM local au choix -- pour ne dependre d'aucun fournisseur unique. L'enjeu pedagogique depasse la technique : comprendre *quand* un agent accelere reellement l'analyse, et *comment* l'encadrer.

Cette serie irrigue le reste du depot par sa rigueur d'evaluation : on la retrouve dans QuantConnect (modeles predictifs de trading), RL (memes gradients, memes reseaux, meme mefiance du surapprentissage) et Probas (l'inference bayesienne du TP) ; son reglage d'hyperparametres rejoint les metaheuristiques de Search ; et ses agents LLM reposent sur les modeles couverts par GenAI -- ou les modeles ONNX de ML.NET servent justement a deployer BERT et Whisper.

C# et Python | [README detaille](MyIA.AI.Notebooks/ML/README.md)

### GenAI -- IA Generative

Comment generer une image a partir d'une phrase, faire parler une machine, composer un fond musical, animer une video, ou brancher un LLM sur ses propres outils ? La plus grande serie du depot explore l'IA generative dans toutes ses modalites. Son fil conducteur n'est pas l'accumulation d'APIs : c'est apprendre a **choisir** entre un modele cloud (DALL-E, GPT-5, Whisper) et un modele open-source auto-heberge (FLUX, Stable Diffusion, Qwen, MusicGen) selon le cout, le controle, le debit et la sensibilite des donnees, puis a **combiner** ces briques dans des pipelines qui tiennent en production. Tout commence par `00-GenAI-Environment`, le passage oblige qui configure cles API, services Docker et validation.

Chaque modalite (Image, Audio, Video) suit la meme montee en quatre niveaux -- Foundation (premiers appels d'API), Advanced (modeles locaux sur GPU, edition fine), Orchestration (workflows multi-modeles) et Applications (cas d'usage concrets) -- et chacune se structure autour d'un fil rouge concret a construire de bout en bout.

**Image** -- De DALL-E 3 et GPT-5 en cloud jusqu'aux modeles auto-heberges (FLUX, Stable Diffusion 3.5, Qwen Image Edit, Z-Image/Lumina) orchestres via ComfyUI. On y apprend a editer plutot que regenerer (inpainting, ControlNet), a composer des graphes de noeuds reproductibles, et a gerer la VRAM (quantizations INT4/FP8). Fil rouge : un generateur de visuels pedagogiques.

**Audio** -- La chaine vocale complete : transcription (Whisper), synthese (OpenAI TTS, Kokoro, Chatterbox), clonage de voix (XTTS), generation musicale (MusicGen, YuE, ACE-Step), separation de sources (Demucs) et TTS expressif a tags prosodiques. Fil rouge : un podcast entierement genere, voix clonee et fond musical compris.

**Video** -- La modalite la plus exigeante : comprehension de sequences (GPT-5, Qwen-VL), generation de mouvement (HunyuanVideo, LTX-Video, Wan, Stable Video Diffusion), super-resolution et interpolation (Real-ESRGAN, RIFE). Fil rouge : transformer un script texte en video pedagogique animee.

**Texte** -- Le socle de tout le reste : prompt engineering, structured outputs (JSON Schema, Pydantic), function calling, RAG moderne, code interpreter, modeles de raisonnement (o-series, GPT-5 thinking), patterns de production, et deploiement de LLMs locaux (vLLM, quantization AWQ/GPTQ).

**Semantic Kernel** -- Le SDK d'orchestration agentique de Microsoft, en Python et en C#/.NET Interactive : plugins, agents, filtres, vector stores, Process Framework, multimodalite et MCP. Demonstrateur phare : un NotebookMaker a trois agents (Admin, Coder, Reviewer) qui genere lui-meme des notebooks pedagogiques.

**Specialisation des modeles** -- Au-dela de l'usage, on entraine : FineTuning (LoRA, QLoRA, SFT, DPO) pour adapter un modele sans tout re-entrainer, et PostTraining pour les techniques d'alignement de pointe (RLHF, DPO, GRPO, RLVR).

**Industrialisation** -- Les applications GenAI se testent : la serie Playwright-OWUI ecrit des tests de bout en bout sur Open WebUI (navigation, streaming, RAG, outils MCP, CI/CD), pour passer de la demonstration jouet au produit deployable.

**Vibe-Coding** -- Le developpement assiste par agents IA, devenu competence centrale : ateliers progressifs sur Claude Code et Roo Code, plus une introduction aux agents autonomes (Claw-Systems), de la decouverte a l'automatisation avancee (skills, sous-agents, MCP, hooks).

Tout converge dans un fil rouge transverse : le **Texte** structure un script, l'**Image** l'illustre, l'**Audio** le narre, la **Video** l'assemble, et **Semantic Kernel** orchestre l'ensemble en agents autonomes -- c'est ce parcours d'integration qui distingue une demo d'un produit deployable.

Python | [README detaille](MyIA.AI.Notebooks/GenAI/README.md)

### QuantConnect -- Trading algorithmique

Peut-on appliquer les techniques d'IA aux marches financiers ? Cette serie repond a cette question en combinant le framework LEAN de QuantConnect avec des approches allant du momentum classique au deep learning.

**Notebooks pedagogiques** -- Du cycle de vie d'un algorithme LEAN aux strategies ML/DL/RL/LLM, en passant par les options, futures, risk management et analyse de sentiment. Progression en cinq phases : fondations LEAN, univers et actifs, trading avance, algorithm framework, puis ML/DL/AI.

**Strategies backtestees** -- Strategies completes avec notebooks de recherche standalone (yfinance/pandas). Les approches vont du momentum multi-actifs aux modeles de facteurs Fama-French, en passant par les options couvertes et le mean reversion. Chaque strategie est accompagnee de son code source et de ses resultats de backtest.

**ML Training Pipeline** -- Pipeline complet d'entrainement et d'evaluation de modeles DL pour le forecasting financier : LSTM, Transformer, iTransformer, PatchTST, Mamba. Donnees crypto panier (10 coins) avec validation walk-forward stricte, evaluation zero-shot de modeles foundation (Chronos-Bolt, Kronos), et baselines comparatives (GARCH, random walk, majority class).

**partner-course-quant-trading** -- Exemples de projets etudiants et notebooks de recherche issus du cours partenaire.

Python | [README detaille](MyIA.AI.Notebooks/QuantConnect/README.md) | [Strategies](MyIA.AI.Notebooks/QuantConnect/projects/README.md)

### RL -- Reinforcement Learning

Introduction a l'apprentissage par renforcement avec Stable Baselines3 : PPO sur CartPole, wrappers et callbacks, experience replay et DQN.

Python | [README detaille](MyIA.AI.Notebooks/RL/README.md)

### IIT -- Theorie de l'Information Integree

La theorie de l'information integree (Tononi) propose une approche mathematique de la conscience : un systeme est conscient dans la mesure ou il integre l'information de maniere non reducible. Ce notebook utilise PyPhi pour calculer le coefficient Phi et explorer les concepts de cause et d'effet en information.

Python | [README detaille](MyIA.AI.Notebooks/IIT/README.md)

### CaseStudies -- Etudes de cas interdisciplinaires

Les etudes de cas fusionnent les techniques apprises en silos -- un solveur SMT, un algorithme genetique, une ontologie OWL, un modele bayesien -- autour d'un probleme metier reel (diagnostic medical, planification oncologique). Chaque projet mobilise trois a quatre paradigmes qui se renforcent au lieu de se concurrencer, articules autour du pattern du jumeau numerique (digital twin). Concue comme un devoir integrateur de fin de cycle, la serie fournit pour chaque projet un template etudiant et une solution de reference.

Python | [README detaille](MyIA.AI.Notebooks/CaseStudies/README.md)

### cross-series -- Applications transverses

Au-dela des notebooks pedagogiques, le repertoire `cross-series/` rassemble des applications completes combinant plusieurs domaines en un livrable autonome. Premier exemple : `matching-cv`, une application web (Flask) qui compare trois approches d'appariement CV-offre -- appariement stable de Gale-Shapley, similarite semantique et RAG hybride -- au croisement de la recherche, de l'IA generative et de l'IA symbolique.

[README detaille](MyIA.AI.Notebooks/cross-series/README.md)

---

## Structure du depot

```text
CoursIA/
  MyIA.AI.Notebooks/          Notebooks interactifs, organises par serie
    Search/                    Algorithmes de recherche (Python, C#)
    Sudoku/                    Resolution multi-paradigme (Python, C#)
    SymbolicAI/                IA symbolique (Python, Lean 4, C#)
      Tweety/ SemanticWeb/ Lean/ Planners/ SmartContracts/ Argument_Analysis/ SymbolicLearning/
    GameTheory/                Theorie des jeux (Python, Lean 4)
    Probas/                    Programmation probabiliste (C#, Python)
    ML/                        Machine Learning (C#, Python)
    RL/                        Reinforcement Learning (Python)
    GenAI/                     IA Generative (Python)
      Image/ Audio/ Video/ Texte/ SemanticKernel/ Vibe-Coding/
    QuantConnect/              Trading algorithmique (Python)
      Python/                  Notebooks pedagogiques
      projects/                Strategies backtestees
      ML-Training-Pipeline/    Pipeline DL forecasting
      partner-course-quant-trading/ Projets etudiants
    CaseStudies/               Etudes de cas interdisciplinaires (Python)
    cross-series/              Applications transverses multi-domaines (Python)
    IIT/                       Information integree (Python)
    Config/                    Configuration API

  scripts/                     Validation, execution, analyse
  docker-configurations/       Infrastructure Docker GPU
  GradeBookApp/                Notation etudiants
  MyIA.AI.Shared/              Bibliotheque C# partagee
  notebook-infrastructure/     Papermill + MCP maintenance
```

---

## Mise en route

### Prerequis

- Python 3.10+ avec pip
- .NET 9.0 SDK (pour notebooks C#)
- VS Code avec extensions Python, Jupyter, .NET Interactive
- WSL (pour Lean et certains outils SymbolicAI)
- Docker + GPU (optionnel, pour GenAI avance)

### Installation rapide

```bash
# 1. Cloner
git clone https://github.com/jsboige/CoursIA.git
cd CoursIA

# 2. Environnement Python (un venv suffit pour la majorite des series)
python -m venv venv
venv\Scripts\activate          # Windows ; sous Linux/WSL : source venv/bin/activate
pip install jupyter ipykernel python-dotenv

# 3. Kernel Jupyter Python
python -m ipykernel install --user --name=coursia --display-name "Python (CoursIA)"

# 4. Kernel .NET Interactive (notebooks C#)
dotnet tool install --global Microsoft.dotnet-interactive
dotnet interactive jupyter install
dotnet restore MyIA.CoursIA.sln

# 5. Dependances de la serie visee (chaque serie porte son requirements.txt)
pip install -r MyIA.AI.Notebooks/<Serie>/requirements.txt
```

Les cles API eventuelles se posent via les `.env.example` (section Configuration). Pour valider
ou executer un notebook, ne pas ecrire de script ad-hoc : le depot fournit une CLI dediee
(section Scripts et validation).

### Installation par serie

La plupart des series sont autonomes et s'ouvrent sur un **notebook de mise en route**
(Setup / Environment) qui installe les dependances de la serie et verifie la chaine d'outils :
c'est le point de depart recommande. Pour les kernels, WSL et toolchains specifiques, des
scripts de preparation dedies accompagnent ces notebooks. Les series sans notebook de setup
s'installent directement via leur `requirements.txt`.

| Serie | Notebook de mise en route | Preparation dediee |
|-------|---------------------------|--------------------|
| GenAI | `GenAI/00-GenAI-Environment/` (Environment-Setup, Docker-Services, API-Endpoints, Validation) | `requirements.txt` (+ `-audio` / `-video`) ; `00-GenAI-Environment/validate_auth.py` |
| GameTheory | `GameTheory/GameTheory-1-Setup.ipynb` | `scripts/setup_wsl_openspiel.sh`, `setup_wsl_lean4.sh`, `setup_lean4_kernel.ps1` |
| Sudoku | `Sudoku/Sudoku-0-Environment-Csharp.ipynb` | kernel .NET Interactive |
| Probas | `Probas/Infer/Infer-1-Setup.ipynb`, `Probas/PyMC/PyMC-1-Setup.ipynb` | `Infer/scripts/setup_environment.ps1` |
| QuantConnect | `QuantConnect/Python/QC-Py-01-Setup.ipynb` | `requirements.txt` |
| Lean | `SymbolicAI/Lean/Lean-1-Setup.ipynb` | `Lean/scripts/setup_wsl_python.sh`, `validate_lean_setup.py` |
| Planners | `SymbolicAI/Planners/00-Environment/Planners-0-Setup.ipynb` | `requirements.txt` ; `SymbolicAI/scripts/install_clingo.py` |
| SemanticWeb | `SymbolicAI/SemanticWeb/SW-1-CSharp-Setup.ipynb` | kernel .NET Interactive |
| SmartContracts | `SymbolicAI/SmartContracts/00-Foundations/SC-1-Setup-Foundry.ipynb`, `SC-2-Setup-Web3py.ipynb` | `setup_env.py`, `scripts/setup_wsl_smartcontracts.sh` |
| Tweety | `SymbolicAI/Tweety/Tweety-1-Setup.ipynb` | `tweety_init.py` (JDK auto-telecharge) |
| Argument Analysis | `SymbolicAI/Argument_Analysis/Argument_Analysis_UI_configuration.ipynb` | `install_jdk_portable.py` |
| IIT | `requirements.txt` | `scripts/setup_pyphi_env.ps1` |
| Search / RL / CaseStudies | `requirements.txt` | -- |
| cross-series | `requirements.txt` | `cross-series/matching-cv/scripts/install_deps.sh` |

Pour les series qui exposent un `requirements.txt`, l'installation directe reste possible :

```bash
pip install -r MyIA.AI.Notebooks/<Serie>/requirements.txt
```

Les notebooks C# (ML.NET, Sudoku, SemanticWeb, Probas/Infer.NET) ne passent pas par pip :
ils s'appuient sur le kernel .NET Interactive et `dotnet restore` (section Mise en route).

---

## Configuration

Les series Search, Sudoku, ML.Net, Probas (Infer.NET), Tweety, SemanticWeb et Planners fonctionnent sans aucune cle API. Les series suivantes necessitent une configuration :

| Serie | Fichier | Variables requises |
|-------|---------|-------------------|
| GenAI | `GenAI/.env` | `OPENAI_API_KEY`, `ANTHROPIC_API_KEY` |
| Lean | `SymbolicAI/Lean/.env` | `OPENAI_API_KEY`, `GITHUB_TOKEN` |
| Argument Analysis | `SymbolicAI/Argument_Analysis/.env` | `OPENAI_API_KEY` |
| QuantConnect | `QuantConnect/.env` | `QC_USER_ID`, `QC_API_TOKEN` |
| C# Notebooks | `Config/settings.json` | `apikey`, `model` |
| Docker ComfyUI | `comfyui-qwen/.env` | `CIVITAI_TOKEN`, `HF_TOKEN` |

Chaque dossier contient un `.env.example` documentant les variables. Copier et editer :

```bash
cp MyIA.AI.Notebooks/GenAI/.env.example MyIA.AI.Notebooks/GenAI/.env
# Editer le fichier .env avec vos cles
```

---

## Kernels Jupyter

| Kernel | Series | Installation |
|--------|--------|--------------|
| `python3` | Tous les notebooks Python | `pip install ipykernel` |
| `.net-csharp` | Sudoku, Search, Probas, ML | `dotnet tool install -g Microsoft.dotnet-interactive` |
| `lean4_jupyter` | Lean, GameTheory (b) | Via `elan` (WSL uniquement) |

Limitations connues : les notebooks C# avec `#!import` necessitent une execution cellule par cellule (incompatible Papermill). Lean 4 requiert WSL sous Windows.

---

## Infrastructure Docker

Pour les notebooks GenAI avances utilisant des modeles locaux (Qwen Image Edit, ComfyUI Video, etc.), une infrastructure Docker avec support GPU est fournie.

Services disponibles : Qwen Image Edit (~29 Go VRAM), ComfyUI Video (~12 Go), Stable Diffusion Forge (~10 Go), Whisper, MusicGen, Kokoro TTS, Demucs.

La pile s'orchestre via le CLI `genai.py` plutot que des commandes `docker` lancees a la main :

```bash
cp docker-configurations/services/comfyui-qwen/.env.example docker-configurations/services/comfyui-qwen/.env
python scripts/genai-stack/genai.py docker status      # etat des services
python scripts/genai-stack/genai.py docker start all   # demarrer
python scripts/genai-stack/genai.py docker stop all    # arreter
python scripts/genai-stack/genai.py gpu                # verifier la VRAM disponible
```

Configuration detaillee dans `docker-configurations/`.

---

## Scripts et validation

Regle de base : **toujours passer par ces scripts pour valider ou executer un notebook,
jamais par un script ecrit pour l'occasion**. La CLI detecte le kernel depuis les metadonnees
du notebook (Python, .NET Interactive, Lean sous WSL).

| Script | Usage |
|--------|-------|
| `scripts/notebook_tools/notebook_tools.py` | CLI multi-series : `validate`, `execute`, `analyze`, `skeleton`, `check-env` |
| `scripts/notebook_tools/notebook_helpers.py` | Manipulation de notebooks, iteration cellule par cellule |
| `scripts/genai-stack/genai.py` | Pile GenAI : `docker`, `validate`, `notebooks`, `gpu` |
| `scripts/smartcontracts/validate_sc_notebooks.py` | Validation dediee Smart Contracts (`--quick`, `--execute --anvil`) |

```bash
# Validation de structure
python scripts/notebook_tools/notebook_tools.py validate MyIA.AI.Notebooks/Sudoku

# Execution (Papermill ; --cell-by-cell pour les notebooks .NET / Lean)
python scripts/notebook_tools/notebook_tools.py execute MyIA.AI.Notebooks/Search --cell-by-cell

# Verification de l'environnement d'une famille
python scripts/notebook_tools/notebook_tools.py check-env GenAI

# Validation complete de la pile GenAI
python scripts/genai-stack/genai.py validate --full
```

Un workflow GitHub Actions valide automatiquement les notebooks a chaque pull request (format, syntaxe, execution de base).

---

## Outils Claude Code

Le depot inclut une configuration Claude Code avec des agents specialises et des commandes slash pour la maintenance des notebooks.

**Commandes principales** : `/verify-notebooks`, `/enrich-notebooks`, `/cleanup-notebooks`, `/build-notebook`, `/execute-notebook`, `/validate-genai`, `/qc-iterative-improve`

**Agents specialises** : notebook-enricher, notebook-validator, notebook-executor, qc-strategy-analyzer, qc-strategy-improver, readme-updater, et d'autres.

Configuration dans `.claude/agents/` et `.claude/skills/`.

---

## Outils et dependances externes

Les dependances principales par serie :

| Outil | Series | Provenance |
|-------|--------|-----------|
| Z3 SMT Solver | Sudoku, Search, SymbolicAI | `requirements.txt` de la serie |
| OR-Tools | Sudoku, Search, Planners | `requirements.txt` de la serie |
| Tweety + JDK | Tweety, Argument_Analysis | JDK auto-telecharge ; reste dans `requirements.txt` |
| Lean 4 + Mathlib | Lean, GameTheory | `elan` (WSL) ; diagnostic via `validate_lean_setup.py` |
| OpenSpiel | GameTheory | `requirements.txt` GameTheory |
| Infer.NET | Probas | NuGet (kernel .NET Interactive) |
| PyPhi | IIT | `requirements.txt` IIT |

---

## Contribution

1. Fork le depot
2. Creer une branche (`git checkout -b feature/nouveau-notebook`)
3. Commit (`git commit -m 'Add: notebook sur les Transformers'`)
4. Push et ouvrir une Pull Request

Conventions : PEP 8 pour Python, conventions standard pour C#, pas d'emojis dans le code, documentation en francais. Chaque famille de notebooks doit inclure un `.env.example` documentant les variables requises.

## Licence

Ce projet est sous licence MIT - voir [LICENSE](LICENSE).

---

Repository : [github.com/jsboige/CoursIA](https://github.com/jsboige/CoursIA)
