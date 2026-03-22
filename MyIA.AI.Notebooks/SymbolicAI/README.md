# SymbolicAI - Intelligence Artificielle Symbolique

Collection de **92 notebooks Jupyter** pour l'apprentissage de l'IA symbolique : logiques formelles, argumentation computationnelle, verification formelle, web semantique, planification automatique, smart contracts et optimisation.

## Vue d'ensemble

| Serie | Notebooks | Exercices | Environnement | Theme | Duree |
|-------|-----------|-----------|---------------|-------|-------|
| [SemanticWeb](#semanticweb---web-semantique) | 17 | 15 (88%) | .NET C# + Python | RDF, SPARQL, OWL, SHACL, GraphRAG | ~12h |
| [SmartContracts](#smartcontracts---blockchain-et-contrats-intelligents) | 27 | 27 (100%) | Python + Solidity/Foundry | Solidity, DeFi, DAO, ZK, Multi-chain | ~20h |
| [Planners](#planners---planification-automatique) | 13 | 12 (92%) | Python + Fast-Downward (WSL/Docker) | PDDL, CP-SAT, VRP, HTN, LLM | ~8h |
| [Lean](#lean---verification-formelle) | 13 | 12 (92%) | Lean 4 (WSL) + Python | Proof assistant, Types dependants, LLMs | ~10h |
| [Tweety](#tweety---tweetyproject) | 10 | 9 (90%) | Python + Java/JPype | Logiques formelles, Argumentation | ~7h |
| [Argument Analysis](#argument-analysis---analyse-argumentative-llm) | 6 | 0 (demo) | Python + Java/JPype + API | Analyse argumentative multi-agents | ~3h |
| [Autres notebooks](#autres-notebooks) | 2 | 2 (100%) | .NET C# | Z3, OR-Tools | ~1h30 |

**Total** : 77 notebooks actifs, ~52h de contenu

---

## Prerequis par serie

| Serie | Kernel | Environnement special | Packages principaux | API Keys |
|-------|--------|----------------------|---------------------|----------|
| **Tweety** | Python | Java/JPype, JDK 17 | jpype1, pysat, clingo | Non |
| **Lean** | Lean 4 / Python (WSL) | WSL, elan, Lean 4 | lean4_jupyter | OPENAI_API_KEY (7-10) |
| **SemanticWeb** | .NET C# / Python | Node.js (certains) | dotNetRDF, rdflib, pySHACL | Non |
| **Planners** | Python | WSL ou Docker (Fast-Downward) | ortools, unified_planning | Non |
| **SmartContracts** | Python | Solidity/solc, Foundry | py-solc-x, web3 | OPENAI_API_KEY (8b) |
| **Argument Analysis** | Python | Java/JPype | semantic-kernel | OPENAI_API_KEY |
| **Autres** | .NET C# | Aucun | Google.OrTools, Z3.Linq | Non |

---

## Tweety - TweetyProject

Serie de **10 notebooks** sur [TweetyProject](https://tweetyproject.org/), bibliotheque Java pour l'IA symbolique. Couvre les logiques formelles, la revision de croyances, et l'argumentation computationnelle.

### Structure detaillee

| # | Notebook | Contenu | Exercices | Prerequis |
|---|----------|---------|-----------|-----------|
| **Fondations** |
| 1 | [Tweety-1-Setup](Tweety/Tweety-1-Setup.ipynb) | Configuration JVM via JPype, JARs (35 modules), outils externes | Setup | Java/JPype |
| 2 | [Tweety-2-Basic-Logics](Tweety/Tweety-2-Basic-Logics.ipynb) | Logique Propositionnelle, SAT4J, PySAT. FOL : predicats, quantificateurs | 2 | Java/JPype |
| 3 | [Tweety-3-Advanced-Logics](Tweety/Tweety-3-Advanced-Logics.ipynb) | Description Logic, Logique Modale (SPASS), QBF, Conditionnelle | 2 | Java/JPype, SPASS |
| **Revision de Croyances** |
| 4 | [Tweety-4-Belief-Revision](Tweety/Tweety-4-Belief-Revision.ipynb) | Postulats AGM, MUS, MaxSAT, mesures d'incoherence | 2 | Java/JPype |
| **Argumentation** |
| 5 | [Tweety-5-Abstract-Argumentation](Tweety/Tweety-5-Abstract-Argumentation.ipynb) | Frameworks de Dung, semantiques (grounded, preferred, stable, CF2) | 2 | Java/JPype |
| 6 | [Tweety-6-Structured-Argumentation](Tweety/Tweety-6-Structured-Argumentation.ipynb) | ASPIC+, DeLP, ABA, ASP avec Clingo | 2 | Java/JPype, Clingo |
| 7a | [Tweety-7a-Extended-Frameworks](Tweety/Tweety-7a-Extended-Frameworks.ipynb) | ADF, Bipolar, WAF, SAF, SetAF, EAF | 2 | Java/JPype |
| 7b | [Tweety-7b-Ranking-Probabilistic](Tweety/Tweety-7b-Ranking-Probabilistic.ipynb) | Ranking semantics, argumentation probabiliste | 2 | Java/JPype |
| **Applications** |
| 8 | [Tweety-8-Agent-Dialogues](Tweety/Tweety-8-Agent-Dialogues.ipynb) | Agents argumentatifs, protocoles de dialogue, loteries | 2 | Java/JPype |
| 9 | [Tweety-9-Preferences](Tweety/Tweety-9-Preferences.ipynb) | Ordres de preference, theorie du vote (Borda, Copeland) | 2 | Java/JPype |

> 9/10 notebooks ont des exercices. Seul Tweety-1-Setup (configuration) n'en a pas.

### Technologies

| Technologie | Usage |
|-------------|-------|
| **JPype** | Bridge Java/Python pour appeler les classes Tweety |
| **PySAT** | Solveurs SAT natifs Python (CaDiCaL, Glucose4, MiniSat) |
| **Clingo** | Answer Set Programming pour ABA et logiques non-monotones |
| **SPASS** | Prouveur de theoremes pour logique modale |
| **EProver** | Prouveur FOL haute performance |

Documentation complete : [Tweety/README.md](Tweety/README.md)

---

## Lean - Verification Formelle

Serie de **13 notebooks** sur **Lean 4**, proof assistant base sur la theorie des types dependants. Couvre des fondations theoriques jusqu'a l'integration des LLMs pour l'assistance automatique aux preuves.

### Structure detaillee

| # | Notebook | Kernel | Contenu | Exercices |
|---|----------|--------|---------|-----------|
| **Fondations** |
| 1 | [Lean-1-Setup](Lean/Lean-1-Setup.ipynb) | Python WSL | Diagnostic environnement, installation elan, Lean 4, lean4_jupyter | Setup |
| 2 | [Lean-2-Dependent-Types](Lean/Lean-2-Dependent-Types.ipynb) | Lean 4 | Calcul des Constructions, types, fonctions, Pi/Sigma-types, inductifs | 9 |
| 3 | [Lean-3-Propositions-Proofs](Lean/Lean-3-Propositions-Proofs.ipynb) | Lean 4 | Curry-Howard, connecteurs, preuves comme fonctions, logique classique vs constructive | 8 |
| 4 | [Lean-4-Quantifiers](Lean/Lean-4-Quantifiers.ipynb) | Lean 4 | Quantificateurs universels et existentiels, proprietes arithmetiques | 7 |
| 5 | [Lean-5-Tactics](Lean/Lean-5-Tactics.ipynb) | Lean 4 | Mode tactique, exact, intro, apply, cases, induction, rw, simp, calc | 5 |
| **Etat de l'art 2024-2026** |
| 6 | [Lean-6-Mathlib-Essentials](Lean/Lean-6-Mathlib-Essentials.ipynb) | Lean 4 | Mathlib4, tactiques puissantes (ring, linarith, omega), Loogle/Moogle | 4 |
| 7 | [Lean-7-LLM-Integration](Lean/Lean-7-LLM-Integration.ipynb) | Python WSL | AlphaProof, LeanCopilot, collaboration humain-LLM-Lean | 2 |
| 7b | [Lean-7b-Examples](Lean/Lean-7b-Examples.ipynb) | Python WSL | Exemples progressifs, comparaison OpenAI vs Anthropic, Erdos | 8 |
| 8 | [Lean-8-Agentic-Proving](Lean/Lean-8-Agentic-Proving.ipynb) | Python WSL | Agents autonomes, Harmonic Aristotle, Erdos #124 | 7 |
| 9 | [Lean-9-SK-Multi-Agents](Lean/Lean-9-SK-Multi-Agents.ipynb) | Python WSL | Semantic Kernel, 5 agents specialises, ProofState | 2 |
| 10 | [Lean-10-LeanDojo](Lean/Lean-10-LeanDojo.ipynb) | Python WSL | LeanDojo, tracing, extraction theoremes, ML pour theorem proving | 2 |
| 11 | [Lean-11-TorchLean](Lean/Lean-11-TorchLean.ipynb) | Lean 4 | Verification formelle de reseaux de neurones | 2 |
| 11py | [Lean-11-TorchLean-Python](Lean/Lean-11-TorchLean-Python.ipynb) | Python | IBP, certificats de robustesse, verification | 7 |

### Kernels requis

- **Lean 4 (WSL)** : Notebooks 2-6, 11 (preuves Lean natives)
- **Python 3 (WSL)** : Notebooks 1, 7-10, 11py (setup, LLM, LeanDojo)

> Note : Les kernels Windows ne fonctionnent pas (signal.SIGPIPE, problemes chemins)

Documentation complete : [Lean/README.md](Lean/README.md)

---

## SemanticWeb - Web Semantique

Serie de **17 notebooks** sur le Web Semantique, combinant **.NET C#** (dotNetRDF) et **Python** (rdflib). Double parcours C#/Python pour les concepts fondamentaux.

### Structure detaillee

| # | Notebook | Kernel | Contenu | Exercices |
|---|----------|--------|---------|-----------|
| **Partie 1 : Fondations RDF** |
| 1 | [SW-1-CSharp-Setup](SemanticWeb/SW-1-CSharp-Setup.ipynb) | .NET C# | Installation dotNetRDF, pile W3C "Layer Cake" | Setup |
| 2 | [SW-2-CSharp-RDFBasics](SemanticWeb/SW-2-CSharp-RDFBasics.ipynb) | .NET C# | Triplets RDF, noeuds, serialisation (Turtle, N-Triples, RDF/XML) | 6 |
| 2b | [SW-2b-Python-RDFBasics](SemanticWeb/SW-2b-Python-RDFBasics.ipynb) | Python | Equivalent Python avec rdflib | 5 |
| 3 | [SW-3-CSharp-GraphOperations](SemanticWeb/SW-3-CSharp-GraphOperations.ipynb) | .NET C# | Parsers/Writers, fusion de graphes, LINQ sur RDF | 7 |
| 4 | [SW-4-CSharp-SPARQL](SemanticWeb/SW-4-CSharp-SPARQL.ipynb) | .NET C# | Query Builder, SELECT/FILTER, OPTIONAL, UNION | 7 |
| 4b | [SW-4b-Python-SPARQL](SemanticWeb/SW-4b-Python-SPARQL.ipynb) | Python | Equivalent Python avec SPARQLWrapper | 5 |
| **Partie 2 : Donnees Liees et Ontologies** |
| 5 | [SW-5-CSharp-LinkedData](SemanticWeb/SW-5-CSharp-LinkedData.ipynb) | .NET C# | DBpedia, Wikidata, requetes federees SERVICE | 6 |
| 5b | [SW-5b-Python-LinkedData](SemanticWeb/SW-5b-Python-LinkedData.ipynb) | Python | Equivalent Python | 5 |
| 6 | [SW-6-CSharp-RDFS](SemanticWeb/SW-6-CSharp-RDFS.ipynb) | .NET C# | RDFS, inference automatique, OntologyGraph | 4 |
| 7 | [SW-7-CSharp-OWL](SemanticWeb/SW-7-CSharp-OWL.ipynb) | .NET C# | OWL 2, profils (EL/QL/RL), restrictions | 5 |
| 7b | [SW-7b-Python-OWL](SemanticWeb/SW-7b-Python-OWL.ipynb) | Python | Equivalent Python avec OWLReady2 | 5 |
| **Partie 3 : Standards Modernes (Python)** |
| 8 | [SW-8-Python-SHACL](SemanticWeb/SW-8-Python-SHACL.ipynb) | Python | SHACL, NodeShape, PropertyShape, pySHACL | 7 |
| 9 | [SW-9-Python-JSONLD](SemanticWeb/SW-9-Python-JSONLD.ipynb) | Python | JSON-LD, Schema.org, SEO | 7 |
| 10 | [SW-10-Python-RDFStar](SemanticWeb/SW-10-Python-RDFStar.ipynb) | Python | RDF 1.2, quoted triples, SPARQL-Star | 5 |
| **Partie 4 : Graphes de Connaissances et IA** |
| 11 | [SW-11-Python-KnowledgeGraphs](SemanticWeb/SW-11-Python-KnowledgeGraphs.ipynb) | Python | kglab, OWLReady2, visualisation NetworkX | 6 |
| 12 | [SW-12-Python-GraphRAG](SemanticWeb/SW-12-Python-GraphRAG.ipynb) | Python | GraphRAG, extraction entites LLM | 6 |
| 13 | [SW-13-Python-Reasoners](SemanticWeb/SW-13-Python-Reasoners.ipynb) | Python | Comparaison raisonneurs OWL (owlrl, HermiT, reasonable) | 2 (faible) |

Documentation complete : [SemanticWeb/README.md](SemanticWeb/README.md)

---

## Planners - Planification Automatique

Serie de **13 notebooks** sur la planification automatique, couvrant PDDL classique, CP-SAT (OR-Tools), VRP, planification temporelle, HTN, et integration LLM.

### Structure detaillee

| # | Notebook | Contenu | Exercices | Prerequis |
|---|----------|---------|-----------|-----------|
| **Fondations** |
| 0 | [Planners-0-Setup](Planners/00-Environment/Planners-0-Setup.ipynb) | Configuration environnement, Fast-Downward | Setup | WSL/Docker |
| 1 | [Planners-1-Introduction](Planners/01-Foundation/Planners-1-Introduction.ipynb) | Concepts de planification, representations | 5 | Python |
| 2 | [Planners-2-PDDL-Basics](Planners/01-Foundation/Planners-2-PDDL-Basics.ipynb) | Syntaxe PDDL, domaines et problemes | 4 | Fast-Downward |
| **Classique** |
| 3 | [Planners-3-State-Space](Planners/01-Foundation/Planners-3-State-Space.ipynb) | Recherche dans l'espace d'etats | 7 | Fast-Downward |
| 4 | [Planners-4-Fast-Downward](Planners/02-Classical/Planners-4-Fast-Downward.ipynb) | Fast Downward, heuristiques | 6 | Docker, Fast-Downward |
| 5 | [Planners-5-Heuristics](Planners/02-Classical/Planners-5-Heuristics.ipynb) | Heuristiques (FF, LM-Cut, Merge-and-Shrink) | 5 | Fast-Downward |
| 6 | [Planners-6-Domains](Planners/02-Classical/Planners-6-Domains.ipynb) | Catalogue de domaines PDDL | 3 | Fast-Downward |
| **Avance** |
| 7 | [Planners-7-OR-Tools](Planners/03-Advanced/Planners-7-OR-Tools.ipynb) | CP-SAT, Job Shop, VRP | 2 | ortools |
| 8 | [Planners-8-Temporal](Planners/03-Advanced/Planners-8-Temporal.ipynb) | Planification temporelle (PDDL 2.1) | 6 | Python |
| 9 | [Planners-9-HTN](Planners/03-Advanced/Planners-9-HTN.ipynb) | Hierarchical Task Networks | 7 | Python |
| **Neuro-symbolique** |
| 10 | [Planners-10-LLM-Planning](Planners/04-NeuroSymbolic/Planners-10-LLM-Planning.ipynb) | LLMs pour la planification | 2 | API keys |
| 11 | [Planners-11-Unified-Planning](Planners/04-NeuroSymbolic/Planners-11-Unified-Planning.ipynb) | Unified Planning Framework | 3 | unified_planning |
| 12 | [Planners-12-LOOP](Planners/04-NeuroSymbolic/Planners-12-LOOP.ipynb) | LLM + OR-Tools + planification | 2 | Fast-Downward |

> 12/13 notebooks ont des exercices. Seul Planners-0-Setup (configuration) n'en a pas.

Documentation complete : [Planners/README.md](Planners/README.md)

---

## SmartContracts - Blockchain et Contrats Intelligents

Serie de **27 notebooks** sur les smart contracts et la blockchain, organisee en 7 modules progressifs couvrant Solidity, DeFi, DAO, verification formelle, cryptographie, et les ecosystemes alternatifs (Move, Solana, Bitcoin, Vyper).

### Structure detaillee

| Module | Notebooks | Contenu |
|--------|-----------|---------|
| **00-Foundations** | SC-0 (Cypherpunk Origins), SC-1 (Setup Foundry), SC-2 (Setup Web3py) | Histoire blockchain, configuration environnement |
| **01-Solidity-Foundation** | SC-3 (Basics), SC-4 (Functions/State), SC-5 (Inheritance), SC-6 (Errors/Events) | Fondations Solidity avec code executable (compile_and_deploy) |
| **02-Solidity-Advanced** | SC-7 (Token Standards), SC-8 (DeFi), SC-9 (DAO), SC-10 (Account Abstraction), SC-11 (LLM-Assisted) | ERC-20/721, DeFi, gouvernance, audit LLM |
| **03-Foundry-Testing** | SC-12 (Foundry Testing), SC-13 (Fuzz/Invariants), SC-14 (Formal Verification) | Tests unitaires, fuzz testing, verification formelle |
| **04-Privacy-Cryptography** | SC-15 (ZK Proofs), SC-16 (Homomorphic Encryption), SC-17 (E2E Voting) | Zero-knowledge, chiffrement homomorphe, vote verifiable |
| **05-Alternative-Chains** | SC-18 (Vyper), SC-19 (Ripple), SC-20 (Bitcoin), SC-21 (Move/Sui), SC-22 (Solana) | Ecosystemes alternatifs |
| **06-Real-World** | SC-23 (Cross-Chain), SC-24 (Testnet), SC-25 (Mainnet), SC-26 (Final Project) | Deploiement, interoperabilite, projet final |

Documentation complete : [SmartContracts/README.md](SmartContracts/README.md)

---

## Argument Analysis - Analyse Argumentative LLM

Pipeline d'analyse argumentative multi-agents avec **Semantic Kernel** et LLMs. Combine detection de sophismes, formalisation logique, et validation par TweetyProject.

> **Note** : Cette serie est un projet/demo, pas un cours. Aucun exercice etudiant. Non adaptee en l'etat pour EPITA.

### Structure detaillee

| # | Notebook | Role |
|---|----------|------|
| 0 | [Agentic-0-init](Argument_Analysis/Argument_Analysis_Agentic-0-init.ipynb) | Configuration LLM, JPype/Tweety, ProjectManagerAgent |
| 1 | [Agentic-1-informal_agent](Argument_Analysis/Argument_Analysis_Agentic-1-informal_agent.ipynb) | InformalAnalysisAgent, detection sophismes |
| 2 | [Agentic-2-pl_agent](Argument_Analysis/Argument_Analysis_Agentic-2-pl_agent.ipynb) | PropositionalLogicAgent, formalisation PL |
| 3 | [Agentic-3-orchestration](Argument_Analysis/Argument_Analysis_Agentic-3-orchestration.ipynb) | Orchestration multi-agents |
| 4 | [Executor](Argument_Analysis/Argument_Analysis_Executor.ipynb) | Pipeline complet, rapport JSON |
| 5 | [UI_configuration](Argument_Analysis/Argument_Analysis_UI_configuration.ipynb) | Interface widgets ipywidgets |

Documentation complete : [Argument_Analysis/README.md](Argument_Analysis/README.md)

---

## Autres Notebooks

### Optimisation et Contraintes (2 notebooks)

| Notebook | Kernel | Contenu | Exercices |
|----------|--------|---------|-----------|
| [OR-tools-Stiegler](OR-tools-Stiegler.ipynb) | .NET C# | Probleme de Stigler, programmation lineaire avec OR-Tools | 2 |
| [Linq2Z3](Linq2Z3.ipynb) | .NET C# | SMT avec LINQ, Z3.Linq, Missionnaires et Cannibales | 1 |

---

## Structure du Repertoire

```
SymbolicAI/
├── Tweety/                    # Serie TweetyProject (9 notebooks)
│   ├── Tweety-1-Setup.ipynb ... Tweety-9-Preferences.ipynb
│   ├── tweety_init.py         # Module d'initialisation partage
│   ├── libs/                  # JARs TweetyProject (35 modules)
│   ├── ext_tools/             # Clingo, SPASS, EProver
│   └── README.md
│
├── Lean/                      # Serie Lean 4 (13 notebooks)
│   ├── Lean-1-Setup.ipynb ... Lean-11-TorchLean-Python.ipynb
│   ├── lean_runner.py         # Backend Python multi-mode
│   ├── scripts/               # Installation, validation WSL
│   └── README.md
│
├── SemanticWeb/               # Web semantique (17 notebooks)
│   ├── SW-1-CSharp-Setup.ipynb ... SW-13-Python-Reasoners.ipynb
│   ├── data/                 # Fichiers RDF, OWL, SHACL, JSON-LD
│   ├── RDF.Net-Legacy/      # Notebook original (reference historique)
│   └── README.md
│
├── Planners/                  # Planification automatique (13 notebooks)
│   ├── 00-Environment/       # Setup
│   ├── 01-Foundation/        # Introduction, PDDL Basics, State Space
│   ├── 02-Classical/         # State Space, Fast-Downward, Heuristics, Domains
│   ├── 03-Advanced/          # OR-Tools, Temporal, HTN
│   ├── 04-NeuroSymbolic/     # LLM-Planning, Unified-Planning, LOOP
│   └── README.md
│
├── SmartContracts/            # Blockchain et smart contracts (27 notebooks)
│   ├── 00-Foundations/        # SC-0 a SC-2 (Origins, Setup)
│   ├── 01-Solidity-Foundation/ # SC-3 a SC-6 (Basics, Functions, Inheritance, Events)
│   ├── 02-Solidity-Advanced/  # SC-7 a SC-11 (Tokens, DeFi, DAO, AA, LLM)
│   ├── 03-Foundry-Testing/    # SC-12 a SC-14 (Testing, Fuzz, Formal)
│   ├── 04-Privacy-Cryptography/ # SC-15 a SC-17 (ZK, HE, Voting)
│   ├── 05-Alternative-Chains/ # SC-18 a SC-22 (Vyper, XRP, BTC, Move, Solana)
│   ├── 06-Real-World/         # SC-23 a SC-26 (Cross-chain, Deploy, Project)
│   └── README.md
│
├── Argument_Analysis/         # Analyse argumentative (6 notebooks, demo)
│   ├── Argument_Analysis_Agentic-0-init.ipynb ... UI_configuration.ipynb
│   └── README.md
│
├── OR-tools-Stiegler.ipynb    # Optimisation LP
├── Linq2Z3.ipynb              # SMT LINQ
│
├── scripts/                   # Scripts utilitaires
├── archive/                   # Versions historiques
├── data/                      # Donnees partagees
├── ext_tools/                 # Outils externes partages
├── libs/                      # Bibliotheques partagees
├── reports/                   # Rapports de qualite
└── README.md                  # Ce fichier
```

---

## Installation

### Prerequis communs

```bash
# Python 3.10+
pip install jupyter ipykernel

# Pour notebooks .NET (C#)
dotnet tool install -g Microsoft.dotnet-interactive
dotnet interactive jupyter install
```

### Par serie

| Serie | Installation | Environnement special |
|-------|--------------|----------------------|
| **Tweety** | Executer `Tweety-1-Setup.ipynb` | JDK 17 + JARs (auto-telecharges) |
| **Lean** | Executer `Lean-1-Setup.ipynb` sous WSL | elan + Lean 4 + lean4_jupyter |
| **Lean (LLM)** | Configurer `.env` avec `OPENAI_API_KEY` | Notebooks 7-10 |
| **SemanticWeb (.NET)** | `dotnet restore MyIA.CoursIA.sln` | dotNetRDF via NuGet |
| **SemanticWeb (Python)** | `pip install -r SemanticWeb/requirements.txt` | rdflib, pySHACL |
| **Planners** | `pip install ortools unified-planning` | Fast-Downward via WSL ou Docker |
| **SmartContracts** | `pip install py-solc-x web3` | Solidity/solc, optionnel: Foundry |
| **Argument Analysis** | Configurer `.env` avec `OPENAI_API_KEY` | Java/JPype |
| **Autres** | `dotnet restore MyIA.CoursIA.sln` | OR-Tools, Z3 via NuGet |

---

## Outils Externes

| Outil | Usage | Series |
|-------|-------|--------|
| **JPype** | Bridge Java/Python | Tweety, Argument Analysis |
| **PySAT** | Solveurs SAT natifs | Tweety |
| **Clingo** | Answer Set Programming | Tweety |
| **SPASS / EProver** | Prouveurs de theoremes | Tweety |
| **Z3** | SMT solver | Tweety, Linq2Z3 |
| **elan / Lean 4** | Proof assistant | Lean |
| **Mathlib4** | Bibliotheque maths Lean | Lean |
| **Semantic Kernel** | Orchestration LLM | Argument Analysis, Lean |
| **OR-Tools** | Optimisation, CP-SAT, VRP | OR-Tools, Planners |
| **Fast Downward** | Planification PDDL | Planners |
| **dotNetRDF** | RDF/SPARQL .NET | SemanticWeb |
| **rdflib** | RDF/SPARQL Python | SemanticWeb |
| **pySHACL** | Validation SHACL | SemanticWeb |
| **Solidity/solc** | Smart contracts | SmartContracts |
| **Foundry** | Test framework Solidity | SmartContracts |

---

## Audit Qualite (mars 2026)

### Couverture exercices (audit 20 mars 2026)

| Serie | Notebooks | Avec exercices | Sans exercices | Status |
|-------|-----------|----------------|----------------|--------|
| SmartContracts | 26 | 26 (100%) | 0 | Complet |
| SemanticWeb | 17 | 16 (94%) | 1 (Setup) | Complet |
| Lean | 13 | 12 (92%) | 1 (Setup) | Complet |
| Planners | 13 | 12 (92%) | 1 (Setup) | Complet |
| Tweety | 10 | 9 (90%) | 1 (Setup) | Complet |
| Argument Analysis | 6 | 0 (0%) | 6 (demo) | N/A |

**Total** : 65/79 notebooks de contenu avec exercices (82%). Les seuls notebooks sans exercices sont les notebooks de setup/configuration (attendu) et la serie demo Argument Analysis.

### Problemes restants

- **Lean-11-TorchLean** : 11 code cells sans outputs (kernel lean4 natif, erreurs PyTorch dtype)
- **SmartContracts** : Certains notebooks sans section prerequis dans le header

---

## Ressources

### TweetyProject
- Site officiel : https://tweetyproject.org/
- GitHub : https://github.com/TweetyProjectTeam/TweetyProject

### Lean 4
- Theorem Proving in Lean 4 : https://leanprover.github.io/theorem_proving_in_lean4/
- Mathlib4 : https://leanprover-community.github.io/mathlib4_docs/
- LeanDojo : https://leandojo.readthedocs.io/

### Autres
- OR-Tools : https://developers.google.com/optimization
- Z3 : https://github.com/Z3Prover/z3
- dotNetRDF : https://dotnetrdf.org/
- Fast Downward : https://www.fast-downward.org/
- Solidity : https://docs.soliditylang.org/

---

## Licence

Les notebooks sont distribues sous licence MIT.
Voir LICENSE a la racine du depot pour details.

---

**Derniere mise a jour** : 2026-03-20
