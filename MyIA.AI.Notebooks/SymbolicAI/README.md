# SymbolicAI - Intelligence Artificielle Symbolique

<!-- CATALOG-STATUS
series: SymbolicAI
pedagogical_count: 92
breakdown: SmartContracts=27, SemanticWeb=18, Lean=14, Planners=13, Tweety=10, Argument_Analysis=6, =2, SymbolicLearning=2
maturity: BETA=77, ALPHA=7, PRODUCTION=7, DRAFT=1
-->

L'intelligence artificielle n'est pas qu'apprentissage automatique et réseaux de neurones. Une grande partie de l'IA classique repose sur le **raisonnement symbolique** : représenter la connaissance sous forme de propositions, de règles et de structures logiques, puis dériver mécaniquement de nouvelles conclusions. C'est cette tradition — des systèmes experts des années 80 aux assistants de preuve modernes comme Lean 4 — que cette série explore en profondeur.

Vous y découvrirez six domaines complémentaires. Le **Web Sémantique** (RDF, SPARQL, OWL) montre comment structurer les connaissances du web pour les rendre exploitables par les machines. La **vérification formelle** avec Lean 4 vous apprend à écrire des preuves mathématiques vérifiées par un ordinateur. L'**argumentation computationnelle** (TweetyProject) modélise le débat et la délibération. La **planification automatique** résout des problèmes concrets de logistique et d'ordonnancement. Les **smart contracts** relient la cryptographie et la logique formelle aux blockchains. Et l'**analyse argumentative** avec les LLMs ponte l'IA symbolique et l'IA neuronale. Chaque sous-série est autonome, mais ensemble elles dessinent une vision cohérente de l'IA symbolique moderne.

**À qui s'adresse cette série** : étudiants en IA, ingénieurs logiciel curieux de logique formelle, et chercheurs souhaitant aller au-delà du machine learning. Les notebooks Python (Tweety, Planners, SmartContracts, SemanticWeb Python) ne nécessitent que Python 3.10+. Les notebooks .NET C# (SemanticWeb, optimisation) requièrent .NET 9.0 + dotnet-interactive. Les notebooks Lean nécessitent WSL + elan. Aucun prérequis en logique avancée : chaque série introduit ses concepts progressivement depuis les fondements.

## Parcours d'apprentissage

### Phase 1 : Logique et argumentation (Tweety, ~7h)

Le parcours commence par Tweety-1-Setup qui configure l'environnement Java/JPype et charge les 35 modules TweetyProject. Les notebooks 2-3 introduisent les logiques formelles (propositionnelle, premier ordre, modale, description) avec des solveurs SAT et des prouveurs de théorèmes. Les notebooks 4-7 couvrent la révision de croyances (postulats AGM), l'argumentation abstraite (sémantiques de Dung), l'argumentation structurée (ASPIC+, ABA, ASP avec Clingo), et les extensions (bipolaire, probabiliste). Les notebooks 8-9 appliquent ces théories aux dialogues d'agents et aux préférences collectives. À l'issue de cette phase, vous maîtrisez les formalismes de base du raisonnement symbolique et pouvez implémenter des systèmes argumentatifs.

### Phase 2 : Représentation de connaissances (SemanticWeb, ~13h)

Le Web Sémantique généralise les concepts logiques de la Phase 1 au web. Les notebooks 1-4 (C# et Python) couvrent RDF (triplets, graphes, sérialisation) et SPARQL (requêtes, filtres, unions). Les notebooks 5-7 abordent les données liées (DBpedia, Wikidata), RDFS (inférence), et OWL (ontologies, profils EL/QL/RL). Les notebooks 8-10 introduisent les standards modernes : SHACL (validation), JSON-LD (SEO), RDF-Star (métadonnées sur métadonnées). Les notebooks 11-12 ferment la boucle avec les graphes de connaissances et GraphRAG (extraction d'entités par LLM). Cette phase présuppose les bases logiques de la Phase 1 mais peut être suivie indépendamment.

### Phase 3 : Vérification formelle (Lean, ~10h)

La série Lean 4 passe de la théorie à la pratique de la preuve formelle. Les notebooks 1-5 posent les fondations : types dépendants, Curry-Howard, quantificateurs, mode tactique. Les notebooks 6-10 explorent l'état de l'art 2024-2026 : Mathlib4, intégration LLM (AlphaProof, LeanCopilot), agents autonomes (Harmonic, Erdos), et Semantic Kernel multi-agents. Les notebooks 11-11py relient la vérification formelle au machine learning (certificats de robustesse pour réseaux de neurones), et le notebook 12 porte le théorème de sensibilité de Huang (2019) en Lean 4. Cette phase est la plus exigeante techniquement (WSL obligatoire, concepts mathématiques avancés) mais aussi la plus innovante.

### Phase 4 : Applications (Planners + SmartContracts, ~30h)

Deux séries applicatives indépendantes exploitent les formalismes des phases précédentes. La **planification automatique** (13 notebooks) couvre PDDL, Fast-Downward, CP-SAT (OR-Tools), planification temporelle, HTN, et l'intégration LLM pour la génération de plans. Les **smart contracts** (27 notebooks) constituent la plus longue sous-série : Solidity fondamental, DeFi (ERC-20/721, swaps, liquidités), DAO, vérification formelle (Foundry fuzz/invariants), cryptographie avancée (ZK proofs, chiffrement homomorphe, vote vérifiable), écosystèmes alternatifs (Move, Solana, Bitcoin, Vyper), et déploiement mainnet. Chaque série est autonome mais enrichie par les phases 1-3.

### Parcours alternatif : Pont LLM (Argument Analysis, ~4h)

Si vous vous intéressez au croisement IA symbolique / IA neuronale, la série Argument Analysis (6 notebooks) implémente un pipeline multi-agents avec Semantic Kernel : détection de sophismes par LLM, formalisation en logique propositionnelle, et validation par TweetyProject. C'est une démo concrète du pont entre les deux paradigmes, présupposant les bases de Tweety (Phase 1) et un accès API OpenAI.

## Vue d'ensemble

| Serie | Notebooks | Exercices | Environnement | Theme | Duree |
|-------|-----------|-----------|---------------|-------|-------|
| [SemanticWeb](#semanticweb---web-semantique) | 18 | 16 (89%) | .NET C# + Python | RDF, SPARQL, OWL, SHACL, GraphRAG | ~13h |
| [SmartContracts](#smartcontracts---blockchain-et-contrats-intelligents) | 27 | 27 (100%) | Python + Solidity/Foundry | Solidity, DeFi, DAO, ZK, Multi-chain | ~22h |
| [Planners](#planners---planification-automatique) | 13 | 12 (92%) | Python + Fast-Downward (WSL/Docker) | PDDL, CP-SAT, VRP, HTN, LLM | ~8h |
| [Lean](#lean---verification-formelle) | 14 | 13 (93%) | Lean 4 (WSL) + Python | Proof assistant, Types dependants, LLMs | ~10h |
| [Tweety](#tweety---tweetyproject) | 10 | 10 (100%) | Python + Java/JPype | Logiques formelles, Argumentation | ~7h |
| [Argument Analysis](#argument-analysis---analyse-argumentative-llm) | 6 | 0 (demo) | Python + Java/JPype + API | Analyse argumentative multi-agents | ~4h |
| [Autres notebooks](#autres-notebooks) | 2 | 2 (100%) | .NET C# | Z3, OR-Tools | ~1h30 |

**Total** : 90 notebooks actifs, ~56h de contenu

---

## Quick Start

**Premier notebook recommande par serie :**

| Serie | Premier notebook | Commande rapide |
|-------|-----------------|-----------------|
| **Tweety** | `Tweety/Tweety-1-Setup.ipynb` | Ouvrir dans Jupyter, executer toutes les cellules |
| **Lean** | `Lean/Lean-1-Setup.ipynb` | `wsl -d Ubuntu -- bash -c "jupyter notebook Lean-1-Setup.ipynb"` |
| **SemanticWeb** | `SemanticWeb/SW-1-CSharp-Setup.ipynb` (.NET) ou `SW-2b-Python-RDFBasics.ipynb` (Python) | `pip install rdflib pySHACL` |
| **Planners** | `Planners/00-Environment/Planners-0-Setup.ipynb` | `pip install ortools unified_planning` |
| **SmartContracts** | `SmartContracts/00-Foundations/SC-0-Cypherpunk-Origins.ipynb` | `pip install py-solc-x web3` |
| **Argument Analysis** | `Argument_Analysis/Argument_Analysis_Agentic-0-init.ipynb` | `pip install semantic-kernel jpype1` + `.env` |

**Pour commencer sans rien installer** : les notebooks Python (Tweety, Planners, SemanticWeb Python, SmartContracts) ne necessitent que `pip install jupyter ipykernel` + les packages listes ci-dessus.

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
| 9 | [Tweety-9-Preferences](Tweety/Tweety-9-Preferences.ipynb) | Ordres de preference, theorie du vote (Borda, Copeland) | 1 | Java/JPype |

> 10/10 notebooks ont des exercices. La configuration de Tweety-1-Setup constitue l'exercice setup de la serie.

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

Serie de **14 notebooks** sur **Lean 4**, proof assistant base sur la theorie des types dependants. Couvre des fondations theoriques jusqu'a l'integration des LLMs pour l'assistance automatique aux preuves.

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
| 12 | [Lean-12-Sensitivity-Theorem](Lean/Lean-12-Sensitivity-Theorem.ipynb) | Lean 4 | Port Lean du theoreme de sensibilite de Huang (2019), hypercube, signing matrix | 4 |

### Kernels requis

- **Lean 4 (WSL)** : Notebooks 2-6, 11, 12 (preuves Lean natives)
- **Python 3 (WSL)** : Notebooks 1, 7-10, 11py (setup, LLM, LeanDojo)

> Note : Les kernels Windows ne fonctionnent pas (signal.SIGPIPE, problemes chemins)

Documentation complete : [Lean/README.md](Lean/README.md)

---

## SemanticWeb - Web Semantique

Serie de **18 notebooks** sur le Web Semantique (dont 1 legacy deprecie), combinant **.NET C#** (dotNetRDF) et **Python** (rdflib). Double parcours C#/Python pour les concepts fondamentaux.

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
| **Bonus** | [SW-13-Python-Reasoners](SemanticWeb/SW-13-Python-Reasoners.ipynb) | Python | Comparaison raisonneurs OWL (owlrl, HermiT, reasonable) | 3 (faible) |

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
├── Tweety/                    # Serie TweetyProject (10 notebooks)
│   ├── Tweety-1-Setup.ipynb ... Tweety-9-Preferences.ipynb
│   ├── tweety_init.py         # Module d'initialisation partage
│   ├── libs/                  # JARs TweetyProject (35 modules)
│   ├── ext_tools/             # Clingo, SPASS, EProver
│   └── README.md
│
├── Lean/                      # Serie Lean 4 (14 notebooks)
│   ├── Lean-1-Setup.ipynb ... Lean-12-Sensitivity-Theorem.ipynb
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

# Pour notebooks .NET (C#) -- ATTENTION: Windows policy peut bloquer dotnet-interactive.exe
dotnet tool install -g Microsoft.dotnet-interactive
dotnet interactive jupyter install
```

> **Windows Policy** : Si `dotnet-interactive.exe` est bloque (Win32Exception 4551), executer en admin PowerShell :
> `Set-ExecutionPolicy -Scope CurrentUser RemoteSigned` puis relancer.

### Tweety

**Status execution : 10/10 SUCCESS**

Le setup est entierement automatise via `Tweety-1-Setup.ipynb` :

1. **JDK 17 portable** : Auto-telecharge dans `Tweety/jdk-17-portable/` (Azul Zulu, ~180MB). Aucune installation systeme requise, pas de UAC.
2. **JARs TweetyProject** : Auto-telecharges dans `Tweety/libs/` depuis Maven Central (35 modules, ~50MB total).
3. **Outils externes** : Clingo, SPASS, EProver dans `Tweety/ext_tools/` (inclus dans le depot).

**Problemes connus :**
- `asp-1.30.jar` et `rpcl-1.30.jar` : Modules absents de Maven Central pour la version 1.30. Non bloquant -- les notebooks gerent l'absence avec try/except.
- Si un JAR fait 0 bytes ou ~554 bytes : re-telecharger manuellement depuis `https://repo1.maven.org/maven2/org/tweetyproject/`.

### Planners

**Status execution : 13/14 SUCCESS** (Fast-Downward-Legacy.ipynb echoue -- kernel .NET bloque)

1. **Packages Python** : `pip install ortools unified_planning`
2. **Fast-Downward** (requis pour notebooks 2-6, 12) : Installer via WSL ou Docker
   - WSL : `sudo apt install fast-downward` ou compiler depuis source
   - Docker : Image `aiblazor/fast-downward` disponible
3. **Notebooks theoriques** (7-11) : Ne necessitent que Python + les packages ci-dessus

### SmartContracts

**Status execution : 15/27 (avec anvil lance : 25/27)**

1. **Kernel Jupyter** : Enregistrer le kernel custom :
   ```bash
   python -m ipykernel install --user --name smartcontracts --display-name "Python (SmartContracts + Foundry)"
   ```
2. **Foundry** (requis pour SC-12 a SC-14) : Installer dans WSL :
   ```bash
   # Dans WSL Ubuntu
   curl -L https://foundry.paradigm.xyz | bash
   source ~/.bashrc
   foundryup
   ```
   Versions testees : forge/cast/anvil/chisel 1.5.1-stable
3. **Solidity** : `pip install py-solc-x web3` -- solc auto-installe par py-solc-x
4. **Anvil** (requis pour SC-3 a SC-10) : Lancer avant l'execution :
   ```bash
   # Dans un terminal WSL
   anvil --host 0.0.0.0
   ```
   Ou en arriere-plan : `wsl -d Ubuntu -- bash -c 'anvil --host 0.0.0.0 &'`
5. **Fichier `.env`** : Configurer dans `SmartContracts/.env` :
   - `ANVIL_RPC=http://127.0.0.1:8545` (local)
   - `LLM_API_KEY` pour SC-11 (via OpenRouter)
   - `DEPLOYER_PRIVATE_KEY` : Mettre une cle de testnet reelle pour SC-24/25, ou laisser le placeholder (ces notebooks echoueront)

**Problemes connus :**
- **SC-3 a SC-10** : Echouent si anvil n'est pas lance sur le port 8545. Solution : lancer `anvil` avant l'execution.
- **SC-15 Zero-Knowledge-Proofs** : SyntaxError f-string imbriquee (`{"CONVAINCU" if ...}`) -- incompatible Python 3.11. Fix : utiliser des parentheses ou une variable intermediaire.
- **SC-24/25** : `hexstr_to_bytes` erreur si `DEPLOYER_PRIVATE_KEY` contient un placeholder non-hex.

### Argument_Analysis

**Status execution : 3/5 (demo, pas cours etudiant)**

1. **JDK 17 portable** : Partage avec Tweety (meme `jdk-17-portable/` si configure)
2. **Fichier `.env`** : Configurer dans `Argument_Analysis/.env` :
   - `OPENAI_API_KEY` (via OpenRouter : `sk-or-v1-...`)
   - `OPENAI_BASE_URL=https://openrouter.ai/api/v1`
   - `TEXT_CONFIG_PASSPHRASE=Propaganda`
   - `BATCH_MODE=true`
3. **Packages** : `pip install semantic-kernel jpype1`

**Problemes connus :**
- **AA-3 orchestration** : Papermill ne preserve pas l'etat entre notebooks. Les definitions de AA-0/1/2 ne sont pas disponibles. Ce notebook doit etre execute manuellement apres les 3 precedents.
- **AA Executor** : Timeout a 300s (pipeline multi-agents long).

### Lean

**Status execution : NON TESTE (WSL kernel timeout)**

1. **WSL obligatoire** : Les notebooks Lean ne fonctionnent pas sous Windows natif (SIGPIPE, problemes de chemins)
2. **Installation** : Executer `Lean-1-Setup.ipynb` sous WSL (installe elan + Lean 4 + lean4_jupyter)
3. **Kernels** :
   - `Lean 4 (WSL)` : Notebooks 2-6, 11 (preuves natives)
   - `Python 3 (WSL)` : Notebooks 1, 7-10, 11py (setup, LLM, LeanDojo)
4. **Fichier `.env`** (pour notebooks 7-10) : `OPENAI_API_KEY` via OpenRouter

### SemanticWeb

**Python : 10/10 SUCCESS | C# : 0/7 (Windows policy)**

1. **Python** : `pip install rdflib pySHACL owlready2 kglab` -- tous les notebooks Python passent
2. **C#** : `dotnet restore MyIA.CoursIA.sln` -- necessite dotnet-interactive fonctionnel
3. **Win32Exception 4551** : Windows peut bloquer dotnet-interactive.exe. Fix admin PowerShell :
   `Set-ExecutionPolicy -Scope CurrentUser RemoteSigned`

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
| SmartContracts | 27 | 27 (100%) | 0 | Complet |
| SemanticWeb | 18 | 16 (89%) | 2 (Setup + Legacy) | Complet |
| Lean | 14 | 13 (93%) | 1 (Setup) | Complet |
| Planners | 13 | 12 (92%) | 1 (Setup) | Complet |
| Tweety | 10 | 10 (100%) | 0 | Complet |
| Argument Analysis | 6 | 0 (0%) | 6 (demo) | N/A |

**Total** : 78/88 notebooks de contenu avec exercices (89%). Les notebooks sans exercices sont les notebooks de setup/configuration (SW-1, Planners-0, Lean-1), le notebook legacy deprecie (RDF.Net) et la serie demo Argument Analysis (6 notebooks).

### Problemes restants

- **Lean-11-TorchLean** : 11 code cells sans outputs (kernel lean4 natif, erreurs PyTorch dtype)
- **SmartContracts** : Certains notebooks sans section prerequis dans le header

---

## Ponts cross-series

Ces connexions entre series sont exploitees dans le curriculum EPITA IA Symbolique (demarrage 18/05/2026).

### Lean <-> GameTheory (Choix social)

| Concept Lean | Concept GameTheory | Notebooks |
|-------------|-------------------|-----------|
| Theoreme d'Arrow (preuve formelle) | Theorie du vote / Choix social | `Lean/social_choice_lean/Arrow.lean` <-> `GameTheory/16b-Social-Choice.ipynb` |
| Theoreme de Sen (preuve formelle) | Impossibilite Pareto liberal | `Lean/social_choice_lean/Sen.lean` <-> `GameTheory/16c-Sen.ipynb` |
| Valeur de Shapley (preuve formelle) | Coalitions, jeux cooperatifs | `Lean/social_choice_lean/Shapley.lean` <-> `GameTheory/16d-Shapley.ipynb` |

### Lean <-> SmartContracts (Verification formelle)

| Concept | Pont | Notebooks |
|---------|------|-----------|
| Theorie des types dependants | Verification formelle de contrats | `Lean/Lean-1-Setup.ipynb` (types) <-> `SmartContracts/04-Privacy-Cryptography/SC-14-Formal-Verification.ipynb` |
| Preuves LLM-assistees | Contrats LLM-assistes | `Lean/Lean-8-Agentic-Proving.ipynb` <-> `SmartContracts/02-Solidity-Advanced/SC-11-LLM-Assisted.ipynb` |
| `sorry` = axiome non prouve | Bugs de contrats non detectes | Concepts paralleles d'incompletude |

### Tweety <-> Argument_Analysis (Argumentation)

| Concept Tweety | Concept Argument_Analysis | Notebooks |
|---------------|--------------------------|-----------|
| Frameworks de Dung | Argumentation multi-agents | `Tweety/Tweety-5-Abstract-Argumentation.ipynb` <-> `Argument_Analysis/Argument_Analysis_Agentic-0-init.ipynb` |
| ASPIC+ (argumentation structuree) | Analyse LLM d'arguments | `Tweety/Tweety-6-Structured-Argumentation.ipynb` <-> `Argument_Analysis/Argument_Analysis_3-Frameworks.ipynb` |
| Dialogues d'agents | Debate multi-agent | `Tweety/Tweety-8-Agent-Dialogues.ipynb` <-> `Argument_Analysis/Argument_Analysis_4-MultiAgent.ipynb` |

### SemanticWeb <-> SmartContracts (Decentralisation)

| Concept | Pont | Notebooks |
|---------|------|-----------|
| Ontologies RDF/OWL | Gouvernance DAO (etat canonique) | `SemanticWeb/SW-6-OWL.ipynb` <-> `SmartContracts/01-Solidity-Foundation/SC-9-DAO-Governance.ipynb` |
| GraphRAG | Indexation on-chain | `SemanticWeb/SW-12-GraphRAG.ipynb` <-> SmartContracts DeFi indexing |
| SHACL (validation) | Smart contract verification | `SemanticWeb/SW-9-SHACL.ipynb` <-> `SmartContracts/04-Privacy-Cryptography/SC-14-Formal-Verification.ipynb` |

### Planners <-> SmartContracts (Coordination)

| Concept | Pont | Notebooks |
|---------|------|-----------|
| Planification multi-agent | MEV / auctions cross-chain | `Planners/03-Advanced/Planners-9-HTN.ipynb` <-> SmartContracts MEV |
| CP-SAT (OR-Tools) | Optimisation gas/fees | `Planners/03-Advanced/Planners-7-OR-Tools.ipynb` <-> `SmartContracts/01-Solidity-Foundation/SC-8-Gas-Optimization.ipynb` |

---

## Ressources

### References academiques

| Domaine | Reference | Couverture |
|---------|-----------|------------|
| IA Symbolique (general) | Russell & Norvig, *AIMA* 4e ed., ch. 7-12 | Recherche, logique, planification |
| Theorie des jeux / choix social | Osborne & Rubinstein, *A Course in Game Theory* (1994) | GameTheory, Lean social choice |
| Logiques formelles | Enderton, *A Mathematical Introduction to Logic* (2001) | Tweety, Lean |
| Argumentation | Dung, "On the Acceptability of Arguments" (1995) | Tweety-5, Argument Analysis |
| Argumentation structuree | Modgil & Prakken, "The ASPIC+ Framework" (2014) | Tweety-6 |
| Revision de croyances | Alchourron, Gardenfors & Makinson, "On the Logic of Theory Change" (1985) | Tweety-4 |
| Web semantique | Berners-Lee et al., "The Semantic Web", *Scientific American* (2001) | SemanticWeb |
| RDF/SPARQL | W3C RDF 1.1 Primer, https://www.w3.org/TR/rdf11-primer/ | SemanticWeb |
| Planification automatique | Ghallab, Nau & Traverso, *Automated Planning: Theory and Practice* (2004) | Planners |
| Planification PDDL | Helmert, "The Fast Downward Planning System" (2006) | Planners-4 |
| Lean 4 | de Moura & Ullrich, "The Lean 4 Theorem Prover" (2021) | Lean |
| Mathlib4 | The Mathlib Community, "The Mathlib Library" (2020) | Lean-6 |
| Smart contracts | Buterin, "Ethereum White Paper" (2014) | SmartContracts |
| Verification formelle | Appel, "Verification of a Cryptographic Primitive: SHA-256" (2015) | SC-14 |
| Zero-knowledge | Ben-Sasson et al., "Scalable Zero Knowledge" (2014) | SC-15 |

### Ressources en ligne

| Ressource | URL |
|-----------|-----|
| TweetyProject | https://tweetyproject.org/ |
| Lean 4 - Theorem Proving | https://leanprover.github.io/theorem_proving_in_lean4/ |
| Mathlib4 docs | https://leanprover-community.github.io/mathlib4_docs/ |
| LeanDojo | https://leandojo.readthedocs.io/ |
| OR-Tools | https://developers.google.com/optimization |
| Z3 Prover | https://github.com/Z3Prover/z3 |
| dotNetRDF | https://dotnetrdf.org/ |
| Fast Downward | https://www.fast-downward.org/ |
| Solidity docs | https://docs.soliditylang.org/ |
| W3C RDF 1.1 | https://www.w3.org/TR/rdf11-primer/ |
| Foundry Book | https://book.getfoundry.sh/ |

---

## Licence

Les notebooks sont distribues sous licence MIT.
Voir LICENSE a la racine du depot pour details.

---

**Derniere mise a jour** : 2026-05-19
