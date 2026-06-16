# SymbolicAI - Intelligence Artificielle Symbolique

[← Notebooks](../README.md) | [↑ ..](../README.md) | [→ Sudoku](../Sudoku/README.md)

<!-- CATALOG-STATUS
series: SymbolicAI
pedagogical_count: 127
breakdown: SmartContracts=27, Lean=24, SemanticWeb=18, Planners=13, SMT=13, Argument_Analysis=11, SymbolicLearning=10, Tweety=10, root=1
maturity: PRODUCTION=122, BETA=4, ALPHA=1
-->

L'intelligence artificielle n'est pas qu'apprentissage automatique et réseaux de neurones. Une grande partie de l'IA classique repose sur le **raisonnement symbolique** : représenter la connaissance sous forme de propositions, de règles et de structures logiques, puis dériver mécaniquement de nouvelles conclusions. C'est cette tradition — des systèmes experts des années 80 aux assistants de preuve modernes comme Lean 4 — que cette série explore en profondeur.

Vous y découvrirez sept domaines complémentaires. Le **Web Sémantique** (RDF, SPARQL, OWL) montre comment structurer les connaissances du web pour les rendre exploitables par les machines. La **vérification formelle** avec Lean 4 vous apprend à écrire des preuves mathématiques vérifiées par un ordinateur. L'**argumentation computationnelle** (TweetyProject) modélise le débat et la délibération. La **planification automatique** résout des problèmes concrets de logistique et d'ordonnancement. Les **smart contracts** relient la cryptographie et la logique formelle aux blockchains. L'**analyse argumentative** avec les LLMs jette un pont entre l'IA symbolique et l'IA neuronale. Et l'**apprentissage symbolique** (AIMA ch. 19) montre comment un agent apprend à partir de connaissances existantes plutôt que de données brutes, jusqu'aux pipelines neuro-symboliques couplés aux LLMs. Chaque sous-série est autonome, mais ensemble elles dessinent une vision cohérente de l'IA symbolique moderne.

**À qui s'adresse cette série** : étudiants en IA, ingénieurs logiciel curieux de logique formelle, et chercheurs souhaitant aller au-delà du machine learning. Les notebooks Python (Tweety, Planners, SmartContracts, SemanticWeb Python, SymbolicLearning) ne nécessitent que Python 3.10+. Les notebooks .NET C# (SemanticWeb, optimisation) requièrent .NET 9.0 + dotnet-interactive. Les notebooks Lean nécessitent WSL + elan. Aucun prérequis en logique avancée : chaque série introduit ses concepts progressivement depuis les fondements.

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

### Parcours alternatif : Apprentissage symbolique (SymbolicLearning, ~9h30)

La série SymbolicLearning (10 notebooks) suit le chapitre 19 d'AIMA : induction pure (Version Space), apprentissage guidé par la connaissance (EBL, RBL), programmation logique inductive (FOIL, résolution inverse, Progol), apprentissage actif d'automates (L* d'Angluin), puis intégration neuro-symbolique jusqu'à un capstone LLM + knowledge graph. Elle ne requiert que Python standard pour l'essentiel et peut être suivie indépendamment des autres phases.

---

## Quick Start

**Premier notebook recommande par série :**

| Serie | Premier notebook | Commande rapide |
|-------|-----------------|-----------------|
| **Tweety** | `Tweety/Tweety-1-Setup.ipynb` | Ouvrir dans Jupyter, executer toutes les cellules |
| **Lean** | `Lean/Lean-1-Setup.ipynb` | `wsl -d Ubuntu -- bash -c "jupyter notebook Lean-1-Setup.ipynb"` |
| **SemanticWeb** | `SemanticWeb/SW-1-CSharp-Setup.ipynb` (.NET) ou `SW-2b-Python-RDFBasics.ipynb` (Python) | `pip install rdflib pySHACL` |
| **Planners** | `Planners/00-Environment/Planners-0-Setup.ipynb` | `pip install ortools unified_planning` |
| **SmartContracts** | `SmartContracts/00-Foundations/SC-0-Cypherpunk-Origins.ipynb` | `pip install py-solc-x web3` |
| **SymbolicLearning** | `SymbolicLearning/SL-1-LogicalLearning.ipynb` | Python 3.10+ standard library, aucune installation |
| **Argument Analysis** | `Argument_Analysis/Argument_Analysis_Agentic-0-init.ipynb` | `pip install semantic-kernel jpype1` + `.env` |

**Pour commencer sans rien installer** : les notebooks Python (Tweety, Planners, SemanticWeb Python, SmartContracts) ne necessitent que `pip install jupyter ipykernel` + les packages listes ci-dessus.

---

## Prerequis par série

| Serie | Kernel | Environnement special | Packages principaux | API Keys |
|-------|--------|----------------------|---------------------|----------|
| **Tweety** | Python | Java/JPype, JDK 17 | jpype1, pysat, clingo | Non |
| **Lean** | Lean 4 / Python (WSL) | WSL, elan, Lean 4 | lean4_jupyter | OPENAI_API_KEY (7-10) |
| **SemanticWeb** | .NET C# / Python | Node.js (certains) | dotNetRDF, rdflib, pySHACL | Non |
| **Planners** | Python | WSL ou Docker (Fast-Downward) | ortools, unified_planning | Non |
| **SmartContracts** | Python | Solidity/solc, Foundry | py-solc-x, web3 | OPENAI_API_KEY (8b) |
| **SymbolicLearning** | Python | Aucun (WSL pour la section Popper de SL-4) | sklearn, rdflib, clingo (optionnels) | OPENROUTER_API_KEY optionnelle (SL-7/SL-10) |
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
| 9 | [Tweety-9-Preferences](Tweety/Tweety-9-Preferences.ipynb) | Ordres de préférence, theorie du vote (Borda, Copeland) | 1 | Java/JPype |

> 10/10 notebooks ont des exercices. La configuration de Tweety-1-Setup constitue l'exercice setup de la série.

### Technologies

| Technologie | Usage |
|-------------|-------|
| **JPype** | Bridge Java/Python pour appeler les classes Tweety |
| **PySAT** | Solveurs SAT natifs Python (CaDiCaL, Glucose4, MiniSat) |
| **Clingo** | Answer Set Programming pour ABA et logiques non-monotones |
| **SPASS** | Prouveur de theoremes pour logique modale |
| **EProver** | Prouveur FOL haute performance |

Documentation complète : [Tweety/README.md](Tweety/README.md)

---

## Lean - Verification Formelle

Serie de **21 notebooks** sur **Lean 4**, proof assistant base sur la theorie des types dependants. Couvre des fondations théoriques jusqu'a l'intégration des LLMs pour l'assistance automatique aux preuves, un tribut a Grothendieck (Lean-13/13b), les jeux de Conway (Lean-14a/14b/14c), et les theoremes de Kochen-Specker (Lean-15) et du Libre Arbitre (Lean-16).

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
| 9 | [Lean-9-SK-Multi-Agents](Lean/Lean-9-SK-Multi-Agents.ipynb) | Python WSL | Semantic Kernel, 5 agents spécialisés, ProofState | 2 |
| 10 | [Lean-10-LeanDojo](Lean/Lean-10-LeanDojo.ipynb) | Python WSL | LeanDojo, tracing, extraction theoremes, ML pour theorem proving | 2 |
| 11 | [Lean-11-TorchLean](Lean/Lean-11-TorchLean.ipynb) | Lean 4 | Verification formelle de réseaux de neurones | 2 |
| 11py | [Lean-11-TorchLean-Python](Lean/Lean-11-TorchLean-Python.ipynb) | Python | IBP, certificats de robustesse, verification | 7 |
| 12 | [Lean-12-Sensitivity-Theorem](Lean/Lean-12-Sensitivity-Theorem.ipynb) | Lean 4 | Port Lean du theoreme de sensibilite de Huang (2019), hypercube, signing matrix | 4 |
| **Hommages et theoremes** |
| 13 | [Lean-13-Grothendieck-Tribute](Lean/Lean-13-Grothendieck-Tribute.ipynb) | Lean 4 | Hommage a Grothendieck : tour Mathlib, micro-formalisations | 3 |
| 13b | [Lean-13b-Lean-Grothendieck](Lean/Lean-13b-Lean-Grothendieck.ipynb) | Python WSL | Grothendieck en Lean, atelier pratique : sources `grothendieck_lean/`, snippets via WSL | 3 |
| 14a | [Lean-14a-Conway-Man-and-Work](Lean/Lean-14a-Conway-Man-and-Work.ipynb) | Python WSL | Conway, l'homme et l'oeuvre : panorama des grands résultats, premières formalisations executees depuis `conway_lean` | 3 |
| 14b | [Lean-14b-Conway-Game-of-Life-Lean](Lean/Lean-14b-Conway-Game-of-Life-Lean.ipynb) | Python WSL | Game of Life as Computation : Doomsday, FRACTRAN, Look-and-Say, Nim, Angel | 4 |
| 14c | [Lean-14c-Conway-Game-of-Life-Golly](Lean/Lean-14c-Conway-Game-of-Life-Golly.ipynb) | Python | Game of Life en images : les 3 piliers, compagnon Golly | 4 |
| 15 | [Lean-15-Kochen-Specker](Lean/Lean-15-Kochen-Specker.ipynb) | Lean 4 | Theoreme de Kochen-Specker (1967), 18 vecteurs Cabello-Estebaranz-Garcia-Alcaine, contextuality quantique | 5 |
| 16 | [Lean-16-Conway-Free-Will-Theorem](Lean/Lean-16-Conway-Free-Will-Theorem.ipynb) | Python WSL | Theoreme du libre arbitre (Conway-Kochen) : axiomes SPIN/TWIN/MIN, port formel adosse a `FreeWillTheorem.lean` | 2 |

### Kernels requis

- **Lean 4 (WSL)** : Notebooks 2-6, 11, 12, 13, 15 (preuves Lean natives)
- **Python 3 (WSL)** : Notebooks 1, 7-10, 11py, 13b, 14a-14c, 16 (setup, LLM, LeanDojo, hommages)

> Note : Les kernels Windows ne fonctionnent pas (signal.SIGPIPE, problemes chemins)

Documentation complète : [Lean/README.md](Lean/README.md)

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
| 5 | [SW-5-CSharp-LinkedData](SemanticWeb/SW-5-CSharp-LinkedData.ipynb) | .NET C# | DBpedia, Wikidata, requêtes federees SERVICE | 6 |
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

Documentation complète : [SemanticWeb/README.md](SemanticWeb/README.md)

---

## Planners - Planification Automatique

Serie de **13 notebooks** sur la planification automatique, couvrant PDDL classique, CP-SAT (OR-Tools), VRP, planification temporelle, HTN, et intégration LLM.

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
| 6b | [Fast-Downward-Legacy](Planners/archive/Fast-Downward-Legacy.ipynb) | Legacy Fast-Downward .NET | 0 | .NET kernel |
| **Avance** |
| 7 | [Planners-7-OR-Tools](Planners/03-Advanced/Planners-7-OR-Tools.ipynb) | CP-SAT, Job Shop, VRP | 2 | ortools |
| 8 | [Planners-8-Temporal](Planners/03-Advanced/Planners-8-Temporal.ipynb) | Planification temporelle (PDDL 2.1) | 6 | Python |
| 9 | [Planners-9-HTN](Planners/03-Advanced/Planners-9-HTN.ipynb) | Hierarchical Task Networks | 7 | Python |
| **Neuro-symbolique** |
| 10 | [Planners-10-LLM-Planning](Planners/04-NeuroSymbolic/Planners-10-LLM-Planning.ipynb) | LLMs pour la planification | 2 | API keys |
| 11 | [Planners-11-Unified-Planning](Planners/04-NeuroSymbolic/Planners-11-Unified-Planning.ipynb) | Unified Planning Framework | 3 | unified_planning |
| 12 | [Planners-12-LOOP](Planners/04-NeuroSymbolic/Planners-12-LOOP.ipynb) | LLM + OR-Tools + planification | 2 | Fast-Downward |

> 12/13 notebooks ont des exercices. Seul Planners-0-Setup (configuration) n'en a pas.

Documentation complète : [Planners/README.md](Planners/README.md)

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

Documentation complète : [SmartContracts/README.md](SmartContracts/README.md)

---

## Argument Analysis - Analyse Argumentative LLM

Pipeline d'analyse argumentative multi-agents avec **Semantic Kernel** et LLMs. Combine détection de sophismes, formalisation logique, et validation par TweetyProject.

> **Note** : Cette série est un projet/demo, pas un cours. Aucun exercice étudiant. Non adaptee en l'etat pour un cours structure.

### Structure detaillee

| # | Notebook | Role |
|---|----------|------|
| 0 | [Agentic-0-init](Argument_Analysis/Argument_Analysis_Agentic-0-init.ipynb) | Configuration LLM, JPype/Tweety, ProjectManagerAgent |
| 1 | [Agentic-1-informal_agent](Argument_Analysis/Argument_Analysis_Agentic-1-informal_agent.ipynb) | InformalAnalysisAgent, détection sophismes |
| 2 | [Agentic-2-pl_agent](Argument_Analysis/Argument_Analysis_Agentic-2-pl_agent.ipynb) | PropositionalLogicAgent, formalisation PL |
| 3 | [Agentic-3-orchestration](Argument_Analysis/Argument_Analysis_Agentic-3-orchestration.ipynb) | Orchestration multi-agents |
| 4 | [Executor](Argument_Analysis/Argument_Analysis_Executor.ipynb) | Pipeline complet, rapport JSON |
| 5 | [UI_configuration](Argument_Analysis/Argument_Analysis_UI_configuration.ipynb) | Interface widgets ipywidgets |

Documentation complète : [Argument_Analysis/README.md](Argument_Analysis/README.md)

---

## SymbolicLearning - Apprentissage Symbolique

Serie de **10 notebooks** Python sur l'apprentissage symbolique (AIMA ch. 19) : induction pure (Version Space), apprentissage guide par la connaissance (EBL, RBL), programmation logique inductive (FOIL, resolution inverse, Progol), apprentissage actif d'automates (L* d'Angluin), et intégration neuro-symbolique jusqu'au capstone LLM + knowledge graph.

### Structure detaillee

| # | Notebook | Contenu | Exercices | Prerequis |
|---|----------|---------|-----------|-----------|
| 1 | [SL-1-LogicalLearning](SymbolicLearning/SL-1-LogicalLearning.ipynb) | CBH, Version Space, Candidate Elimination | 5 | Python |
| 2 | [SL-2-KnowledgeBasedLearning](SymbolicLearning/SL-2-KnowledgeBasedLearning.ipynb) | EBL, introduction au RBL (determinations) | 3 | SL-1 |
| 3 | [SL-3-RelevanceLearning](SymbolicLearning/SL-3-RelevanceLearning.ipynb) | Treillis des determinations, MINIMAL-CONSISTENT-DET, RBL vs sklearn | 3 | SL-2 |
| 4 | [SL-4-InductiveLogicProgramming](SymbolicLearning/SL-4-InductiveLogicProgramming.ipynb) | FOIL, resolution inverse, knowledge graphs, Popper (LFF) | 4 | SL-1 |
| 5 | [SL-5-NeuroSymbolic](SymbolicLearning/SL-5-NeuroSymbolic.ipynb) | T-norms, predicats neuronaux, LTN, DeepProbLog | 4 | SL-1 |
| 6 | [SL-6-KnowledgeGraphs-ILP](SymbolicLearning/SL-6-KnowledgeGraphs-ILP.ipynb) | rdflib, AMIE rule mining, completion KG, ASP avec clingo | 4 | SL-4 |
| 7 | [SL-7-LLM-SymbolicLearning](SymbolicLearning/SL-7-LLM-SymbolicLearning.ipynb) | Extraction de règles LLM, verification symbolique (Gemini optionnel) | 4 | SL-1 |
| 8 | [SL-8-ActiveAutomataLearning](SymbolicLearning/SL-8-ActiveAutomataLearning.ipynb) | L* d'Angluin, table d'observation, requêtes MQ/EQ, Myhill-Nerode | 4 | SL-1 |
| 9 | [SL-9-InverseResolution](SymbolicLearning/SL-9-InverseResolution.ipynb) | LGG de Plotkin, theta-subsomption, clause bottom, recherche Progol | 5 | SL-4 |
| 10 | [SL-10-Capstone-NeuroSymbolic](SymbolicLearning/SL-10-Capstone-NeuroSymbolic.ipynb) | Pipeline neuro-symbolique 6 etages, LLM réel aux deux extremites | 4 | SL-5 a SL-7 |

> 10/10 notebooks ont des exercices — 40 au total, organises en table de pioche pour la seance de restitution (chaque exercice est assorti d'une question-twist).

Documentation complète : [SymbolicLearning/README.md](SymbolicLearning/README.md)

---

## Autres Notebooks

### Optimisation et Contraintes (2 notebooks)

| Notebook | Kernel | Contenu | Exercices |
|----------|--------|---------|-----------|
| [OR-tools-Stiegler](OR-tools-Stiegler.ipynb) | .NET C# | Probleme de Stigler, programmation lineaire avec OR-Tools | 2 |
| [01_Linq2Z3_Intro](SMT/Z3/01_Linq2Z3_Intro.ipynb) | .NET C# | SMT avec LINQ, Z3.Linq, Missionnaires et Cannibales | 3 |

Le notebook Z3 inaugure la série [SMT/Z3/](SMT/Z3/README.md) (SMT declaratif via Z3.Linq), regroupee avec la série Python [SMT/Z3-Python/](SMT/Z3-Python/README.md) sous le chapeau [SMT/](SMT/README.md) (Satisfiability Modulo Theories).

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
├── Lean/                      # Serie Lean 4 (21 notebooks)
│   ├── Lean-1-Setup.ipynb ... Lean-16-Conway-Free-Will-Theorem.ipynb
│   ├── lean_runner.py         # Backend Python multi-mode
│   ├── scripts/               # Installation, validation WSL
│   └── README.md
│
├── SemanticWeb/               # Web semantique (18 notebooks)
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
├── SymbolicLearning/          # Apprentissage symbolique (10 notebooks)
│   ├── SL-1-LogicalLearning.ipynb ... SL-10-Capstone-NeuroSymbolic.ipynb
│   ├── reference/             # Notes AIMA ch. 19
│   └── README.md
│
├── SMT/                       # Solveurs SMT (Satisfiability Modulo Theories)
│   ├── Z3/                     # Serie Z3.Linq C# (SMT declaratif via LINQ)
│   │   ├── 01_Linq2Z3_Intro.ipynb ... 05_Meal_Planner_Hierarchical.ipynb
│   │   └── README.md
│   ├── Z3-Python/              # Serie z3-py (API complete imperative)
│   │   ├── Z3-Python-01-Introduction.ipynb ... Z3-Python-03-Tactics.ipynb
│   │   └── README.md
│   └── README.md              # Chapeau SMT
├── OR-tools-Stiegler.ipynb    # Optimisation LP
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

Le setup est entierement automatisé via `Tweety-1-Setup.ipynb` :

1. **JDK 17 portable** : Auto-télécharge dans `Tweety/jdk-17-portable/` (Azul Zulu, ~180MB). Aucune installation système requise, pas de UAC.
2. **JARs TweetyProject** : Auto-télécharges dans `Tweety/libs/` depuis Maven Central (35 modules, ~50MB total).
3. **Outils externes** : Clingo, SPASS, EProver dans `Tweety/ext_tools/` (inclus dans le depot).

**Problemes connus :**
- `asp-1.30.jar` et `rpcl-1.30.jar` : Modules absents de Maven Central pour la version 1.30. Non bloquant -- les notebooks gerent l'absence avec try/except.
- Si un JAR fait 0 bytes ou ~554 bytes : re-télécharger manuellement depuis `https://repo1.maven.org/maven2/org/tweetyproject/`.

### Planners

**Status execution : 13/14 SUCCESS** (Fast-Downward-Legacy.ipynb echoue -- kernel .NET bloque)

1. **Packages Python** : `pip install ortools unified_planning`
2. **Fast-Downward** (requis pour notebooks 2-6, 12) : Installer via WSL ou Docker
   - WSL : `sudo apt install fast-downward` ou compiler depuis source
   - Docker : Image `aiblazor/fast-downward` disponible
3. **Notebooks théoriques** (7-11) : Ne necessitent que Python + les packages ci-dessus

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
   Ou en arrière-plan : `wsl -d Ubuntu -- bash -c 'anvil --host 0.0.0.0 &'`
5. **Fichier `.env`** : Configurer dans `SmartContracts/.env` :
   - `ANVIL_RPC=http://127.0.0.1:8545` (local)
   - `LLM_API_KEY` pour SC-11 (via OpenRouter)
   - `DEPLOYER_PRIVATE_KEY` : Mettre une cle de testnet réelle pour SC-24/25, ou laisser le placeholder (ces notebooks echoueront)

**Problemes connus :**
- **SC-3 a SC-10** : Echouent si anvil n'est pas lance sur le port 8545. Solution : lancer `anvil` avant l'execution.
- **SC-15 Zero-Knowledge-Proofs** : SyntaxError f-string imbriquee (`{"CONVAINCU" if ...}`) -- incompatible Python 3.11. Fix : utiliser des parentheses ou une variable intermédiaire.
- **SC-24/25** : `hexstr_to_bytes` erreur si `DEPLOYER_PRIVATE_KEY` contient un placeholder non-hex.

### Argument_Analysis

**Status execution : 3/5 (demo, pas cours étudiant)**

1. **JDK 17 portable** : Partage avec Tweety (même `jdk-17-portable/` si configure)
2. **Fichier `.env`** : Configurer dans `Argument_Analysis/.env` :
   - `OPENAI_API_KEY` (via OpenRouter : `sk-or-v1-...`)
   - `OPENAI_BASE_URL=https://openrouter.ai/api/v1`
   - `TEXT_CONFIG_PASSPHRASE=Propaganda`
   - `BATCH_MODE=true`
3. **Packages** : `pip install semantic-kernel jpype1`

**Problemes connus :**
- **AA-3 orchestration** : Papermill ne preserve pas l'etat entre notebooks. Les définitions de AA-0/1/2 ne sont pas disponibles. Ce notebook doit être execute manuellement après les 3 précédents.
- **AA Executor** : Timeout a 300s (pipeline multi-agents long).

### Lean

**Status execution : valide via papermill sur les kernels WSL (`lean4`, `python3-wsl`)**

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
| **Z3** | SMT solver | Tweety, Z3 |
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

### Couverture exercices (mise a jour 11 juin 2026)

| Serie | Notebooks | Avec exercices | Sans exercices | Status |
|-------|-----------|----------------|----------------|--------|
| SmartContracts | 27 | 27 (100%) | 0 | Complet |
| SemanticWeb | 18 | 16 (89%) | 2 (Setup + Legacy) | Complet |
| Lean | 21 | 20 (95%) | 1 (Setup) | Complet |
| Planners | 13 | 12 (92%) | 1 (Setup) | Complet |
| Tweety | 10 | 10 (100%) | 0 | Complet |
| SymbolicLearning | 10 | 10 (100%) | 0 | Complet |
| Argument Analysis | 6 | 0 (0%) | 6 (demo) | N/A |

**Total** : 95/105 notebooks de contenu avec exercices (90%). Les notebooks sans exercices sont les notebooks de setup/configuration (SW-1, Planners-0, Lean-1), le notebook legacy (RDF.Net), et la série demo Argument Analysis (6 notebooks).

### Problemes restants

- **Lean-11-TorchLean** : 11 code cells sans outputs (kernel lean4 natif, erreurs PyTorch dtype)
- **SmartContracts** : Certains notebooks sans section prerequis dans le header

---

## Ponts cross-séries

Ces connexions entre séries sont exploitees dans le curriculum IA Symbolique.

### Lean <-> GameTheory (Choix social)

| Concept Lean | Concept GameTheory | Notebooks |
|-------------|-------------------|-----------|
| Theoreme d'Arrow (preuve formelle) | Theorie du vote / Choix social | `GameTheory/social_choice_lean/SocialChoice/Arrow.lean` <-> `GameTheory/GameTheory-16-MechanismDesign.ipynb` |
| Theoreme de Sen (preuve formelle) | Impossibilite du paretien liberal | `GameTheory/social_choice_lean/SocialChoice/Sen.lean` <-> `GameTheory/GameTheory-16-MechanismDesign.ipynb` |
| Valeur de Shapley | Coalitions, jeux cooperatifs | `GameTheory/GameTheory-15b-Lean-CooperativeGames.ipynb` <-> `GameTheory/GameTheory-15-CooperativeGames.ipynb` |

### Lean <-> SmartContracts (Verification formelle)

| Concept | Pont | Notebooks |
|---------|------|-----------|
| Theorie des types dependants | Verification formelle de contrats | `Lean/Lean-1-Setup.ipynb` (types) <-> `SmartContracts/03-Foundry-Testing/SC-14-Formal-Verification.ipynb` |
| Preuves LLM-assistees | Contrats LLM-assistes | `Lean/Lean-8-Agentic-Proving.ipynb` <-> `SmartContracts/02-Solidity-Advanced/SC-11-LLM-Assisted.ipynb` |
| `sorry` = axiome non prouve | Bugs de contrats non detectes | Concepts paralleles d'incompletude |

### Tweety <-> Argument_Analysis (Argumentation)

| Concept Tweety | Concept Argument_Analysis | Notebooks |
|---------------|--------------------------|-----------|
| Frameworks de Dung | Argumentation multi-agents | `Tweety/Tweety-5-Abstract-Argumentation.ipynb` <-> `Argument_Analysis/Argument_Analysis_Agentic-0-init.ipynb` |
| ASPIC+ (argumentation structuree) | Analyse LLM d'arguments | `Tweety/Tweety-6-Structured-Argumentation.ipynb` <-> `Argument_Analysis/Argument_Analysis_Agentic-3-orchestration.ipynb` |
| Dialogues d'agents | Debat multi-agent | `Tweety/Tweety-8-Agent-Dialogues.ipynb` <-> `Argument_Analysis/Argument_Analysis_Executor.ipynb` |

### SemanticWeb <-> SmartContracts (Decentralisation)

| Concept | Pont | Notebooks |
|---------|------|-----------|
| Ontologies RDF/OWL | Gouvernance DAO (etat canonique) | `SemanticWeb/SW-7-CSharp-OWL.ipynb` <-> `SmartContracts/02-Solidity-Advanced/SC-9-DAO-Governance.ipynb` |
| GraphRAG | Indexation on-chain | `SemanticWeb/SW-12-Python-GraphRAG.ipynb` <-> SmartContracts DeFi indexing |
| SHACL (validation) | Smart contract verification | `SemanticWeb/SW-8-Python-SHACL.ipynb` <-> `SmartContracts/03-Foundry-Testing/SC-14-Formal-Verification.ipynb` |

### Planners <-> SmartContracts (Coordination)

| Concept | Pont | Notebooks |
|---------|------|-----------|
| Planification multi-agent | MEV / auctions cross-chain | `Planners/03-Advanced/Planners-9-HTN.ipynb` <-> SmartContracts MEV |
| CP-SAT (OR-Tools) | Optimisation sous contraintes (DeFi) | `Planners/03-Advanced/Planners-7-OR-Tools.ipynb` <-> `SmartContracts/02-Solidity-Advanced/SC-8-DeFi-Primitives.ipynb` |

---

## Ressources

### References academiques

| Domaine | Reference | Couverture |
|---------|-----------|------------|
| IA Symbolique (général) | Russell & Norvig, *AIMA* 4e ed., ch. 7-12 | Recherche, logique, planification |
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

## FAQ

### Qu'est-ce que l'IA symbolique et pourquoi l'étudier a l'ere des LLMs ?

L'IA symbolique repose sur la **manipulation explicite de symboles et de règles** (logique, ontologies, planification, contrats) plutot que sur l'apprentissage statistique. Les LLMs sont puissants mais opaques : ils ne garantissent pas la correction logique, ne peuvent pas verifier formellement un résultat, et hallucinent. L'IA symbolique apporte ce que les modeles statistiques ne fournissent pas : raisonnement **verifiable, explicable et certifie**. Les deux paradigmes sont complementaires — l'avenir est neuro-symbolique.

### Quelle est la difference entre Tweety et Z3 ?

**TweetyProject** est une bibliotheque Java pour la logique formelle (propositionnelle, FOL, modale, argumentation, revision de croyances). Elle est utilisee via JPype en Python. **Z3** (Microsoft Research) est un solveur SMT (Satisfiability Modulo Theories) qui automatisé la resolution de problemes logiques complexes. Tweety est oriente enseignement (comprendre les semantiques), Z3 est oriente resolution (prouver/infirmer des proprietes). Les deux apparaissent dans GameTheory (Arrow/SAT) et Search (CSP).

### Comment installer l'environnement Tweety ?

Ouvrez le notebook `Tweety-1-Setup.ipynb` : il télécharge automatiquement JDK 17 et les 35 JARs TweetyProject. Vous pouvez aussi lancer `python scripts/download_tweety_tools.py --all` en ligne de commande. Les dependances Python sont `jpype1 requests tqdm clingo z3-solver python-sat`.

### Par quelle sous-série commencer si je n'ai pas de JDK installe ?

Les séries **SemanticWeb** (notebooks Python), **Planners** (notebooks théoriques 7-11) et **Lean** (notebooks Python 1, 7-10) ne necessitent aucun JDK. **Tweety** et **Argument Analysis** utilisent JPype (bridge Java/Python) avec un JDK 17 portable auto-télécharge par le notebook de setup (pas d'installation système, pas de UAC). Si vous evitez les notebooks C# (qui requierent dotnet-interactive), vous pouvez travailler entierement en Python avec uniquement `pip install rdflib ortools unified_planning`.

### Pourquoi Tweety utilise-t-il JPype plutot que des implémentations Python natives ?

TweetyProject est la bibliotheque de référence pour l'IA symbolique formelle (argumentation de Dung, ASPIC+, revision de croyances, logiques modales). Elle couvre des domaines ou il n'existe pas d'equivalent Python mature : solveurs d'argumentation structures, frameworks d'agent dialogues, logiques epistemiques. JPype permet d'appeler directement les JARs Java depuis Python sans reimplementation. Les notebooks gerent la bridge de maniere transparente via `tweety_init.py`.

### Quelle est la difference entre les notebooks C# et Python de SemanticWeb ?

Les **notebooks Python** (SW-8 a SW-13) utilisent `rdflib`, `pySHACL`, `owlready2` et `kglab` — 10/10 s'executent sans probleme. Les **notebooks C#** (SW-1 a SW-7) utilisent `dotNetRDF` via .NET Interactive et peuvent echouer sous Windows si la policy d'execution bloque `dotnet-interactive.exe` (Win32Exception 4551). Les mêmes concepts (RDF, SPARQL, OWL, SHACL) sont couverts dans les deux stacks. Si vous n'avez pas besoin specifiquement de .NET, les notebooks Python suffisent pour le parcours complet.

### Comment executer les notebooks Lean sans GPU ni installation système ?

Les notebooks Lean utilisent **WSL (Windows Subsystem for Linux)** comme runtime — pas de GPU necessaire. Le notebook `Lean-1-Setup.ipynb` installe automatiquement `elan` (gestionnaire de toolchains Lean) et `lean4_jupyter` dans WSL. Les notebooks de preuves (2-6, 11) tournent sur le kernel `Lean 4 (WSL)` natif. Les notebooks LLM/prover (7-10) tournent sur `Python 3 (WSL)` et necessitent une cle API OpenRouter. Si WSL n'est pas disponible, les notebooks Python du même domaine (1, 7-10) peuvent être executes en Python natif.

### Peut-on étudier les SmartContracts sans blockchain réelle ?

Oui, c'est l'approche pédagogique de la série. **Anvil** (Foundry) fournit un simulateur Ethereum local qui tourne en une commande (`anvil --host 0.0.0.0`) sous WSL. Les notebooks SC-3 a SC-10 deploient et testent des contrats sur cette chaine locale — aucun ether réel, aucun testnet. Les notebooks théoriques (SC-0 a SC-2, SC-15 a SC-26) explorent les concepts (ZK proofs, DeFi, DAO, cross-chain) principalement via code Python/Solidity sans déploiement. Seuls SC-24 et SC-25 (déploiement réel) necessitent une cle testnet.

---

## Licence

Les notebooks sont distribues sous licence MIT.
Voir LICENSE a la racine du depot pour details.

---

*Version 1.1.0 — Juin 2026*

---

**Derniere mise a jour** : 2026-06-11
