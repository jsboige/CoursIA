# SymbolicAI - Intelligence Artificielle Symbolique

Collection de **44 notebooks Jupyter** pour l'apprentissage de l'IA symbolique : logiques formelles, argumentation computationnelle, verification formelle, web semantique, planification automatique et optimisation.

## Vue d'ensemble

| Serie | Notebooks | Cellules | Theme | Duree |
|-------|-----------|----------|-------|-------|
| [Tweety](#tweety---tweetyproject) | 10 | ~200 | Logiques formelles, Argumentation | ~7h |
| [Lean](#lean---verification-formelle) | 11 | ~454 | Proof assistant, Types dependants, LLMs | ~8h |
| [SemanticWeb](#semanticweb---web-semantique) | 13 | ~400 | RDF, SPARQL, OWL, SHACL, GraphRAG | ~10h |
| [Argument Analysis](#argument-analysis---analyse-argumentative-llm) | 6 | ~76 | Analyse argumentative multi-agents | ~3h |
| [Autres notebooks](#autres-notebooks) | 3 | ~75 | Z3, OR-Tools, Planification | ~1h30 |

**Total** : 44 notebooks, ~1320 cellules, ~30h30 de contenu

---

## Tweety - TweetyProject

Serie complete de **10 notebooks** sur [TweetyProject](https://tweetyproject.org/), bibliotheque Java pour l'IA symbolique. Couvre les logiques formelles, la revision de croyances, et l'argumentation computationnelle.

### Structure detaillee

| # | Notebook | Cellules | Contenu detaille |
|---|----------|----------|------------------|
| **Fondations** |
| 1 | [Tweety-1-Setup](Tweety/Tweety-1-Setup.ipynb) | 34 | Configuration JVM via JPype, telechargement automatique JARs (35 modules), outils externes (Clingo, SPASS, EProver), JDK Zulu 17 portable |
| 2 | [Tweety-2-Basic-Logics](Tweety/Tweety-2-Basic-Logics.ipynb) | 31 | **Logique Propositionnelle** : syntaxe, parseurs, SAT4J, comparaison solveurs PySAT (CaDiCaL, Glucose, MiniSat). **FOL** : predicats, fonctions, quantificateurs, unification |
| 3 | [Tweety-3-Advanced-Logics](Tweety/Tweety-3-Advanced-Logics.ipynb) | 23 | **Description Logic (DL)** : concepts, roles, TBox/ABox. **Logique Modale** : operateurs box/diamond, SPASS. **QBF** : formules booleennes quantifiees. **Conditionnelle** |
| **Revision de Croyances** |
| 4 | [Tweety-4-Belief-Revision](Tweety/Tweety-4-Belief-Revision.ipynb) | 22 | Postulats AGM, operateurs de contraction/revision, **MUS** (Minimal Unsatisfiable Subsets), **MaxSAT**, mesures d'incoherence (MI, MIC, Eta, Contension) |
| **Argumentation** |
| 5 | [Tweety-5-Abstract-Argumentation](Tweety/Tweety-5-Abstract-Argumentation.ipynb) | 14 | **Frameworks de Dung** : graphes d'attaque, semantiques (grounded, preferred, stable, semi-stable, CF2), acceptabilite, ensembles admissibles |
| 6 | [Tweety-6-Structured-Argumentation](Tweety/Tweety-6-Structured-Argumentation.ipynb) | 18 | **ASPIC+** : regles strictes/defeasibles, preferences. **DeLP** : Defeasible Logic Programming. **ABA** : Assumption-Based. **ASP** avec Clingo |
| 7a | [Tweety-7a-Extended-Frameworks](Tweety/Tweety-7a-Extended-Frameworks.ipynb) | 24 | **ADF** (Abstract Dialectical Frameworks) : conditions d'acceptation. **Bipolar** : support + attaque. **WAF** : poids. **SAF** : social. **SetAF** : attaques collectives. **EAF** : attaques sur attaques |
| 7b | [Tweety-7b-Ranking-Probabilistic](Tweety/Tweety-7b-Ranking-Probabilistic.ipynb) | 10 | **Ranking semantics** : classement des arguments (Categoriser, Burden, Discussion). **Probabiliste** : degres de croyance |
| **Applications** |
| 8 | [Tweety-8-Agent-Dialogues](Tweety/Tweety-8-Agent-Dialogues.ipynb) | 11 | **Agents argumentatifs** : ArguingAgent. **Protocoles de dialogue** : Grounded Game. **Loteries argumentatives** |
| 9 | [Tweety-9-Preferences](Tweety/Tweety-9-Preferences.ipynb) | 11 | **Ordres de preference** : totaux, partiels, lexicographiques. **Theorie du vote** : Borda, Copeland, agregation sociale |

### Technologies utilisees

| Technologie | Usage dans Tweety |
|-------------|-------------------|
| **JPype** | Bridge Java/Python pour appeler les classes Tweety |
| **PySAT** | Solveurs SAT natifs Python (CaDiCaL, Glucose4, MiniSat) |
| **Clingo** | Answer Set Programming pour ABA et logiques non-monotones |
| **SPASS** | Prouveur de theoremes pour logique modale |
| **EProver** | Prouveur FOL haute performance |
| **Z3** | SMT solver pour MARCO (enumeration MUS) |

### Modules TweetyProject couverts

```
logics.pl          Logique Propositionnelle      logics.fol         Premier Ordre
logics.dl          Description Logic             logics.ml          Modale
logics.qbf         QBF                           logics.cl          Conditionnelle
beliefdynamics     Revision AGM                  arg.dung           Frameworks Dung
arg.aspic          ASPIC+                        arg.delp           DeLP
arg.aba            ABA                           arg.adf            ADF
arg.bipolar        Bipolaire                     arg.weighted       Pondere
arg.social         Social                        arg.setaf          SetAF
arg.extended       Attaques recursives           arg.rankings       Classement
arg.prob           Probabiliste                  agents.dialogues   Dialogues
preferences        Vote et preferences           lp.asp             ASP
```

Documentation complete : [Tweety/README.md](Tweety/README.md)

---

## Lean - Verification Formelle

Serie de **11 notebooks** sur **Lean 4**, proof assistant base sur la theorie des types dependants. Couvre des fondations theoriques jusqu'a l'integration des LLMs pour l'assistance automatique aux preuves.

### Structure detaillee

| # | Notebook | Cellules | Kernel | Contenu detaille |
|---|----------|----------|--------|------------------|
| **Fondations** |
| 1 | [Lean-1-Setup](Lean/Lean-1-Setup.ipynb) | 21 | Python WSL | Diagnostic environnement, installation automatique elan, Lean 4, lean4_jupyter, verification complete |
| 2 | [Lean-2-Dependent-Types](Lean/Lean-2-Dependent-Types.ipynb) | 50 | Lean 4 | **Calcul des Constructions** : types de base, fonctions, produits, hierarchie d'univers (Type, Prop), `let`, `variable`, Pi-types, Sigma-types, inductifs (Nat, List) |
| 3 | [Lean-3-Propositions-Proofs](Lean/Lean-3-Propositions-Proofs.ipynb) | 50 | Lean 4 | **Curry-Howard** : Prop, connecteurs (And, Or, Not, Iff), preuves comme fonctions, transitivite, elimination, egalite et substitution, logique classique vs constructive |
| 4 | [Lean-4-Quantifiers](Lean/Lean-4-Quantifiers.ipynb) | 46 | Lean 4 | `forall` : introduction/elimination. `exists` : Exists.intro/elim. Proprietes arithmetiques Nat, combinaison de quantificateurs, hypotheses anonymes |
| 5 | [Lean-5-Tactics](Lean/Lean-5-Tactics.ipynb) | 70 | Lean 4 | **Mode tactique** : `by`, etat de preuve. Tactiques : `exact`, `intro`, `apply`, `have`, `show`, `cases`, `induction`, `rw`, `simp`, `calc`, `constructor`, `left`/`right` |
| **Etat de l'art 2024-2026** |
| 6 | [Lean-6-Mathlib-Essentials](Lean/Lean-6-Mathlib-Essentials.ipynb) | 44 | Lean 4 | **Mathlib4** : installation Lake, structure (4M+ lignes), tactiques puissantes (`ring`, `linarith`, `omega`, `norm_num`, `field_simp`), recherche Loogle/Moogle |
| 7 | [Lean-7-LLM-Integration](Lean/Lean-7-LLM-Integration.ipynb) | 32 | Python WSL | **AlphaProof** : architecture DeepMind, IMO 2024. **LeanCopilot** : integration VSCode. Patterns collaboration humain-LLM-Lean, prompting efficace |
| 7b | [Lean-7b-Examples](Lean/Lean-7b-Examples.ipynb) | 22 | Python WSL | Exemples progressifs, theoremes simples, theoremes Mathlib, visualisations, comparaison OpenAI vs Anthropic, problemes d'Erdos comme benchmark |
| 8 | [Lean-8-Agentic-Proving](Lean/Lean-8-Agentic-Proving.ipynb) | 21 | Python WSL | **Agents autonomes** : recherche theoremes, generation tactiques, verification, orchestration. **Harmonic Aristotle** : decomposition recursive, resolution Erdos #124 |
| 9 | [Lean-9-SK-Multi-Agents](Lean/Lean-9-SK-Multi-Agents.ipynb) | 48 | Python WSL | **Semantic Kernel** : 5 agents specialises (SearchAgent, TacticAgent, VerifyAgent, ErrorAgent, Orchestrator), etat partage `ProofState`, plugins SK |
| 10 | [Lean-10-LeanDojo](Lean/Lean-10-LeanDojo.ipynb) | 50 | Python WSL | **LeanDojo** : tracing de repos Lean, extraction theoremes, environnement Dojo interactif, machine learning pour theorem proving |

### Percees majeures 2024-2026

| Systeme | Accomplissement | Date |
|---------|-----------------|------|
| **AlphaProof** (DeepMind) | Medaille d'argent IMO 2024, 4/6 problemes resolus | Jul 2024 |
| **DeepSeek-Prover** | Problemes Erdos 379, 987, 730, 198 | 2024-2025 |
| **Harmonic Aristotle** | Erdos #124 variant (~30 ans ouvert) en 6h | Dec 2025 |
| **Mathlib4** v4.27.0 | 4M+ lignes, utilise par Terry Tao | Jan 2026 |

### Kernels requis

- **Lean 4 (WSL)** : Notebooks 2-6 (preuves Lean natives)
- **Python 3 (WSL)** : Notebooks 1, 7-10 (setup, LLM, LeanDojo)

> Note : Les kernels Windows ne fonctionnent pas (signal.SIGPIPE, problemes chemins)

Documentation complete : [Lean/README.md](Lean/README.md)

---

## Argument Analysis - Analyse Argumentative LLM

Pipeline d'analyse argumentative multi-agents avec **Semantic Kernel** et LLMs. Combine detection de sophismes, formalisation logique, et validation par TweetyProject.

### Architecture Multi-Agents

```
                    +-------------------+
                    | ProjectManager    |
                    | (Orchestration)   |
                    +--------+----------+
                             |
           +-----------------+-----------------+
           |                                   |
+----------v----------+            +-----------v---------+
| InformalAnalysisAgent|           | PropositionalLogic  |
| - Detection arguments |           | Agent               |
| - Taxonomie sophismes |           | - Formalisation PL  |
| - Analyse rhetorique  |           | - Validation Tweety |
+---------------------+            +---------------------+
```

### Structure detaillee

| # | Notebook | Cellules | Role |
|---|----------|----------|------|
| 0 | [Argument_Analysis_Agentic-0-init](Argument_Analysis/Argument_Analysis_Agentic-0-init.ipynb) | 23 | **Configuration** : LLM (OpenAI/Anthropic), JPype/Tweety, `RhetoricalAnalysisState`, `StateManagerPlugin`, Service LLM global, `ProjectManagerAgent` |
| 1 | [Argument_Analysis_Agentic-1-informal_agent](Argument_Analysis/Argument_Analysis_Agentic-1-informal_agent.ipynb) | 9 | **InformalAnalysisAgent** : `InformalAnalysisPlugin`, prompts semantiques, detection d'arguments et sophismes, taxonomie CSV |
| 2 | [Argument_Analysis_Agentic-2-pl_agent](Argument_Analysis/Argument_Analysis_Agentic-2-pl_agent.ipynb) | 9 | **PropositionalLogicAgent** : `PropositionalLogicPlugin`, formalisation PL, integration Tweety, validation logique |
| 3 | [Argument_Analysis_Agentic-3-orchestration](Argument_Analysis/Argument_Analysis_Agentic-3-orchestration.ipynb) | 8 | **Orchestration** : strategies de conversation, execution collaborative, conclusion |
| 4 | [Argument_Analysis_Executor](Argument_Analysis/Argument_Analysis_Executor.ipynb) | 15 | **Pipeline complet** : chargement environnement, UI, execution, rapport de validation JSON, cross-validation |
| 5 | [Argument_Analysis_UI_configuration](Argument_Analysis/Argument_Analysis_UI_configuration.ipynb) | 12 | **Interface** : widgets ipywidgets, selection texte, configuration tache, cache optionnel |

### Composants cles

| Composant | Description |
|-----------|-------------|
| `RhetoricalAnalysisState` | Etat partage entre agents (arguments detectes, formalisations, validations) |
| `StateManagerPlugin` | Plugin SK pour lecture/ecriture de l'etat |
| `InformalAnalysisPlugin` | Detection arguments informels, classification sophismes |
| `PropositionalLogicPlugin` | Formalisation en logique propositionnelle, appels Tweety |
| Taxonomie CSV | Base de 50+ sophismes classes (ad hominem, pente glissante, faux dilemme, etc.) |

### Configuration

```bash
cd Argument_Analysis
cp .env.example .env
# Editer .env :
#   OPENAI_API_KEY=sk-...
#   BATCH_MODE=true     # Pour tests automatises (skip widgets)
#   BATCH_TEXT="..."    # Texte optionnel pour mode batch
```

Documentation complete : [Argument_Analysis/README.md](Argument_Analysis/README.md)

---

## SemanticWeb - Web Semantique

Serie de **13 notebooks** sur le Web Semantique, combinant **.NET C#** (dotNetRDF, fondations RDF/SPARQL/OWL) et **Python** (rdflib, standards modernes, IA). Refonte complete du notebook monolithique `RDF.Net.ipynb` (original conserve dans [SemanticWeb/RDF.Net-Legacy/](SemanticWeb/RDF.Net-Legacy/)).

### Structure detaillee

| # | Notebook | Kernel | Contenu detaille |
|---|----------|--------|------------------|
| | **Partie 1 : Fondations RDF** | | |
| 1 | [SW-1-Setup](SemanticWeb/SW-1-Setup.ipynb) | .NET C# | Installation dotNetRDF, concepts RDF, pile W3C, premier graphe |
| 2 | [SW-2-RDFBasics](SemanticWeb/SW-2-RDFBasics.ipynb) | .NET C# | Triplets, noeuds (URI, bnodes, litteraux), serialisation |
| 3 | [SW-3-GraphOperations](SemanticWeb/SW-3-GraphOperations.ipynb) | .NET C# | Lecture, ecriture, fusion, selection, listes RDF |
| 4 | [SW-4-SPARQL](SemanticWeb/SW-4-SPARQL.ipynb) | .NET C# | Query Builder, SELECT, FILTER, OPTIONAL, UNION |
| | **Partie 2 : Donnees Liees et Ontologies** | | |
| 5 | [SW-5-LinkedData](SemanticWeb/SW-5-LinkedData.ipynb) | .NET C# | DBpedia, Wikidata, requetes federees SERVICE |
| 6 | [SW-6-RDFS](SemanticWeb/SW-6-RDFS.ipynb) | .NET C# | Vocabulaire RDFS, inference, hierarchies de classes |
| 7 | [SW-7-OWL](SemanticWeb/SW-7-OWL.ipynb) | .NET C# | OWL 2, OntologyGraph, profils EL/QL/RL |
| | **Partie 3 : Ecosysteme Python et Standards Modernes** | | |
| 8 | [SW-8-PythonRDF](SemanticWeb/SW-8-PythonRDF.ipynb) | Python | rdflib, SPARQLWrapper, comparaison dotNetRDF vs rdflib |
| 9 | [SW-9-SHACL](SemanticWeb/SW-9-SHACL.ipynb) | Python | Validation pySHACL, contraintes, qualite des donnees |
| 10 | [SW-10-JSONLD](SemanticWeb/SW-10-JSONLD.ipynb) | Python | JSON-LD, Schema.org, donnees structurees web |
| 11 | [SW-11-RDFStar](SemanticWeb/SW-11-RDFStar.ipynb) | Python | RDF 1.2 (RDF-Star), quoted triples, SPARQL-Star |
| | **Partie 4 : Graphes de Connaissances et IA** | | |
| 12 | [SW-12-KnowledgeGraphs](SemanticWeb/SW-12-KnowledgeGraphs.ipynb) | Python | Construction KGs, kglab, OWLReady2, visualisation |
| 13 | [SW-13-GraphRAG](SemanticWeb/SW-13-GraphRAG.ipynb) | Python | KG + LLMs, Microsoft GraphRAG, extraction entites |

### Technologies utilisees

| Technologie | Version | Usage |
|-------------|---------|-------|
| **dotNetRDF** | 3.2.1 | Core RDF/SPARQL en .NET (SW-1 a SW-7) |
| **rdflib** | 7.5.0 | Core RDF/SPARQL en Python (SW-8 a SW-13) |
| **pySHACL** | 0.27.0 | Validation SHACL (SW-9) |
| **OWLReady2** | 0.50+ | Manipulation ontologies (SW-12) |
| **kglab** | 0.6.1+ | Abstraction graphes de connaissances (SW-12) |

### Standards W3C couverts

RDF 1.1/1.2, SPARQL 1.1, RDFS, OWL 2, SHACL, JSON-LD 1.1

Documentation complete : [SemanticWeb/README.md](SemanticWeb/README.md)

---

## Planners - Planification Automatique

Introduction a la planification automatique avec Fast Downward, un planificateur PDDL de reference.

| Notebook | Cellules | Kernel | Contenu |
|----------|----------|--------|---------|
| [Fast-Downward](Planners/Fast-Downward.ipynb) | 46 | Python | Planification PDDL, heuristiques, A*, Blocks World |

Documentation complete : [Planners/README.md](Planners/README.md)

---

## Autres Notebooks

### Optimisation et Contraintes (2 notebooks)

| Notebook | Cellules | Kernel | Contenu |
|----------|----------|--------|---------|
| [OR-tools-Stiegler](OR-tools-Stiegler.ipynb) | 17 | .NET C# | **Probleme de Stigler** : regime optimal a cout minimal. Programmation lineaire avec OR-Tools, contraintes nutritionnelles, resolution LP |
| [Linq2Z3](Linq2Z3.ipynb) | 12 | .NET C# | **SMT avec LINQ** : integration Z3.Linq, syntaxe declarative. **Missionnaires et Cannibales** : modelisation, recherche solution optimale |

### Web Semantique

> **Note** : Le notebook monolithique `RDF.Net.ipynb` a ete remplace par la serie complete [SemanticWeb](SemanticWeb/README.md) (13 notebooks, ~10h). L'original est conserve dans [SemanticWeb/RDF.Net-Legacy/](SemanticWeb/RDF.Net-Legacy/). Voir la section [SemanticWeb](#semanticweb---web-semantique) ci-dessus.

### Planification Automatique (1 notebook)

| Notebook | Cellules | Kernel | Contenu |
|----------|----------|--------|---------|
| [Fast-Downward](Planners/Fast-Downward.ipynb) | 46 | .NET C# | **Planification classique** : modele STRIPS, limites, PDDL. **Fast Downward** : heuristiques (FF, LM-Cut, Merge-and-Shrink), A*, recherche avant/arriere. **Probleme Gripper** : domaine et probleme PDDL, execution |

Sections detaillees :
- Presentation Fast Downward et OR-Tools
- Representation STRIPS et PDDL
- Syntaxe ligne de commande
- Options de traduction
- Heuristiques et strategies de recherche

---

## Structure du Repertoire

```
SymbolicAI/
├── Tweety/                    # Serie TweetyProject (10 notebooks, ~200 cellules)
│   ├── Tweety-1-Setup.ipynb
│   ├── Tweety-2-Basic-Logics.ipynb
│   ├── Tweety-3-Advanced-Logics.ipynb
│   ├── Tweety-4-Belief-Revision.ipynb
│   ├── Tweety-5-Abstract-Argumentation.ipynb
│   ├── Tweety-6-Structured-Argumentation.ipynb
│   ├── Tweety-7a-Extended-Frameworks.ipynb
│   ├── Tweety-7b-Ranking-Probabilistic.ipynb
│   ├── Tweety-8-Agent-Dialogues.ipynb
│   ├── Tweety-9-Preferences.ipynb
│   ├── tweety_init.py         # Module d'initialisation partage
│   ├── libs/                  # JARs TweetyProject (35 modules)
│   ├── resources/             # Fichiers exemples (.aspic, .aba, .delp)
│   ├── ext_tools/             # Clingo, SPASS, EProver
│   ├── jdk-17-portable/       # JDK Zulu (auto-telecharge)
│   ├── scripts/               # Validation, benchmarks SAT
│   └── README.md
│
├── Lean/                      # Serie Lean 4 (11 notebooks, ~454 cellules)
│   ├── Lean-1-Setup.ipynb
│   ├── Lean-2-Dependent-Types.ipynb
│   ├── Lean-3-Propositions-Proofs.ipynb
│   ├── Lean-4-Quantifiers.ipynb
│   ├── Lean-5-Tactics.ipynb
│   ├── Lean-6-Mathlib-Essentials.ipynb
│   ├── Lean-7-LLM-Integration.ipynb
│   ├── Lean-7b-Examples.ipynb
│   ├── Lean-8-Agentic-Proving.ipynb
│   ├── Lean-9-SK-Multi-Agents.ipynb
│   ├── Lean-10-LeanDojo.ipynb
│   ├── lean_runner.py         # Backend Python multi-mode
│   ├── .env.example           # Config API LLM
│   ├── scripts/               # Installation, validation WSL
│   ├── examples/              # Fichiers .lean exemples
│   ├── tests/                 # Tests LeanDojo, kernel WSL
│   └── README.md
│
├── Argument_Analysis/         # Analyse argumentative (6 notebooks, ~76 cellules)
│   ├── Argument_Analysis_Agentic-0-init.ipynb
│   ├── Argument_Analysis_Agentic-1-informal_agent.ipynb
│   ├── Argument_Analysis_Agentic-2-pl_agent.ipynb
│   ├── Argument_Analysis_Agentic-3-orchestration.ipynb
│   ├── Argument_Analysis_Executor.ipynb
│   ├── Argument_Analysis_UI_configuration.ipynb
│   ├── .env.example           # Config OpenAI
│   ├── data/                  # Taxonomie sophismes CSV
│   └── ontologies/            # Ontologies OWL argumentation
│
├── SemanticWeb/               # Web semantique (13 notebooks, ~400 cellules)
│   ├── SW-1-Setup.ipynb ... SW-13-GraphRAG.ipynb
│   ├── data/                 # Fichiers RDF, OWL, SHACL, JSON-LD, CSV
│   ├── RDF.Net-Legacy/      # Notebook original (reference historique)
│   ├── requirements.txt
│   └── README.md
│
├── Planners/                  # Planification PDDL (46 cellules)
│   └── Fast-Downward.ipynb
│
├── OR-tools-Stiegler.ipynb    # Optimisation LP (17 cellules)
├── Linq2Z3.ipynb              # SMT LINQ (12 cellules)
│
├── scripts/                   # Scripts utilitaires
│   └── extract_notebook_content.py  # Extraction contenu notebooks
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

| Serie | Installation |
|-------|--------------|
| **Tweety** | Executer `Tweety-1-Setup.ipynb` - telechargement automatique JDK 17 + JARs |
| **Lean** | Executer `Lean-1-Setup.ipynb` - installation elan + Lean 4 + lean4_jupyter |
| **Lean (LLM)** | Configurer `.env` avec `OPENAI_API_KEY` pour notebooks 7-10 |
| **Argument Analysis** | Configurer `.env` avec `OPENAI_API_KEY` |
| **Autres** | Executer `dotnet restore MyIA.CoursIA.sln` |

---

## Outils Externes

| Outil | Version | Usage | Serie |
|-------|---------|-------|-------|
| **JPype** | 1.4+ | Bridge Java/Python | Tweety, Argument Analysis |
| **Clingo** | 5.6+ | Answer Set Programming | Tweety |
| **SPASS** | 3.9 | Prouveur modal | Tweety |
| **EProver** | 3.0+ | Prouveur FOL | Tweety |
| **Z3** | 4.12+ | SMT solver | Tweety, Linq2Z3 |
| **PySAT** | 1.8+ | SAT solvers natifs | Tweety |
| **elan** | latest | Gestionnaire Lean | Lean |
| **Mathlib4** | 4.27+ | Bibliotheque maths | Lean |
| **Semantic Kernel** | 1.0+ | Orchestration LLM | Argument Analysis, Lean |
| **OR-Tools** | 9.8+ | Optimisation | OR-Tools, Planners |
| **Fast Downward** | latest | Planification PDDL | Planners |
| **dotNetRDF** | 3.2+ | RDF/SPARQL | SemanticWeb |
| **rdflib** | 7.5+ | RDF/SPARQL Python | SemanticWeb |
| **pySHACL** | 0.27+ | Validation SHACL | SemanticWeb |

---

## Validation

```bash
# Tweety - validation rapide
cd Tweety/scripts && python verify_all_tweety.py --quick

# Tweety - verification environnement complet
python verify_all_tweety.py --check-env

# Lean - validation
cd Lean && python scripts/validate_lean_setup.py

# Lean - avec WSL
python scripts/validate_lean_setup.py --wsl

# Notebooks .NET
dotnet restore MyIA.CoursIA.sln
```

---

## Ressources

### TweetyProject
- Site officiel : https://tweetyproject.org/
- Documentation API : https://tweetyproject.org/api/
- GitHub : https://github.com/TweetyProjectTeam/TweetyProject

### Lean 4
- Theorem Proving in Lean 4 : https://leanprover.github.io/theorem_proving_in_lean4/
- Documentation : https://leanprover.github.io/lean4/doc/
- Mathlib4 : https://leanprover-community.github.io/mathlib4_docs/
- Loogle (recherche syntaxique) : https://loogle.lean-lang.org/
- Moogle (recherche semantique) : https://www.moogle.ai/

### LLM et Theorem Proving
- LeanCopilot : https://github.com/lean-dojo/LeanCopilot
- LeanDojo : https://leandojo.readthedocs.io/
- AlphaProof : https://deepmind.google/discover/blog/ai-solves-imo-problems-at-silver-medal-level/

### Semantic Kernel
- Documentation : https://learn.microsoft.com/semantic-kernel/
- GitHub Python : https://github.com/microsoft/semantic-kernel

### Autres
- OR-Tools : https://developers.google.com/optimization
- Z3 : https://github.com/Z3Prover/z3
- dotNetRDF : https://dotnetrdf.org/
- Fast Downward : https://www.fast-downward.org/

---

## Licence

Les notebooks sont distribues sous licence MIT.
Voir LICENSE a la racine du depot pour details.

---

**Derniere mise a jour** : 2026-02-13
