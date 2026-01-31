# SymbolicAI - Intelligence Artificielle Symbolique

Collection de notebooks Jupyter pour l'apprentissage de l'IA symbolique : logiques formelles, argumentation computationnelle, verification formelle, planification automatique et optimisation.

## Vue d'ensemble

| Serie | Notebooks | Theme | Duree |
|-------|-----------|-------|-------|
| [Tweety](#tweety---tweetyproject) | 10 | Logiques formelles, Argumentation | ~7h |
| [Lean](#lean---verification-formelle) | 10 | Proof assistant, Verification formelle | ~6h40 |
| [Argument Analysis](#argument-analysis---analyse-argumentative-llm) | 6 | Analyse argumentative avec LLM | ~3h |
| [Autres notebooks](#autres-notebooks) | 4 | Z3, OR-Tools, RDF, Planification | ~2h |

**Duree totale estimee** : ~19 heures

---

## Tweety - TweetyProject

Serie complete de 10 notebooks sur [TweetyProject](https://tweetyproject.org/), bibliotheque Java pour l'IA symbolique.

### Structure

| # | Notebook | Theme | Duree |
|---|----------|-------|-------|
| **Fondations** |
| 1 | [Tweety-1-Setup](Tweety/Tweety-1-Setup.ipynb) | Configuration JVM, JARs, outils externes | 20 min |
| 2 | [Tweety-2-Basic-Logics](Tweety/Tweety-2-Basic-Logics.ipynb) | Logique Propositionnelle (PL) et FOL | 45 min |
| 3 | [Tweety-3-Advanced-Logics](Tweety/Tweety-3-Advanced-Logics.ipynb) | DL, Modale, QBF, Conditionnelle | 40 min |
| **Revision de Croyances** |
| 4 | [Tweety-4-Belief-Revision](Tweety/Tweety-4-Belief-Revision.ipynb) | CrMas, MUS, MaxSAT, Mesures d'incoherence | 50 min |
| **Argumentation** |
| 5 | [Tweety-5-Abstract-Argumentation](Tweety/Tweety-5-Abstract-Argumentation.ipynb) | Dung AF, Semantiques (grounded, preferred, stable, CF2) | 55 min |
| 6 | [Tweety-6-Structured-Argumentation](Tweety/Tweety-6-Structured-Argumentation.ipynb) | ASPIC+, DeLP, ABA, ASP (Clingo) | 60 min |
| 7a | [Tweety-7a-Extended-Frameworks](Tweety/Tweety-7a-Extended-Frameworks.ipynb) | ADF, Bipolar, WAF, SAF, SetAF, EAF | 50 min |
| 7b | [Tweety-7b-Ranking-Probabilistic](Tweety/Tweety-7b-Ranking-Probabilistic.ipynb) | Ranking semantics, Probabiliste | 40 min |
| **Applications** |
| 8 | [Tweety-8-Agent-Dialogues](Tweety/Tweety-8-Agent-Dialogues.ipynb) | Agents, Dialogues argumentatifs, Loteries | 35 min |
| 9 | [Tweety-9-Preferences](Tweety/Tweety-9-Preferences.ipynb) | Preferences, Theorie du vote | 30 min |

### Technologies
- **JPype** : Integration Java/Python
- **PySAT** : Solveurs SAT (CaDiCaL, Glucose, MiniSat)
- **Clingo** : Answer Set Programming
- **Z3** : SMT solver

Documentation complete : [Tweety/README.md](Tweety/README.md)

---

## Lean - Verification Formelle

Serie de 10 notebooks sur **Lean 4**, proof assistant base sur la theorie des types dependants.

### Structure

| # | Notebook | Theme | Duree |
|---|----------|-------|-------|
| **Fondations** |
| 1 | [Lean-1-Setup](Lean/Lean-1-Setup.ipynb) | Installation elan, kernel Jupyter | 15 min |
| 2 | [Lean-2-Dependent-Types](Lean/Lean-2-Dependent-Types.ipynb) | Calcul des Constructions, types | 35 min |
| 3 | [Lean-3-Propositions-Proofs](Lean/Lean-3-Propositions-Proofs.ipynb) | Curry-Howard, preuves par termes | 45 min |
| 4 | [Lean-4-Quantifiers](Lean/Lean-4-Quantifiers.ipynb) | forall, exists, egalite | 40 min |
| 5 | [Lean-5-Tactics](Lean/Lean-5-Tactics.ipynb) | Mode tactique (apply, intro, rw, simp) | 50 min |
| **Etat de l'art** |
| 6 | [Lean-6-Mathlib-Essentials](Lean/Lean-6-Mathlib-Essentials.ipynb) | Mathlib4, ring/linarith/omega | 45 min |
| 7 | [Lean-7-LLM-Integration](Lean/Lean-7-LLM-Integration.ipynb) | LeanCopilot, AlphaProof | 50 min |
| 7b | [Lean-7b-Examples](Lean/Lean-7b-Examples.ipynb) | Exemples pratiques LLM | 30 min |
| 8 | [Lean-8-Agentic-Proving](Lean/Lean-8-Agentic-Proving.ipynb) | Agents autonomes, APOLLO | 55 min |
| 9 | [Lean-9-LeanDojo](Lean/Lean-9-LeanDojo.ipynb) | LeanDojo, theorem proving ML | 45 min |

### Percees recentes (2024-2026)
- **AlphaProof** (DeepMind) : Medaille d'argent IMO 2024
- **Harmonic Aristotle** : Resolution Erdos #124 en 6h
- **Mathlib4** : 4M+ lignes, utilise par Terry Tao

Documentation complete : [Lean/README.md](Lean/README.md)

---

## Argument Analysis - Analyse Argumentative LLM

Pipeline d'analyse argumentative avec Semantic Kernel et LLMs.

### Structure

| Notebook | Description |
|----------|-------------|
| [Argument_Analysis_Agentic-0-init](Argument_Analysis/Argument_Analysis_Agentic-0-init.ipynb) | Configuration OpenAI, Semantic Kernel |
| [Argument_Analysis_Agentic-1-informal_agent](Argument_Analysis/Argument_Analysis_Agentic-1-informal_agent.ipynb) | Agent d'analyse informelle |
| [Argument_Analysis_Agentic-2-pl_agent](Argument_Analysis/Argument_Analysis_Agentic-2-pl_agent.ipynb) | Agent logique propositionnelle |
| [Argument_Analysis_Agentic-3-orchestration](Argument_Analysis/Argument_Analysis_Agentic-3-orchestration.ipynb) | Orchestration multi-agents |
| [Argument_Analysis_Executor](Argument_Analysis/Argument_Analysis_Executor.ipynb) | Pipeline complet |
| [Argument_Analysis_UI_configuration](Argument_Analysis/Argument_Analysis_UI_configuration.ipynb) | Interface widgets |

### Configuration

```bash
cd Argument_Analysis
cp .env.example .env
# Ajouter OPENAI_API_KEY et BATCH_MODE=true pour tests automatises
```

---

## Autres Notebooks

### Optimisation et Contraintes

| Notebook | Description | Kernel |
|----------|-------------|--------|
| [OR-tools-Stiegler](OR-tools-Stiegler.ipynb) | Probleme de Stiegler avec OR-Tools | .NET C# |
| [Linq2Z3](Linq2Z3.ipynb) | Integration Z3 avec LINQ | .NET C# |

### RDF et Web Semantique

| Notebook | Description | Kernel |
|----------|-------------|--------|
| [RDF.Net](RDF.Net/RDF.Net.ipynb) | RDF, SPARQL, dotNetRDF | .NET C# |

### Planification Automatique

| Notebook | Description | Kernel |
|----------|-------------|--------|
| [Fast-Downward](Planners/Fast-Downward.ipynb) | Planification avec Fast Downward | Python |

---

## Structure du Repertoire

```
SymbolicAI/
├── Tweety/                    # Serie TweetyProject (10 notebooks)
│   ├── Tweety-1-Setup.ipynb ... Tweety-9-Preferences.ipynb
│   ├── libs/                  # JARs TweetyProject
│   ├── ext_tools/             # Clingo, SPASS
│   ├── jdk-17-portable/       # JDK Zulu (auto-telecharge)
│   ├── scripts/               # Scripts de validation
│   └── README.md
│
├── Lean/                      # Serie Lean 4 (10 notebooks)
│   ├── Lean-1-Setup.ipynb ... Lean-9-LeanDojo.ipynb
│   ├── lean_runner.py         # Backend Python multi-mode
│   ├── scripts/               # Scripts installation/validation
│   └── README.md
│
├── Argument_Analysis/         # Analyse argumentative LLM (6 notebooks)
│   ├── Argument_Analysis_*.ipynb
│   ├── data/                  # Taxonomie sophismes
│   └── ontologies/            # Ontologies OWL
│
├── RDF.Net/                   # Web semantique
│   └── RDF.Net.ipynb
│
├── Planners/                  # Planification automatique
│   └── Fast-Downward.ipynb
│
├── OR-tools-Stiegler.ipynb    # Optimisation
├── Linq2Z3.ipynb              # SMT solving
│
├── archive/                   # Versions historiques
├── data/                      # Donnees partagees
├── ext_tools/                 # Outils externes partages
├── libs/                      # Bibliotheques partagees
├── reports/                   # Rapports de qualite
├── scripts/                   # Scripts utilitaires
└── README.md                  # Ce fichier
```

---

## Installation

### Prerequis communs

```bash
# Python 3.10+
pip install jupyter ipykernel

# Pour notebooks .NET
dotnet tool install -g Microsoft.dotnet-interactive
dotnet interactive jupyter install
```

### Par serie

**Tweety** : Executer `Tweety-1-Setup.ipynb` (telechargement automatique JDK + JARs)

**Lean** : Executer `Lean-1-Setup.ipynb` (installation elan + Lean 4)

**Argument Analysis** : Configurer `.env` avec `OPENAI_API_KEY`

---

## Outils Externes

| Outil | Usage | Serie |
|-------|-------|-------|
| **JPype** | Bridge Java/Python | Tweety |
| **Clingo** | Answer Set Programming | Tweety |
| **SPASS** | Prouveur modal | Tweety |
| **Z3** | SMT solver | Tweety, Linq2Z3 |
| **PySAT** | SAT solvers (CaDiCaL, Glucose) | Tweety |
| **elan** | Gestionnaire versions Lean | Lean |
| **Mathlib4** | Bibliotheque mathematique Lean | Lean |
| **OR-Tools** | Optimisation combinatoire | OR-Tools |
| **Fast Downward** | Planification PDDL | Planners |

---

## Validation

```bash
# Tweety
cd Tweety/scripts && python verify_all_tweety.py --quick

# Lean
cd Lean && python scripts/validate_lean_setup.py

# Notebooks .NET
dotnet restore MyIA.CoursIA.sln
```

---

## Ressources

### TweetyProject
- Site : https://tweetyproject.org/
- API : https://tweetyproject.org/api/

### Lean 4
- Documentation : https://leanprover.github.io/lean4/doc/
- Mathlib4 : https://leanprover-community.github.io/mathlib4_docs/

### Semantic Kernel
- Documentation : https://learn.microsoft.com/semantic-kernel/

---

## Licence

Les notebooks sont distribues sous licence MIT.
Voir LICENSE a la racine du depot pour details.

---

**Derniere mise a jour** : 2026-01-31
