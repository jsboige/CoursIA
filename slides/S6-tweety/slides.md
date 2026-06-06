---
theme: ../theme-ia101
title: "IA Symbolique - TweetyProject"
info: IA 101 - Intelligence artificielle symbolique avec TweetyProject
paginate: true
drawings:
  persist: false
transition: slide-left
mdc: true
layout: cover
---

# TweetyProject — IA Symbolique en Java

- Logiques formelles : Propositionnelle, FOL, Modale, DL
- Argumentation computationnelle : Dung, ASPIC+, ABA
- Revision de croyances et incoherence
- Agents dialogiques et preferences
- Integration Python via JPype

---
layout: section
---

# Plan

---

# Sommaire

## Objectifs pedagogiques

- Decouvrir **TweetyProject** : la bibliotheque Java reference pour l'IA symbolique
- Comprendre les **logiques formelles** et leurs solveurs (SAT, QBF, DL)
- Explorer l'**argumentation computationnelle** : frameworks de Dung et extensions
- Maitriser la **revision de croyances** et la gestion de l'incoherence
- Implementer des **agents dialogiques** capables de debattre et negocier

## Prerequis

- Python 3.10+ · Java 17+ (telechargement auto) · JPype1
- Connaissances de base en logique propositionnelle et FOL

## Duree totale estimee

**~7 heures** (10 notebooks, 20 min a 60 min chacun)

---
layout: section
---

# Fondations

---

# Tweety 1 — Configuration et Ecosystem

## Mise en place de l'environnement

- Telechargement automatique **JDK 17** et des **35 JARs TweetyProject**
- Demarrage JVM via **JPype** depuis Python
- Verification de l'installation : chaque module TweetyProject teste

## Architecture TweetyProject

```python
import jpype
import jpype.imports

# Demarrer la JVM avec tous les JARs
classpath = ":".join(jar_files)
jpype.startJVM(jvmpath, f"-Djava.class.path={classpath}")

from org.tweetyproject.logics.pl.syntax import *
from org.tweetyproject.logics.fol.syntax import *
```

> **Notebook** : `Tweety-1-Setup.ipynb` — 20 min

---

# Tweety 2 — Logiques de Base (PL + FOL)

## Logique Propositionnelle

- Syntaxe : `PlFormula`, `Proposition`, connecteurs (And, Or, Not, Impl)
- Semantique : `PossibleWorld`, `PlBeliefSet`
- Solveurs : `SimplePlReasoner`, `SatSolver` (SAT4J)

## Logique du Premier Ordre

```python
from org.tweetyproject.logics.fol.syntax import FolSignature, FolFormula
from org.tweetyproject.logics.fol.reasoner import SimpleFolReasoner

sig = FolSignature()
sig.add(Sort("Person"))
sig.add(Predicate("Mortal", [sig.getSort("Person")]))
```

- Quantificateurs universels et existentiels
- Unification et resolution FOL

> **Notebook** : `Tweety-2-Basic-Logics.ipynb` — 45 min

---

# Tweety 3 — Logiques Avancees

## Description Logics (DL)

- Ontologies TBox / ABox : concepts, roles, individus
- Raisonnement : subsomption, coherence, instanciation
- Intégration **OWL** via raisonneur HermiT

## Logique Modale et QBF

```python
from org.tweetyproject.logics.ml.syntax import MlFormula
# □φ (necessairement phi) et ◇φ (possiblement phi)
box_phi = Box(phi)    # Necessarily
diamond_phi = Diamond(phi)  # Possibly
```

- **QBF** : formules booleennes quantifiees (∀x ∃y ...)
- **Logique Conditionnelle** : regles conditionnelles et inference non-monotone

> **Notebook** : `Tweety-3-Advanced-Logics.ipynb` — 40 min

---
layout: section
---

# Revision de Croyances

---

# Tweety 4 — Revision de Croyances

## Le probleme de la revision

Quand nouvelles informations **contredisent** les croyances existantes, que faire ?

- **AGM** : postulats de revision (Alchourrón, Gärdenfors, Makinson 1985)
- **CrMas** : base de croyances avec mesure d'incoherence
- **MaxSAT** : maximiser croyances satisfaites sous contraintes

## Mesures d'incoherence

```python
from org.tweetyproject.logics.pl.analysis import *
from org.tweetyproject.logics.pl.sat import Sat4jSolver

solver = Sat4jSolver()
inc_measure = NaiveMusEnumerator(solver)
# Mesure MI (Minimal Inconsistent Subsets)
mi_value = inc_measure.inconsistencyMeasure(belief_base)
```

- **MUS** : Minimal Unsatisfiable Subsets
- **MCS** : Minimal Correction Subsets

> **Notebook** : `Tweety-4-Belief-Revision.ipynb` — 50 min

---
layout: section
---

# Argumentation Computationnelle

---

# Tweety 5 — Argumentation Abstraite (Dung)

## Frameworks de Dung (1990)

Un framework d'argumentation = `(A, →)` : ensemble d'arguments + relation d'attaque

## Semantiques d'extension

| Semantique | Definition |
|-----------|------------|
| **Admissible** | auto-defende, sans attaque interne |
| **Preferred** | maximale admissible |
| **Grounded** | minimale complete |
| **Stable** | attaque tout argument hors de l'extension |

```python
from org.tweetyproject.arg.dung.syntax import DungTheory, Argument, Attack
af = DungTheory()
a, b, c = Argument("a"), Argument("b"), Argument("c")
af.add(Attack(a, b)); af.add(Attack(b, c))
```

> **Notebook** : `Tweety-5-Abstract-Argumentation.ipynb` — 55 min

---

# Tweety 6 — Argumentation Structuree

## ASPIC+ : Arguments structurees

- **Regles strictes** (modus ponens) et **defeasibles** (revisables)
- **Attaques** : rebut, undercut, undermining
- **Preference** sur les regles pour resoudre les conflits

## DeLP et ABA

```python
from org.tweetyproject.arg.aspic.syntax import *
# Regle defeasible : "oiseau => vole"
rule = DefeasibleInferenceRule(flies, [bird])
theory = AspicArgumentationTheory(rules)
reasoner = SimpleAspicReasoner(PreferredSemantics())
```

- **DeLP** (Defeasible Logic Programming) : integration Prolog
- **ABA** (Assumption-Based Argumentation) : hypotheses et contrariness

> **Notebook** : `Tweety-6-Structured-Argumentation.ipynb` — 60 min

---

# Tweety 7a — Frameworks Etendus

## ADF : Abstract Dialectical Frameworks

Generalise les frameworks de Dung : **acceptance conditions** par argument

## Frameworks bipolaires et ponderés

- **Bipolar AF** : attaque + support
- **Weighted AF** : poids numeriques sur les attaques
- **SetAF** : attaques d'ensembles d'arguments

```python
from org.tweetyproject.arg.adf.syntax import Adf, AbstractDialecticalFramework
from org.tweetyproject.arg.bipolar.syntax import BipolarArgFramework
```

- **SAF** (Social AF) : agregation de vote sur les attaques
- **CF2** : semantique pour frameworks avec cycles pairs

> **Notebook** : `Tweety-7a-Extended-Frameworks.ipynb` — 50 min

---

# Tweety 7b — Ranking et Probabiliste

## Semantiques de ranking

Ordonner les arguments par **force** plutot que les grouper en extensions

| Approche | Principe |
|---------|---------|
| **Categoriser** | Iterative graded semantics |
| **BBS** | Burden-Based Semantics |
| **StratInc** | Stratified Incoherence |
| **Euler** | Force numerique (PageRank-style) |

## Argumentation Probabiliste

```python
from org.tweetyproject.arg.prob.syntax import ProbabilisticArgumentationFramework
paf = ProbabilisticArgumentationFramework()
paf.setProbability(arg_a, 0.8)  # prob. que l'argument est present
```

> **Notebook** : `Tweety-7b-Ranking-Probabilistic.ipynb` — 40 min

---
layout: section
---

# Applications

---

# Tweety 8 — Agents Dialogiques

## Protocoles d'argumentation multi-agents

- **Dialogue** : echange structure d'arguments entre agents
- **Persuasion** : convaincre l'adversaire de changer de position
- **Negociation** : trouver un accord mutuellement acceptable
- **Inquiry** : exploration collaborative de la verite

```python
from org.tweetyproject.agents.dialogues.oppmodels import *
from org.tweetyproject.agents.dialogues.lotteries import *

# Agent avec modele d'opinion
agent = GroundedAgent(belief_base, opp_model)
protocol = PersuasionProtocol()
session = DialogueSession(agent1, agent2, protocol)
session.run()
```

> **Notebook** : `Tweety-8-Agent-Dialogues.ipynb` — 35 min

---

# Tweety 9 — Preferences et Vote

## Ordres de preference

- **Preference order** : relations totales / partielles sur alternatives
- **Agregation** : combiner les preferences de plusieurs agents
- **Theorie du vote** : Borda, Copeland, Schulze, STV

```python
from org.tweetyproject.preferences.syntax import PreferenceOrder
from org.tweetyproject.preferences.aggregation import BordaAggregator

prefs = [PreferenceOrder([a, b, c]), PreferenceOrder([b, c, a])]
winner = BordaAggregator().aggregate(prefs)
```

- **Arrow's theorem** : impossibilite du choix social rationnel
- Lien avec `GameTheory/social_choice_lean/` (preuves formelles en Lean 4)

> **Notebook** : `Tweety-9-Preferences.ipynb` — 30 min

---
layout: section
---

# Synthese et Ressources

---

# Ecosysteme TweetyProject

## Modules couverts dans la serie

| Module | Theme | Notebooks |
|--------|-------|-----------|
| `logics.pl`, `logics.fol` | Logiques de base | 2-3 |
| `logics.dl`, `logics.ml` | Logiques avancees | 3 |
| `logics.pl.analysis` | Revision / Incoherence | 4 |
| `arg.dung`, `arg.prob` | Argumentation abstraite | 5, 7b |
| `arg.aspic`, `arg.aba` | Argumentation structuree | 6 |
| `arg.adf`, `arg.bipolar` | Frameworks etendus | 7a |
| `agents.dialogues` | Agents dialogiques | 8 |
| `preferences` | Vote et preferences | 9 |

## Liens avec les autres series

- **S1-argumentation** : fondements theoriques de l'argumentation
- **S7-lean** : preuves formelles des theoremes d'impossibilite (Arrow)
- **03-logique** : cours magistral logique et planification

---

# Pour aller plus loin

## Documentation et references

- **TweetyProject** : https://tweetyproject.org/ (Matthias Thimm)
- **JPype** : https://jpype.readthedocs.io/ (integration Java/Python)
- **Dunne & Bench-Capon** (2002) : Coherence in finite argument systems
- **Dung (1995)** : On the acceptability of arguments
- **Modgil & Prakken (2014)** : ASPIC+ formal definition

## Notebooks connexes dans CoursIA

```
SymbolicAI/
├── Tweety/          ← cette serie (10 notebooks)
├── Lean/            ← preuves formelles (14 notebooks)
└── Argument_Analysis/  ← analyse de textes argumentatifs (5 notebooks)
```

## Extensions possibles

- Intégration avec **Neo4j** pour les graphes d'argumentation
- Visualisation interactive des frameworks (D3.js / Cytoscape)
- Argumentation pour l'**explicabilite des modeles ML**

---
layout: section
---

# Questions?

---
layout: end
---

# Merci

Serie TweetyProject — IA 101

`MyIA.AI.Notebooks/SymbolicAI/Tweety/`
