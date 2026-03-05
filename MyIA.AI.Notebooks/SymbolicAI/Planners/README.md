# Planification Automatique - Automated Planning

Cette serie de notebooks introduit la **Planification Automatique**, une branche fondamentale de l'IA qui genere des sequences d'actions pour atteindre des objectifs.

## Objectifs d'apprentissage

A l'issue de cette serie, vous saurez :
1. **Modeliser** des problemes de planification en PDDL (Planning Domain Definition Language)
2. **Utiliser** les planificateurs modernes (Fast Downward, OR-Tools, unified-planning)
3. **Comprendre** les heuristiques de recherche (h-add, h-max, h-FF, LM-cut)
4. **Etendre** la planification au temporel, hierarchique et neuro-symbolique

## Structure

**13 notebooks** organises en 5 parties | **Duree totale** : ~8h

### Partie 0 : Environnement (00-Environment/)

| # | Notebook | Kernel | Contenu | Duree | Statut |
|---|----------|--------|---------|-------|--------|
| 0 | [Planners-0-Setup](00-Environment/Planners-0-Setup.ipynb) | Python | Installation unified-planning, OR-Tools, Docker Fast Downward | 20 min | COMPLET |

### Partie 1 : Fondations (01-Foundation/)

| # | Notebook | Kernel | Contenu | Duree | Statut |
|---|----------|--------|---------|-------|--------|
| 1 | [Planners-1-Introduction](01-Foundation/Planners-1-Introduction.ipynb) | Python | Concepts, modele STRIPS, triptyque Etat-Action-But | 30 min | COMPLET |
| 2 | [Planners-2-PDDL-Basics](01-Foundation/Planners-2-PDDL-Basics.ipynb) | Python | Syntaxe PDDL, domaines, problemes, predicats, actions | 40 min | COMPLET |
| 3 | [Planners-3-State-Space](01-Foundation/Planners-3-State-Space.ipynb) | Python | Espaces d'etats, graphes de recherche, explosion combinatoire | 35 min | COMPLET |

### Partie 2 : Planification Classique (02-Classical/)

| # | Notebook | Kernel | Contenu | Duree | Statut |
|---|----------|--------|---------|-------|--------|
| 4 | [Planners-4-Fast-Downward](02-Classical/Planners-4-Fast-Downward.ipynb) | Python | Architecture FD, Docker, A*, GBFS, EHC, heuristiques | 45 min | COMPLET |
| 5 | [Planners-5-Heuristics](02-Classical/Planners-5-Heuristics.ipynb) | Python | h-add, h-max, h-FF, landmarks | 40 min | COMPLET |
| 6 | [Planners-6-Domains](02-Classical/Planners-6-Domains.ipynb) | Python | Blocks World, Logistics, Gripper, Ferry, Hanoi | 50 min | COMPLET |

### Partie 3 : Approches Avancees (03-Advanced/)

| # | Notebook | Kernel | Contenu | Duree | Statut |
|---|----------|--------|---------|-------|--------|
| 7 | [Planners-7-OR-Tools](03-Advanced/Planners-7-OR-Tools.ipynb) | Python | CP-SAT, programmation par contraintes, scheduling | 45 min | COMPLET |
| 8 | [Planners-8-Temporal](03-Advanced/Planners-8-Temporal.ipynb) | Python | PDDL 2.1, durees, parallelisme, ordonnancement | 40 min | COMPLET |
| 9 | [Planners-9-HTN](03-Advanced/Planners-9-HTN.ipynb) | Python | Hierarchical Task Networks, methodes, decomposition | 45 min | COMPLET |

### Partie 4 : Neuro-Symbolique (04-NeuroSymbolic/)

| # | Notebook | Kernel | Contenu | Duree | Statut |
|---|----------|--------|---------|-------|--------|
| 10 | [Planners-10-LLM-Planning](04-NeuroSymbolic/Planners-10-LLM-Planning.ipynb) | Python | LLMs pour la planification, prompting, plan repair | 50 min | COMPLET |
| 11 | [Planners-11-Unified-Planning](04-NeuroSymbolic/Planners-11-Unified-Planning.ipynb) | Python | Interface unifiee, multi-solveurs, comparaisons | 40 min | COMPLET |
| 12 | [Planners-12-LOOP](04-NeuroSymbolic/Planners-12-LOOP.ipynb) | Python | Learning to Plan, modeles neuronaux pour heuristiques | 45 min | COMPLET |

---

## Niveaux de difficulte

| Niveau | Description | Notebooks |
|--------|-------------|-----------|
| Foundation | Introduction, concepts de base | 0, 1, 2, 3 |
| Intermediate | Algorithmes, outils pratiques | 4, 5, 6, 7, 8, 9 |
| Advanced | Extensions, recherche | 10, 11, 12 |

## Prerequis

### Connaissances requises
- Python 3.9+ (programmation orientee objet)
- Algorithmique de base (graphes, recherche)
- Logique propositionnelle (predicats, connecteurs)

### Pour les notebooks avances
- Bases en machine learning (notebooks 10-12)
- API OpenAI/Anthropic (notebook 10)
- Connaissance de PDDL (notebooks 8-9)

## Installation

### 1. Environnement Python

```bash
# Creer un environnement virtuel
python -m venv venv
source venv/bin/activate  # Linux/Mac
# ou venv\Scripts\activate  # Windows

# Installer les dependances
pip install unified-planning ortools numpy matplotlib networkx
```

### 2. Docker pour Fast Downward (recommande)

```bash
# Telecharger l'image Docker Fast Downward
docker pull aiplanning/fast-downward
```

### 3. Verification

```bash
python -c "import unified_planning; from ortools.sat.python import cp_model; print('OK')"
docker run --rm aiplanning/fast-downward --help
```

## Technologies utilisees

| Technologie | Description | Notebooks |
|-------------|-------------|-----------|
| **unified-planning** | Interface Python unifiee pour planificateurs | Tous |
| **Fast Downward** | Planificateur optimal (IPC winner) | 4, 5, 6 |
| **OR-Tools CP-SAT** | Programmation par contraintes Google | 7 |
| **PDDL** | Langage standard de planification | 2-9 |
| **OpenAI/Anthropic API** | LLMs pour planification | 10 |

## Architecture de la serie

```
SymbolicAI/Planners/
├── README.md
├── 00-Environment/
│   └── Planners-0-Setup.ipynb           # Configuration environnement
├── 01-Foundation/
│   ├── Planners-1-Introduction.ipynb    # Concepts, STRIPS
│   ├── Planners-2-PDDL-Basics.ipynb     # Syntaxe PDDL
│   └── Planners-3-State-Space.ipynb     # Espaces d'etats
├── 02-Classical/
│   ├── Planners-4-Fast-Downward.ipynb   # A*, heuristiques
│   ├── Planners-5-Heuristics.ipynb      # h-add, h-max, h-FF
│   └── Planners-6-Domains.ipynb         # Domaines classiques
├── 03-Advanced/
│   ├── Planners-7-OR-Tools.ipynb        # CP-SAT
│   ├── Planners-8-Temporal.ipynb        # Planification temporelle
│   └── Planners-9-HTN.ipynb             # Planification hierarchique
├── 04-NeuroSymbolic/
│   ├── Planners-10-LLM-Planning.ipynb   # LLM + Planning
│   ├── Planners-11-Unified-Planning.ipynb # Interface unifiee
│   └── Planners-12-LOOP.ipynb           # Learning to Plan
└── archive/
    └── Fast-Downward-Legacy.ipynb       # Version archivee
```

## PDDL - Planning Domain Definition Language

PDDL est le langage standard pour decrire des problemes de planification.

### Domaine (domain.pddl)

```lisp
(define (domain blocks)
  (:requirements :strips :typing)
  (:types block)
  (:predicates
    (on ?x - block ?y - block)
    (clear ?x - block)
    (ontable ?x - block)
    (holding ?x - block)
    (handempty)
  )
  (:action pick-up
    :parameters (?x - block)
    :precondition (and (clear ?x) (ontable ?x) (handempty))
    :effect (and (holding ?x) (not (ontable ?x)) (not (clear ?x)) (not (handempty))))
)
```

### Probleme (problem.pddl)

```lisp
(define (problem blocks-tower)
  (:domain blocks)
  (:objects a b c - block)
  (:init
    (ontable a) (ontable b) (ontable c)
    (clear a) (clear b) (clear c)
    (handempty)
  )
  (:goal (and (on a b) (on b c)))
)
```

## Domaines PDDL classiques

Les notebooks utilisent les domaines standards de l'IPC (International Planning Competition) :

| Domaine | Description | Complexite |
|---------|-------------|------------|
| **Blocks World** | Empiler des blocs | Simple |
| **Gripper** | Robot avec pinces deplace des balles | Simple |
| **Logistics** | Transport de colis entre lieux | Moyen |
| **Depots** | Gestion d'entrepot avec grues | Moyen |
| **Satellite** | Planification d'observations spatiales | Complexe |

## Concepts cles

| Concept | Definition |
|---------|------------|
| **STRIPS** | Modele de planification avec preconditions/add/delete (1971) |
| **PDDL** | Planning Domain Definition Language - standard IPC depuis 1998 |
| **Heuristique** | Fonction estimant le cout pour atteindre le but |
| **A*** | Algorithme de recherche optimale avec heuristique admissible |
| **Landmark** | Fait qui doit etre vrai a un moment du plan |
| **HTN** | Hierarchical Task Network - decomposition de taches |
| **LM-cut** | Heuristique admissible basee sur les landmarks |

## Comparaison des approches

| Approche | Optimalite | Vitesse | Expressivite |
|----------|------------|---------|--------------|
| **A* + h-max** | Admissible | Rapide | STRIPS |
| **A* + LM-cut** | Optimal | Moyen | STRIPS |
| **GBFS + h-FF** | Satisficing | Tres rapide | STRIPS+ |
| **CP-SAT** | Optimal | Variable | Contraintes |
| **HTN** | Variable | Rapide | Hierarchique |

## Fast Downward

Planificateur optimal developpe a l'Universite de Bale :

| Caracteristique | Description |
|-----------------|-------------|
| **Algorithmes** | A*, GBFS, LAMA |
| **Heuristiques** | FF, add, landmark-cut |
| **Performance** | Gagnant IPC multiple fois |

### Utilisation via Docker

```bash
# Execution via Docker
docker run --rm -v $(pwd)/pddl:/data aiplanning/fast-downward \
  /data/domain.pddl /data/problem.pddl --search "astar(lmcut())"
```

### Utilisation via unified-planning

```python
from unified_planning.shortcuts import *
from up_fast_downward import FastDownwardPDDLPlanner

# Definir le probleme avec unified-planning
problem = Problem('my-problem')
# ... (voir notebooks pour details)

# Resoudre avec Fast Downward
planner = FastDownwardPDDLPlanner()
result = planner.solve(problem)
```

## Navigation guide

### Progression recommandee

1. **Debutants** : Commencer par `00-Environment/Planners-0-Setup.ipynb`
2. **Fondations** : Suivre `01-Foundation/` dans l'ordre
3. **Pratique** : Explorer `02-Classical/` pour les outils
4. **Avance** : `03-Advanced/` et `04-NeuroSymbolic/` selon interets

### Liens de navigation

Chaque notebook contient :
- Header avec liens vers precedent/suivant
- Navigation vers cet index
- Ancres internes pour les sections

## Tests et validation

```bash
# Verifier la structure des notebooks
python scripts/notebook_tools/notebook_tools.py validate MyIA.AI.Notebooks/SymbolicAI/Planners --quick

# Execution complete (mode batch)
BATCH_MODE=true python scripts/notebook_tools/notebook_tools.py execute MyIA.AI.Notebooks/SymbolicAI/Planners
```

## Ressources externes

### Documentation
- [unified-planning](https://github.com/aiplan4eu/unified-planning) - Bibliotheque Python
- [Fast Downward](https://www.fast-downward.org/) - Planificateur de reference
- [PDDL Reference](https://planning.wiki/) - Documentation PDDL complete

### Cours et tutorials
- [AI Planning - University of Edinburgh](https://www.coursera.org/learn/ai-planning)
- [Classical Planning - Stanford](https://www.youtube.com/watch?v=WEDagb6TsK8)
- [IPC Benchmarks](https://github.com/aibasel/downward-benchmarks) - Problemes standards

### Publications
- Helmert (2006) - "The Fast Downward Planning System"
- Hoffmann & Nebel (2001) - "The FF Planning System"
- Richter & Westphal (2010) - "LAMA: Planner"

## Relation avec SymbolicAI

La planification automatique est une branche de l'IA symbolique :
- Raisonnement sur actions et etats
- Recherche dans espace d'etats
- Heuristiques admissibles pour optimalite

Voir aussi :
- [Tweety](../Tweety/) - Logique et argumentation
- [Lean](../Lean/) - Verification formelle
- [Z3](../Z3/) - Solveur SMT

## Contribution

Pour contribuer a cette serie :

1. Suivre les conventions de [CLAUDE.md](../../../CLAUDE.md)
2. Respecter la structure pedagogique (header, objectifs, interpretations)
3. Utiliser `scripts/notebook_tools/notebook_helpers.py` pour la manipulation
4. Tester avec `python scripts/notebook_tools/notebook_tools.py validate`

## Licence

Voir la licence du repository principal.

---

**Navigation** : [SymbolicAI](../README.md) | [Accueil](../../../CLAUDE.md)
