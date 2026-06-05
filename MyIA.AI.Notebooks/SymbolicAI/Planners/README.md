# Planification Automatique - Automated Planning

<!-- CATALOG-STATUS
series: SymbolicAI-Planners
pedagogical_count: 13
breakdown: Environment=1, Foundation=3, Classical=3, Advanced=3, NeuroSymbolic=3
maturity: PRODUCTION=9, BETA=4
-->

Cette serie de notebooks introduit la **Planification Automatique**, une branche fondamentale de l'IA qui genere des sequences d'actions pour atteindre des objectifs.

La planification repond a une question differente de celle de l'apprentissage : non pas « que predire ? » mais « **que faire ?** ». A partir d'un modele du monde — un etat initial, des actions avec leurs preconditions et effets, un but — un planificateur cherche automatiquement une suite d'actions qui mene au but. C'est une technologie eprouvee : elle pilote des robots (manipulation, navigation), optimise la logistique et l'ordonnancement, et a dirige des engins spatiaux autonomes (Remote Agent sur Deep Space 1, planification d'activites des rovers martiens). Le langage **PDDL** a standardise la maniere de decrire ces problemes, donnant naissance a tout un ecosysteme de solveurs comparables. La planification connait aujourd'hui un regain d'interet avec les LLMs, comme moyen de doter les modeles de langage d'une capacite d'action verifiable et orientee vers un but.

**13 notebooks** | **5 parties** | **~8h**

**A qui s'adresse cette serie** : etudiants en IA, ingenieurs en robotique et logistique, developpeurs souhaitant integrer la planification symbolique dans leurs applications. Aucun prerequis en planification : les concepts sont introduits progressivement depuis les fondements STRIPS jusqu'aux approches neuro-symboliques modernes.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 13 (1 setup + 3 foundation + 3 classical + 3 advanced + 3 neuro-symbolic) |
| Duree totale | ~8h |
| Langage | Python 3.9+ |
| Kernel | Python 3 |
| Solveurs | Fast Downward, OR-Tools CP-SAT, unified-planning |
| Environnement | Docker (Fast Downward), pip (Python packages) |

## Parcours d'apprentissage

### Phase 1 : Fondations (Notebooks 1-3, ~2h)

La serie debute par le notebook Setup (0) qui configure automatiquement l'environnement : installation de `unified-planning`, OR-Tools, verification de Docker et lancement du conteneur Fast Downward. Le notebook 1 (Introduction) presente le triptyque fondamental Etat-Action-But, le modele STRIPS (1971) avec ses hypotheses — statique, deterministe, observable, discret, instantane — et le contexte historique depuis Fikes & Nilsson jusqu'aux LLMs modernes. Le notebook 2 (PDDL-Basics) plonge dans la syntaxe PDDL : domaines, problemes, types, predicats, actions, preconditions et effets. Le notebook 3 (State-Space) explore l'explosion combinatoire ($O(2^n)$ predicats) et la necessite des heuristiques pour guider la recherche dans l'espace d'etats. A l'issue de cette phase, vous savez modeliser un probleme en PDDL et comprendre pourquoi la recherche aveugle ne suffit pas.

### Phase 2 : Planification Classique (Notebooks 4-6, ~3h)

Les notebooks 4 a 6 constituent le coeur technique de la serie. Le notebook 4 (Fast-Downward) presente l'architecture en trois etapes de Fast Downward (translator PDDL→SAS+, preprocessor C++, search C++) et montre comment l'executer via Docker et unified-planning. Les algorithmes de recherche (A*, Greedy, EHC) y sont testes sur Blocks World et Logistics. Le notebook 5 (Heuristics) approfondit la theorie : classification admissible/non-admissible ($h^{add}$, $h^{max}$, $h^{FF}$, LM-cut), comparaison experimentale des heuristiques sur le nombre de noeuds expanses, et guide de selection. Le notebook 6 (Domains) couvre les domaines standards de l'IPC (Blocks World, Logistics, Gripper, Satellite) avec des problemes de complexite croissante. A l'issue, vous pouvez configurer un planificateur optimal, choisir l'heuristique adequat, et modeliser n'importe quel domaine IPC.

### Phase 3 : Approches Avancees (Notebooks 7-9, ~3h)

La planification classique epuise ses limites des que les problemes deviennent trop grands pour l'exploration d'etats. Les notebooks 7 a 6 proposent des alternatives. Le notebook 7 (OR-Tools) introduce la programmation par contraintes avec CP-SAT de Google OR-Tools : modelisation de contraintes (all-different, cumulative, table), scheduling, et optimisation multi-objectif. Le notebook 8 (Temporal) etend au domaine temporel avec PDDL 2.1 : durées d'actions, parallelisme, contraintes temporelles simples et denses, ordonnancement de taches. Le notebook 9 (HTN) presente la planification hierarchique (Task Networks) : taches primitives vs abstraites, methodes de decomposition, langage HDDL, solveur inspire de SHOP2, et comparaison avec STRIPS. A l'issue, vous disposez de trois paradigmes complementaires pour les problemes qui depassent la planification classique.

### Phase 4 : Neuro-Symbolique (Notebooks 10-12, ~3h)

La derniere partie explore la frontier entre IA symbolique et apprentissage profond. Le notebook 10 (LLM-Planning) montre comment les Large Language Models peuvent genérer des plans a partir de descriptions en langage naturel, le prompting pour la planification, et le plan repair. Le notebook 11 (Unified-Planning) detaille l'interface unifiee `unified-planning` : connection a plusieurs solveurs en quelques lignes, comparaison croisée des performances, et portabilite du modele PDDL entre moteurs. Le notebook 12 (LOOP) introduit le paradigme **Learning to Plan** : architecture LOOP (state encoder, policy network, value network), encodage PDDL en tenseurs (one-hot, GNN), entraînement par imitation et renforcement, resultats sur benchmarks IPC (85.8% coverage), et comparison avec KRCL. Ce notebook conclut la serie avec les tendances futures : foundation models, meta-learning, inverse reinforcement learning.

### Parcours alternatifs

#### Parcours rapide (4h, minimum viable)
Pour découvrir l'essentiel rapidement :
1. `0-Setup` (20 min) : installer et verifier l'environnement
2. `1-Introduction` (30 min) : comprendre les concepts
3. `4-Fast-Downward` (45 min) : executer un vrai planificateur
4. `11-Unified-Planning` (40 min) : comparer les solveurs

#### Parcours classique (5h, optimalite)
Pour maitriser les planificateurs optimaux :
1. `0-Setup` → `1-Introduction` → `2-PDDL-Basics` → `3-State-Space`
2. `4-Fast-Downward` → `5-Heuristics` → `6-Domains`

#### Parcours contraintes + temporel (6h, scheduling)
Pour les applications de planification par contraintes et temporelles :
1. `0-Setup` → `1-Introduction` → `2-PDDL-Basics`
2. `7-OR-Tools` → `8-Temporal` → `9-HTN`

#### Parcours neuro-symbolique (5h, recherche)
Pour les approches combinees apprentissage profond + symbolique :
1. `0-Setup` → `1-Introduction` → `4-Fast-Downward`
2. `10-LLM-Planning` → `11-Unified-Planning` → `12-LOOP`

## Quel parcours choisir ?

### Si vous débutez en planification
**Commencez par les fondations.** Le notebook 1 (Introduction) pose le vocabulaire (etat, action, but, STRIPS) et le contexte historique. Le notebook 2 (PDDL-Basics) apprend la syntaxe standard du domaine. Sans ces bases, les notebooks suivants seront difficiles a suivre.

**Passez a la planification classique quand :** vous avez un domaine PDDL defini et voulez trouver un plan optimal rapidement. Fast Downward + LM-cut est le choix par defaut.

### Si vous venez de la recherche operationnelle
**Commencez par OR-Tools (notebook 7).** Le CP-SAT est familier aux optimiseurs : modelisation par contraintes, fonctions objectif, solveur commercial (ou open-source). La transition vers la planification est naturelle.

**Passez a PDDL quand :** vous avez besoin de la portabilite du modele (meme domaine, solveurs multiples) ou que vous voulez exploiter les heuristiques specialisees de Fast Downward.

### Si vous ne savez pas quoi choisir

| Critere | Recommandation |
|---------|----------------|
| Juste decouvrir la planification | **Planners-0-Setup** + **Planners-1-Introduction** |
| Un premier planificateur qui marche | **Planners-4-Fast-Downward** (Docker + Blocks World) |
| Optimisation de scheduling | **Planners-7-OR-Tools** |
| Planification hierarchique | **Planners-9-HTN** (SHOP2, decomposition) |
| Frontier LLM + IA | **Planners-10-LLM-Planning** |
| Approche neuro-symbolique avancée | **Planners-12-LOOP** (85.8% IPC coverage) |
| Comparer tous les solveurs | **Planners-11-Unified-Planning** |

## Structure

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

## Objectifs d'apprentissage

A l'issue de cette serie, vous saurez :

1. **Modeliser** des problemes de planification en PDDL (Planning Domain Definition Language)
2. **Utiliser** les planificateurs modernes (Fast Downward, OR-Tools, unified-planning)
3. **Comprendre** les heuristiques de recherche ($h^{add}$, $h^{max}$, $h^{FF}$, LM-cut)
4. **Etendre** la planification au temporel, hierarchique et neuro-symbolique

## Niveaux de difficulte

| Niveau | Description | Notebooks |
|--------|-------------|-----------|
| Foundation | Introduction, concepts de base | 0, 1, 2, 3 |
| Intermediate | Algorithmes, outils pratiques | 4, 5, 6, 7, 8, 9 |
| Advanced | Extensions, recherche | 10, 11, 12 |

## Contenu detaille des notebooks

Chaque notebook introduit un concept ou modele specifique. Le tableau ci-dessous resume en une ligne l'apport pedagogique de chacun — au-dela du titre, c'est le **concept cle** qu'il enseigne.

| # | Notebook | Apport pedagogique |
|---|----------|-------------------|
| 0 | Setup | Boucle environnement : verification Python → installation packages → Docker → premier PDDL |
| 1 | Introduction | Triptyque Etat-Action-But, hypotheses STRIPS (1971), taxonomie des paradigmes |
| 2 | PDDL-Basics | Syntaxe PDDL : domaines, problemes, types, predicats, actions, preconditions, effets |
| 3 | State-Space | Explosion combinatoire $O(2^n)$, necessite des heuristiques, graphe d'etats |
| 4 | Fast-Downward | Architecture 3 etapes (translator/preprocessor/search), A* vs Greedy vs EHC via Docker |
| 5 | Heuristics | Classification admissible/non-admissible : $h^{add}$, $h^{max}$, $h^{FF}$, LM-cut, comparison expériméntale |
| 6 | Domains | Domaines IPC standards (Blocks, Logistics, Gripper, Satellite), complexité croissante |
| 7 | OR-Tools | CP-SAT, programmation par contraintes, modelisation de scheduling, contraintes alldifferent |
| 8 | Temporal | PDDL 2.1, durations d'actions, parallelisme, contraintes temporelles, ordonnancement |
| 9 | HTN | Planification hierarchique : taches primitives/abstraites, methodes, HDDL, SHOP2 |
| 10 | LLM-Planning | Planification avec LLMs, prompting, plan repair, limites et avantages |
| 11 | Unified-Planning | Interface multi-solveurs, comparaison croisée, portabilité du modele |
| 12 | LOOP | Learning to Plan : state encoder, policy network, value network, 85.8% IPC coverage |

---

## Vue d'ensemble des parties

### Partie 0 : Environnement (00-Environment/)

| # | Notebook | Kernel | Contenu | Duree |
|---|----------|--------|---------|-------|
| 0 | [Planners-0-Setup](00-Environment/Planners-0-Setup.ipynb) | Python | Installation unified-planning, OR-Tools, Docker Fast Downward | 20 min |

### Partie 1 : Fondations (01-Foundation/)

| # | Notebook | Kernel | Contenu | Duree |
|---|----------|--------|---------|-------|
| 1 | [Planners-1-Introduction](01-Foundation/Planners-1-Introduction.ipynb) | Python | Concepts, modele STRIPS, triptyque Etat-Action-But | 30 min |
| 2 | [Planners-2-PDDL-Basics](01-Foundation/Planners-2-PDDL-Basics.ipynb) | Python | Syntaxe PDDL, domaines, problemes, predicats, actions | 40 min |
| 3 | [Planners-3-State-Space](01-Foundation/Planners-3-State-Space.ipynb) | Python | Espaces d'etats, graphes de recherche, explosion combinatoire | 35 min |

### Partie 2 : Planification Classique (02-Classical/)

| # | Notebook | Kernel | Contenu | Duree |
|---|----------|--------|---------|-------|
| 4 | [Planners-4-Fast-Downward](02-Classical/Planners-4-Fast-Downward.ipynb) | Python | Architecture FD, Docker, A*, GBFS, EHC, heuristiques | 45 min |
| 5 | [Planners-5-Heuristics](02-Classical/Planners-5-Heuristics.ipynb) | Python | h-add, h-max, h-FF, landmarks | 40 min |
| 6 | [Planners-6-Domains](02-Classical/Planners-6-Domains.ipynb) | Python | Blocks World, Logistics, Gripper, Ferry, Hanoi | 50 min |

### Partie 3 : Approches Avancees (03-Advanced/)

| # | Notebook | Kernel | Contenu | Duree |
|---|----------|--------|---------|-------|
| 7 | [Planners-7-OR-Tools](03-Advanced/Planners-7-OR-Tools.ipynb) | Python | CP-SAT, programmation par contraintes, scheduling | 45 min |
| 8 | [Planners-8-Temporal](03-Advanced/Planners-8-Temporal.ipynb) | Python | PDDL 2.1, durees, parallelisme, ordonnancement | 40 min |
| 9 | [Planners-9-HTN](03-Advanced/Planners-9-HTN.ipynb) | Python | Hierarchical Task Networks, methodes, decomposition | 45 min |

### Partie 4 : Neuro-Symbolique (04-NeuroSymbolic/)

| # | Notebook | Kernel | Contenu | Duree |
|---|----------|--------|---------|-------|
| 10 | [Planners-10-LLM-Planning](04-NeuroSymbolic/Planners-10-LLM-Planning.ipynb) | Python | LLMs pour la planification, prompting, plan repair | 50 min |
| 11 | [Planners-11-Unified-Planning](04-NeuroSymbolic/Planners-11-Unified-Planning.ipynb) | Python | Interface unifiee, multi-solveurs, comparaisons | 40 min |
| 12 | [Planners-12-LOOP](04-NeuroSymbolic/Planners-12-LOOP.ipynb) | Python | Learning to Plan, modeles neuronaux pour heuristiques | 45 min |

---

## Qu'est-ce que la planification ?

| Aspect | Description |
|--------|-------------|
| **Entree** | Etat initial + modele du domaine + condition but |
| **Sortie** | Sequence d'actions (plan) executable |
| **Hypothese** | Deterministe, observable, discret (STRIPS classique) |
| **Complexite** | NP-complet en general ($O(2^n)$ etats possibles) |
| **Garantie** | Optimal si heuristique admissible (A*) |

## Prerequis

### Connaissances requises

- **Python 3.9+** : programmation orientee objet, types, dataclasses
- **Algorithmique de base** : graphes (BFS, DFS, A*), recherche
- **Logique propositionnelle** : predicats, connecteurs logiques, quantificateurs

### Pour les notebooks avances

- **Bases en machine learning** (notebooks 10-12) : reseaux de neurones, loss, backpropagation
- **API OpenAI/Anthropic** (notebook 10) : prompts LLM, generation de texte
- **Connaissance de PDDL** (notebooks 8-9) : domains, problems, types

### Pour les notebooks pratiques

- **Docker** (notebooks 4-6) : execution du conteneur Fast Downward sur le port 8200
- **OR-Tools** (notebook 7) : modelisation de contraintes, solveur CP-SAT

## Prerequis techniques

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
# Telecharger l'image Docker Fast Downward (serveur HTTP port 8200)
docker pull jsboige/coursia-fast-downward:latest
```

L'image fournit un serveur API HTTP sur le port 8200. Les notebooks appellent l'endpoint `/plan` avec un payload JSON `{domain, problem, search}` et recoivent le plan optimal.

### 3. Verification

```bash
python -c "import unified_planning; from ortools.sat.python import cp_model; print('OK')"
# Verifier le serveur Fast Downward (port 8200)
curl -s http://localhost:8200/health
```

## Outils couverts

| Outil | Description | Notebooks |
|-------|-------------|-----------|
| **unified-planning** | Interface Python unifiee pour planificateurs PDDL | Tous |
| **Fast Downward** | Planificateur optimal IPC winner (A*, LM-cut) | 4, 5, 6 |
| **OR-Tools CP-SAT** | Solveur de contraintes Google (scheduling) | 7 |
| **PDDL** | Planning Domain Definition Language (standard IPC) | 2-9 |
| **HDDL** | Hierarchical Domain Definition Language (HTN) | 9 |
| **OpenAI/Anthropic API** | LLMs pour generation de plans | 10 |
| **PyTorch** | Reseaux de neurones pour heuristiques (LOOP) | 12 |

## Domaines PDDL classiques

Les notebooks utilisent les domaines standards de l'IPC (International Planning Competition) :

| Domaine | Description | Complexite | Notebooks |
|---------|-------------|------------|-----------|
| **Blocks World** | Empiler des blocs pour une tour | Simple | 1, 2, 4, 5, 6 |
| **Gripper** | Robot avec pinces deplace des balles | Simple | 4, 6, 12 |
| **Logistics** | Transport de colis entre lieux avec vehicules | Moyen | 4, 6, 8, 9 |
| **Depots** | Gestion d'entrepot avec grues | Moyen | 6 |
| **Satellite** | Planification d'observations spatiales | Complexe | 6 |
| **Hanoi** | Tour de Hanoi (recursivite naturelle) | Moyen | 6 |

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

## Comparaison des approches

| Approche | Optimalite | Vitesse | Expressivite |
|----------|------------|---------|--------------|
| **A* + LM-cut** | Admissible | Rapide | STRIPS |
| **A* + FF** | Non garanti | Tres rapide | STRIPS+ |
| **GBFS + FF** | Non | Tres rapide | STRIPS+ |
| **CP-SAT** | Optimal | Variable | Contraintes |
| **HTN** | Variable | Rapide | Hierarchique |
| **LOOP** | Non | Variable | Generalise |

## Fast Downward

Planificateur optimal developpe a l'Universite de Bale :

| Caracteristique | Description |
|-----------------|-------------|
| **Architectures** | Translator (PDDL→SAS+) → Preprocessor → Search |
| **Algorithmes** | A*, GBFS (eager/lazy), EHC, LAMA |
| **Heuristiques** | FF, add, hmax, LM-cut, merge-and-shrink |
| **Performance** | Gagnant IPC multiple fois |

### Utilisation via Docker (serveur HTTP)

```bash
# Lancer le conteneur Fast Downward (port 8200)
docker run -d --name coursia-fast-downward -p 8200:8200 jsboige/coursia-fast-downward:latest

# Soumettre un probleme via l'API HTTP
curl -X POST http://localhost:8200/plan \
  -H "Content-Type: application/json" \
  -d '{"domain": "<domain.pddl>", "problem": "<problem.pddl>", "search": "astar(lmcut())"}'
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

## HTN - Planification Hierarchique

La planification HTN (Hierarchical Task Network) structure la recherche par decomposition de taches :

| Concept | Definition |
|---------|------------|
| **Tache primitive** | Action directement executable (ex: `drive(truck, A, B)`) |
| **Tache abstraite** | Tache a decomposer (ex: `deliver(pkg, A, B)`) |
| **Methode** | Regle de decomposition avec preconditions et sous-taches |
| **HDDL** | Langage standard pour domaines HTN (extension de PDDL) |

### Algorithme SHOP2

SHOP2 (Simple Hierarchical Ordered Planner 2) utilise la decomposition ordonnee :

1. Traiter la premiere tache de la liste
2. Si primitive : verifier preconditions, appliquer, passer a la suivante
3. Si abstraite : choisir une methode applicable, remplacer par sous-taches
4. Backtracking : essayer la methode suivante si echec

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
| **CP-SAT** | Constraint Programming-Satisfiability (OR-Tools) |
| **Learning to Plan** | Apprentissage de heuristiques par reseaux de neurones |
| **LOOP** | Framework neuro-symbolique, 85.8% coverage IPC |

## Caracteristiques de la serie

| Caracteristique | Description |
|-----------------|-------------|
| **Progression** | Fondations → Classique → Avance → Neuro-symbolique |
| **Pratique** | Chaque notebook contient des exemples executes et des exercices |
| **Outils reels** | Fast Downward (IPC winner), OR-Tools (Google), unified-planning |
| **Domaines IPC** | Blocks World, Logistics, Gripper — les memes que les competitions |
| **Output verify** | Tous les notebooks sont executes avec outputs inclus |
| **Navigation** | Headers avec liens precedent/suivant dans chaque notebook |

## Quick Start

```bash
# 1. Installer les dependances Python
pip install unified-planning ortools numpy matplotlib networkx

# 2. Verifier l'installation
python -c "import unified_planning; from ortools.sat.python import cp_model; print('OK')"

# 3. Premier notebook (introduction aux concepts)
jupyter notebook 01-Foundation/Planners-1-Introduction.ipynb
```

Pour les notebooks 4-6 (Fast Downward), l'image Docker `jsboige/coursia-fast-downward` fournit un serveur API HTTP sur le port 8200 : `docker pull jsboige/coursia-fast-downward:latest`. Les notebooks theoriques (1-3, 7-12) ne necessitent que Python.

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
- [OR-Tools CP-SAT](https://developers.google.com/optimization/cp/cp_sat) - Documentation Google

### Cours et tutorials

- [AI Planning - University of Edinburgh](https://www.coursera.org/learn/ai-planning)
- [Classical Planning - Stanford](https://www.youtube.com/watch?v=WEDagb6TsK8)
- [IPC Benchmarks](https://github.com/aibasel/downward-benchmarks) - Problemes standards

### Publications

| Reference | Couverture |
|-----------|------------|
| Ghallab, Nau & Traverso, *Automated Planning: Theory and Practice* (2004) | Textbook de reference, toute la serie |
| Russell & Norvig, *AIMA* 4e ed., ch. 10-11 | Cadre general planification |
| Helmert, "The Fast Downward Planning System" (2006) | Notebooks 4-6 |
| Hoffmann & Nebel, "The FF Planning System" (2001) | Heuristique h-FF, notebook 5 |
| Richter & Westphal, "LAMA: Planner" (2010) | Landmarks, notebook 5 |
| Fox & Long, "PDDL2.1: An Extension to PDDL for Expressing Temporal Planning Domains" (2003) | Notebook 8 |
| Erol, Hendler & Nau, "HTN Planning: Complexity and Expressivity" (1994) | Notebook 9 |
| Valmeekam et al., "On the Planning Abilities of Large Language Models" (2024) | Notebook 10 |

## Relation avec SymbolicAI

La planification automatique est une branche de l'IA symbolique :

- Raisonnement sur actions et etats
- Recherche dans espace d'etats
- Heuristiques admissibles pour optimalite

### Ponts avec les autres series

| Serie | Connection | Details |
| ----- | ---------- | ------- |
| **[Tweety](../Tweety/)** | Logique et argumentation | Les solveurs SAT/CSP de Tweety complementent les planificateurs PDDL. Les dialogues argumentatifs (Tweety-8) sont des instances de planification multi-agents. |
| **[Lean](../Lean/)** | Verification formelle | Les plans generes peuvent etre verifies formellement. Les heuristiques d'admissibilite (h-max, LM-cut) reposent sur des preuves de correction similaires aux tactiques Lean. |
| **[SmartContracts](../SmartContracts/)** | Execution planifiee | Les smart contracts DeFi (liquidations, arbitrage) sont des problemes de planification sous contraintes temporelles et de gaz. Le notebook SC-14 (verification formelle) croise OR-Tools (Planners-7). |
| **[GameTheory](../../GameTheory/)** | Jeux sequentiels | La recherche adversariale (A*, minimax) est commune a la planification classique et a la theorie des jeux. Les jeux cooperatifs (Shapley) sont des problemes d'allocation de taches planifiables. |
| **[Search](../../Search/)** | Fondements communs | La serie Search couvre les algorithmes de base (BFS, DFS, A*) utilises dans les planificateurs. CSP (Search Part2) correspond a OR-Tools CP-SAT (Planners-7). |
| Lecture transversale | [La mer qui monte](../../../docs/grothendieckian-lens.md) | Grille de lecture grothendieckienne du depot : changement de representation, certification A/B/C |

## Cross-series Bridges

| Serie | Lien | Connection |
| ------- | ------ | ----------- |
| [Lean](../Lean/README.md) | Verification formelle | Les plans PDDL generes peuvent etre verifies formellement dans Lean |
| [Tweety](../Tweety/README.md) | Logique et argumentation | Les solveurs SAT de Tweety peuvent resoudre des sous-problemes de planification |
| [SmartContracts](../SmartContracts/README.md) | Ordonnancement | Les liquidations DeFi sont des problemes de planification temporelle (notebook 8) |
| [GameTheory](../../GameTheory/README.md) | Recherche sequentielle | A* en planification et minimax en jeux partagent la meme structure de graphe |
| [Search](../../Search/README.md) | Fondations algorithmiques | A*, BFS, DFS de Search sont les bases des planificateurs classiques |

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
