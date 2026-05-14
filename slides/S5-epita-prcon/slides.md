---
theme: ../theme-ia101
title: "Soutenances Programmation par Contraintes — EPITA SCIA 2026"
info: Template jury soutenance PrCon — 20 min par groupe
paginate: true
drawings:
  persist: false
transition: slide-left
mdc: true
layout: cover
---

# Soutenances PrCon

Programmation par Contraintes — EPITA SCIA 2026

**Dates** : 18 mai (lundi) / 22 mai (vendredi)

**Format** : Visio — 20 min par groupe (intro 5 + presentation 10 + Q&A 5)

---
layout: section
---

# Organisation (5 min)

---

# Informations pratiques

| | Session 1 | Session 2 |
|---|-----------|-----------|
| **Date** | Lundi 18 mai 2026 | Vendredi 22 mai 2026 |
| **Horaires** | A confirmer | A confirmer |
| **Visio** | Lien a communiquer | Lien a communiquer |
| **Groupes** | ~10 groupes | ~9 groupes |

- 19 groupes inscrits, ~50 etudiants
- 44 sujets en 12 categories (A-L) + Cat M Finance Quantitative
- Depot : `jsboigeEpita/2026-Epita-Programmation-par-Contraintes`

---

# Deroulement — 20 min par groupe

| Phase | Duree | Contenu |
|-------|-------|---------|
| **Introduction** | 5 min | Contexte, choix du sujet, problematique |
| **Presentation technique** | 10 min | Modelalisation, implementation, resultats |
| **Questions** | 5 min | Jury + etudiants |

**Consignes :**
- Partage d'ecran obligatoire (code + demonstrations)
- Pas de slides obligatoires — le code et les resultats sont le support
- Tests et benchmarks attendus pour toute implementation

---

# Grille de notation — /20

| Critere | Points | Description |
|---------|--------|-------------|
| **Modelisation contraintes** | 5 | Pertinence du modele CP, variables, domaines, contraintes |
| **Implementation** | 5 | Qualite du code, utilisation du solveur, gestion des cas |
| **Tests + Benchmarks** | 5 | Couverture de tests, comparaisons de performances, analyse |
| **Presentation** | 3 | Clarte, structure, demonstrations live |
| **Questions** | 2 | Comprehension du sujet, reponse aux questions jury |

**Bonus/malus :** taille du groupe (solo = +1, 4+ = -1), contributions PR supplementaires (+1 max)

---
layout: section
---

# Catalogue des sujets

---

# Categories A-D : Puzzles et Jeux

| Cat | Sujets (exemples) |
|-----|--------------------|
| **A** | Sudoku, N-Queens, Magic Square |
| **B** | Kakuro, Nonogram, Cryptarithmetic |
| **C** | Job-Shop Scheduling, Timetabling |
| **D** | Crossword, Wordle, Word Search |

**Points d'attention jury :**
- Modelisation : variable par case ? par contrainte ? par ligne/colonne ?
- Choix du solveur (OR-Tools CP-SAT, Z3, minizinc, custom)
- Strategies de branchement et propagation

---

# Categories E-L : Applications

| Cat | Theme |
|-----|-------|
| **E** | Logistique (VRP, Bin Packing) |
| **F** | Planification (RCPSP, Machine Scheduling) |
| **G** | Reseaux (Graph Coloring, Network Design) |
| **H** | Generation (Procedural, Music, Level Design) |
| **I** | Bioinformatique (Phylogeny, Protein Folding) |
| **J** | Allocation (Matching, Assignment) |
| **K** | Optimisation (Knapsack, Cutting Stock) |
| **L** | Autres (Decomposition, Symmetry Breaking) |

**Cat M** : Finance Quantitative (Portfolio Optimization, Risk Parity)

---
layout: section
---

# Template Jury — Notes par groupe

---

# Fiche d'evaluation — [Nom du groupe]

**Groupe** : _________________
**Sujet** : _________________ (Cat __)
**Membres** : _________________

| Critere | Note /5 | Commentaires |
|---------|---------|--------------|
| Modelisation | ___ /5 | |
| Implementation | ___ /5 | |
| Tests + Benchmarks | ___ /5 | |
| Presentation | ___ /3 | |
| Questions | ___ /2 | |
| **Total** | **___ /20** | |

**Bonus/malus** : ___ | **Note finale** : **___ /20**

---

# Points de vigilance jury

**Modelisation (5 pts) :**
- Variables bien definies (domaine, type)
- Contraintes completes et non-redondantes
- Objectif clair (satisfaction vs optimisation)
- Symetries identifiees et traitees

**Implementation (5 pts) :**
- Code lisible et structure
- Utilisation correcte de l'API du solveur
- Gestion des cas limites (instance vide, unsolvable)
- Choix de recherche (heuristique, branching)

**Tests (5 pts) :**
- Instances de test variees (petit, moyen, grand)
- Benchmarks comparatifs (temps, nombre de noeuds)
- Analyse des resultats (scalability, bottlenecks)

---
layout: section
---

# Logistique

---

# Checklist pre-soutenance

- [ ] Lien visio teste par chaque groupe
- [ ] Depot etudiant a jour (dernieres PRs mergees)
- [ ] Grille de notation distribuee au jury
- [ ] Timer visible pendant les soutenances
- [ ] Recording configure (screen + audio)

# Checklist post-soutenance

- [ ] Notes compilees dans Google Form
- [ ] Bonus/malus appliques
- [ ] Export format EPITA SCIA
- [ ] Transmission scolarite < 72h
- [ ] Recording archive

---

# Ressources

**Depot etudiant** : `github.com/jsboigeEpita/2026-Epita-Programmation-par-Contraintes`

**Notebooks CoursIA** : `MyIA.AI.Notebooks/SymbolicAI/Planners/` (Planners-7 OR-Tools)

**Solveurs recommandes** :
- **OR-Tools CP-SAT** : `pip install ortools` — industrial-grade
- **Z3 (SMT)** : `pip install z3-solver` — logique + optimisation
- **python-constraint** : `pip install constraint` — pedagogique

---
layout: center
---

# Questions ?

*Bonne soutenance a tous !*
