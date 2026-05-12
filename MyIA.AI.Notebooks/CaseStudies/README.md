# CaseStudies - Etudes de cas interdisciplinaires

<!-- CATALOG-STATUS
series: CaseStudies
pedagogical_count: 4
breakdown: Diagnostic-Medical=2, Oncology-Planning=2
maturity: DRAFT=2, ALPHA=1, PRODUCTION=1
-->

Etudes de cas interdisciplinaires combinant plusieurs domaines de l'IA dans des projets appliques.

**4 notebooks** | **2 projets** | **~6-8h**

## Structure

```text
CaseStudies/
├── Diagnostic-Medical/    # Systeme de diagnostic multi-contraintes (A*, genetique, Z3)
│   ├── student/           # Template etudiant
│   ├── solution/          # Solution de reference
│   └── data/              # Donnees de test
├── Oncology-Planning/     # Planification oncologique (CSP, Pyro probabiliste, ontologie)
│   ├── student/           # Template etudiant
│   ├── solution/          # Solution de reference
│   └── data/              # Donnees patients
└── requirements.txt       # Dependances communes
```

## Projets

### Diagnostic Medical

Systeme de diagnostic medical combinant recherche informee (A*), algorithmes genetiques, et validation par contraintes (Z3). Application au diabete de type 2 avec 10 patients de test.

- **Technologies** : Python, z3-solver, heapq, pandas
- **Concepts** : Recherche A*, algorithmes genetiques, CSP, validation par contraintes

[README complet](Diagnostic-Medical/README.md) | 2 notebooks (student + solution) | ~3-4h

### Oncology Planning (OncoPlan)

Protocole oncologique adaptatif combinant IA symbolique (ontologie, CSP/OR-Tools) et programmation probabiliste (Pyro) pour l'aide a la decision en oncologie. Modele de jumeau numerique patient.

- **Technologies** : Python, pyro-ppl, ortools, pandas
- **Concepts** : Ontologies, planification CSP, infarence bayesienne, programmation probabiliste

[README complet](Oncology-Planning/README.md) | 2 notebooks (student + solution) | ~3-4h

## Installation

```bash
pip install -r requirements.txt
```

Dependances principales : numpy, pandas, matplotlib, seaborn, z3-solver, pyro-ppl, ortools

## Connections cross-series

Les etudes de cas de cette serie sont des projets interdisciplinaires qui combinent les techniques de plusieurs series du cursus.

### CaseStudies et Search (Recherche et CSP)

Le **Diagnostic Medical** utilise directement les algorithmes de la serie Search :

- **Recherche informee (A-star)** (Search Part 1) : le diagnostic medical est un probleme de recherche dans un espace d'etats (symptomes -> maladies). Les heuristiques A-star guident l'exploration.
- **CSP et Z3** (Search Part 2) : la validation des diagnostics par contraintes (Z3) est une application directe de la programmation par contraintes. Les solveurs SAT/SMT de Search completent les algorithmes genetiques du CaseStudy.

### CaseStudies et Probas (Inference Probabiliste)

L'**Oncology Planning** utilise Pyro pour la programmation probabiliste :

- **Inference bayesienne** (Probas notebooks 17-20) : le modele de jumeau numerique patient repose sur l'inference bayesienne pour estimer les parametres de reponse au traitement.
- **Modeles probabilistes** (Probas avec Infer.NET) : les modeles generatifs Pyro sont les memes concepts que les modeles probabilistes de la serie Probas, appliques ici a un domaine medical.

### CaseStudies et Planners (Planification)

L'**Oncology Planning** integre OR-Tools pour la planification CSP :

- **CP-SAT** (Planners-7) : la planification des protocoles de chimiotherapie est un probleme de scheduling sous contraintes (doses, delais, toxicite cumulee). OR-Tools CP-SAT, etudie dans Planners-7, est directement applique ici.
- **Planification temporelle** (Planners-8) : les contraintes temporelles entre cycles de traitement correspondent aux modeles PDDL 2.1 de Planners-8.

### CaseStudies et SemanticWeb (Web Semantique)

L'**Oncology Planning** utilise une ontologie pour representer les connaissances medicales :

- **Ontologies OWL** (SemanticWeb SW-4/5) : l'ontologie medicale du projet (medicaments, pathologies, interactions) est structuree en OWL/RDF, comme les ontologies etudiees dans la serie SemanticWeb.
- **Raisonnement ontologique** : les inférences sur les contre-indications medicamenteuses utilisent les memes raisonneurs que la serie SemanticWeb.

### CaseStudies et RL (Apprentissage par Renforcement)

Le **Diagnostic Medical** avec algorithmes genetiques et le **jumeau numerique** patient anticipent les methodes RL :

- **Optimisation par simulation** : le jumeau numerique patient (OncoPlan) est un environnement de simulation similaire aux environnements RL. L'adaptation du protocole pourrait etre formulee comme un probleme RL (etat patient, action traitement, recompense survie).
- **Exploration vs exploitation** : les algorithmes genetiques du diagnostic medical echangent exploration (mutation) et exploitation (selection), comme en RL.
