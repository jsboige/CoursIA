# CaseStudies - Etudes de cas interdisciplinaires

<!-- CATALOG-STATUS
series: CaseStudies
pedagogical_count: 4
breakdown: Diagnostic-Medical=2, Oncology-Planning=2
maturity: BETA
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
