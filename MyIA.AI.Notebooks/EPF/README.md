# EPF - Devoirs et Evaluations

Controles continus du cours **IA101 - Intelligence Artificielle** (EPF 2026). Ces devoirs integrent les concepts des autres sections du repository (Probas, SymbolicAI, Search).

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Cours | IA101 - Intelligence Artificielle |
| Etablissement | EPF 2026 |
| Controles | 2 (CC1, CC2) |
| Format | Notebooks Jupyter (Python) |

## Structure

```
EPF/
└── IA101-Devoirs/
    ├── CC1-Exploratoire-Symbolique/      # Diagnostic medical
    │   ├── CC1-Diagnostic-Medical.ipynb   # Squelette etudiant
    │   ├── CC1-Diagnostic-Medical-corrige.ipynb
    │   ├── enonce/sujet.md
    │   ├── data/patients.csv
    │   └── README.md
    │
    └── CC2-Symbolique-Probabiliste/      # OncoPlan
        ├── enonce/
        │   ├── sujet.md
        │   ├── CC2_OncoPlan_Squelette.ipynb
        │   └── ressources/patients_oncology.csv
        ├── corrige/CC2_OncoPlan_Corrige.ipynb
        └── README.md
```

## CC1 - Diagnostic Medical (IA Exploratoire et Symbolique)

**Sujet** : Systeme de diagnostic medical pour la gestion multi-contraintes du diabete de type 2

**Duree** : 3 heures | **Points** : 20

### Objectifs pedagogiques

| Composant | Points | Contenu |
|-----------|--------|---------|
| Agent diagnostique | 4 pts | Regles cliniques, classification |
| Algorithme A* | 3 pts | Espace d'etats, heuristique admissible |
| Algorithme genetique | 2 pts | Optimisation de parametres |
| Solveur Z3 | 2 pts | Validation de protocoles |
| Qualite code | 1 pt | Structure, lisibilite |
| Documentation | 1 pt | Commentaires, rapport |
| Analyse complexite | 1 pt | Mesures, comparaisons |

### Technologies

- Python 3.8+
- numpy, pandas, matplotlib
- z3-solver (>=4.8.0)
- heapq, collections

## CC2 - OncoPlan (IA Symbolique et Probabiliste)

**Sujet** : Protocole oncologique adaptatif pour traitement du cancer

**Duree** : 8-12 heures | **Format** : Binome autorise | **Points** : 20

### Architecture en 3 parties

| Partie | Points | Contenu |
|--------|--------|---------|
| **Pharmacien symbolique** | 4 pts | Ontologie, incompatibilites medicamenteuses |
| **Planning CSP** | 6 pts | OR-Tools/Z3, cycles 21 jours, contraintes |
| **Medecine probabiliste** | 8 pts | Pyro, profil toxicite, prediction neutropenie |

### Technologies

- Toutes les dependances CC1 +
- Pyro (programmation probabiliste)
- OR-Tools (Google CP-SAT)
- rdflib (optionnel, pour ontologies)

## Liens avec le repository

| Section | Relation |
|---------|----------|
| [Probas/Infer/](../Probas/Infer/) | Fondements probabilistes pour CC2 |
| [SymbolicAI/](../SymbolicAI/) | Z3, OR-Tools, RDF pour CC1/CC2 |
| [Search/](../Search/) | Algorithmes A*, genetiques pour CC1 |
| [GradeBookApp/](../../GradeBookApp/) | Notation collegiale des controles |

## Installation

```bash
# Environnement Python
python -m venv venv
venv\Scripts\activate  # Windows

# Dependances CC1
pip install numpy pandas matplotlib seaborn z3-solver

# Dependances supplementaires CC2
pip install pyro-ppl ortools
```

## Consignes generales

1. **CC1** : Travail individuel, 3 heures en conditions d'examen
2. **CC2** : Binome autorise, rendu sous 2 semaines
3. **Bonus** : Innovation, UI, tests exhaustifs (+2 pts max)
4. **Soumission** : Via plateforme cours (format .ipynb + .pdf)

## Ressources pedagogiques

- [README CC1](IA101-Devoirs/CC1-Exploratoire-Symbolique/README.md) - Guide etudiant detaille
- [README CC2](IA101-Devoirs/CC2-Symbolique-Probabiliste/README.md) - Glossaire Pyro et conseils

## Evaluation

Les notes sont calculees via [GradeBookApp](../../GradeBookApp/) avec :
- Evaluation collegiale (etudiants + professeur)
- Ponderation configurable par epreuve
- Bonus/malus taille de groupe
- Centrage-reduction statistique

## Licence

Voir la licence du repository principal.
