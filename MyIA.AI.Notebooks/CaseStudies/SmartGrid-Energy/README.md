# SmartGrid-Energy - Ordonnancement énergétique sous incertitude

[← CaseStudies](../README.md) | [↑ Études de cas](../README.md)

Étude de cas intégratrice (CC3, EPF IA — 3-4h, 20 points) : piloter un mini-réseau électrique en
combinant **optimisation sous contraintes** (CP-SAT), **raisonnement bayésien** (risque de
défaillance) et **arbitrage multi-objectif** (coût vs émissions). C'est le problème réel de
l'*unit commitment / dispatch* : décider heure par heure quelles centrales allumer et à quelle
puissance, alors que la production renouvelable est incertaine.

## Le problème

Un jumeau numérique `PowerNetwork` simule un réseau à 3 centrales pilotables :

| Centrale | Puissance | Coût marginal | Émissions |
|----------|-----------|---------------|-----------|
| Charbon | 50-400 MW | 30 EUR/MWh | 900 kg CO2/MWh |
| Gaz | 20-250 MW | 60 EUR/MWh | 400 kg CO2/MWh |
| Hydro | 0-150 MW | 10 EUR/MWh | 0 kg CO2/MWh |

Il faut couvrir une demande horaire de 480 à 600 MW sur 6 heures, en présence d'un apport
renouvelable aléatoire. Aucun paradigme ne suffit seul : le solveur de contraintes garantit la
faisabilité physique mais ignore l'aléatoire ; le modèle bayésien quantifie le risque mais ne
produit pas de plan ; le score multi-objectif arbitre mais suppose des candidats faisables.
L'étude de cas fait composer les trois **dans le bon ordre**.

## Architecture en 4 couches

| Partie | Couche | Technique | Fonction à implémenter |
|--------|--------|-----------|------------------------|
| 1 | Dispatch faisable | CP-SAT (OR-Tools) | `solve_dispatch_cp` |
| 2 | Risque de défaillance | Bayésien (survivor function) | `failure_risk` |
| 3 | Arbitrage coût/CO2 | Score multi-objectif normalisé | `multi_objective_score` |
| 4 | Comparaison de stratégies | Analyse comparative (3 stratégies) | `comparative_analysis` |

Les concepts transversaux travaillés : composition **ordonnée** des paradigmes (filtrer >
modéliser > optimiser), jumeau numérique réactif aux décisions, tension incertitude vs
contraintes dures, et absence de solution unique en multi-objectif (compromis de type Pareto).

## Structure du dossier

```
SmartGrid-Energy/
├── student/
│   └── SmartGrid-Energy.ipynb    # Template étudiant (stubs à compléter)
├── solution/
│   └── SmartGrid-Energy.ipynb    # Solution de référence (exécutée, sorties incluses)
├── subject.md                    # Sujet complet : énoncé, barème, exercices
└── README.md                     # Ce fichier
```

Les deux notebooks partagent la même trame (20 cellules dont 8 de code) ; la version étudiante
remplace les corps de fonctions par des stubs guidés (`# TODO`, indices par étape), la version
solution est committée exécutée de bout en bout.

## Barème (20 points)

| Critère | Points |
|---------|--------|
| Partie 1 — dispatch CP-SAT (contraintes correctes, statut OPTIMAL) | 5 |
| Partie 2 — risque bayésien (survivor function + interprétation) | 4 |
| Partie 3 — score multi-objectif (normalisation cohérente) | 4 |
| Partie 4 — analyse comparative (3 stratégies, conclusion argumentée) | 4 |
| Exercices d'extension (1 minimum au choix) | 3 |

Trois exercices d'extension approfondissent le système : **réserve tournante n-1** (couvrir la
perte de la plus grosse centrale en service), **sensibilité au prior** (comment le risque évolue
quand l'incertitude renouvelable est divisée ou multipliée par 2), et **équité territoriale**
(troisième objectif évitant de concentrer les centrales polluantes sur une région).

## Lancement

```bash
pip install -r ../requirements.txt   # ortools>=9.8, numpy (kernel Python 3)
jupyter lab student/SmartGrid-Energy.ipynb
```

Le sujet détaillé (énoncé complet, données, critères) est dans [subject.md](subject.md).

## Études de cas associées

- [Diagnostic-Medical](../Diagnostic-Medical/README.md) — CC1 : règles cliniques + A* + génétique + Z3
- [Oncology-Planning](../Oncology-Planning/README.md) — CC2 : ontologie OWL + contraintes + bayésien
- [README CaseStudies](../README.md) — principe d'intégration multi-paradigmes de la série
