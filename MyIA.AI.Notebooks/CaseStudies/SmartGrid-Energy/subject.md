---
title: "CC3 - Ordonnancement Energetique sous Incertitude"
description: "Etude de cas - Ordonnancement de la production energetique d'un reseau electrique sous incertitude renouvelable"
author: "EPF IA / CoursIA"
date: "2026-07-01"
version: "1.0.0"
tags: ["CC3", "SmartGrid", "unit-commitment", "cp-sat", "bayesien", "multi-objectif", "energie", "transition-energetique"]
duration: "3-4 heures"
points: "20"
---

# CC3 - Ordonnancement Energetique sous Incertitude
## SmartGrid : dispatch de la production electrique sous incertitude renouvelable

### Objectifs pedagogiques

Cette etude de cas evalue votre capacité a **composer plusieurs paradigmes d'IA** pour resoudre un
probleme metier réel de la transition energetique : decider, heure par heure, quelles centrales activer
et a quel niveau de production (*unit commitment* / dispatch) pour satisfaire la demande electrique tout
en minimisant le cout et les emissions de CO2.

**Competences evaluees :**
- Programmation par contraintes (OR-Tools CP-SAT, unit commitment NP-difficile)
- Inference probabiliste (modèle bayesien de l'incertitude renouvelable)
- Optimisation multi-objectif (cout + CO2 + risque, front de Pareto)
- Architecture en couches : filtrer (contraintes) avant de modeliser (incertitude) avant d'optimiser
- Application sectorielle (reseau electrique, transition energetique)

### Contexte du probleme

Un operateur de reseau electrique doit, pour chaque heure de la journee, decider quelles centrales
pilotables activer (charbon, gaz, hydro) et a quel niveau de production, afin de satisfaire la demande
des consommateurs. La difficulté vient de trois facteurs combines :

1. **l'incertitude** : la production renouvelable (eolien, solaire) est stochastique ; la demande varie ;
2. **les contraintes dures** : chaque centrale a une capacité minimale stable (`pmin`) et maximale
   (`pmax`), et ne peut pas etre exploitee en dessous de `pmin` ;
3. **les objectifs multiples conflictuels** : le charbon est bon marche mais tres emissif ; le gaz est
   intermediaire ; l'hydro est propre mais capacité limitee.

Une seule technique ne suffit pas : un solveur deterministe ignore l'incertitude, un modèle probabiliste
seul ne respecte pas les contraintes physiques. Le systeme doit les **composer dans le bon ordre**.

### Le jumeau numerique

On dispose d'un modèle de reseau (`PowerNetwork`) representant :
- 3 centrales pilotables : Charbon (50-400 MW, 30 EUR/MWh, 900 kg/MWh), Gaz (20-250 MW, 60 EUR/MWh,
  400 kg/MWh), Hydro (0-150 MW, 10 EUR/MWh, 0 kg/MWh)
- une demande horaire sur 6 heures : [500, 520, 480, 540, 600, 580] MW
- une production renouvelable moyenne + incertitude (ecart-type) par heure

### Les 4 couches a implementer

| Partie | Couche | Technique | Livrable attendu |
|--------|--------|-----------|------------------|
| **1** | Contraintes dures | OR-Tools CP-SAT | `solve_dispatch_cp` : unit commitment min-cout |
| **2** | Incertitude | Modèle bayesien | `failure_risk` : probabilité de defaillance |
| **3** | Optimisation | Multi-objectif pondere | `multi_objective_score` : score normalise |
| **4** | Decision | Analyse comparative | `comparative_analysis` : 3 strategies comparees |

### Exercices d'extension

Apres les 4 couches de base, 3 exercices approfondissent le systeme :

- **Exercice 1 (reserve tournante n-1)** : ajouter une contrainte de securite — la reserve disponible
  doit couvrir la perte de la plus grosse centrale en service.
- **Exercice 2 (sensibilité au prior)** : analyser comment le risque de defaillance evolue quand on
  modifie l'incertitude renouvelable (x0.5, x1, x2). Quelle heure devient la plus risqueuse ?
- **Exercice 3 (equite territoriale)** : ajouter un troisieme objectif evitant qu'une region subisse
  toutes les centrales les plus polluantes.

### Données et lancement

- **Notebook etudiant** : `student/SmartGrid-Energy.ipynb` (a completer)
- **Notebook solution** : `solution/SmartGrid-Energy.ipynb` (reference)
- **Dependances** : `ortools>=9.8`, `numpy` (cf `CaseStudies/requirements.txt`)
- **Kernel** : Python 3

### Criteres d'evaluation

| Critere | Points | Detail |
|---------|--------|--------|
| Partie 1 - CP-SAT dispatch | 5 | Solveur fonctionnel, contraintes correctes, statut OPTIMAL |
| Partie 2 - Risque bayesien | 4 | Survivor function correcte, interpretation des valeurs |
| Partie 3 - Multi-objectif | 4 | Normalisation coherente, score calcule |
| Partie 4 - Analyse comparative | 4 | 3 strategies, table comparatif, conclusion argumentee |
| Exercices (au choix, 1 minimum) | 3 | Implementation + analyse |
| **Total** | **20** | |

### Concepts cles transversaux

- **Composition ordonnee** des paradigmes : l'ordre importe (filtrer > modeliser > optimiser)
- **Jumeau numerique** : modèle de reseau reactif aux decisions de dispatch
- **Incertitude vs contraintes** : un systeme trop rigide ignore l'aléatoire ; trop flou, il ignore la physique
- **Multi-objectif** : pas de solution unique optimale, mais un compromis (front de Pareto)

Cf [README CaseStudies](../README.md) pour le principe d'integration et les etudes de cas associees.
