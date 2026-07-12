---
title: "CC1 - IA Exploratoire et Symbolique"
description: "Devoir de contrôle continu - Système de Diagnostic Médical Multi-Contraintes pour le Diabète de Type 2"
author: "EPF IA Biomédicale"
date: "2025-11-04"
version: "2.0.0"
tags: ["CC1", "IA101", "diagnostic-medical", "multi-contraintes", "diabete-type2", "optimisation-genetique", "z3-solver"]
duration: "3 heures"
points: "20"
---

# CC1 - IA Exploratoire et Symbolique
## Système de Diagnostic Médical Multi-Contraintes pour le Diabète de Type 2

### Objectifs Pédagogiques

Ce devoir vise à évaluer votre maîtrise des concepts fondamentaux de l'intelligence artificielle exploratoire et symbolique à travers une application concrète dans le domaine biomédical. Vous développerez un système de diagnostic intelligent qui combine trois approches complémentaires :

**Compétences évaluées :**
- Algorithmes de recherche (BFS, DFS, A*)
- Programmation par contraintes (Z3, CSP)
- Algorithmes génétiques et optimisation
- Analyse de complexité et performance
- Application biomédicale (diabète type 2)
- Documentation technique et communication

### Contexte du Problème

Le diabète de type 2 représente un défi de santé publique majeur, nécessitant une approche de diagnostic personnalisée qui combine :
- **Analyse multi-dimensionnelle** : Glycémie, HbA1c, symptômes, antécédents
- **Contraintes thérapeutiques** : Protocoles médicaux, interactions médicamenteuses, contre-indications
- **Optimisation personnalisée** : Adaptation des traitements selon le profil patient

Votre système doit intégrer trois approches algorithmiques complémentaires :
1. **Agent de Diagnostic Rationnel** : Système qui perçoit les données patient et propose des diagnostics
2. **Optimisation Génétique** : Algorithme évolutionnaire pour personnaliser les seuils diagnostiques
3. **Validation par Contraintes** : Solveur Z3 pour valider les protocoles thérapeutiques

### Données du Problème

#### Structure Patient
```python
from dataclasses import dataclass
from typing import List, Optional
from datetime import datetime

@dataclass
class Patient:
    """Représente un patient pour le système de diagnostic"""
    id: int                          # Identifiant unique (1-1000)
    nom: str                        # Nom du patient
    age: int                         # Âge en années (18-80)
    glycemie_jeun: float           # Glycémie à jeun (mg/dL)
    glycemie_postprandiale: float  # Glycémie post-prandiale (mg/dL)
    hba1c: float                    # Hémoglobine glyquée (%)
    symptomes: List[str]             # Liste des symptômes
    antecedents: List[str]           # Antécédents médicaux
    date_consultation: datetime      # Date de consultation
    pression_arterielle: Optional[float] = None  # Pression artérielle systolique
    imc: Optional[float] = None               # Indice de masse corporelle
```

#### Protocoles Thérapeutiques de Référence
```python
protocoles_diabete_type2 = {
    "objectifs_glycemie": {
        "jeun": [80, 130],      # mg/dL
        "postprandial": [120, 180]  # mg/dL (2h après repas)
    },
    "objectifs_hba1c": {
        "cible": "<7.0%",        # Hémoglobine glyquée cible
        "alerte": ">8.0%"        # Seuil d'alerte
    },
    "contraintes_traitement": {
        "metformine": {
            "contre_indications": ["insuffisance_rénale_sévère", "acidose_lactique"],
            "dose_max": 3000  # mg/jour
        },
        "insuline": {
            "contre_indications": ["hypoglycémie_sévère_non_traitée"],
            "ajustement": "selon_glycemie"
        },
        "statines": {
            "contre_indications": ["maladie_hépatique_active"],
            "surveillance": "transaminases_hepatiques"
        }
    },
    "contraintes_globales": [
        "hba1c < 7.0%",
        "pas_d_hypoglycémie_sévère",
        "surveillance_poids",
        "activité_physique_régulière"
    ]
}
```

### Objectifs à Réaliser

#### Partie 1 : Agent de Diagnostic Basique (6 points)
Implémenter un système de diagnostic qui évalue les patients selon les règles cliniques standards :
1. **Évaluation initiale** : Classification du risque diabétique (Normal, Pré-diabète, Diabète Type 2)
2. **Analyse symptômes** : Interprétation des symptômes typiques du diabète
3. **Recommandations** : Suggestions basées sur les protocoles médicaux

#### Partie 2 : Optimisation par Recherche A* (6 points)
Améliorer le système en utilisant un algorithme de recherche informée :
1. **Espace d'états** : Définir les états possibles du processus diagnostique
2. **Heuristique médicale** : Fonction d'évaluation basée sur les critères cliniques
3. **Algorithme A*** : Implémentation avec optimisation du chemin de diagnostic

#### Partie 3 : Optimisation Génétique (4 points)
Développer un algorithme génétique pour optimiser les paramètres diagnostiques :
1. **Chromosomes** : Représentation des seuils et paramètres diagnostiques
2. **Fitness médicale** : Fonction d'évaluation basée sur les critères cliniques
3. **Évolution** : Optimisation des paramètres par sélection naturelle

#### Partie 4 : Validation par Contraintes (4 points)
Intégrer un solveur de contraintes pour valider les protocoles thérapeutiques :
1. **Modélisation CSP** : Traduction des contraintes médicales en problème de satisfaction
2. **Solveur Z3** : Utilisation de Z3 pour la résolution efficace
3. **Validation** : Vérification des protocoles selon les contraintes

### Exemples de Données

#### Cas de Test 1 : Situation Simple
```python
patients_test = [
    Patient(1, "Alice", 45, 110.0, 160.0, 6.8, ["fatigue", "soif intense"], 
           "antécédents familiaux", datetime.now()),
    
    Patient(2, "Bob", 58, 140.0, 200.0, 8.2, ["vision troubleée", "fatigue"], 
           "hypertension", datetime.now()),
    
    Patient(3, "Claire", 35, 90.0, 150.0, 5.5, ["polyurie", "soif"], 
           "surpoids", datetime.now()),
]
```

#### Cas de Test 2 : Situation Complexe
```python
patients_complexes = [
    Patient(4, "David", 67, 130.0, 180.0, 7.5, ["fatigue", "troubles visuels"], 
           "néphropathie", datetime.now(), 140.0, 28.5),
    
    Patient(5, "Emma", 72, 150.0, 220.0, 9.1, ["maux pieds", "engourdissement"], 
           "cardiopathie", datetime.now(), 160.0, 32.1),
    
    Patient(6, "Frank", 55, 125.0, 170.0, 6.9, ["hypoglycémie"], 
           "hypoglycémie_récurrente", datetime.now(), 130.0, 27.8),
]
```

### Environnement Technique

#### Langages et Librairies
- **Python 3.8+** requis
- **Librairies autorisées** :
  - `z3-solver` : Solveur SMT pour contraintes
  - `deap` ou `genetic` : Algorithmes génétiques
  - `numpy`, `scipy` : Calculs scientifiques
  - `matplotlib`, `seaborn` : Visualisation des résultats
  - `heapq`, `collections` : Algorithmes de base
  - `pandas` : Manipulation des données

#### Contraintes de Performance
- **Temps d'exécution** : <3 secondes pour 100 patients
- **Mémoire utilisée** : <200MB pour 1000 patients
- **Portabilité** : Code compatible Windows/Linux/macOS

### Barème d'Évaluation

| Critère | Points | Détails d'Évaluation |
|----------|---------|-------------------|
| **Agent Diagnostic** | 4 pts | Règles cliniques pertinentes, classification correcte |
| **Algorithme A*** | 3 pts | Espace d'états complet, heuristique admissible, optimalité |
| **Optimisation Génétique** | 2 pts | Chromosomes bien conçus, fitness pertinente, convergence |
| **Validation par Contraintes** | 2 pts | Modélisation CSP correcte, utilisation efficace de Z3 |
| **Qualité de Code** | 1 pt | Structure modulaire, lisibilité, optimisation |
| **Documentation** | 1 pt | Commentaires clairs, rapport d'analyse, présentation |
| **Analyse de Complexité** | 1 pt | Mesures pertinentes, analyse critique, comparaisons |
| **Innovation** | 1 pt | Approche originale, optimisations significatives |
| **Tests** | 1 pt | Couverture des cas, validation robuste |
| **Total** | **15 pts** | |

### Critères de Qualité

#### Excellence (16-20 points)
- Solution innovante combinant élégamment les 3 approches
- Code de qualité professionnelle avec optimisations pertinentes
- Analyse critique approfondie avec comparaisons algorithmiques détaillées
- Documentation exemplaire avec schémas, exemples et mesures de performance

#### Très Bien (13-15 points)
- Solution correcte et efficace dans les 3 approches
- Code bien structuré et commenté
- Analyse pertinente avec mesures de performance complètes
- Documentation complète et claire

#### Bien (10-12 points)
- Solution fonctionnelle combinant les approches
- Code correct mais perfectible
- Analyse basique avec complexité mesurée
- Documentation minimale mais fonctionnelle

#### Passable (8-9 points)
- Solution partielle (manque une approche)
- Code fonctionnel mais désorganisé
- Analyse superficielle
- Documentation incomplète

#### Insuffisant (<8 points)
- Solution non fonctionnelle
- Code incorrect ou incomplet
- Analyse absente ou erronée
- Documentation manquante

### Références

#### Théorie
- **Russell & Norvig**, *Artificial Intelligence: A Modern Approach*, Chapitres 1, 3, 4, 6
- **Dechter**, *Learning While Searching in Constraint-Satisfaction Problems*
- **Pearl**, *Heuristics: Intelligent Search Strategies for Computer Problem Solving*

#### Algorithmes
- **A\* Search** : https://en.wikipedia.org/wiki/A*_search_algorithm
- **Genetic Algorithms** : https://en.wikipedia.org/wiki/Genetic_algorithm
- **Constraint Programming** : https://en.wikipedia.org/wiki/Constraint_programming
- **Z3 Solver** : https://github.com/Z3Prover/z3

#### Applications Médicales
- **Guidelines ADA/EASD** : Recommandations diabète de type 2
- **WHO Diabetes Guidelines** : Standards internationaux pour le diagnostic
- **Medical Constraint Systems** : Littérature sur les applications CSP en santé

### Livrables Attendus

1. **CC1-Diagnostic-Medical.ipynb** : Notebook template à compléter par les étudiants
2. **data/patients.csv** : Données de test pour valider les implémentations
3. **Rapport d'analyse** : Document PDF ou Markdown (3-5 pages) incluant :
   - Analyse de complexité des algorithmes
   - Comparaison des performances
   - Justification des choix algorithmiques
   - Mesures et graphiques

### Calendrier

- **Date de remise** : 21 jours après la publication du sujet
- **Pénalité de retard** : -1 point par jour de retard
- **Format de remise** : Archive ZIP avec tous les livrables

### Extensions Possibles

#### Pour Étudiants Avancés
- **Apprentissage Automatique** : Optimisation des heuristiques par machine learning
- **Interface Web** : Version web de l'interface avec Flask/Django
- **Base de Données** : Persistance des données patients avec SQLite/PostgreSQL
- **Multi-objectifs** : Optimisation selon plusieurs critères médicaux

#### Bonus (+1 à +2 points)
- **Innovation Algorithmique** : Approche originale ou optimisation significative
- **Interface Utilisateur** : Interface graphique ou web intuitive
- **Tests Exhaustifs** : Couverture complète y compris cas limites complexes
- **Performance Exceptionnelle** : Temps d'exécution < 50% des attentes

---

*Bonne chance !*
*Publié le : 2025-11-04*
*Version finale : 2.0.0*