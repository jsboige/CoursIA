# CaseStudies - Études de cas interdisciplinaires

<!-- CATALOG-STATUS
series: CaseStudies
pedagogical_count: 4
breakdown: Diagnostic-Medical=2, Oncology-Planning=2
maturity: BETA=2, PRODUCTION=2
-->

[← Notebooks](../README.md) | [↑ ..](../README.md) | [→ QuantConnect](../QuantConnect/README.md)

Études de cas interdisciplinaires combinant plusieurs domaines de l'IA dans des projets appliqués.

La force des études de cas réside dans leur capacité à **fusionner les techniques apprises en silos** : un solveur SMT (Search), un algorithme génétique (Sudoku), une ontologie OWL (SemanticWeb) et un modèle bayésien (Probas) ne valent pas grand chose isolément face à une question réelle. C'est leur combinaison, orchestrée autour d'un problème métier (diagnostic médical, protocole oncologique), qui transforme un catalogue d'outils en **système décisionnel cohérent**. Les deux projets de cette série illustrent ce passage : chacun mobilise 3 à 4 paradigmes IA différents qui se renforcent mutuellement plutôt que de se concurrencer.

## À qui s'adresse cette série

Cette série s'adresse aux **étudiants en fin de cycle** (M1/M2 ou équivalent ingénieur) ayant déjà parcouru les séries fondamentales (Search, SymbolicAI, Probas, SemanticWeb). Elle constitue typiquement un **devoir de contrôle continu intégrateur** ou un projet de groupe couvrant plusieurs paradigmes IA dans un même livrable. La pédagogie privilégie l'**autonomie** : chaque projet propose un template étudiant minimal et une solution de référence pour autoévaluation.

Les profils types visés :

- Étudiants en informatique ou IA construisant un portefeuille de projets multi-paradigmes
- Développeurs/data scientists explorant l'intégration de techniques hétérogènes (symbolique + probabiliste)
- Enseignants cherchant des **devoirs d'intégration** mobilisant 3-4 séries du cursus

## Pourquoi des études de cas interdisciplinaires ?

L'IA réelle ne fonctionne quasi-jamais avec un seul paradigme. Un assistant diagnostic exploite à la fois des **règles symboliques** (contre-indications absolues), des **modèles probabilistes** (incertitude sur les symptômes), des **algorithmes de recherche** (exploration de l'arbre de diagnostics) et des **contraintes formelles** (validation par solveur). Réduire ce problème à une seule technique conduit à des systèmes brittle (règles only), opaques (deep learning only) ou inutilisables (probabiliste only sans contraintes dures).

### Le principe d'intégration

| Couche | Rôle | Techniques | Exemple OncoPlan |
|--------|------|-----------|------------------|
| **Connaissances métier** | Représenter le domaine | Ontologies OWL, règles | Médicaments, interactions, contre-indications |
| **Contraintes dures** | Filtrer l'impossible | CSP, SMT, OR-Tools | Doses cumulées, délais entre cures |
| **Incertitude** | Modéliser l'aléatoire | Bayésien, Pyro, Infer.NET | Réponse patient, toxicité prédite |
| **Optimisation** | Choisir la meilleure option | A*, génétique, RL | Calendrier optimal de cures |
| **Décision finale** | Synthèse et explication | Workflow, scoring | Recommandation justifiée au clinicien |

Une seule couche ne suffit pas, et l'**ordre de composition** importe : on filtre avant d'optimiser, on modélise l'incertitude avant de valider sous contraintes. Les études de cas matérialisent ces patterns d'architecture.

### Le pattern "twin numérique"

Les deux projets reposent sur un **modèle de patient simulé** : un objet logiciel qui représente l'état clinique (symptômes, antécédents, paramètres biologiques) et réagit à des interventions (diagnostic proposé, traitement appliqué). Ce pattern, appelé **jumeau numérique** (digital twin), est devenu central en santé numérique, en industrie 4.0 et en simulation environnementale. L'apprendre sur 10 patients diabétiques (Diagnostic-Medical) ou un cas oncologique (Oncology-Planning) prépare directement aux applications professionnelles.

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

### Diagnostic Médical

Système de diagnostic médical combinant recherche informée (A*), algorithmes génétiques, et validation par contraintes (Z3). Application au diabète de type 2 avec 10 patients de test.

- **Technologies** : Python, z3-solver, heapq, pandas
- **Concepts** : Recherche A*, algorithmes génétiques, CSP, validation par contraintes

[README complet](Diagnostic-Medical/README.md) | 2 notebooks (student + solution) | ~3-4h

### Oncology Planning (OncoPlan)

Protocole oncologique adaptatif combinant IA symbolique (ontologie, CSP/OR-Tools) et programmation probabiliste (Pyro) pour l'aide à la décision en oncologie. Modèle de jumeau numérique patient.

- **Technologies** : Python, pyro-ppl, ortools, pandas
- **Concepts** : Ontologies, planification CSP, inférence bayésienne, programmation probabiliste

[README complet](Oncology-Planning/README.md) | 2 notebooks (student + solution) | ~3-4h

## Acquis d'apprentissage

À l'issue de cette série, l'étudiant est capable de :

### Compétences techniques

- **Concevoir une architecture IA hybride** combinant raisonnement symbolique (règles, ontologies, contraintes) et apprentissage statistique (modèles probabilistes, optimisation évolutionnaire)
- **Modéliser un domaine métier** avec un vocabulaire formel (classes, propriétés, axiomes) sans confondre représentation et inférence
- **Décomposer un problème complexe** en sous-problèmes adressés par la technique la plus adaptée (filtrage par contraintes, recherche heuristique, inférence bayésienne)
- **Composer plusieurs solveurs** (Z3, OR-Tools, Pyro, A*) dans un pipeline cohérent où la sortie de l'un alimente l'autre
- **Valider un système décisionnel** sur des cas réels (patients diabétiques, protocoles oncologiques) avec métriques de qualité et explicabilité

### Compétences méthodologiques

- **Identifier les couches d'un système IA** (données -> connaissances -> contraintes -> modèles -> décision) et leur ordre de composition
- **Choisir entre approches déterministes et probabilistes** selon que les contraintes sont absolues ou négociables
- **Justifier le recours à l'IA hybride** plutôt qu'à un seul paradigme : robustesse, explicabilité, conformité réglementaire
- **Documenter un projet IA interdisciplinaire** : architecture, choix algorithmiques, limites connues, périmètre de validation

### Compétences applicatives (domaine médical)

- **Manipuler des données patient** (CSV structurées, anonymisation, intégrité des CSP)
- **Encoder un protocole thérapeutique** sous forme d'ontologie + contraintes (délais, doses, interactions)
- **Estimer une incertitude clinique** via inférence bayésienne et amplification (`poutine.scale` en Pyro)
- **Construire un jumeau numérique** simulant la réaction d'un patient à une intervention

## Concepts clés transversaux

Cette série consolide cinq concepts qui reviennent dans tous les systèmes IA appliqués modernes :

| Concept | Définition | Manifestation dans CaseStudies | Cours connexes |
|---------|------------|--------------------------------|----------------|
| **Architecture hybride** | Pipeline combinant techniques symboliques et statistiques | Diagnostic : A* + GA + Z3 / OncoPlan : Ontologie + CSP + Pyro | [SymbolicAI](../SymbolicAI/README.md), [Probas](../Probas/README.md) |
| **Jumeau numérique** | Modèle logiciel d'un objet/personne réagissant à des interventions | Modèle patient (état, paramètres bio, réponse au traitement) | [RL](../RL/README.md), [Probas](../Probas/README.md) |
| **Knowledge engineering** | Formalisation explicite des connaissances métier en classes/règles | Ontologie oncologique, règles de diagnostic | [SemanticWeb](../SymbolicAI/SemanticWeb/README.md) |
| **Inférence sous contraintes** | Résolution conjointe d'un problème avec contraintes dures et incertitudes | OncoPlan : calendrier valide ET probable | [Search](../Search/README.md), [SymbolicAI/Tweety](../SymbolicAI/Tweety/README.md) |
| **Décision sous incertitude** | Choisir entre options avec résultats probabilistes et regret asymétrique | OncoPlan : adapter ou non un protocole | [Probas](../Probas/README.md), [GameTheory](../GameTheory/README.md) |

Ces concepts ne sont pas exclusifs au domaine médical : on les retrouve à l'identique en **finance algorithmique** (jumeau de marché + contraintes réglementaires + signaux probabilistes), **logistique** (jumeau de flotte + planification + prévisions) et **maintenance prédictive** (jumeau équipement + règles métier + Bayésien). Le choix du médical est pédagogique : domaine riche en contraintes formelles et en incertitude irréductible.

## Pour aller plus loin

### Articles de référence

- **Khan et al. (2021)** - *Hybrid AI for Clinical Decision Support: A Survey* — panorama des architectures hybrides en santé numérique
- **Goodall et al. (2022)** - *Digital Twins in Healthcare: Trends, Applications, and Implementation Challenges* — état de l'art jumeaux numériques patient
- **Hooker (2012)** - *Integrated Methods for Optimization* — fondements de la composition CP/SAT/MILP utilisée en OncoPlan
- **Bingham et al. (2019)** - *Pyro: Deep Universal Probabilistic Programming* — paper de référence pour la couche probabiliste

### Extensions possibles

| Extension | Description | Techniques mobilisées |
|-----------|-------------|----------------------|
| **Apprentissage par renforcement** | Formuler OncoPlan en MDP : état patient -> action protocole -> récompense survie | PPO, DQN ([RL](../RL/README.md) notebooks 5-6) |
| **LLM en boucle** | Utiliser un LLM pour générer des hypothèses diagnostiques, valider par Z3 | [Sudoku](../Sudoku/README.md) notebook 17, Semantic Kernel |
| **Multi-agent** | Plusieurs médecins virtuels délibèrent (diagnostic, prescription, monitoring) | [RL](../RL/README.md) notebook 6, [GameTheory](../GameTheory/README.md) |
| **Explicabilité** | Générer une trace narrative des décisions ontologie + contraintes + Bayésien | [SymbolicAI](../SymbolicAI/README.md), Tweety argumentation |
| **Federated learning** | Entraînement réparti entre hôpitaux sans partage des données patient | Adaptation [ML](../ML/README.md), considérations RGPD |

### Aspects éthiques et réglementaires

Les systèmes IA appliqués au domaine médical sont soumis à des contraintes légales (RGPD, AI Act européen, FDA aux US) et éthiques (explicabilité, biais, responsabilité). Les projets de cette série sont **académiques** : ils utilisent des données synthétiques ou anonymisées et ne sont pas destinés à un usage clinique. Toute transposition réelle exigerait :

- Validation clinique sur cohorte représentative et publication peer-reviewed
- Certification dispositif médical (Classes I-IV selon risque)
- Audit éthique (CER, CNIL pour les données patient en France)
- Explicabilité documentée de chaque décision automatisée

Ces dimensions sont abordées en survol dans les notebooks mais méritent un module dédié pour une formation professionnelle complète.

## Installation

```bash
pip install -r requirements.txt
```

Dépendances principales : numpy, pandas, matplotlib, seaborn, z3-solver, pyro-ppl, ortools

## FAQ

### Faut-il avoir suivi toutes les séries avant de commencer les études de cas ?

Non, mais les prérequis varient par projet. Le **Diagnostic Médical** nécessite d'avoir vu Search Part 1 (recherche informée) et Search Part 2 (CSP/Z3). L'**Oncology Planning** nécessite Probas (inférence bayésienne) et idéalement Planners (CP-SAT). Chaque projet indique les prérequis spécifiques dans sa section. Commencez par le projet dont vous maîtrisez les prérequis.

### Qu'est-ce qu'un jumeau numérique patient ?

Un **jumeau numérique** est un modèle computationnel qui simule le comportement d'un patient virtuel face à un traitement. Dans OncoPlan, le modèle probabiliste (Pyro) estime la réponse tumorale en fonction des paramètres patient (âge, stade, biomarqueurs) et du protocole proposé. Le jumeau permet de tester des scénarios de traitement sans risque pour le patient réel.

### Les données médicales sont-elles réelles ?

Les notebooks utilisent des **données synthétiques** (générées pour être pédagogiquement réalistes) ou des **données publiques anonymisées** (quand disponibles). Aucune donnée patient réelle n'est incluse. Les modèles sont simplifiés pour rester compréhensible — un modèle clinique réel aurait des dizaines de variables supplémentaires.

### Quels packages Python sont nécessaires ?

`pip install -r requirements.txt` installe tout : numpy, pandas, matplotlib, seaborn, z3-solver, pyro-ppl, ortools. Aucune dépendance externe (API, Docker, GPU) n'est requise.

### Quelle est la différence entre diagnostic médical et planification oncologique ?

Le **Diagnostic Médical** résout un problème de classification : étant donné des symptômes, identifier la maladie (recherche dans un espace d'états + contraintes Z3). L'**Oncology Planning** résout un problème d'optimisation : étant donné un diagnostic, planifier le meilleur protocole de traitement sous contraintes de toxicité et délais (CP-SAT + modèle probabiliste). Ce sont deux paradigmes distincts couverts par des séries différentes.

### Quelle est la différence entre le template étudiant et la solution ?

Le template étudiant (`student/`) contient le squelette du projet : classes avec méthodes `pass` ou `return None` (`# TODO étudiant`), structures de données pré-remplies, et tests unitaires pour valider chaque composant. La solution (`solution/`) implémente chaque méthode complètement. La pédagogie recommande un parcours en 3 phases : (1) comprendre la solution de référence, (2) implémenter le template en s'appuyant sur les tests, (3) étendre avec des variantes personnelles. Le template est exécutable end-to-end grâce aux stubs conformes (pas de `raise NotImplementedError`).

---

*Version 1.1.0 — Juin 2026*
