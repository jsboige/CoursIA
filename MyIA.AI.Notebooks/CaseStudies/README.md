# CaseStudies - Etudes de cas interdisciplinaires

<!-- CATALOG-STATUS
series: CaseStudies
pedagogical_count: 4
breakdown: Diagnostic-Medical=2, Oncology-Planning=2
maturity: BETA=2, PRODUCTION=2
-->

Etudes de cas interdisciplinaires combinant plusieurs domaines de l'IA dans des projets appliques.

La force des etudes de cas reside dans leur capacite a **fusionner les techniques apprises en silos** : un solveur SMT (Search), un algorithme genetique (Sudoku), une ontologie OWL (SemanticWeb) et un modele bayesien (Probas) ne valent pas grand chose isolement face a une question reelle. C'est leur combinaison, orchestree autour d'un probleme metier (diagnostic medical, protocole oncologique), qui transforme un catalogue d'outils en **systeme decisionnel coherent**. Les deux projets de cette serie illustrent ce passage : chacun mobilise 3 a 4 paradigmes IA differents qui se renforcent mutuellement plutot que de se concurrencer.

**4 notebooks** | **2 projets** | **~6-8h**

## A qui s'adresse cette serie

Cette serie s'adresse aux **etudiants en fin de cycle** (M1/M2 ou equivalent ingenieur) ayant deja parcouru les series fondamentales (Search, SymbolicAI, Probas, SemanticWeb). Elle constitue typiquement un **devoir de controle continu integrateur** ou un projet de groupe couvrant plusieurs paradigmes IA dans un meme livrable. La pedagogie privilegie l'**autonomie** : chaque projet propose un template etudiant minimal et une solution de reference pour autoevaluation.

Les profils types vises :

- Etudiants en informatique ou IA construisant un portefeuille de projets multi-paradigmes
- Developpeurs/data scientists explorant l'integration de techniques heterogenes (symbolique + probabiliste)
- Enseignants cherchant des **devoirs d'integration** mobilisant 3-4 series du cursus

## Pourquoi des etudes de cas interdisciplinaires ?

L'IA reelle ne fonctionne quasi-jamais avec un seul paradigme. Un assistant diagnostic exploite a la fois des **regles symboliques** (contre-indications absolues), des **modeles probabilistes** (incertitude sur les symptomes), des **algorithmes de recherche** (exploration de l'arbre de diagnostics) et des **contraintes formelles** (validation par solveur). Reduire ce probleme a une seule technique conduit a des systemes brittle (regles only), opaques (deep learning only) ou inutilisables (probabiliste only sans contraintes dures).

### Le principe d'integration

| Couche | Role | Techniques | Exemple OncoPlan |
|--------|------|-----------|------------------|
| **Connaissances metier** | Representer le domaine | Ontologies OWL, regles | Medicaments, interactions, contre-indications |
| **Contraintes dures** | Filtrer l'impossible | CSP, SMT, OR-Tools | Doses cumulees, delais entre cures |
| **Incertitude** | Modeliser l'aleatoire | Bayesien, Pyro, Infer.NET | Reponse patient, toxicite predite |
| **Optimisation** | Choisir la meilleure option | A*, genetique, RL | Calendrier optimal de cures |
| **Decision finale** | Synthese et explication | Workflow, scoring | Recommandation justifiee au clinicien |

Une seule couche ne suffit pas, et l'**ordre de composition** importe : on filtre avant d'optimiser, on modelise l'incertitude avant de valider sous contraintes. Les etudes de cas materialisent ces patterns d'architecture.

### Le pattern "twin numerique"

Les deux projets reposent sur un **modele de patient simule** : un objet logiciel qui represente l'etat clinique (symptomes, antecedents, parametres biologiques) et reagit a des interventions (diagnostic propose, traitement applique). Ce pattern, appele **jumeau numerique** (digital twin), est devenu central en sante numerique, en industrie 4.0 et en simulation environnementale. L'apprendre sur 10 patients diabetiques (Diagnostic-Medical) ou un cas oncologique (Oncology-Planning) prepare directement aux applications professionnelles.

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

## Acquis d'apprentissage

A l'issue de cette serie, l'etudiant est capable de :

### Competences techniques

- **Concevoir une architecture IA hybride** combinant raisonnement symbolique (regles, ontologies, contraintes) et apprentissage statistique (modeles probabilistes, optimisation evolutionnaire)
- **Modeliser un domaine metier** avec un vocabulaire formel (classes, proprietes, axiomes) sans confondre representation et inference
- **Decomposer un probleme complexe** en sous-problemes adresses par la technique la plus adaptee (filtrage par contraintes, recherche heuristique, inference bayesienne)
- **Composer plusieurs solveurs** (Z3, OR-Tools, Pyro, A*) dans un pipeline coherent ou la sortie de l'un alimente l'autre
- **Valider un systeme decisionnel** sur des cas reels (patients diabetiques, protocoles oncologiques) avec metriques de qualite et explicabilite

### Competences methodologiques

- **Identifier les couches d'un systeme IA** (donnees -> connaissances -> contraintes -> modeles -> decision) et leur ordre de composition
- **Choisir entre approches deterministes et probabilistes** selon que les contraintes sont absolues ou negociables
- **Justifier le recours a l'IA hybride** plutot qu'a un seul paradigme : robustesse, explicabilite, conformite reglementaire
- **Documenter un projet IA interdisciplinaire** : architecture, choix algorithmiques, limites connues, perimetre de validation

### Competences applicatives (domaine medical)

- **Manipuler des donnees patient** (CSV structures, anonymisation, integrite des CSP)
- **Encoder un protocole therapeutique** sous forme d'ontologie + contraintes (delais, doses, interactions)
- **Estimer une incertitude clinique** via inference bayesienne et amplification (`poutine.scale` en Pyro)
- **Construire un jumeau numerique** simulant la reaction d'un patient a une intervention

## Concepts cles transversaux

Cette serie consolide cinq concepts qui reviennent dans tous les systemes IA appliques modernes :

| Concept | Definition | Manifestation dans CaseStudies | Cours connexes |
|---------|------------|--------------------------------|----------------|
| **Architecture hybride** | Pipeline combinant techniques symboliques et statistiques | Diagnostic : A* + GA + Z3 / OncoPlan : Ontologie + CSP + Pyro | [SymbolicAI](../SymbolicAI/README.md), [Probas](../Probas/README.md) |
| **Jumeau numerique** | Modele logiciel d'un objet/personne reagissant a des interventions | Modele patient (etat, parametres bio, reponse au traitement) | [RL](../RL/README.md), [Probas](../Probas/README.md) |
| **Knowledge engineering** | Formalisation explicite des connaissances metier en classes/regles | Ontologie oncologique, regles de diagnostic | [SemanticWeb](../SymbolicAI/SemanticWeb/README.md) |
| **Inference sous contraintes** | Resolution conjointe d'un probleme avec contraintes dures et incertitudes | OncoPlan : calendrier valide ET probable | [Search](../Search/README.md), [SymbolicAI/Tweety](../SymbolicAI/Tweety/README.md) |
| **Decision sous incertitude** | Choisir entre options avec resultats probabilistes et regret asymetrique | OncoPlan : adapter ou non un protocole | [Probas](../Probas/README.md), [GameTheory](../GameTheory/README.md) |

Ces concepts ne sont pas exclusifs au domaine medical : on les retrouve a l'identique en **finance algorithmique** (jumeau de marche + contraintes reglementaires + signaux probabilistes), **logistique** (jumeau de flotte + planification + previsions) et **maintenance predictive** (jumeau equipement + regles metier + Bayesien). Le choix du medical est pedagogique : domaine riche en contraintes formelles et en incertitude irreductible.

## Pour aller plus loin

### Articles de reference

- **Khan et al. (2021)** - *Hybrid AI for Clinical Decision Support: A Survey* — panorama des architectures hybrides en sante numerique
- **Goodall et al. (2022)** - *Digital Twins in Healthcare: Trends, Applications, and Implementation Challenges* — etat de l'art jumeaux numeriques patient
- **Hooker (2012)** - *Integrated Methods for Optimization* — fondements de la composition CP/SAT/MILP utilisee en OncoPlan
- **Bingham et al. (2019)** - *Pyro: Deep Universal Probabilistic Programming* — paper de reference pour la couche probabiliste

### Extensions possibles

| Extension | Description | Techniques mobilisees |
|-----------|-------------|----------------------|
| **Apprentissage par renforcement** | Formuler OncoPlan en MDP : etat patient -> action protocole -> recompense survie | PPO, DQN ([RL](../RL/README.md) notebooks 5-6) |
| **LLM en boucle** | Utiliser un LLM pour generer des hypotheses diagnostiques, valider par Z3 | [Sudoku](../Sudoku/README.md) notebook 17, Semantic Kernel |
| **Multi-agent** | Plusieurs medecins virtuels delibererent (diagnostic, prescription, monitoring) | [RL](../RL/README.md) notebook 6, [GameTheory](../GameTheory/README.md) |
| **Explicabilite** | Generer une trace narrative des decisions ontologie + contraintes + Bayesien | [SymbolicAI](../SymbolicAI/README.md), Tweety argumentation |
| **Federated learning** | Entrainement reparti entre hopitaux sans partage des donnees patient | Adaptation [ML](../ML/README.md), considerations RGPD |

### Aspects ethiques et reglementaires

Les systemes IA appliques au domaine medical sont soumis a des contraintes legales (RGPD, AI Act europeen, FDA aux US) et ethiques (explicabilite, biais, responsabilite). Les projets de cette serie sont **academiques** : ils utilisent des donnees synthetiques ou anonymisees et ne sont pas destines a un usage clinique. Toute transposition reelle exigerait :

- Validation clinique sur cohorte representative et publication peer-reviewed
- Certification dispositif medical (Classes I-IV selon risque)
- Audit ethique (CER, CNIL pour les donnees patient en France)
- Explicabilite documentee de chaque decision automatisee

Ces dimensions sont abordees en survol dans les notebooks mais meritent un module dedie pour une formation professionnelle complete.

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
