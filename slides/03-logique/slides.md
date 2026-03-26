---
theme: ../theme-ia101
title: "03 Logique"
info: Cours Intelligence Artificielle
paginate: true
drawings:
  persist: false
transition: slide-left
mdc: true
layout: cover
---

# Bases de connaissance et Logique

- Intelligence Artificielle - III
- Logique propositionnelle
- Logique du premier ordre
- Planification
- Représentation des connaissances

---

# Plan du cours

- Introduction
- Résolution de problèmes
- Bases de connaissances et logique
- Raisonnement probabiliste
- Apprentissage
- Traitement du langage naturel
- TP final projets trimestriels

---

# Sommaire

- Agents fondés sur la connaissance
- Logique propositionnelle
- Logique du premier ordre
- Planification
- Représentation de connaissances
- TP: Mise en œuvre de l'inférence en logique propositionnelle et en logique du premier ordre

---

---

layout: image-right
image: ./images/img_001.png
---

# Agents fondés sur les connaissances

- Comprend:
  - une base de connaissance (KB), composée d'énoncés formulés dans un langage formel de représentation des connaissances
  - un système d'inférence (raisonnement) qui produit de nouveaux énoncés pour prendre des décisions
- Fonctions principales: Tell ( KB) et Ask ( KB)
- Niveaux de l'architecture:
  - Connaissances (formulation naturelle)
  - Logique (formulation en énoncés)
  - Implémentation (représentation physique des énoncés)

---

# Exemple: le monde du Wumpus

- **Jeu de role simpliste** mais riche pour illustrer le raisonnement logique
- **Environnement** : grille 4x4, salles a explorer, dangers caches (Wumpus, puits)
- **But** : trouver l'or et sortir vivant
- **Actions** : avancer, tourner, saisir, tirer une fleche, sortir
- **Percepts** : odeur (Wumpus adjacent), brise (puits adjacent), lueur (or), choc (mur), cri (Wumpus tue)
- L'agent doit **raisonner logiquement** sur ses percepts pour deduire la position des dangers

---

layout: image-right
image: ./images/img_003.png
---

# Représentation et logique

- Représentation de connaissance
  - Objectif = forme manipulable par l'ordinateur
- Définition d'un langage de représentation:
  - Syntaxe: séquences possibles de symboles formant les énoncés
  - Sémantique: faits du monde auxquels les énoncés correspondent
  - Un Monde « possible » = un Modèle qui satisfait l'énoncé
- Raisonnement:
  - Conséquence logique  inférence
  - Exemple: énumération = vérification de modèles

---

layout: image-right
image: ./images/img_006.png
---

# Représentation et logique (2/2)

- Propriétés:
  - Correction:
    - **préserve la validité sémantique**
    - = dérive des conséquences
  - Cohérence / consistance:
    - Pas de contradiction
  - Complétude:
    - Dériver tout ce qui est valide

---

# Types de logiques

- **Ontologie** : étude de ce qui existe dans le monde modélise
- **Epistemologie** : étude de ce qui peut etre connu par l'agent

| Logique | Variables | Quantifie sur | Decidable ? |
|---------|-----------|---------------|-------------|
| Propositionnelle | Symboles booleens | -- | Oui (NP-complet) |
| Premier ordre (FOL) | Objets du domaine | Variables | Semi-decidable |
| Ordre superieur (HOL) | Relations, fonctions | Relations | Non |
| Modale | + mondes possibles | Necessaire/possible | Selon variante |

---

---

layout: center
---

# Questions?

---

# Sommaire

- Agents fondés sur la connaissance
- Logique propositionnelle
- Logique du premier ordre
- Planification
- Représentation de connaissances
- TP: Mise en œuvre de l'inférence en logique propositionnelle et en logique du premier ordre

---

# Logique propositionnelle

- Syntaxe
  - Constantes
    - Vrai, Faux
  - Symboles
    - (énoncés atomiques)
  - Connecteurs
    - Négation
    - Conjonction
    - Disjonction
    - (double) Implication

---

layout: image-right
image: ./images/img_008.png
---

# Logique propositionnelle (2/2)

- Sémantique
  - Modèle  valeur de vérité des symboles
  - Puis tables de vérité
- Exemple: (interprétation)
  - C signifie « il fait chaud »
  - H signifie « il fait humide »
  - P signifie « il pleut »
  - (C  H)  P
- Une tautologie est vraie pour toute interpretation (contradiction : toujours fausse)

| C | H | P | C ∧ H | (C ∧ H) → P |
|---|---|---|-------|-------------|
| V | V | V | V | **V** |
| V | V | F | V | **F** |
| V | F | V | F | V |
| V | F | F | F | V |
| F | V | V | F | V |
| F | V | F | F | V |
| F | F | V | F | V |
| F | F | F | F | V |

---

# Procédure d'inférence simple

- Approche par vérification de modèle (truth table)
- Procédure cohérente et complète (par définition)
- Mais coûteuse

---

# Inférence efficace

- Approches plus efficaces
  - Unités distinctes
  - Élimination des sous-expressions
  - Propagation unitaire
- Heuristiques
  - Unité préféré
  - Unité minimum
  - Même-littéraux
- Stratégies
  - 2-SAT
  - DPLL (Davis-Putnam-Logemann-Loveland)

---

# Propriétés de satisfaisabilité

- Satisfaisabilité (SAT)
  - Existe-t-il une interprétation qui rend l'énoncé vrai?
- Problème NP-complet
  - Théorème Cook-Levin (1971)
  - Réduction polynomiale de problèmes NP
- Algorithmes spécialisés
  - DPLL
  - Choco (Java)
  - MiniSAT (C++)

---

# SAT Solvers

- Algorithmes complets
  - DPLL
  - CDCL (Conflict-Driven Clause Learning)
- Algorithmes approchés
  - GSAT
  - WalkSAT
- Applications
  - Vérification formelle
  - Planification
  - Cryptanalyse

---

---

layout: section
---

# Résumé logique propositionnelle

- Syntaxe: symboles booléens et connecteurs
- Sémantique: interprétations et tables de vérité
- Inférence: vérification de modèles, DPLL
- Applications: satisfaisabilité, vérification

---

---

layout: cover
---

# Logique du premier ordre

---

layout: image-right
image: ./images/img_009.png
---

# Logique du premier ordre

- Extension de la logique propositionnelle
  - Variables: objets du domaine
  - Quantificateurs: ∀ (pour tout), ∃ (il existe)
  - Prédicats: relations sur les objets
  - Fonctions: applications du domaine vers lui-même

---

# Syntaxe de la logique du premier ordre

- Termes
  - Constantes: John, Paris
  - Variables: x, y, z
  - Fonctions: father(John), plus(x,y)
- Atomes
  - Prédicats: loves(John,Mary), greater(5,3)
  - Vrai, Faux
- Formules
  - Connecteurs: ¬, ∧, ∨, →, ↔
  - Quantificateurs: ∀x, ∃y

---

# Exemples de formules FOL

- ∀x loves(x,x)  Tout le monde s'aime
- ∀x ∃y loves(x,y)  Tout le monde aime quelqu'un
- ∀x (man(x) → mortal(x))  Tous les hommes sont mortels
- ∃x (man(x) ∧ immortal(x))  Il existe un homme immortel

---

# Inférence en logique du premier ordre

- Opérations Tell, Ask
  - Assertions  Tell (ex: TELL(KB, King(John)))
  - requêtes / buts  Ask (ex: ASK(KB, King(John)))
  - substitution / liste de liaison  AskVars (ex: ASKVARS(KB, Person(x)))
- Réduction à l'inférence propositionnelle
  - Règles des quantificateurs
  - + Symboles fermés  => symboles propositionnels
  - + Composition de fonctions finie
  -  procédure complète mais semi-décidable (théorème de l'incomplétude de Gödel), très lente

---

layout: image-right
image: ./images/img_010.png
---

# Unification

- Substitutions (ex: subst({x/IceCream, y/Ziggy}, eats(y,x)) = eats(Ziggy, IceCream) )
- Recherche d'unificateurs les plus généraux  Élimine l'étape d'instanciation
- UNIFY(Knows(John, x), Knows(y,Mother (y))) = {y/John, x/Mother (John)}
- Modus ponens generalise → inference naturelle, + indexation → acceleration
  - Exemple pas-a-pas : UNIFY(Knows(John, x), Knows(y, Mother(y))) → {y/John, x/Mother(John)}

---

# Procédures d'inférence en FOL

- Chainages
  - Chainage avant  bases de données déductives, systèmes de production
  - Chainage arrière  programmation logique  (Prolog) + mémoisation
- Exemple:
  - **The law says that it is a crime for an American to**
    - sell weapons to hostile nations. The country Nono,
    - an enemy of America, has some missiles M1, and
    - all of its missiles were sold to it by Colonel West,
    - who is American. Who's a criminal?

---

layout: image-right
image: ./images/img_022.png
---

# Procédures d'inférence en FOL (2/2)

- Résolution
  - Système de preuve complet
  - **Stratégies pour réduire la taille de**
    - l'espace de résolution (démodulation, paramodulation)
  - Démonstrateurs de théorèmes sophistiqués ex: OTTER; e-prover
- Notations
  - p v (q ^ r) <-> p + (q * r)
  - Prolog: cat(X) :- furry(X), meows (X), has(X, claws)
  - Lispy: forall ?x (implies (and (furry ?x) (meows ?x) (has ?x claws)) (cat ?x)))

---

# Logiques d'ordre superieur

- **FOL** quantifie sur des variables representant des **objets**
- **HOL** (Higher-Order Logic) quantifie sur les **relations et fonctions elles-memes**
  - Ex : ∀f ∀g (f = g) ↔ (∀x f(x) = g(x)) -- extensionnalite
  - Ex : ∀r transitive(r) ↔ (∀x∀y∀z r(x,y) ∧ r(y,z) → r(x,z))
- Plus expressif mais **indecidable** (pas d'algorithme complet garanti de terminer)
- **Outils et demonstrateurs** :
  - Tweety (framework Java pour logiques argumentatives)
  - E-prover (demonstrateur automatique pour FOL)
  - **Lean** (assistant de preuve interactif, tres actif en mathématiques)

---

# Logique modale

- Extension avec les modalités
  - de la logique propositionnelle
  - Ou de la logique du premier ordre
- Modalités
  - Possibilité (peut être vrai)
  - Nécessité (doit être vrai)
  - Contingence (vrai dans certains cas)

---

layout: image-right
image: ./images/img_011.png
---

# Logique modale (2/2)

- Syntaxe: opérateurs
  - "◊" (diamant = possibilité)
  - "□" (carré = nécessité)
- Sémantique: mondes possibles
- Applications:
  - Philosophie (modalités épistémiques)
  - Informatique (systèmes muli-agents, vérification formelle)
  - Mathématiques (théorie des ensembles, des jeux, de la preuve)
  - Argumentation (raisonnement modal) Mondes possibles
  - Argumentum

---

# Logiques argumentatives

- Extension des logiques appliquées à l'argumentation
  - Analyse de la structure, la validité, la force des arguments
- Logique argumentative abstraite (de Dung)
  - Modèle sous forme de graphe (Noeuds = arguments, arrêtes = attaques )
  - Notion d'ensembles stable / extensions (pas d'attaques internes)
  - Exemple : si A attaque B et B attaque C, alors {A, C} est une extension stable

---

# Logiques argumentatives (2/2)

- Autres logiques argumentatives extensions de Dung
  - Aspic (SPecification, and Interrogation with Constraints)
    - Règles, contraintes, attaques entre arguments
    - Satisfaction des règles, validité des arguments, résolution des conflits
  - ABA (Assumption-Based Argumentation)
    - Utilisation d' ensembles d'hypothèses
    - Relations de soutien et d'attaques
    - Cohérences des ensembles et forces contextuels des arguments
  - Argumentum

---

layout: image-right
image: ./images/img_023.png
---

# Argument mining

- Objectif: reconstruire la structure inférentielle depuis le texte et le discours
- Domaine naissant:
  - Groupes de recherches: CMNA, COMMA, ACL etc.
  - Toutils: DisLog Language, Topic Based Modelling
  - Ontologie: Argument Interchange Format
    - AIF+ rajoute le dialogue
- Outils d'annotation argumentative
  - Ex: Ova+
- Dimension sociale
  - Importance du travail collaboratif
  - Débat, jeux de dialogue ex:  "<statement>,<challenge><defense>"

---

# Bons arguments

- Critères d'Aristote (rhetorique) reprise dans Toulmin
- Structure d'un bon argument
  - **Conclusion** ce que l'on veut démontrer
  - **Prémisses** ce qui permet de démontrer la conclusion
  - **Liaison** comment on démontre
  - **Appui** pourquoi on croit les prémisses
  - **Réfutation** anticiper et contrer les objections

---

# Bons arguments (2/2)

- Cinq critères de force d'un argument
  - Prémisses pertinentes
    - Liées à la conclusion
    - Contre-exemple: Tous les chats sont gris. Le chat du voisin est un chat. Donc il est gris.
  - Prémisses acceptables
    - Bien établies, croyables
    - Contre-exemple: Tous les Martiens sont verts. Donc la tour Eiffel est verte.

---

# Bons arguments (3/3)

- Prémisses suffisantes à démontrer la conclusion
  - Difficile à systématiser,
  - Cf. certaines sciences (échantillons statistiques) ou expérience
- Prémisses fournissant une réfutation effective des critiques anticipées
  - Le plus difficile, manque le plus souvent
  - Permet de départager de « presque » bons arguments
- Renforcer un argument:
  - Balayer ces 5 critères et le modifier en conséquence

---

# Qu'est-ce qu'un argument fallacieux?

- La violation de l'un des critères définissant un bon argument
  - Faille structurelle
  - Prémisse non pertinente
  - Prémisse sous le standard d'acceptabilité
  - Prémisses insuffisantes à établir la conclusion
  - Pas de réfutation effective des critiques anticipées
- Nommées ou non
  - Cf. Taxonomie
  - Nom pas nécessaire, mais utile

---

# Qu'est-ce qu'un argument fallacieux? (2/2)

- Dénoncer un argument fallacieux
  - Autodestruction par reconstruction en forme standard
  - Méthode du contre-exemple absurde
- Fair-play:
  - Pas trop en faire,
  - Que si nécessaire,
  - Accepter ses propres erreurs,
  - Eviter si possible de mentionner la notion d'argument fallacieux
- Fin de l'aparté

---

layout: section
---

# Résumé logique du premier ordre

- Extension de la propositionnelle avec quantificateurs
- Syntaxe: termes, atomes, formules
- Inférence: unification, chainage, résolution
- Variantes: modale, argumentative, ordre supérieur

---

---

layout: image-right
image: ./images/img_012.png
---

# Planification

- Problèmes à base de connaissances
  - État initial
  - Actions
  - But
- Recherche de plans
  - Séquences d'actions
  - Optimalité
- Méthodes
  - Forward search
  - Backward search
  - Heuristiques

---

# Représentation des problèmes de planification

- États
  - Ensembles de propositions
  - Ex: At(Location(Agent,Paris)), At(Treasure,Cairo))
- Actions
  - Préconditions
  - Effets
  - Ex: Move(Agent,X,Y)
    - Pre: At(Agent,X), Connected(X,Y)
    - Add: At(Agent,Y)
    - Del: At(Agent,X)

---

# Planification classique

- STRIPS (Stanford Research Institute Problem Solver)
  - États: ensembles de propositions
  - Actions: prédicats ajoutés/retirés
  - Heuristiques: Goal Count, h^+ additive
- Graphplan
  - Planification par niveaux
  - Mutex: actions incompatibles
- SATPlan
  - Réduction à SAT

---

layout: image-right
image: ./images/img_013.png
---

# Planification avec contraintes

- CSP (Constraint Satisfaction Problems)
  - Variables
  - Domaines
  - Contraintes
- Méthodes
  - Backtracking
  - Forward checking
  - Arc consistency
  - Local search

---

# Planification temporelle

- Durées
  - Actions temporisées
  - Contraintes temporelles
- Exemple
  - Start: t=0
  - Action A: durée 5
  - Action B: durée 3
  - Contrainte: B commence après A
  - Solution: A[0-5], B[5-8]

---

layout: image-right
image: ./images/img_014.png
---

# Planification en logique

- SitCalc (Situation Calculus)
  - Relations: State(n,P)
  - Actions: Result(a,s)
  - Fluents: F(n)
- HTN (Hierarchical Task Network)
  - Décomposition de tâches
  - Sous-tâches
- Partial Order Planning (POP)
  - Plan partiel
  - Ordre

---

# Représentation des connaissances

- Formalismes
  - Logiques
  - Ontologies
  - Frames
  - Description Logics
- Applications
  - Base de connaissances
  - Web sémantique
  - Expert systems

---

# Ontologies

- Définition
  - Théorie d'une conceptualisation
  - Partage d'ontologies
- Composantes
  - Concepts
  - Relations
  - Axiomes
- Formalismes
  - RDF(S)
  - OWL
  - OWL2

---

# Web sémantique

- Vision
  - Données avec signification
  - Machine readable
- Pile W3C
  - XML
  - RDF
  - OWL
  - SPARQL
- Applications
  - Recherche sémantique
  - Interopérabilité

---

# Frames

- Structure de données
  - Slots
  - Valeurs par défaut
  - Contraintes
- Périodification
  - Vues
  - Méthodes
  - Héritage

---

# Description Logics

- Sous-ensemble de FOL
- Concepts
  - Atomes
  - Union
  - Intersection
  - Complément
- Relations
  - Propriétés
  - Rôles
- Algorithmes
  - TBox, ABox
  - Inference: satisfiability, subsumption

---

layout: section
---

# Résumé représentation des connaissances

- Ontologies
  - Méta-modèles de données
- Web sémantique
  - Représentation de faits
  - Pile sémantique du W3C
- Systèmes de raisonnement
  - Maintenance de la vérité
- Smart Contracts
  - Signatures, chiffrement et Preuves
  - Divulgation partielle et contractualisée

---

---

layout: center
---

# Questions?

---

# Plan du cours

- Introduction
- Résolution de problèmes
- Bases de connaissances et logique
- Raisonnement probabiliste
- Apprentissage
- Traitement du langage naturel
- TP final projets trimestriels

---

# Projets de groupe (1/2)

- Moteur de recherche augmenté par le raisonnement et le langage naturel
  - Grammaire et sémantique des contenus et des requêtes. Lucene.Net, OpenNLP, SharpRDF, FOL
- Conception de bots de services sur réseaux sociaux
  - Chat Bots, AIML, Reddit et agents de service, NLP, RDF, APIs
- Conception d'un modèle d'inférence pour l'analyse de sentiment
  - Conception d'un modèle probabiliste, Infer.Net, démarche expérimentale, Reddit
- Création d'une plateforme sémantique LDP à partir d'un index structuré.
  - Structuration et ouverture des données = Linked Data. Lucene.Net, SharpRDF
- Résolution de Captchas par deep learning
  - Apprentissage via un réseau de neurones convolutif. PyTorch, TensorFlow, transfer learning

---

# Projets de groupe (2/2)

- Entrainement de stratégies de trading algorithmiques sur crypto monnaies.
  - Réseaux de neurones récurrents (LSTM), scikit-learn, données Binance API
- Amélioration par l'apprentissage d'un agent joueur de Go simple
  - Le Go et l'IA, récentes avancées (AlphaGo). PyTorch, reinforcement learning
- Évolution de vaisseaux spatiaux par algorithmes génétiques dans le jeu de la vie.
  - Approches évolutionnistes, automates cellulaires. DEAP, Golly, Python
- Pilotage d'un cluster de cache distribué pour le portage d'applications  dans le Cloud
  - Caches distribués, scaling, stratégies et clustering. Redis

---

# Pour aller plus loin : Notebooks

> **Lean 4** (10 notebooks) : Assistants de preuve, logique d'ordre supérieur
> `MyIA.AI.Notebooks/SymbolicAI/Lean/`

> **Z3 / SMT** : Solveurs modulo théorie, SAT, contraintes
> `MyIA.AI.Notebooks/Sudoku/Sudoku-4-Z3.ipynb`

> **Argumentation (Tweety)** : Logiques argumentatives de Dung, ASPIC, ABA
> `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/`

> **Web sémantique (RDF)** : Triplets, ontologies, SPARQL
> `MyIA.AI.Notebooks/SymbolicAI/RDF/`

> **CSPs et planification** : Problèmes de satisfaction de contraintes
> `MyIA.AI.Notebooks/Search/CSPs_Intro.ipynb`
> `MyIA.AI.Notebooks/Sudoku/Sudoku-3-ORTools.ipynb`

---

---

layout: cover
---

# Merci

- Jean-Sylvain Boige
- jsboige@myia.org