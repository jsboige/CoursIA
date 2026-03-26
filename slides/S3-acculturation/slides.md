---
theme: ../theme-ia101
title: "S3 Acculturation IA"
info: Cours Intelligence Artificielle
paginate: true
drawings:
  persist: false
transition: slide-left
mdc: true
layout: cover
---

# Intelligence(s)

- Jean-Sylvain Boige
- jsboige@myia.org
- Telecom Bretagne
- Cogs, Brighton UK
- Aricie - DNN - PKP

![w:250](images/img_001.png)
![w:250](images/img_002.png)
![w:250](images/img_003.png)

---

# Sommaire

- Qu'est-ce que l'intelligence artificielle ?
- Racines, histoire et état de l'art
- Structure des agents rationnel
- Intelligence exploratoire
- Comment chercher la solution à un problème ?
- Intelligence Symbolique
- Comment utiliser le raisonnement et les mathématiques ?
- Intelligence probabiliste
- Comment agir dans l'incertitude ?
- Apprentissage
- Comment utiliser les données et l'expérience ?
- Application: le langage naturel

---
layout: image-right
image: ./images/img_004.png
---


<!-- notes: Timing? -->

---

<!-- _class: section -->

# Intelligence artificielle

- Introduction
- Agents rationnels
- Intelligences

---

<!-- _class: columns-layout -->

# Qu'est-ce que l'intelligence artificielle?

<div class="columns">
<div class="col-left">

- Définitions multiples
- Notre angle :
  - « Agir de façon rationnelle »
- Conception d'agents

**Fondements**

- Philosophie
- Maths
- Economie
- Biologie
- Neurosciences
- Psychologie
- Informatique
- Théorie du contrôle
- Linguistique

</div>
<div class="col-right">

![w:380](images/img_005.png)

</div>
</div>

<!-- notes: Définitions multiples de l'intelligence et de l'IA
Concevoir != comprendre
Définition mouvante:
Automates  Calculateur  Algorithmes  Bases de connaissances  Systèmes experts  Apprentissage profond  ?
4 types d'approches:
Notre angle principal: « Agir de façon rationnelle »
Conception d'agents
Philosophie	Logique, méthodes de raisonnement, esprit physique, apprentissage, langage, raison
Maths 		Représentation formelle et preuve, algorithmes, calcul, (in)décidabilité, complexité, probabilités
Economie	Utilité, théorie des jeux, la décision, agents économiques rationnels
Biologie		Intelligence naturelle et animale
Neurosciences	Substrat physique de l'activité mentale
Psychologie	Comportement, Perception cognition, contrôle moteur, techniques expérimentales
Informatique	Origines, ordinateurs puissants et logiciels
Théorie du 	Maximiser une fonction objective contrôle	dans le temps
Linguistique	Représentation de connaissances, grammaire -->

---

<!-- _class: columns-layout dense -->

# Développement (1/2)

<div class="columns">
<div class="col-left">

**Histoire succincte**

- 1940-70 : Enthousiasme des débuts
  - Turing, Dartmouth, Lisp
  - Samuel, Newell & Simon
- 1970s : Complexité calculatoire
  - Réseaux de neurones en pause
  - Systèmes experts
- 1980s : L'IA devient une industrie
  - Robotique, vision
- 1990s : L'IA devient une science

<div style="text-align: center; margin-top: 8px;">
![h:100](images/img_006.png)
</div>

</div>
<div class="col-right">

**État de l'art**

- 1997 : Deep Blue (échecs)
- 2000s : Prouveurs, planification
- 2007 : Jeu de dames résolu
- 2010s : Explosion deep-learning
  - 2014 : GANs
  - 2016 : AlphaGo
- NLP : Transformers, LLMs

<div style="display: flex; gap: 10px; margin-top: 8px;">
![h:45](images/img_007.jpg)
![h:45](images/img_008.jpg)
</div>

</div>
</div>

<!-- notes: Ne pas passer trop de temps sur les jeux (pas des gamers) -->

---

# Développement (2/2)

- **2000s** : Data mining, apprentissage bayesien, web semantique, prouveurs automatiques
- **2010s** : Explosion du deep learning et du big data
  - 2014 : GANs (génération d'images), 2016 : AlphaGo (Go)
  - 2017 : Transformers ("Attention is All You Need")
  - 2018 : AlphaZero (echecs, Go, shogi sans connaissances humaines)
  - 2019 : Pluribus (poker), AlphaStar (Starcraft 2)
- **2020s** : LLMs et IA generative deviennent grand public
  - GPT-3 (2020), ChatGPT (2022), GPT-4 (2023), Claude 3 (2024)
  - Stable Diffusion, Midjourney, DALL-E : génération d'images
  - 2025 : agents IA autonomes, vibe coding, IA multimodale

> **Chronologie cle** : Turing (1950) → Dartmouth (1956) → Hiver IA (1974) → Deep Blue (1997) → AlphaGo (2016) → ChatGPT (2022) → Agents IA (2025)

---

# Dans la vie de tous les jours

- **Poste** : reconnaissance des adresses et tri automatique du courrier
- **Banque** : lecture des cheques, verification des signatures, évaluation de credits
- **Medecine** : diagnostic assiste, prescriptions, suivi et prevention
- **Service client** : synthese/reconnaissance vocale, chatbots (ChatGPT, Claude)
- **Transport** : detection de plaques, conduite autonome (Tesla, Waymo)
- **Internet** : marketing personnalise, detection de spam et de fraude
- **Industrie** : conception, fabrication et exploitation assistees par IA
- **Image numerique** : detection de visages, mise au point, compression
- **Jeux** : personnages et adversaires intelligents (NPCs adaptatifs)

---

<!-- _class: columns-layout -->

# Les agents

<div class="columns">
<div class="col-left">

**Définition**

- L'agent rationnel
  - Entité qui perçoit par des capteurs
  - agit par des effecteurs.
- Dans un environnement
  - Fait la bonne action
  - Maximise son succès.
  - Pas omniscient
  - Réactif, proactif, interactif, autonome
- Limitations
  - ressources disponibles

</div>
<div class="col-right">

![w:350](images/img_009.png)

</div>
</div>

<!-- notes: « La bonne action »: celle qui maximise le succès.
Mesure de de la performance
Critère objectif de succès.
Maximisation de la mesure de performance
A partir de la suite de percepts et de l'état de connaissance.
Rationnel != omniscient
Réactivité, Proactivité
Exploration =  modification des percepts
Interaction, Autonomie
Comportement issu de l'expérience
Environnement limité:
la rationalité parfaite n'est souvent pas atteignable.
 Objectif = les meilleures performances
Compte tenu des ressources disponibles
Rationalité humaine
Normatif (logique)  Conséquentialiste (succès cognitif) -->

---

<!-- _class: columns-layout -->

# Conception d'agents

<div class="columns">
<div class="col-left">

**Environnement de tache**

- Description PEAS : Performance, Environnement, Actionneurs, Senseurs

**Agent reflexe**

- Pas de mémoire, reagit aux percepts courants
- Regles condition → action (si obstacle, alors freiner)

![w:300](images/img_010.png)

</div>
<div class="col-right">

![w:380](images/img_011.png)

</div>
</div>

<!-- notes: Insister sur le cas pratique (e.g. Elon Musk)
 design best program for given machine resources -->

---

<!-- _class: section -->

# Quiz

- Taxi autonome:
  - Description Peas
  - Intelligences

---

<!-- _class: columns-layout -->

# Agent réflexe fondé sur un modèle

<div class="columns">
<div class="col-left">

**Agent réflexe avec modèle**

- Fonctionnement interne
- Etat du monde
- Niveau de représentation

**Compromis**

- Flexibilité vs complexité

</div>
<div class="col-right">

![w:380](images/img_012.png)

</div>
</div>

<!-- notes: (virer?)
 design best program for given machine resources -->

---

# Intelligences

- **Procedurale** : automates et algorithmes déterministes (instructions pas a pas)
- **Exploratoire** : recherche dans un espace d'etats (parcours de graphes, A*)
- **Symbolique** : raisonnement logique, bases de connaissances, planification
- **Probabiliste** : gestion de l'incertitude, réseaux bayesiens, decision
- **Apprentissage** : amelioration par l'expérience (supervise, renforcement, deep learning)

![w:200](images/img_013.jpg) ![w:200](images/img_014.png) ![w:200](images/img_015.jpg)

---
layout: center
---

# Questions?

---

<!-- _class: section -->

# Intelligence exploratoire

- Recherches non informée et informée
- Jeux
- Problèmes à satisfaction de contraintes

---

<!-- _class: columns-layout -->

# Agent explorateur

<div class="columns">
<div class="col-left">

**Agent fonde sur des buts**

- Passe du reactif au deliberatif
- Planifie ses actions par exploration

![w:300](images/img_016.png)

</div>
<div class="col-right">

**Résolution de problèmes**

- Objectif ?
- Actions ?
- Représentation ?

![w:300](images/img_017.png)

</div>
</div>

<!-- notes:  design best program for given machine resources -->

---

<!-- _class: columns-layout dense -->

# Formulation de problèmes

<div class="columns">
<div class="col-left">

**Itinéraire**

![w:300](images/img_018.png)

- Etat initial, test de but
- Transitions
- Etats, Actions
- Coût de chemin
- Solution = Séquence

</div>
<div class="col-right">

**Abstractions**

- Assemblage robotique
- Problèmes jouets

![w:200](images/img_019.png)
![w:200](images/img_020.png)
![w:200](images/img_021.png)

</div>
</div>

---

<!-- _class: columns-layout -->

# Arbre d'exploration

<div class="columns">
<div class="col-left">

**Idée de base**

- Développement des états successeur
- **Choix des nœuds**
  - = Stratégie d'exploration

![w:320](images/img_022.jpg)

</div>
<div class="col-right">

**Exemple: Enigme**

- Missionnaires et cannibales
  - Barque de 2 places
  - Jamais + de cannibales

![w:280](images/img_023.png)
![w:100](images/img_024.png)

</div>
</div>

---

<!-- _class: section -->

# Quiz

- Missionnaires et cannibales
- Intelligences

---

<!-- _class: columns-layout dense -->

# Stratégies d'exploration (1/2)

<div class="columns">
<div class="col-left">

**Non informées**

- En largeur
- En profondeur
- Ex: Où sont mes clefs ?
- Bidirectionnelle

![w:220](images/img_025.png)
![w:220](images/img_026.png)
![w:220](images/img_027.png)

</div>
<div class="col-right">

**Informées**

- Évaluation des états
- Heuristique
- Estimation du coût restant
- Ex: Distance à vol d'oiseau
- Par le meilleur d'abord
  - Exploration gloutonne
  - Algorithme A*
  - Demo Pathfinding.js

![w:220](images/img_028.png)
![w:220](images/img_029.png)

</div>
</div>

---

<!-- _class: columns-layout dense -->

# Stratégies d'exploration (2/2)

<div class="columns">
<div class="col-left">

- Si seule la solution compte
  - pas le chemin
  - Modification d'un seul état
- Paysage de l'espace des états
  - Optimisation d'une fonction
  - Escalade, descente de gradient

![w:220](images/img_030.png)
![w:220](images/img_031.png)

</div>
<div class="col-right">

- Problèmes :
  - Bloqué sur un optimum local
- Solutions:
  - Recuit simulé
  - Ex: le carton de babioles
  - Exploration en faisceaux
  - Ex: Perdus en foret
  - Sélection naturelle = combinaison
  - Algorithmes génétiques

![w:220](images/img_032.png)
![w:220](images/img_033.png)

</div>
</div>

<!-- notes: Démo GeneticSharp -->

---

<!-- _class: columns-layout dense -->

# Jeux

<div class="columns">
<div class="col-left">

**Jeux vs Exploration**

- Arbre de jeu
- Environnements
  - multi-agents, concurrentiels
  - Classe la plus étudiées
  - Alternés, déterministes
  - A somme nulle (h1 = -h2)
  - A information parfaite
- Difficulté
  - Arbre d'exploration impraticable
  - Performance critique: temps
  - Stochastiques, information imparfaite
  - Libratus (poker), Starcraft 2

</div>
<div class="col-right">

**Arbre Minimax**

- Actions joueurs Max et Min + utilité terminale

**Techniques**

- Minimax, Alpha-Beta
- Avec arrêt + évaluation heuristique
- Techniques probabilistes
- Expectiminimax
- Méthodes de Monte-Carlo

![w:350](images/img_031.png)

</div>
</div>

---

<!-- _class: columns-layout dense -->

# Problèmes à satisfaction de contraintes

<div class="columns">
<div class="col-left">

**Définition CSPs**

- Jusqu'ici: représentation atomique
- CSP = Etat factorisé
- Etat = variables sur des domaines
- Test de but = contraintes sur les variables
- Bonnes méthodes générales
- Meilleures que l'exploration standard
- Exemple
  - Coloration de carte

</div>
<div class="col-right">

**Techniques**

- Exploration avec heuristiques
  - H1 ? H2 ? H3 ?
  - Ex: le coffre de voiture
- Inférence
  - Mise en cohérence des domaines
  - Ex: Sudoku
- Structure des problèmes
  - Sous-problèmes, Arbres
- Structure des valeurs
  - Symétrie (rupture de)

<div class="img-grid-2x2">
![w:150](images/img_034.jpg)
![w:150](images/img_035.png)
![w:150](images/img_036.png)
![w:150](images/img_037.png)
</div>

</div>
</div>

<!-- notes: Se concentrer sur le coffre de voitureMinimum de valeurs restantes
Variable la + contraignante
Valeur la – contraignante -->

---
layout: center
---

# Questions?

---

<!-- _class: section -->

# Intelligence symbolique

- Logique propositionnelle
- Logique du premier ordre
- Agents fondés sur la connaissance
- Planification

<!-- notes: Faire 1 slide des 3 suivants, se concentrer sur les exemples -->

---

<!-- _class: columns-layout -->

# Représentation et logique

<div class="columns">
<div class="col-left">

**Enoncés**

- Langage
- Syntaxe
- Sémantique
- Types de logiques

**Inférence**

- Propriétés
- correction, consistance, complétude

</div>
<div class="col-right">

**Bases de connaissances**

**Raisonnement**

![w:300](images/img_035.png)
![w:300](images/img_036.png)

</div>
</div>

---

<!-- _class: columns-layout -->

# Logique propositionnelle

<div class="columns">
<div class="col-left">

- Syntaxe
- Sémantique
  - Tables de vérité
- Inférence logique
  - Règles cohérentes
  - Ex: Modus ponens
  - Preuve déductive
- Procédures
  - Chainages
  - Résolution
  - DPLL, WalkSAT
- Solveurs SAT
  - Problèmes NP-complets

</div>
<div class="col-right">

<div class="img-grid">
![w:200](images/img_038.png)
![w:200](images/img_039.png)
![w:200](images/img_040.png)
</div>

</div>
</div>

---

<!-- _class: columns-layout dense -->

# Logique du premier ordre (FOL)

<div class="columns">
<div class="col-left">

- Modélise
  - Objets, Propriétés
  - Relations, Fonctions
- Quantificateurs:
  - Il existe x - x
  - Pour chaque x - x
- Sémantiques multiples
  - de base de données

</div>
<div class="col-right">

**Exemple: investigation**

- Missile(x) ET Possède(Corée, x) => Vend(West, x ,Corée)
- Missile(x) => Arme(x)
- Enemy(x,America) => Hostile(x)
- Américain(x) ET Arme(y) ET Vend(x,y,z) ET Hostile(z) => Criminel(x)

![w:300](images/img_040.png)

</div>
</div>

---

<!-- _class: columns-layout dense -->

# Application: argumentation

<div class="columns">
<div class="col-left">

**Code de conduite**

- Principes de conduite intellectuelle
  - Faillibilité
  - Recherche de la vérité
  - Clarté
  - Charge de la preuve
  - Charité
  - Structure, Pertinence, Acceptabilité, Suffisance, Réfutation
  - Suspension du jugement
  - Résolution

</div>
<div class="col-right">

**Qu'est-ce qu'un argument?**

- Standards
  - procédural efficace
  - éthique important
- Une proposition (conclusion) supportée par
  - D'autres proposition (Prémisses)
  - Le raisonnement
- Argument =/= Opinion
- Déduction vs Induction
  - Déduction  nécessité logique
  - Induction  Corroboration
  - Prémisses particulières
  - Argument Moral  principe
  - Légal  loi, jurisprudence etc.
  - Esthétique  critère

</div>
</div>

---

<!-- _class: columns-layout dense -->

# Analyse rhétorique

<div class="columns">
<div class="col-left">

**Un bon argument**

- Respecte 5 critères
  - Structure bien formée
  - Prémisse pertinentes
    - pour la vérité de la conclusion
  - Prémisses acceptables
    - par une personne raisonnable
  - Prémisses suffisantes
    - à démontrer la conclusion
  - Fournissant une réfutation effective
    - des critiques anticipées
- Renforcer un argument
  - Balayer ces 5 critères

</div>
<div class="col-right">

**Un argument fallacieux**

- Viole l'un des critères
- Taxonomie
- Comment le dénoncer
  - Reconstruction standard
  - Contre-exemple absurde
  - Fair-play

<div class="img-grid">
![w:220](images/img_042.jpg)
![w:220](images/img_041.jpg)
</div>

</div>
</div>

<!-- notes: Ne pas passer trop de temps sur la taxonomie, passer sur le Jeu rapidement -->

---

<!-- _class: columns-layout dense -->

# Application: Planification

<div class="columns">
<div class="col-left">

**Expression de problème**

- Langage formel
- But à atteindre
- Listes des opérations

**Approches**

- Exploration des états, plans
- Heuristiques ?
- Calcul situationnel
- Théorèmes en FOL
- Planification par contraintes
- Planification à Ordre partiel
- Décomposition hiérarchique

</div>
<div class="col-right">

<div class="img-grid">

![](images/img_043.png)
![](images/img_044.png)
![](images/img_045.png)
![](images/img_046.png)
![](images/img_047.jpg)

</div>

</div>
</div>

<!-- notes: Zapper -->

---

<!-- _class: columns-layout -->

# Autres Applications (1/2)

<div class="columns">
<div class="col-left">

- Solveurs Modulo Théorie
  - SAT + Quantificateurs
  - + Théories arithmétiques
  - + Optimiseurs
- Ingénierie de connaissances
  - Triplets, Ontologies
  - Web sémantique
  - W3C
  - Linked Data

</div>
<div class="col-right">

![w:300](images/img_048.png)
![w:300](images/img_049.png)

</div>
</div>

<!-- notes: Simplifier pour le public, Passer vite sur les formats de l'ingénierie de connaissance -->

<!-- Exemples : triplets RDF (sujet-predicat-objet), ontologies OWL, SPARQL -->

---

# Autres Applications (2/2)

- Systèmes à maintenance de vérité (TMS)
  - Révision des croyances
  - JTMS, ATMS: justice
  - Générateurs d'hypothèses
- Smart-contracts
  - Cryptographie
  - Blockchain
  - Non-divulgation

---
layout: image-right
image: ./images/img_050.png
---


<!-- notes: insister sur smart-contracts -->

<!-- Blockchain : registre distribue, consensus, execution automatique de contrats -->

---
layout: center
---

# Questions?

---

<!-- _class: section -->

# Intelligence probabiliste

- Quantification de l'incertitude
- Raisonnement probabiliste
- Prise de décision
- Théorie des jeux

---

<!-- _class: columns-layout -->

# Agir dans l'incertitude

<div class="columns">
<div class="col-left">

**Le monde est incertain**

- Entrées incertaines
  - Données manquantes,  bruitées
  - Connaissance incertaine
  - Causalités complexes
  - Environnement stochastique
- Sorties incertaines
  - Abduction, induction
  - Inférence incomplète

</div>
<div class="col-right">

**Agent fondé sur l'utilité**

- Raisonnement probabiliste
- Résultats probabilistes
- Alternatives
- Niveau de succès espéré

![w:350](images/img_051.png)

</div>
</div>

<!-- notes: Exemple Rainman -->

---

<!-- _class: columns-layout dense -->

# Probabilité

<div class="columns">
<div class="col-left">

**Fondements**

- Les probabilités resument notre incertitude (paresse, ignorance)
- Probabilites subjectives : degre de croyance d'un agent
- Se mettent a jour avec les observations

**Règle de Bayes**

- Diagnostic
- P(Cause | Effet) = P(Effet | Cause) x P(Cause) / P(Effet)

</div>
<div class="col-right">

**Programmation probabiliste**

- Réseau Bayésien naïf
  - Attributs indépendants
- Modèles graphiques
  - Indépendance conditionnelle
  - Facteurs de distributions continues

<div class="img-grid">
![w:180](images/img_052.png)
![w:180](images/img_053.png)
![w:180](images/img_054.png)
</div>

</div>
</div>

<!-- notes: Faire 1 slide avec le suivant (exemple météo, ne pas rentrer dans le détail Markov & co) -->

---

<!-- _class: columns-layout dense -->

# Réseaux bayésiens dynamiques

<div class="columns">
<div class="col-left">

**Chaînes de Markov**

- Indépendance conditionnelle
- Passé / Futur
- Modèle de transition
  - Probabiliste
  - **Distribution** stationnaire
- Chaînes de Markov cachées
  - Observations bruitées

<div class="img-grid">
![w:150](images/img_055.png)
![w:150](images/img_056.png)
![w:150](images/img_057.png)
</div>

</div>
<div class="col-right">

**Applications**

- Traitement du langage naturel
- Classification, Extraction
- Reconnaissance, Traduction
- Google 1.0: Page rank
- Suivi de trajectoire
- Météo, radars, économie etc.
- Filtres de Kalman
- Apprentissage

<div class="img-grid">
![w:150](images/img_058.png)
![w:150](images/img_059.png)
![w:150](images/img_060.jpg)
</div>

</div>
</div>

---

<!-- _class: columns-layout dense -->

# Prise de décision

<div class="columns">
<div class="col-left">

- Théorie de la décision
  - Que faire?
  - Théorie des probabilités
  - Que croire ?
  - Théorie de l'utilité
  - Que vouloir ?
- Utilité de l'argent
  - Goût du risque ?
  - Prime
  - Utilité espérée
  - biaisée (malédiction)
  - + Humains pas rationnel
- Prise de décision simple
  - Réseaux de décision
- Décision complexe
  - Processus de Markov
  - Politique optimale

</div>
<div class="col-right">

<div class="img-grid">

![w:150](images/img_061.png)
![w:150](images/img_062.png)
![w:150](images/img_063.png)
![w:150](images/img_064.png)
![w:150](images/img_065.jpg)
![w:150](images/img_066.jpg)

</div>

</div>
</div>

<!-- notes: Insister sur les exemples.Ordonnancement
Transitivité
Continuité
Substituabilité
Monotonie
Décomposabilité
Effet de certitude,
Régression fallacieuse,
évitement d'ambiguïté,
effet de cadrage
effet d'ancrage -->

---

<!-- _class: columns-layout -->

# Théorie des jeux (1/2)

<div class="columns">
<div class="col-left">

**Environnement multi-agents**

- Analyse stratégique
- Interdépendances stratégiques
- Design d'agent
  - Quelle stratégie?
- Design de mécanisme
  - Quelles règles?

</div>
<div class="col-right">

**Optimisation de stratégies**

- Solution = profil de stratégies
- Pures (déterministes)
- Mixtes (probabilistes)
- Utilité espérée

<div class="img-grid">
![w:180](images/img_067.png)
![w:180](images/img_068.png)
![w:180](images/img_069.png)
</div>

</div>
</div>

<!-- notes: Aller plus vite, se concentrer sur les exemples -->

---

<!-- _class: columns-layout -->

# Théorie des jeux (2/2)

<div class="columns">
<div class="col-left">

**Jeux simultanés**

- Matrice de gains
- Dominance
- Equilibres de Nash
- Purs et mixtes (2n+1)
- Topologie

![w:300](images/img_070.png)

</div>
<div class="col-right">

**Jeux séquentiels**

- Plusieurs manches
- Forme extensive
- Crédibilité
- Punitions, Menaces, Promesses
- Induction
  - avant/arrière

![w:300](images/img_071.jpg)

</div>
</div>

<!-- Forme extensive : arbre ou chaque noeud = decision, feuilles = gains -->

---

<!-- _class: columns-layout -->

# Extensions

<div class="columns">
<div class="col-left">

**Algorithmes**

- Espaces infinis
- Hotelling
- Jeux Bayésiens
  - Information incomplète
  - Jeux de signalisation
- Jeux différentiels

</div>
<div class="col-right">

**Equilibres approchés**

- ε-équilibres
- Minimisation de regret contrefactuel
- Cepheus
- Libratus
- Deepstack

<div class="img-grid">
![w:180](images/img_072.png)
![w:180](images/img_073.png)
![w:180](images/img_074.png)
</div>

</div>
</div>

<!-- notes: Faire 1 slide des 3 avec Exemple de Bayrou -->

---

<!-- _class: columns-layout -->

# Conception de mécanismes

<div class="columns">
<div class="col-left">

**Concepts**

- Théorie des jeux inverse
- Quelles bonnes règles ?
- Max d'une utilité globale?
- Principe de révélation
  - Mécanismes manipulables
  - Non-stratégiques

</div>
<div class="col-right">

**Résultats**

- Enchères de Vickrey
- Tragédie des communs
- Taxe carbone
- Conditions byzantines
- Bitcoin
- Stratégies sociétales
  - Évolution de la confiance

<div class="img-grid">
![w:180](images/img_075.png)
![w:180](images/img_076.png)
![w:180](images/img_077.jpg)
</div>

</div>
</div>

---

<!-- _class: columns-layout -->

# Décisions collectives

<div class="columns">
<div class="col-left">

**Théorie du choix social**

- Théorie de la négociation
- Théorie des votes
- Résultats négatifs
  - Critère de Condorcet
  - Electeur médian

</div>
<div class="col-right">

**Méthodes de Condorcet**

- Schulze
- Autres bon Scrutins
  - Vote par assentiment
  - Jugement majoritaire
  - Scrutin bipartipludique

![w:280](images/img_078.png)
![w:280](images/img_079.jpg)

</div>
</div>

---

<!-- _class: section -->

# Quiz

- Présidentielles: vainqueur de Condorcet
- Intelligences

---
layout: center
---

# Questions?

---

<!-- _class: section -->

# Apprentissage

- Apprentissage supervisé
- Arbres de décision
- Deep learning
- Modèles non-paramétriques
- Apprentissage et connaissances
- Apprentissage par renforcement

---

<!-- _class: columns-layout -->

# Apprentissage

<div class="columns">
<div class="col-left">

**Enjeux**

- Environnements inconnus
- Méthode de conception de systèmes
- Améliorer la prise de décision
- Les performances

</div>
<div class="col-right">

**Structure d'agent**

- Modules
  - Performance
  - Apprentissage
  - Critique
  - Générateur de problème

![w:350](images/img_080.png)

</div>
</div>

<!-- notes: En parler au début (chatpGPT & co), diminuer de moitié les slides -->

---

<!-- _class: columns-layout dense -->

# Caractéristiques (1/2)

<div class="columns">
<div class="col-left">

**Composants d'apprentissage**

- Type d'apprentissage
  - Inductif
  - Déductif
- Type de feedback:
  - Supervisé: les réponses correctes
  - Non-supervisé: clusters
  - Par renforcement: récompenses

</div>
<div class="col-right">

**Apprentissage inductif**

- Nature affectée par
  - Environnement / données
  - Connaissance a priori / modèles
  - Feedback pour apprendre

![w:280](images/img_081.png)
![w:280](images/img_082.png)

</div>
</div>

<!-- notes: Passer vite -->

---

<!-- _class: columns-layout -->

# Caractéristiques (2/2)

<div class="columns">
<div class="col-left">

- On construit une hypothèse
  - h consistante avec les données
- Ensemble de sortie
  - Classification
  - Régression
- Rasoir d'Occam
  - Parcimonie
- Entraînement
- Validation
- **Méthodes**
  - d'ensemble
  - Boosting

</div>
<div class="col-right">

![w:300](images/img_083.png)
![w:300](images/img_084.png)

</div>
</div>

---

<!-- _class: columns-layout -->

# Arbres de décision

<div class="columns">
<div class="col-left">

**Principe**

- Attributs  Décision
- A partir d'exemples

**Techniques**

- Ordre des attributs
- Gain entropique
- Compacité
- Elagage
- Régression
- Quantisation
- Random forest
- Ensemble

</div>
<div class="col-right">

<div class="img-grid-2x2">

![](images/img_085.png)
![](images/img_086.png)
![](images/img_087.png)
![](images/img_088.png)

</div>

</div>
</div>

---

# Classification

- Utilisation de dimensions supérieures
- Classification linéaire

---
layout: image-right
image: ./images/img_089.png
---


---

<!-- _class: columns-layout -->

# Réseaux de neurones artificiels

<div class="columns">
<div class="col-left">

- Inspiration biologique
- Neurone artificiel
  - Fonctions d'activation
- Multi-couches
  - Expressivité croissante

</div>
<div class="col-right">

<div class="img-grid-2x2">

![](images/img_090.png)
![](images/img_091.png)
![](images/img_092.png)
![](images/img_093.png)

</div>

</div>
</div>

---

<!-- _class: columns-layout -->

# Apprentissage profond

<div class="columns">
<div class="col-left">

- Réseaux profonds
  - Multicouche traditionnel classifier
- Hiérarchies naturelles
  - **Pixel, bord, teston, motif,**
    - partie, objet
  - **Caractère, mot, groupe,**
    - clause, phrase, histoire
- Réseaux convolués
  - Noyaux de convolution
  - Sous-échantillonnage

</div>
<div class="col-right">

<div class="img-grid-2x2">

![](images/img_094.png)
![](images/img_095.png)
![](images/img_096.png)
![](images/img_097.png)

</div>

</div>
</div>

---

<!-- _class: columns-layout -->

# Extensions 2010+

<div class="columns">
<div class="col-left">

- Réseaux récurrents
  - Mémoire à court terme
  - Réseaux LSTM
  - MAJ d'un état de cellule
- Réseaux résiduels
  - Réinjection des entrées
- GANs
  - Réseaux adversériaux

</div>
<div class="col-right">

<div class="img-grid">

![w:150](images/img_098.png)
![w:150](images/img_099.png)
![w:150](images/img_100.png)
![w:150](images/img_101.png)
![w:150](images/img_102.png)
![w:150](images/img_103.png)

</div>

</div>
</div>

<!-- GANs : generateur vs discriminateur, portraits StyleGAN, deepfakes -->

---

<!-- _class: columns-layout dense -->

# Extensions 2015+

<div class="columns">
<div class="col-left">

- Modèles Bayésiens
  - Régularisation
  - Ex: Auto-encodeurs Var.
- Graph Neural Networks
  - Généralisation géométrique
  - Agrégation de voisinage
- Réseaux attentionnels
  - Economie de ressources
  - Séquences
  - Transformers, Multi-têtes
- Semi-supervisé, Transfert
- LLMs : Bert, GPT

</div>
<div class="col-right">

<div class="img-grid">

![w:150](images/img_104.png)
![w:150](images/img_105.jpg)
![w:150](images/img_106.png)
![w:150](images/img_107.png)
![w:150](images/img_108.png)
![w:150](images/img_109.png)

</div>

</div>
</div>

<!-- Transformer : encodeur-decodeur, self-attention multi-tetes, positional encoding -->

---

<!-- _class: columns-layout -->

# Extensions 2020+

<div class="columns">
<div class="col-left">

**Modèles multimodaux**

- E.g Texte+Image
- Datasets, Encodeurs
- Rapprochement des plongements

**Modèles de diffusion**

- Prédiction d'un bruit
- Diffusion latente
- Autoencodeur Variationnel
- Conditionnement multimodal
- Mécanisme attentionnel

</div>
<div class="col-right">

<div class="img-grid-2x2">

![](images/img_110.png)
![](images/img_111.png)
![](images/img_112.png)
![](images/img_113.png)

</div>

</div>
</div>

<!-- Diffusion : bruit gaussien progressif → apprentissage du debruitage inverse -->

---

<!-- _class: columns-layout -->

# Apprentissage non paramétrique

<div class="columns">
<div class="col-left">

**Principes**

- Jusque là, paramétrique
- Arbres de décisions, NNs
- Ici, par les instances
- Les données servent à prédire

**Machines à vecteurs de support**

- K Plus proches voisins
- Noyaux de pondérations
- Séparateurs à marge maximale
- Astuce du noyau

</div>
<div class="col-right">

<div class="img-grid-2x2">

![](images/img_114.png)
![](images/img_115.png)
![](images/img_116.png)
![](images/img_117.png)

</div>

</div>
</div>

---

<!-- _class: columns-layout dense -->

# Apprentissage et connaissances

<div class="columns">
<div class="col-left">

- Utilisation de la connaissance
  - Passé + futur
  - Construction d'un énoncé en FOL
- Exploration: Version Space learning
- Apprentissage par explication
  - Ex: brochette
  - Explanation Based Learning
- Fondé sur la pertinence
  - Ex: langue du pays
  - Relevance Based learning
- Fondé sur des connaissances
  - Ex: Interne médical
  - Knowledge Based Inductive Learning
- Programmation logique inductive (Prolog)

</div>
<div class="col-right">

![w:350](images/img_118.png)
![w:350](images/img_119.png)

</div>
</div>

---

<!-- _class: columns-layout dense -->

# Apprentissage par renforcement

<div class="columns">
<div class="col-left">

- Pas d'exemple
  - Feedback = bon ou mauvais
- Processus de décision de Markov
  - Récompense à apprendre
  - Possibilité de Shaping
- 3 architectures
  - Basé sur l'utilité
  - Q-learning (utilité/action)
  - Agent réflex = apprentissage de politique
- 2 familles
  - Passif (politique fixée)
  - Actif  nécessité d'explorer
- Approximations
  - Modèles paramétriques
  - Deep Q-learning

</div>
<div class="col-right">

![w:350](images/img_120.png)
![w:350](images/img_121.png)

</div>
</div>

---
layout: center
---

# Questions?

---

<!-- _class: section -->

# Langage naturel (NLP)

- Modèle du langage
- Communication
- Agents conversationnels (chatbots)

---

<!-- _class: columns-layout dense -->

# Modèles du langage

<div class="columns">
<div class="col-left">

- N-grams
  - Modèles de Markov
  - Traitements
  - lissage, perplexité
- Utilisation
  - Classification, catégorisation
  - Langue, genre, spam
  - Analyse de sentiments
- Recherche d'information
  - Indexation
  - + traitement requêtes
  - + score  résultats

</div>
<div class="col-right">

- Extraction d'information
  - Automates à états finis:
  - Regexs, Transducteurs
  - Modèles probabilistes
  - Extraction d'ontologie
  - Machine reading

<div class="img-grid">
![w:180](images/img_122.png)
![w:180](images/img_123.png)
![w:180](images/img_124.png)
</div>

</div>
</div>

---

<!-- _class: columns-layout dense -->

# Grammaires

<div class="columns">
<div class="col-left">

**Caractéristiques**

- Communication
- Echange d'information
- Analyse du langage
  - Modèles de communication
  - = grammaires + sémantique
- Formalismes
  - Classes de Chomsky
  - Catégories = Part Of Speech

</div>
<div class="col-right">

**Grammaires probabilistes**

- Sans contexte (PCFGs)
- Syntaxique, Apprentissages
- Grammaires augmentées
  - Avec contexte, Sémantiques
- Interpréteurs
  - Modèles sémantiques
  - Ambiguités, Modèles imbriqués

<div class="img-grid">
![w:220](images/img_125.png)
![w:220](images/img_126.png)
</div>

</div>
</div>

---

<!-- _class: columns-layout -->

# Speech/Text to Text/Speech

<div class="columns">
<div class="col-left">

- Traduction automatisée
  - Modèles statistiques
- Reconnaissance de la parole
  - Modèles acoustiques + langage
- Modèles profonds
  - Réseaux récurrents / Transformers
  - Résumé, analyse syntaxique
  - Modèles sémantiques profonds

</div>
<div class="col-right">

<div class="img-grid-2x2">

![](images/img_127.png)
![](images/img_128.png)
![](images/img_129.png)
![](images/img_130.png)

</div>

</div>
</div>

---

<!-- _class: columns-layout dense -->

# Agents conversationnels

<div class="columns">
<div class="col-left">

- Agents algorithmiques couplé au NLP
  - Modèles de langage
  - Intentions = tâches
  - Entités = objets et propriétés
  - Instances = exemples
- Architecture
  - Connecteurs à des canaux
  - Contextes de dialogues
- Conception
  - Développement hors ligne
  - Actions, KBs
  - Modèles du langage
  - Bootstrap
  - Entraînement en ligne

</div>
<div class="col-right">

![w:280](images/img_131.png)
![w:250](images/img_132.png)
![w:250](images/img_133.png)

</div>
</div>

---

<!-- _class: columns-layout dense -->

# Applications des chatbots

<div class="columns">
<div class="col-left">

**Processus de création**

- Définition des objectifs
  - Fonctions, besoins etc.
- Définition du processus
  - Arborescence narrative
- Spécifications / Périmètre
- Identifier / rassembler les données
  - FAQ, DB, KB
- Budgétisation (10000 à 500K)
- Choix des canaux
  - Mobile, réseaux sociaux etc.
- Choix technologique
- Réalisation + entrainement
- Mise en production
- Amélioration

</div>
<div class="col-right">

**Exemples**

- Hôtels et transports : SNCF
- Achats en ligne : Amazon
- Télécoms : Verizon
- Finance : Orange
- Médias : CNN
- Ami virtuel : Replika
- Support juridique interne : ADP

</div>
</div>

<!-- Chatbots modernes : ChatGPT (OpenAI), Claude (Anthropic), Gemini (Google) -->

---

# Intelligence conversationnelle

- **Quiz** : quelles formes d'intelligence sont mobilisees par un chatbot ?
  - Exploratoire : navigation dans l'arbre de dialogue
  - Symbolique : comprehension des intentions, raisonnement logique
  - Probabiliste : modèles de langage, prediction du mot suivant
  - Apprentissage : entrainement sur des corpus massifs, fine-tuning RLHF
- L'agent conversationnel combine toutes les intelligences du cours

---
layout: center
---

# Questions?

---

# Pour aller plus loin : Notebooks

Ce deck couvre tous les domaines de l'IA. Pour approfondir avec des exemples pratiques :

> **GenAI - IA Generative**
> `MyIA.AI.Notebooks/GenAI/`
> Transformers, diffusion models, LLMs, génération d'images

> **Search - Recherche et Optimisation**
> `MyIA.AI.Notebooks/Search/`
> Algorithmes genetiques, A*, optimisation locale

> **ML - Machine Learning**
> `MyIA.AI.Notebooks/ML/`
> ML.NET, arbres de decision, classification, regression

> **SymbolicAI - IA Symbolique**
> `MyIA.AI.Notebooks/SymbolicAI/`
> RDF, Z3 SMT, Tweety, Lean, ontologies, web semantique

> **Probas - Modeles Probabilistes**
> `MyIA.AI.Notebooks/Probas/`
> Infer.NET, réseaux bayesiens, inference probabiliste

> **GameTheory - Théorie des Jeux**
> `MyIA.AI.Notebooks/GameTheory/`
> OpenSpiel, equilibres de Nash, jeux strategiques

---

# Merci

Jean-Sylvain Boige
jsboige@myia.org
