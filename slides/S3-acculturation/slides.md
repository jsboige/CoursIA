---
theme: ../theme-ia101
title: "Intelligence Artificielle - Acculturation"
info: IA 101 - Panorama complet de l'intelligence artificielle
paginate: true
drawings:
  persist: false
transition: slide-left
mdc: true
layout: cover
---


<div class="h-full flex flex-col items-center justify-center text-center">

  <h1 class="text-7xl font-serif text-rose-800 leading-tight">Intelligence(s)</h1>

  <div class="w-32 h-px bg-rose-800/40 my-8"></div>

  <div class="text-xl tracking-widest uppercase text-slate-500">Une introduction à l'IA pour décideurs</div>

  <div class="mt-16 text-lg tracking-wide">Jean-Sylvain Boige</div>
  <div class="text-sm text-slate-500 mt-1">jsboige@myia.org — Telecom Bretagne — Cogs Brighton UK</div>

  <div class="mt-16 flex justify-center gap-16 items-center">
    <img src="./images/img_003.png" class="h-12" alt="DNN" />
    <img src="./images/img_001.png" class="h-14" alt="myIA" />
    <img src="./images/img_002.png" class="h-10" alt="Cogs" />
  </div>

</div>


---


# Sommaire

<div class="grid grid-cols-[1fr_230px_1fr] gap-6 mt-4 items-center">
<div>

**Qu'est-ce que l'intelligence artificielle ?**<br>
<span class="text-sm text-slate-500">Racines, histoire et état de l'art — structure des agents rationnels</span>

**Intelligence exploratoire**<br>
<span class="text-sm text-slate-500">Comment chercher la solution à un problème ?</span>

**Intelligence symbolique**<br>
<span class="text-sm text-slate-500">Comment utiliser le raisonnement et les mathématiques ?</span>

</div>
<div class="flex items-center justify-center">
  <img src="./images/img_004.png" class="rounded shadow-lg w-full max-h-[390px] object-contain" alt="Couverture AIMA Russell & Norvig" />
</div>
<div>

**Intelligence probabiliste**<br>
<span class="text-sm text-slate-500">Comment agir dans l'incertitude ?</span>

**Apprentissage**<br>
<span class="text-sm text-slate-500">Comment utiliser les données et l'expérience ?</span>

**Application : le langage naturel**<br>
<span class="text-sm text-slate-500">Chatbots, LLM, IA générative et agents</span>

</div>
</div>



---
layout: section
---



# Intelligence artificielle

- Introduction
- Agents rationnels
- Intelligences


---



# Qu'est-ce que l'intelligence artificielle?


- Définitions multiples
- Notre angle :
  - « Agir de façon rationnelle »
- Conception d'agents

**Fondements**

- Philosophie
- Maths
- Économie
- Biologie
- Neurosciences
- Psychologie
- Informatique
- Théorie du contrôle
- Linguistique

<img src="./images/img_005.png" class="absolute top-[110px] right-[20px] w-[460px]" alt="Neurone biologique : dendrites, soma, axone, synapse — l'inspiration des réseaux de neurones artificiels" />
---

# Développement (1/2)

<div class="grid grid-cols-[38%_62%] gap-6">
<div>

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

</div>
<div class="flex flex-col items-center justify-center gap-5">
  <img src="./images/img_006.png" class="w-full max-h-[210px] object-contain" alt="Repères historiques" />
  <div class="flex w-full gap-8 items-center justify-center">
    <img src="./images/img_007.jpg" class="h-16 max-w-[35%] object-contain" alt="Logo DARPA" />
    <img src="./images/img_008.jpg" class="h-12 max-w-[55%] object-contain" alt="Logo ImageNet" />
  </div>
</div>
</div>

> **État de l'art** : voir la slide « Développement (2/2) » pour la chronologie moderne (1997 → 2025).

---


# Développement (2/2)

- **2000s** : Data mining, apprentissage bayésien, web sémantique, prouveurs automatiques
- **2010s** : Explosion du deep learning et du big data
  - 2014 : GANs (génération d'images), 2016 : AlphaGo (Go)
  - 2017 : Transformers ("Attention is All You Need")
  - 2018 : AlphaZero (échecs, Go, shogi sans connaissances humaines)
  - 2019 : Pluribus (poker), AlphaStar (Starcraft 2)
- **2020s** : LLMs et IA générative deviennent grand public
  - GPT-3 (2020), ChatGPT (2022), GPT-4 (2023), Claude 3 (2024), GPT-4o (2024), Claude 3.5 Sonnet (2024), Gemini 1.5/2 (2024-2025)
  - Stable Diffusion, Midjourney, DALL-E : génération d'images
  - 2025 : agents IA autonomes, vibe coding, IA multimodale

> **Chronologie cle** : Turing (1950) → Dartmouth (1956) → Hiver IA (1974) → Deep Blue (1997) → AlphaGo (2016) → ChatGPT (2022) → Agents IA (2025)


---


# Dans la vie de tous les jours

<div class="grid grid-cols-[64%_36%] gap-6 items-center">
<div>

- **Poste** : reconnaissance des adresses et tri automatique du courrier
- **Banque** : lecture des chèques, vérification des signatures, évaluation de crédits
- **Médecine** : diagnostic assiste, prescriptions, suivi et prévention
- **Service client** : synthèse/reconnaissance vocale, chatbots (ChatGPT, Claude)
- **Transport** : détection de plaques, conduite autonome (Tesla, Waymo)
- **Internet** : marketing personnalise, détection de spam et de fraude
- **Industrie** : conception, fabrication et exploitation assistées par IA
- **Image numérique** : détection de visages, mise au point, compression
- **Jeux** : personnages et adversaires intelligents (NPCs adaptatifs)

</div>
<div class="flex items-center justify-center">
  <img src="./images/img_013.jpg" class="w-full max-h-[360px] object-contain rounded-lg shadow-lg" alt="Écosystème IoT — objets du quotidien connectés" />
</div>
</div>


---



# Les agents


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

<img src="./images/img_009.png" class="absolute top-[110px] right-[20px] w-[460px]" alt="Les agents" />
---

# Conception d'agents


**Environnement de tache**

- Description PEAS : Performance, Environnement, Actionneurs, Senseurs

**Agent réflexe**

- Pas de mémoire, réagit aux percepts courants
- Regles condition → action (si obstacle, alors freiner)

<img src="./images/img_010.png" class="w-[260px] max-w-full max-h-[220px] object-contain" alt="Tableau PEAS : cinq types d'agents avec mesure de performance, environnement, effecteurs, capteurs" />

<img src="./images/img_011.png" class="absolute top-[290px] right-[20px] w-[360px] max-w-full max-h-[240px] object-contain" alt="Agent réflexe" />




---
layout: section
---



# Quiz

- Taxi autonome:
  - Description Peas
  - Intelligences


---



# Agent réflexe fondé sur un modèle


**Agent réflexe avec modèle**

- Fonctionnement interne
- État du monde
- Niveau de représentation

**Compromis**

- Flexibilité vs complexité

<img src="./images/img_012.png" class="absolute top-[110px] right-[20px] w-[460px]" alt="Agent réflexe fondé sur un modèle" />
---


# Intelligences

- **Procédurale** : automates et algorithmes déterministes (instructions pas à pas)
- **Exploratoire** : recherche dans un espace d'états (parcours de graphes, A*)
- **Symbolique** : raisonnement logique, bases de connaissances, planification
- **Probabiliste** : gestion de l'incertitude, réseaux bayésiens, décision
- **Apprentissage** : amélioration par l'expérience (supervisé, renforcement, deep learning)

<div class="flex justify-center items-center gap-12 mt-8">
  <img src="./images/img_015.jpg" class="h-[190px] max-w-[42%] object-contain" alt="Recherche de chemin dans un réseau : intelligence exploratoire" />
  <img src="./images/img_014.png" class="h-[190px] max-w-[42%] object-contain" alt="Processus de décision markovien : intelligence probabiliste" />
</div>


---


# Décider seul, décider face à quelqu'un

<div class="grid grid-cols-2 gap-8 mt-3">

<div>

### Théorie de la **décision**

L'incertitude vient de la **nature**. Elle ne vous veut rien.

- On maximise une **utilité espérée**
- L'objet cherché est un **optimum**
- Outils : probabilités, utilité, arbres de décision, processus markoviens
- Chez vous : prime pure, chargement de sécurité, aversion au risque

</div>

<div>

### Théorie des **jeux**

L'incertitude vient d'un **autre décideur**, qui optimise aussi — parfois contre vous.

- On cherche un **équilibre**, pas un optimum
- L'objet cherché est l'**équilibre de Nash**
- Outils : matrices de gains, minimax, information asymétrique, conception de mécanismes
- Chez vous : antisélection, aléa moral, signal, dépistage

</div>

</div>

<div class="mt-8 text-slate-600 border-l-2 border-rose-800/40 pl-5 leading-relaxed">

**Le même livre fonde les deux** — von Neumann &amp; Morgenstern, 1944. La théorie des jeux *dérive* de la décision, mais elle en change l'objet : dès que l'autre choisit aussi, l'optimum s'évanouit et seul l'équilibre subsiste.

</div>


---


# Ce que la théorie des jeux ajoute — et ce qu'elle a donné à l'IA

<div class="grid grid-cols-[1.05fr_1fr] gap-7 mt-2">

<div>

### Des objets que la décision seule ne produit pas

- **Antisélection** — celui qui se sait mauvais risque s'assure en premier *(Akerlof, 1970)*
- **Aléa moral** — être couvert change le comportement de l'assuré
- **Signal et dépistage** — le contrat est construit pour *faire révéler* l'information cachée *(Spence 1973 ; Rothschild &amp; Stiglitz 1976, sur le marché de l'assurance)*
- **Jeux bayésiens** — décider quand on ignore le type de l'autre *(Harsanyi)*

</div>

<div>

### En intelligence artificielle

- **Minimax et élagage alpha-bêta** : le socle des programmes de jeu depuis les années 1950
- **Jeu contre soi-même** : le programme s'entraîne sans professeur en s'affrontant *(AlphaGo, AlphaZero)*
- **Apprentissage par renforcement multi-agent** : plusieurs agents apprennent en s'influençant
- **Enchères et conception de mécanismes** : ce qui régit la publicité en ligne

</div>

</div>

<div class="mt-8 text-slate-600 border-l-2 border-rose-800/40 pl-5 leading-relaxed">

**Vos contrats sont déjà des mécanismes de jeu.** Franchise, bonus-malus, coassurance ne sont pas des paramètres tarifaires : ce sont des dispositifs d'incitation. La théorie des jeux est la discipline qui les conçoit.

</div>


---
layout: section
---



# Questions?

---
layout: section
---



# Intelligence exploratoire

- Recherches non informée et informée
- Jeux
- Problèmes à satisfaction de contraintes


---


# Agent explorateur

<div class="grid grid-cols-2 gap-8 items-start">
<div>

**Agent fonde sur des buts**

- Passe du réactif au délibératif
- Planifie ses actions par exploration

<img src="./images/img_016.png" class="w-full max-h-[220px] object-contain" alt="Carte de la Roumanie : Arad, Sibiu, Bucharest et distances routières (exemple canonique AIMA)" />

</div>
<div>

**Résolution de problèmes**

- Objectif ?
- Actions ?
- Représentation ?

<img src="./images/img_017.png" class="w-full max-h-[220px] object-contain" alt="Résolution de problèmes" />

</div>
</div>

---


# Formulation de problèmes

<div class="grid grid-cols-[40%_60%] gap-6">
<div>

**Itinéraire**

- État initial, test de but
- Transitions
- États, Actions
- Coût de chemin
- Solution = Séquence

<img src="./images/img_018.png" class="w-full max-h-[190px] object-contain" alt="Plateau de dames avec six pions noirs disposés sur l'échiquier" />

</div>
<div>

**Abstractions**

- Assemblage robotique
- Problèmes jouets

<img src="./images/img_robot_extracted.png" class="w-full max-h-[135px] object-contain" alt="Bras robotique articulé — assemblage robotique" />
<div class="grid grid-cols-2 gap-4 mt-2">
  <img src="./images/img_019.png" class="w-full max-h-[115px] object-contain" alt="8-puzzle (état initial mélangé)" />
  <img src="./images/img_021.png" class="w-full max-h-[115px] object-contain" alt="Missionnaires et cannibales" />
</div>

</div>
</div>



---

# Arbre d'exploration

<div class="grid grid-cols-2 gap-0 -mt-4 -mb-2">
<div class="bg-orange-700 text-white px-4 py-2 text-base font-bold text-center">Idée de base</div>
<div class="bg-slate-800 text-white px-4 py-2 text-base font-bold text-center">Exemple : Énigme</div>
</div>

- Développement des états successeur
- **Choix des nœuds**
  - = Stratégie d'exploration

<img src="./images/img_020.png" class="w-[420px] max-w-full max-h-[280px] object-contain" alt="Arbre d'exploration Arad → Bucharest (Roumanie, AIMA) — exemple canonique de recherche dans un graphe d'états" />


**Exemple: Énigme**

- Missionnaires et cannibales
  - Barque de 2 places
  - Jamais + de cannibales

<img src="./images/img_023.png" class="absolute top-[110px] right-[20px] w-[280px] max-h-[200px] object-contain" alt="Graphe d'états avec frontière de recherche en pointillés rouges et valeurs d'évaluation 380-420" />
<img src="./images/img_024.png" class="absolute top-[300px] right-[20px] w-[460px] max-h-[100px] object-contain" alt="Séquence d'arbres binaires A-G avec curseur sur le nœud en cours d'exploration" />



---
layout: section
---



# Quiz

- Missionnaires et cannibales
- Intelligences


---
layout: default
---



# Stratégies d'exploration (1/2)

<div class="grid grid-cols-2 gap-0 -mt-4">
<div class="bg-orange-700 text-white px-6 py-3 text-xl font-bold text-center">Non informées</div>
<div class="bg-slate-800 text-white px-6 py-3 text-xl font-bold text-center">Informées</div>
</div>

<div class="grid grid-cols-2 gap-8 mt-6">

<div>

- En largeur
- En profondeur
- Bidirectionnelle
- Ex: Où sont mes clefs ?

</div>

<div>

- Évaluation des états
  - **Heuristique**
  - Estimation du coût restant
  - Ex: Distance à vol d'oiseau
- Par le meilleur d'abord
  - Exploration gloutonne
  - Algorithme A*
  - [Demo Pathfinding.js](https://qiao.github.io/PathFinding.js/visual/)

</div>

</div>

<div class="grid grid-cols-2 gap-8 mt-4 items-center">
  <img src="./images/img_025.png" class="w-full max-h-[145px] object-contain" alt="Arbres binaires illustrant la recherche en profondeur, nœuds visités en gris foncé" />
  <img src="./images/img_026.png" class="w-full max-h-[145px] object-contain" alt="Arbre de recherche dense étalé en motif radial, avec nœuds Départ et But" />
</div>


---


# Stratégies d'exploration (2/2)


- Si seule la solution compte
  - pas le chemin
  - Modification d'un seul état
- Paysage de l'espace des états
  - Optimisation d'une fonction
  - Escalade, descente de gradient


- Problèmes :
  - Bloqué sur un optimum local
- Solutions:
  - Recuit simulé
  - Ex: le carton de babioles
  - Exploration en faisceaux
  - Ex: Perdus en foret
  - Sélection naturelle = combinaison
  - Algorithmes génétiques

<div class="absolute top-[130px] right-[20px] w-[560px] flex flex-col gap-2">
<div class="flex gap-2">
<img src="./images/img_027.png" class="w-[275px] max-h-[120px] max-w-full object-contain" alt="Cycle d'un algorithme génétique : initial population → fitness → sélection → croisement → mutation" />
<img src="./images/img_028.png" class="w-[275px] max-h-[120px] max-w-full object-contain" alt="Croisement sur le problème des huit reines : deux échiquiers parents combinés par addition et permutation" />
</div>
<div class="img-grid-2x2">
<img src="./images/img_030.png" class="max-h-[140px] max-w-full object-contain" alt="Paysage d'optimisation avec trajectoire de descente" />
<img src="./images/img_031.png" class="max-h-[140px] max-w-full object-contain" />
<img src="./images/img_032.png" class="max-h-[140px] max-w-full object-contain" alt="Représentations d'états : atomique, factorisée, structurée" />
<img src="./images/img_033.png" class="max-h-[140px] max-w-full object-contain" alt="Niveaux d'abstraction imbriqués d'un espace d'états" />
</div>
</div>




---

# Jeux

<div class="grid grid-cols-2 gap-0 -mt-4 -mb-2">
<div class="bg-orange-700 text-white px-4 py-2 text-base font-bold text-center">Jeux vs Exploration</div>
<div class="bg-slate-800 text-white px-4 py-2 text-base font-bold text-center">Arbre Minimax</div>
</div>


<div class="grid grid-cols-[60%_40%] gap-6 items-center">
<div class="dense-list">

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

**Techniques**

- Actions joueurs Max et Min + utilité terminale
- Minimax, Alpha-Beta
- Avec arrêt + évaluation heuristique
- Techniques probabilistes (Expectiminimax, Monte-Carlo)

</div>
<div class="flex items-center justify-center">
  <img src="./images/img_031.png" class="w-full max-h-[340px] object-contain" alt="Arbre minimax du morpion : niveaux MAX(X) et MIN(O), utilités -1/0/+1" />
</div>
</div>



---
layout: default
---



# Problèmes à satisfaction de contraintes

<div class="grid grid-cols-2 gap-0 -mt-4 -mb-2">
<div class="bg-orange-700 text-white px-4 py-2 text-base font-bold text-center">Définition CSPs</div>
<div class="bg-slate-800 text-white px-4 py-2 text-base font-bold text-center">Techniques</div>
</div>


<div class="grid grid-cols-2 gap-8">

<div>

- Jusqu'ici: représentation atomique
- CSP = État factorisé
- État = variables sur des domaines
- Test de but = contraintes sur les variables
- Bonnes méthodes générales
- Meilleures que l'exploration standard
- Exemple
  - Coloration de carte

</div>

<div>

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

<div class="flex gap-2">
<img src="./images/img_035.png" class="w-[120px] max-w-full max-h-[140px] object-contain" alt="Schéma de sémantique : énoncés reliés par « a pour conséquence » et « causent » aux aspects du monde réel" />
<img src="./images/img_036.png" class="w-[120px] max-w-full max-h-[140px] object-contain" alt="Illustration Winograd : ordinateur échangeant phrases et conclusions avec un humain et un robot" />
<img src="./images/img_037.png" class="w-[120px] max-w-full max-h-[140px] object-contain" alt="Grammaire de la logique propositionnelle : Énoncé, ÉnoncéAtomique, priorité des opérateurs ¬, ∧, ∨, ⇒, ⇔" />

</div>

</div>

</div>



---
layout: section
---



# Questions?

---
layout: section
---



# Intelligence symbolique

- Logique propositionnelle
- Logique du premier ordre
- Agents fondés sur la connaissance
- Planification



---
layout: default
---



# Représentation et logique


<div class="grid grid-cols-2 gap-8">

<div>

**Enoncés**

- Langage
- Syntaxe
- Sémantique
- Types de logiques

**Inférence**

- Propriétés
- correction, consistance, complétude

</div>

<div>

**Bases de connaissances**

**Raisonnement**

<img src="./images/img_035.png" class="w-[300px] max-w-full max-h-[300px] object-contain" alt="Schéma de sémantique : énoncés reliés par « a pour conséquence » et « causent » aux aspects du monde réel" />
<img src="./images/img_036.png" class="w-[300px] max-w-full max-h-[300px] object-contain" alt="Illustration Winograd : ordinateur échangeant phrases et conclusions avec un humain et un robot" />

</div>

</div>



---



# Logique propositionnelle


- Syntaxe
- Sémantique
  - Tables de vérité
- Inférence logique
  - Règles cohérentes
  - Ex: Modus ponens
  - Preuve déductive
- Procédures
  - Chaînages
  - Résolution
  - DPLL, WalkSAT
- Solveurs SAT
  - Problèmes NP-complets

<div class="grid grid-cols-2 gap-2 absolute top-[130px] right-[20px] w-[600px]">
<img src="./images/img_038.png" class="max-h-[190px] w-full object-contain" alt="Table de vérité en français des connecteurs logiques P, Q (négation, conjonction, disjonction, implication)" />
<img src="./images/img_039.png" class="max-h-[190px] w-full object-contain" alt="Diagrammes de Venn des connecteurs logiques : (P ∨ Q), (P ∧ Q), (P ⇒ Q), (P ⇔ Q)" />
<img src="./images/img_040.png" class="max-h-[190px] w-full object-contain" alt="Réseau sémantique : Mammals, Persons, Mary, John reliés par liens d'héritage et propriétés" />
</div>
---



# Logique du premier ordre (FOL)


<div class="grid grid-cols-2 gap-5 -mt-2">
<div>

- Modélise
  - Objets, Propriétés
  - Relations, Fonctions
- Quantificateurs:
  - Il existe x - x
  - Pour chaque x - x
- Sémantiques multiples
  - de base de données


</div>
<div>

**Exemple: investigation**

- Missile(x) ET Possède(Corée, x) => Vend(West, x ,Corée)
- Missile(x) => Arme(x)
- Enemy(x,America) => Hostile(x)
- Américain(x) ET Arme(y) ET Vend(x,y,z) ET Hostile(z) => Criminel(x)

<img src="./images/img_040.png" class="w-[300px] max-w-full max-h-[300px] object-contain" alt="Réseau sémantique : Mammals, Persons, Mary, John reliés par liens d'héritage et propriétés" />

</div>
</div>
---



# Application: argumentation

<div class="grid grid-cols-2 gap-0 -mt-4 -mb-2">
<div class="bg-orange-700 text-white px-4 py-2 text-base font-bold text-center">Code de conduite</div>
<div class="bg-slate-800 text-white px-4 py-2 text-base font-bold text-center">Qu'est-ce qu'un argument ?</div>
</div>

<div class="grid grid-cols-2 gap-5 -mt-2">
<div>

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
<div>

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



# Analyse rhétorique

<div class="grid grid-cols-2 gap-5 -mt-2">
<div>

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
<div>

**Un argument fallacieux**

- Viole l'un des critères
- Taxonomie
- Comment le dénoncer
  - Reconstruction standard
  - Contre-exemple absurde
  - Fair-play

<div class="img-grid">
<img src="./images/img_041.jpg" class="w-[220px] max-w-full max-h-[300px] object-contain" alt="Cartes à jouer disposées en spirale arc-en-ciel sur une table en bois" />

</div>

</div>
</div>
---



# Application: Planification

<div class="grid grid-cols-2 gap-0 -mt-4 -mb-2">
<div class="bg-orange-700 text-white px-4 py-2 text-base font-bold text-center">Expression de problème</div>
<div class="bg-slate-800 text-white px-4 py-2 text-base font-bold text-center">Approches</div>
</div>


- Langage formel
- But à atteindre
- Listes des opérations

- Exploration des états, plans
- Heuristiques ?
- Calcul situationnel
- Théorèmes en FOL
- Planification par contraintes
- Planification à Ordre partiel
- Décomposition hiérarchique

<div class="grid grid-cols-2 gap-2 absolute top-[130px] right-[20px] w-[600px]">
<img src="./images/img_043.png" class="max-h-[190px] w-full object-contain" alt="Graphe de planification : Start, Go(HWS), Go(SM), Buy(Drill/Milk/Bananas), Finish avec états At/Have" />
<img src="./images/img_044.png" class="max-h-[190px] w-full object-contain" alt="Décomposition HTN « Build House » : Obtain Permit, Construction et sous-tâches" />
<img src="./images/img_045.png" class="max-h-[190px] w-full object-contain" alt="Plan de transport aérien en logique : Init, Goal, actions Load/Unload/Fly avec préconditions et effets" />
<img src="./images/img_046.png" class="max-h-[190px] w-full object-contain" alt="Plan d'actions logiques : Load(C1,P1,SFO), Fly(P1,SFO,JFK), Unload (transport aérien)" />
</div>
---



# Autres Applications (1/2)


- Solveurs Modulo Théorie
  - SAT + Quantificateurs
  - + Théories arithmétiques
  - + Optimiseurs
- Ingénierie de connaissances
  - Triplets, Ontologies
  - Web sémantique
  - W3C
  - Linked Data

<div class="img-stack absolute top-[110px] right-[20px] w-[460px]">
<img src="./images/img_048.png" class="w-full object-contain" alt="Cartographie des médias et réseaux sociaux : TV, presse, blogs, forums, podcasts, partage vidéo et photo" />
<img src="./images/img_049.png" class="w-full object-contain" alt="Architecture du web sémantique : Trust, Proof, Logic, Ontology, RDF, XML, URI, Unicode" />
</div>

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

<!-- Image: images/img_050.png -->


<!-- Blockchain : registre distribué, consensus, exécution automatique de contrats -->


---
layout: section
---



# Questions?

---
layout: section
---



# Intelligence probabiliste

- Quantification de l'incertitude
- Raisonnement probabiliste
- Prise de décision
- Théorie des jeux


---



# Agir dans l'incertitude


<div class="grid grid-cols-2 gap-5 -mt-2">
<div>

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
<div>

**Agent fondé sur l'utilité**

- Raisonnement probabiliste
- Résultats probabilistes
- Alternatives
- Niveau de succès espéré

<img src="./images/img_051.png" class="w-[350px] max-w-full max-h-[300px] object-contain" alt="Nuage de points en croix sur un repère f(x) en fonction de x (données à ajuster)" />

</div>
</div>


---



# Probabilité


<div class="grid grid-cols-2 gap-5 -mt-2">
<div>

**Fondements**

- Les probabilités résument notre incertitude (paresse, ignorance)
- Probabilités subjectives : degré de croyance d'un agent
- Se mettent a jour avec les observations

**Règle de Bayes**

- Diagnostic
- P(Cause | Effet) = P(Effet | Cause) x P(Cause) / P(Effet)


</div>
<div>

**Programmation probabiliste**

- Réseau Bayésien naïf
  - Attributs indépendants
- Modèles graphiques
  - Indépendance conditionnelle
  - Facteurs de distributions continues

<div class="img-grid">
<img src="./images/img_052.png" class="w-[180px] max-w-full max-h-[300px] object-contain" alt="Ajustement d'un nuage de points par une courbe bleue oscillante, une droite rouge et un segment vert" />
<img src="./images/img_053.png" class="w-[180px] max-w-full max-h-[300px] object-contain" alt="Surapprentissage : courbe orange très oscillante collée aux points, contre droite et segment de régression" />
<img src="./images/img_054.png" class="w-[180px] max-w-full max-h-[300px] object-contain" alt="Courbe gaussienne centrée en 0, largeur σ (distribution normale)" />

</div>
</div>
</div>

---



# Réseaux bayésiens dynamiques

<div class="grid grid-cols-2 gap-5 -mt-2">
<div>

**Chaînes de Markov**

- Indépendance conditionnelle
- Passé / Futur
- Modèle de transition
  - Probabiliste
  - **Distribution** stationnaire
- Chaînes de Markov cachées
  - Observations bruitées

<div class="img-grid">
<img src="./images/img_055.png" class="w-[150px] max-w-full max-h-[300px] object-contain" alt="Chaîne de Markov cachée : états X₁ à Xₙ, observations E₁ à Eₙ" />
<img src="./images/img_056.png" class="w-[150px] max-w-full max-h-[300px] object-contain" alt="Fourmis stylisées avec symboles x1 à x4 et ondes bleues et rouges (illustration intelligence en essaim)" />
<img src="./images/img_057.png" class="w-[150px] max-w-full max-h-[300px] object-contain" alt="Réseau bayésien météo : soleil, nuages, pluie reliés par probabilités conditionnelles" />
</div>

</div>
<div>

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
<img src="./images/img_058.png" class="w-[150px] max-w-full max-h-[300px] object-contain" alt="Modèle à états cachés temporel : états X_t et observations Z_t au fil du temps" />
<img src="./images/img_059.png" class="w-[150px] max-w-full max-h-[300px] object-contain" alt="Graphe orienté : nœuds bleus reliés par flèches pleines et pointillées" />

</div>

</div>
</div>
---



# Prise de décision

<div class="dense-list">

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

<div class="grid grid-cols-2 gap-2 absolute top-[130px] right-[20px] w-[600px]">
<img src="./images/img_061.png" class="max-h-[190px] w-full object-contain" alt="Courbe d'utilité concave : utilité U en fonction du montant en dollars" />
<img src="./images/img_062.png" class="max-h-[190px] w-full object-contain" alt="Diagramme d'influence : décision AirportSite, conséquences Deaths/Noise/Cost, utilité U" />
<img src="./images/img_063.png" class="max-h-[190px] w-full object-contain" alt="Processus de décision markovien : états S0-S2, actions a0-a1, récompenses +5/-1, probabilités de transition" />
<img src="./images/img_064.png" class="max-h-[190px] w-full object-contain" alt="Grille 3x3 de navigation avec flèches de politique, cases +1/-1, piège, et inégalité sur R(s)" />
</div>
---



# Théorie des jeux (1/2)

<div class="grid grid-cols-2 gap-5 -mt-4">
<div>
<div class="bg-orange-700 text-white px-4 py-2 text-base font-bold text-center mb-2">Environnement multi-agents</div>

- Analyse stratégique
- Interdépendances stratégiques
- Design d'agent
  - Quelle stratégie?
- Design de mécanisme
  - Quelles règles?

</div>
<div>
<div class="bg-slate-800 text-white px-4 py-2 text-base font-bold text-center mb-2">Optimisation de stratégies</div>

- Solution = profil de stratégies
- Pures (déterministes)
- Mixtes (probabilistes)
- Utilité espérée

<div class="img-grid mt-2 grid grid-cols-3 gap-2">
<img src="./images/img_067.png" class="w-full max-h-[260px] object-contain" alt="Matrice du dilemme du prisonnier : se taire/avouer, peines de (-1,-1) à (-8,-8)" />
<img src="./images/img_068.png" class="w-full max-h-[260px] object-contain" alt="Arbre de jeu Stackelberg : Burn/Not Burn, Invade/Concede, Fight/Retreat avec utilités" />
<img src="./images/img_069.png" class="w-full max-h-[260px] object-contain" alt="Arbre de jeu de poker en trois rues : Pre-flop, Flop, Turn avec Fold/Call/Check/Raise" />
</div>

</div>
</div>
---



# Théorie des jeux (2/2)

<div class="grid grid-cols-2 gap-8 -mt-4">
<div>
<div class="bg-orange-700 text-white px-4 py-2 text-base font-bold text-center mb-2">Jeux simultanés</div>

- Matrice de gains
- Dominance
- Équilibres de Nash
- Purs et mixtes (2n+1)
- Topologie

</div>
<div>
<div class="bg-slate-800 text-white px-4 py-2 text-base font-bold text-center mb-2">Jeux séquentiels</div>

- Plusieurs manches
- Forme extensive
- Crédibilité
- Punitions, Menaces, Promesses
- Induction
  - avant/arrière

<!-- Forme extensive : arbre ou chaque noeud = décision, feuilles = gains -->

</div>
</div>

<div class="flex justify-center mt-4">
  <img src="./images/img_070.png" class="w-[420px] max-h-[230px] object-contain" alt="Matrice de gains du jeu Ballet/Fight : préférences croisées des deux joueurs, valeurs (2,1) et (1,2)" />
</div>
---



# Extensions



<div class="grid grid-cols-2 gap-5 -mt-2">
<div>

**Algorithmes**

- Espaces infinis
- Hotelling
- Jeux Bayésiens
  - Information incomplète
  - Jeux de signalisation
- Jeux différentiels


</div>
<div>


**Équilibres approchés**

- ε-équilibres
- Minimisation de regret contrefactuel
- Cepheus
- Libratus
- Deepstack

<div class="img-grid">
<img src="./images/img_072.png" class="w-[180px] max-w-full max-h-[300px] object-contain" alt="Composition abstraite : panneau jaune, point rouge et point bleu, bandes verticales" />
<img src="./images/img_073.png" class="w-[180px] max-w-full max-h-[300px] object-contain" alt="Surface 3D incurvée en selle, rendu bleu translucide sans texte" />
<img src="./images/img_074.png" class="w-[180px] max-w-full max-h-[300px] object-contain" alt="Surface 3D incurvée f(x,y) dans une boîte avec un point rouge marqué" />

</div>



</div>
</div>
---



# Conception de mécanismes

<div class="grid grid-cols-2 gap-5 -mt-4">
<div>
<div class="bg-orange-700 text-white px-4 py-2 text-base font-bold text-center mb-2">Concepts</div>

- Théorie des jeux inverse
- Quelles bonnes règles ?
- Max d'une utilité globale?
- Principe de révélation
  - Mécanismes manipulables
  - Non-stratégiques

</div>
<div>
<div class="bg-slate-800 text-white px-4 py-2 text-base font-bold text-center mb-2">Résultats</div>

- Enchères de Vickrey
- Tragédie des communs
- Taxe carbone
- Conditions byzantines
- Bitcoin
- Stratégies sociétales
  - Évolution de la confiance

<div class="img-grid mt-2 flex flex-col gap-2 items-center">
<img src="./images/img_075.png" class="max-h-[120px] max-w-[300px] object-contain" alt="Mécanismes institutionnels : acteurs, messages, mécanisme (engrenages), résultat" />
<img src="./images/img_076.png" class="max-h-[120px] max-w-[300px] object-contain" alt="Jeu itératif du prisonnier avec roue de stratégies : Copycat, Cheater, Cooperator, Grudger, Detective..." />
</div>

</div>
</div>
---



# Décisions collectives



<div class="grid grid-cols-2 gap-5 -mt-2">
<div>

**Théorie du choix social**

- Théorie de la négociation
- Théorie des votes
- Résultats négatifs
  - Critère de Condorcet
  - Électeur médian


</div>
<div>


**Méthodes de Condorcet**

- Schulze
- Autres bon Scrutins
  - Vote par assentiment
  - Jugement majoritaire
  - Scrutin bipartipludique

<img src="./images/img_078.png" class="w-[280px] max-w-full max-h-[300px] object-contain" alt="Zone d'accord de négociation salariale : salages rejetés par chacun, fourchette 0 à 50 dollars" />



</div>
</div>
---
layout: section
---



# Quiz

- Présidentielles: vainqueur de Condorcet
- Intelligences


---
layout: section
---



# Questions?

---
layout: section
---



# Apprentissage

- Apprentissage supervisé
- Arbres de décision
- Deep learning
- Modèles non-paramétriques
- Apprentissage et connaissances
- Apprentissage par renforcement


---



# Apprentissage



<div class="grid grid-cols-2 gap-5 -mt-2">
<div>

**Enjeux**

- Environnements inconnus
- Méthode de conception de systèmes
- Améliorer la prise de décision
- Les performances


</div>
<div>


**Structure d'agent**

- Modules
  - Performance
  - Apprentissage
  - Critique
  - Générateur de problème

<img src="./images/img_080.png" class="w-[350px] max-w-full max-h-[300px] object-contain" alt="Agent d'apprentissage : critique, composant d'apprentissage, composant de performance, générateur de problèmes" />




</div>
</div>
---



# Caractéristiques (1/2)



<div class="grid grid-cols-2 gap-5 -mt-2">
<div>

**Composants d'apprentissage**

- Type d'apprentissage
  - Inductif
  - Déductif
- Type de feedback:
  - Supervisé: les réponses correctes
  - Non-supervisé: clusters
  - Par renforcement: récompenses


</div>
<div>


**Apprentissage inductif**

- Nature affectée par
  - Environnement / données
  - Connaissance a priori / modèles
  - Feedback pour apprendre

<img src="./images/img_081.png" class="w-[280px] max-w-full max-h-[300px] object-contain" alt="Nuage de points en croix sur un repère f(x) en fonction de x" />
<img src="./images/img_082.png" class="w-[280px] max-w-full max-h-[300px] object-contain" alt="Ajustement du nuage par une courbe bleue oscillante, une droite rouge et un segment vert" />




</div>
</div>
---



# Caractéristiques (2/2)


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

<div class="img-stack absolute top-[110px] right-[20px] w-[460px]">
<img src="./images/img_083.png" class="w-full object-contain" alt="Surapprentissage : courbe orange oscillante collée aux points contre droite et segment de régression" />
<img src="./images/img_084.png" class="w-full object-contain" alt="Découpage des données : échantillonnage, entraînement, validation, test avec sélection de modèle" />
</div>
---



# Arbres de décision


**Principe**

- Attributs  Décision
- A partir d'exemples

**Techniques**

- Ordre des attributs
- Gain entropique
- Compacité
- Élagage
- Régression
- Quantisation
- Random forest
- Ensemble

<div class="grid grid-cols-2 gap-2 absolute top-[130px] right-[20px] w-[600px]">
<img src="./images/img_085.png" class="max-h-[190px] w-full object-contain" alt="Arbre de décision « Faut-il attendre ? » (exemple restaurant)" />
<img src="./images/img_086.png" class="max-h-[190px] w-full object-contain" alt="Table d'exemples d'entraînement : Autre, Bar, Vendredi, Faim, Clients, Prix, Pluie, Réservation, Type, Estimation — 12 exemples" />
<img src="./images/img_087.png" class="max-h-[190px] w-full object-contain" alt="Partitions d'attributs Clients? et Type? : ronds verts et rouges séparés en sous-ensembles" />
<img src="./images/img_088.png" class="max-h-[190px] w-full object-contain" alt="Forêt aléatoire : nœud X, arbres tree1-treeB, vote (classification) ou moyenne (régression)" />
</div>
---


# Classification

- Utilisation de dimensions supérieures
- Classification linéaire

<img src="./images/img_089.png" class="w-[620px] max-w-full mt-6 mx-auto object-contain" alt="Astuce du noyau : données non séparables linéairement en 2D, séparables par un plan après passage en 3D" />


---



# Réseaux de neurones artificiels


- Inspiration biologique
- Neurone artificiel
  - Fonctions d'activation
- Multi-couches
  - Expressivité croissante

<div class="grid grid-cols-2 gap-2 absolute top-[130px] right-[20px] w-[600px]">
<img src="./images/img_090.png" class="max-h-[190px] w-full object-contain" alt="Neurone biologique : dendrites, soma, axone — l'inspiration des réseaux artificiels" />
<img src="./images/img_091.png" class="max-h-[190px] w-full object-contain" />
<img src="./images/img_092.png" class="max-h-[190px] w-full object-contain" alt="Réseau de neurones fully-connected : une entrée, quatre neurones cachés, dix sorties" />
<img src="./images/img_093.png" class="max-h-[190px] w-full object-contain" alt="Fonctions d'activation : sigmoïde, tanh, ReLU, Leaky ReLU, Maxout, ELU — formules et courbes" />
</div>
---



# Apprentissage profond


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

<div class="grid grid-cols-2 gap-2 absolute top-[130px] right-[20px] w-[600px]">
<img src="./images/img_094.png" class="max-h-[190px] w-full object-contain" alt="Opération de convolution : volume d'entrée 7x7x3 et noyau 3x3x3 glissant sur la matrice" />
<img src="./images/img_095.png" class="max-h-[190px] w-full object-contain" alt="Architecture CNN historique : couches « Simple cells » (convolutions multiples) et « Complex cells » (sous-échantillonnage par pooling)" />
<img src="./images/img_096.png" class="max-h-[190px] w-full object-contain" alt="Transfert learning : photo de voiture, extracteur de caractéristiques, caractéristiques de haut niveau, classifieur entraînable" />
<img src="./images/img_097.png" class="max-h-[190px] w-full object-contain" alt="RNN déroulé : cellule A récurrente, entrées x0 à xt, sorties h0 à ht" />
</div>
---



# Extensions 2010+


- Réseaux récurrents
  - Mémoire à court terme
  - Réseaux LSTM
  - MAJ d'un état de cellule
- Réseaux résiduels (2015)
  - Réinjection des entrées
- GANs (2014)
  - Réseaux adversériaux

<div class="grid grid-cols-3 gap-2 absolute top-[130px] right-[20px] w-[600px]">
<img src="./images/img_098.png" class="max-h-[150px] w-full object-contain" alt="RNN déroulé : cellule récurrente A, entrées x0 à xt, sorties h0 à ht" />
<img src="./images/img_099.png" class="max-h-[150px] w-full object-contain" alt="Cellule récurrente LSTM : portes sigmoïdes σ, tanh, états cachés h entre les pas de temps" />
<img src="./images/img_100.png" class="max-h-[150px] w-full object-contain" alt="RNN à cinq cellules A alignées : entrées x0-x4, sorties h0-h4" />
<img src="./images/img_101.png" class="max-h-[150px] w-full object-contain" alt="Porte sigmoïde σ de cellule LSTM — rendu dégradé, figure à régénérer (voir issue dédiée)" />
<img src="./images/img_102.png" class="max-h-[150px] w-full object-contain" alt="GAN : bruit aléatoire, générateur produisant une image forgée, discriminateur classant réel/factice" />
<img src="./images/img_103.png" class="max-h-[150px] w-full object-contain" alt="Bloc résiduel ResNet : deux couches, connexion identité, H(x)=F(x)+x" />
</div>

<!-- GANs : générateur vs discriminateur, portraits StyleGAN, deepfakes -->
---



# Extensions 2015+ — au-delà de la grille


- Modèles Bayésiens
  - Régularisation
  - Ex: Auto-encodeurs Var.
- Graph Neural Networks
  - Généralisation géométrique
  - Agrégation de voisinage

<div class="grid grid-cols-3 gap-4 absolute bottom-[40px] left-[50px] right-[50px]">
<img src="./images/img_106.png" class="max-h-[190px] w-full object-contain" alt="Autoencodeur variationnel : encodeur, mu/sigma, échantillonnage, décodeur, perte reconstruction + KL" />
<img src="./images/img_107.png" class="max-h-[190px] w-full object-contain" alt="Graphe irrégulier versus grille de texte séquentielle — deux structures de données" />
<img src="./images/img_108.png" class="max-h-[190px] w-full object-contain" alt="Pipeline GNN : graphe d'entrée, blocs GNN, graphe transformé, couche de classification, prédiction" />
</div>

<!-- Auto-encodeurs variationnels : encodeur mu/sigma, echantillonnage, perte reconstruction + KL. GNN : donnees en graphe irregulier plutot qu'en grille, agregation de voisinage. -->
---



# Extensions 2015+ — attention et LLMs


- Réseaux attentionnels
  - Économie de ressources
  - Séquences
  - Transformers, Multi-têtes (2017 : « Attention Is All You Need »)
- Semi-supervisé, Transfert
- LLMs : BERT (2018), GPT-1 (2018)
  - GPT-2 (2019, zero-shot), GPT-3 (2020, in-context few-shot)
  - T5 (2019, text-to-text unifié)
- Modèles efficients (2020+)
  - Reformer, Longformer : attention linéaire ou par fenêtres
  - Mamba (2023) et State Space Models : complexité linéaire, alternative aux Transformers pour séquences longues
  - Hyena, RWKV : mélanges convolutifs et RNN-like pour le même usage

<div class="grid grid-cols-3 gap-4 absolute bottom-[35px] left-[50px] right-[50px]">
<img src="./images/img_104.png" class="max-h-[135px] w-full object-contain" alt="Deux photos d'une femme lançant un frisbee dans un parc, légendées en anglais" />
<img src="./images/img_105.jpg" class="max-h-[135px] w-full object-contain" alt="Attention mot à mot : traduction de « How was your day » avec poids d'importance colorés" />
<img src="./images/img_109.png" class="max-h-[135px] w-full object-contain" alt="Architecture Transformer encodeur-décodeur avec auto-attention, exemple de traduction du tchèque" />
</div>

<!-- Transformer : encodeur-decodeur, self-attention multi-tetes, positional encoding. LLMs : GPT-2 (2019) zero-shot, GPT-3 (2020) in-context few-shot, T5 (2019) text-to-text unifie. Modeles efficients 2020+ : Reformer, Longformer. -->
---



# Extensions 2020+ — modèles multimodaux


**Modèles multimodaux**

- E.g Texte+Image
- Datasets, Encodeurs
- Rapprochement des plongements
  - CLIP (2021, OpenAI) : contraste texte-image sur 400 M de paires
  - ALIGN, Florence (2021-2022) : variantes industrielles
- Génération conditionnelle
  - DALL-E (2022, OpenAI), Imagen (2022, Google)
  - GPT-4V (2023), Gemini (2023) : compréhension multimodale

<div class="grid grid-cols-2 gap-4 absolute bottom-[35px] left-[50px] right-[50px]">
<img src="./images/img_110.png" class="max-h-[160px] w-full object-contain" alt="Trois paires image-légende : rue de Kyoto, aigle en vol, paysage montagneux" />
<img src="./images/img_111.png" class="max-h-[160px] w-full object-contain" alt="CLIP : plongements image et texte comparés, mise à jour des modèles, verdict similaire ou non" />
</div>

<!-- Multimodaux : CLIP (2021) contraste texte-image sur 400 M de paires, ALIGN / Florence, DALL-E (2022), Imagen (2022), GPT-4V / Gemini (2023). -->
---



# Extensions 2020+ — diffusion et alignement


**Modèles de diffusion**

- Prédiction d'un bruit (DDPM, Ho et al. 2020)
- Diffusion latente (LDM / Stable Diffusion, Rombach et al. 2021-2022)
  - Espace latent d'un autoencodeur variationnel pré-entraîné
  - Conditionnement texte (CLIP text encoder) + débruitage U-Net
- Conditionnement multimodal
- Mécanisme attentionnel (cross-attention Q/K/V)

**Alignement et produit grand public**

- RLHF (2022, InstructGPT) : affinage par retour humain
- ChatGPT (nov. 2022, OpenAI) : 100 M d'utilisateurs en 2 mois
- Générations suivantes : Llama 3 / 3.1 / 4 (2024-2025), DeepSeek-V3 (2024), Qwen2.5 (2024-2025), Gemma 2 (2024)
- Frontier multimodaux omni : GPT-4o (mai 2024), Claude 3.5 Sonnet (2024), Gemini 1.5 / 2 (2024-2025)
- Modèles open-weight : Llama 2 (2023), Mistral, Mixtral (MoE 2023-2024)

<div class="grid grid-cols-2 gap-4 absolute bottom-[25px] left-[50px] right-[50px]">
<img src="./images/img_112.png" class="max-h-[100px] w-full object-contain" alt="Chaîne de Markov de diffusion : bruitage progressif de xT vers x0 puis débruitage inverse" />
<img src="./images/img_113.png" class="max-h-[100px] w-full object-contain" alt="U-Net de débruitage latent : encodeur, décodeur, attention croisée Q/K/V, conditionnements et pas de temps" />
</div>

<!-- Diffusion latente (LDM / Stable Diffusion, Rombach 2021-2022) : bruit latent + U-Net + cross-attention. Alignement : RLHF (InstructGPT 2022), ChatGPT (nov 2022), Llama 2 / Mistral / Mixtral (2023-2024). Générations suivantes (2024-2025) : Llama 3 / 4, DeepSeek-V3, Qwen2.5, Gemma 2 ; frontier omni : GPT-4o, Claude 3.5 Sonnet, Gemini 1.5 / 2. -->
---



# Apprentissage non paramétrique


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

<div class="grid grid-cols-2 gap-2 absolute top-[130px] right-[20px] w-[600px]">
<img src="./images/img_114.png" class="max-h-[190px] w-full object-contain" alt="Courbe en cloche gaussienne centrée en zéro, densité de probabilité" />
<img src="./images/img_115.png" class="max-h-[190px] w-full object-contain" alt="Diagramme de Voronoi bicolore : points rouges et bleus, classification par cellules" />
<img src="./images/img_116.png" class="max-h-[190px] w-full object-contain" alt="SVM : deux classes (étoiles rouges, triangles verts), hyperplan, marge, vecteurs de support" />
<img src="./images/img_117.png" class="max-h-[190px] w-full object-contain" alt="Astuce du noyau : nuage 2D non séparable projeté en 3D où un plan sépare les classes" />
</div>
---



# Apprentissage et connaissances


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

<div class="img-stack absolute top-[110px] right-[20px] w-[460px]">
<img src="./images/img_118.png" class="w-full object-contain" alt="Système d'apprentissage inductif fondé sur connaissances : exemples, connaissance du domaine, modèle induit" />
<img src="./images/img_119.png" class="w-full object-contain" alt="Boucle agent-environnement : récompense, état, action" />
</div>
---



# Apprentissage par renforcement


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

<div class="img-stack absolute top-[110px] right-[20px] w-[460px]">
<img src="./images/img_120.png" class="w-full object-contain" alt="Boucle d'apprentissage par renforcement : agent, environnement, échanges récompense/état/action" />
<img src="./images/img_121.png" class="w-full object-contain" alt="Jeu Atari Breakout : deux captures d'écran avec score — terrain classique du RL" />
</div>
---
layout: section
---



# Questions?

---
layout: section
---



# Langage naturel (NLP)

- Modèle du langage
- Communication
- Agents conversationnels (chatbots)


---



# Modèles du langage



<div class="grid grid-cols-2 gap-5 -mt-2">
<div>

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

<img src="./images/img_122.png" class="w-full max-w-[400px] mx-auto max-h-[76px] object-contain mt-4" alt="Formule de probabilité jointe d'une séquence par chaîne de Markov : produit des P(ci | ci-2:i-1)" />

</div>
<div>


- Extraction d'information
  - Automates à états finis:
  - Regexs, Transducteurs
  - Modèles probabilistes
  - Extraction d'ontologie
  - Machine reading

<img src="./images/img_123.png" class="w-full max-w-[240px] mx-auto max-h-[96px] object-contain mt-6" alt="Trois pictogrammes de sentiment : positif (pouce levé vert), neutre (main jaune), négatif (pouce rouge)" />


</div>
</div>
---



# NLP et NLU : la carte des tâches



<img src="./images/img_124.png" class="w-full max-h-[372px] object-contain mt-2" alt="Diagramme de Venn des tâches du TAL : l'ensemble NLP contient catégorisation de texte, analyse syntaxique, étiquetage morpho-syntaxique (POS), reconnaissance d'entités nommées (NER), résolution de coréférences et traduction automatique ; le sous-ensemble NLU contient extraction de relations, résumé, analyse sémantique, paraphrase et inférence en langue naturelle, question-réponse, analyse de sentiments et agents de dialogue" />

<div class="text-center text-sm opacity-75 mt-4">

Le <strong>NLU</strong> est un sous-ensemble du <strong>NLP</strong> : les tâches de la zone verte supposent une représentation du <em>sens</em>, celles de la zone bleue seule s'en passent.

</div>



---



# Grammaires



<div class="grid grid-cols-2 gap-5 -mt-2">
<div>

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
<div>


**Grammaires probabilistes**

- Sans contexte (PCFGs)
- Syntaxique, Apprentissages
- Grammaires augmentées
  - Avec contexte, Sémantiques
- Interpréteurs
  - Modèles sémantiques
  - Ambiguités, Modèles imbriqués

<div class="img-grid">
<img src="./images/img_125.png" class="w-[220px] max-w-full max-h-[300px] object-contain" alt="Règle de grammaire probabiliste PCFG : VP vers Verb (0,70) ou VP NP (0,30)" />
<img src="./images/img_126.png" class="w-[220px] max-w-full max-h-[300px] object-contain" alt="Arbre syntaxique probabiliste de « Every wumpus smells » avec probabilités par nœud" />

</div>


</div>
</div>
---



# Speech/Text to Text/Speech


- Traduction automatisée
  - Modèles statistiques
- Reconnaissance de la parole
  - Modèles acoustiques + langage
- Modèles profonds
  - Réseaux récurrents / Transformers
  - Résumé, analyse syntaxique
  - Modèles sémantiques profonds

<div class="grid grid-cols-2 gap-2 absolute top-[130px] right-[20px] w-[600px]">
<img src="./images/img_127.png" class="max-h-[190px] w-full object-contain" alt="Seq2seq avec attention : encodeur « hello how are you », décodeur allemand « hallo wie geht es dir »" />
<img src="./images/img_128.png" class="max-h-[190px] w-full object-contain" alt="Résultats de recherche d'un modèle CLSM : requêtes et titres de documents retournés" />
<img src="./images/img_129.png" class="max-h-[190px] w-full object-contain" alt="Signal audio analogique, version échantillonnée, et découpage en trames avec caractéristiques" />
<img src="./images/img_130.png" class="max-h-[190px] w-full object-contain" alt="Traduction par interlingua : sémantique commune puis syntaxe et mots anglais/français (John loves Mary / Jean aime Marie)" />
</div>
---



# Agents conversationnels


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

<div class="img-stack absolute top-[110px] right-[20px] w-[460px]">
<img src="./images/img_131.png" class="w-full object-contain" alt="Architecture Microsoft Bot Framework : service bot, connecteur, canaux (Skype, Slack, Facebook...)" />
<img src="./images/img_132.png" class="w-full object-contain" alt="Interface LUIS : énoncé utilisateur annoté avec entité reconnue (réservation de congés)" />
<img src="./images/img_133.png" class="w-full object-contain" alt="Pipeline de dialogue : prétraitement de l'entrée, NLU, gestion de dialogue, génération, sortie" />
</div>
---



# Applications des chatbots



<div class="grid grid-cols-2 gap-5 -mt-2">
<div>

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
- Réalisation + entraînement
- Mise en production
- Amélioration


</div>
<div>


**Exemples**

- Hôtels et transports : SNCF
- Achats en ligne : Amazon
- Télécoms : Verizon
- Finance : Orange
- Médias : CNN
- Ami virtuel : Replika
- Support juridique interne : ADP


<!-- Chatbots modernes : ChatGPT (OpenAI), Claude (Anthropic), Gemini (Google) -->


</div>
</div>
---


# Intelligence conversationnelle

- **Quiz** : quelles formes d'intelligence sont mobilisées par un chatbot ?
  - Exploratoire : navigation dans l'arbre de dialogue
  - Symbolique : compréhension des intentions, raisonnement logique
  - Probabiliste : modèles de langage, prédiction du mot suivant
  - Apprentissage : entraînement sur des corpus massifs, fine-tuning RLHF
- L'agent conversationnel combine toutes les intelligences du cours


---
layout: section
---



# Questions?

---
layout: section
---


# IA générative & vibe coding

- 2022-2026 : la révolution des modèles de fondation
- LLMs, IA générative multimodale, agents et vibe coding
- Notre expérience : notebooks GenAI et stack self-hosted


---


# La révolution des modèles de fondation

**Le tournant : la « mise à l'échelle » (scaling)**

- Plus de données, plus de calcul, plus de paramètres
- Des capacités nouvelles émergent au-delà d'un seuil
  - Comprendre, traduire, résumer, écrire du code
- Ces modèles deviennent la base (« fondation ») de nombreuses applications

```mermaid
graph LR
    A[Données massives] --> C[Modèle de fondation]
    B[Calcul massif] --> C
    C --> D[Capacités émergentes]
    D --> E[GPT, Claude, Gemini...]
```

> Pour approfondir : notebooks `GenAI/Texte/`


---


# « Tokens » : l'unité que le modèle manipule

Un modèle ne lit ni des lettres, ni des mots : il lit des **tokens** — des fragments de texte fréquents, découpés statistiquement sur le corpus d'entraînement.

<div class="grid grid-cols-2 gap-8 mt-6">
<div>

**Le découpage n'est pas le mot**

| Texte | Découpage |
|---|---|
| assurance | `assurance` |
| sinistralité | `sinistr` · `alité` |
| IARD | `I` · `ARD` |

<div class="text-sm text-slate-500 mt-3">
Ordre de grandeur en français : <b>1 token ≈ 4 caractères ≈ 0,75 mot</b>.
</div>

</div>
<div>

**Pourquoi cela vous concerne**

- Le modèle ne fait qu'une chose : **prédire le token suivant**, un à la fois
- La **fenêtre de contexte** (ce qu'il peut « avoir sous les yeux ») se compte en tokens
- Le **prix** et la **latence** se facturent au token, en entrée comme en sortie
- Un mot rare, un nom propre ou un sigle métier coûte plus de tokens qu'un mot courant

</div>
</div>

> Conséquence de gestion : « combien de documents puis-je lui donner ? » et « combien cela coûte ? » sont **la même question**, posée en tokens.


---


# Du token au sens : les embeddings

Le **vocabulaire** et l'**espace de sens** sont deux choses différentes — c'est la confusion la plus fréquente, et la plus coûteuse à l'usage.

<div class="grid grid-cols-2 gap-8 mt-6">
<div>

**Le vocabulaire : une liste**

- Une table d'environ **250 000 entrées** dans les modèles récents
- Un token n'y est **qu'un numéro** — c'est un espace de **dimension 1**
- Trop étroit pour le sens : « voler » y a **une seule** entrée, qu'il s'agisse de dérober ou de prendre l'air

</div>
<div>

**L'embedding : un espace fait pour le sens**

- **768 à 4 096 dimensions**, apprises à l'entraînement
- Chaque numéro y est projeté sur un **vecteur dense**
- Les homonymes s'y séparent, et l'on peut y calculer : *roi − homme + femme ≈ reine*
- C'est cet espace qu'indexent les **bases vectorielles** et la recherche sémantique (RAG)

</div>
</div>

> Dans un Transformer, on part de l'embedding du token nu — sa définition de dictionnaire — puis, couche après couche, l'attention croise ces vecteurs : les homonymes se lèvent d'abord, puis sujets et verbes s'associent, et le sens du récit se construit. Il n'est **jamais** la juxtaposition des définitions.


---


# L'avènement des Transformers

**Avant 2017** — le texte est lu séquentiellement (RNN, LSTM) : le début de la phrase s'estompe à mesure qu'on avance. Les longues dépendances se perdent.

**2017, « Attention is All You Need »** — chaque token regarde **tous les autres en même temps** et pondère ceux qui comptent pour lui.

<div class="grid grid-cols-2 gap-8 mt-4">
<div>

**L'attention, sur un cas métier**

<div class="text-sm mt-2">
« Le <b class="text-rose-700">contrat</b> que l'assuré a signé après sa visite <b class="text-rose-700">est valable</b>. »
</div>

<div class="text-sm text-slate-500 mt-2">
Pour accorder « est valable », le modèle doit rattacher le verbe à <b>contrat</b> — sept mots plus tôt — et non à <b>visite</b>, qui le précède immédiatement. L'attention lui permet de pointer directement le bon mot, quelle qu'en soit la distance.
</div>

</div>
<div>

**Les deux conséquences**

- **Portée** : les dépendances longues sont capturées, donc le sens tient sur un document entier
- **Parallélisme** : tous les tokens sont traités simultanément — donc sur GPU, donc **à grande échelle**

<div class="text-sm text-slate-500 mt-3">
C'est ce second point qui a tout déclenché : l'architecture a rendu l'entraînement massif <i>économiquement possible</i>. Le « scaling » de la slide précédente n'est pas une trouvaille séparée — il est ce que les Transformers ont rendu praticable.
</div>

</div>
</div>


---


# LLMs & ChatGPT : l'IA grand public

- 2017 : Transformers (« Attention is All You Need ») — le fondement
- 2020 : GPT-3 — des capacités qui émergent à l'échelle
- 2022 : ChatGPT — l'IA conversationnelle grand public
- 2023-2026 : GPT-4/5, Claude, Gemini, modèles open-source

**Alignement par instruction**

```mermaid
graph LR
    A[Pré-entraînement<br/>corpus massif] --> B[Fine-tuning supervisé<br/>exemples d'instructions]
    B --> C[RLHF<br/>retour humain]
    C --> D[Assistant aligné]
```

> ChatGPT a atteint 100 millions d'utilisateurs en 2 mois : l'IA devient un produit de masse


---


# IA générative multimodale

Un seul paradigme, plusieurs modalités — un modèle peut générer et comprendre différents types de contenus :

- **Texte** : rédaction, traduction, résumé, code (`GenAI/Texte/`)
- **Image** : génération et édition (`GenAI/Image/` — DALL-E, Qwen-Image-Edit, SDXL)
- **Audio** : synthèse vocale et transcription (`GenAI/Audio/` — Whisper, Kokoro, XTTS)
- **Vidéo** : génération et analyse (`GenAI/Video/` — Hunyuan, LTX, AnimateDiff)

```mermaid
graph TD
    A[Modèle de fondation multimodal] --> B[Texte]
    A --> C[Image]
    A --> D[Audio]
    A --> E[Vidéo]
```


---


# Modèles de diffusion : générer une image

<div class="grid grid-cols-[1fr_1fr] gap-6 mt-2">

<div>

**Principe : apprendre à débruiter**

- Phase aller : on ajoute progressivement du bruit à une image
- Phase retour : le modèle apprend à retirer le bruit pas à pas
- À partir d'un bruit pur, il reconstruit une image cohérente
- Diffusion latente : opérer dans un espace compact (moins de calcul)

```mermaid
graph LR
    A[Image] --> B[+ bruit<br/>aller] --> C[Bruit pur]
    C --> D[- bruit<br/>retour appris] --> E[Nouvelle image]
```

</div>

<div>

<img src="./images/img_112.png" class="w-full object-contain" alt="Processus de diffusion : bruitage progressif puis debruitage inverse" />

<img src="./images/img_113.png" class="w-[88%] mx-auto mt-3 object-contain" alt="Architecture latent diffusion : encodeur, U-Net de débruitage dans l'espace latent, décodeur" />

</div>

</div>

> Les générateurs d'images (DALL-E, Stable Diffusion, Midjourney) reposent sur ce principe


---


# RAG : connecter un LLM à vos données

- Le LLM seul connaît ses données d'entraînement (fenêtre de connaissance figée)
- RAG = Retrieval Augmented Generation — « génération augmentée par la récupération »
  - Les documents sont indexés en vecteurs (embeddings)
  - À chaque question, on récupère les passages les plus pertinents
  - On les injecte dans le prompt, puis le LLM génère une réponse fondée
- Effets : réponses à jour, traçables, moins d'hallucinations

```mermaid
graph LR
    A[Documents] --> B[Embeddings<br/>vecteurs]
    B --> C[(Base vectorielle)]
    D[Question] --> E[Récupération<br/>top-k]
    C --> E
    E --> F[Prompt enrichi]
    F --> G[Réponse fondée]
```

> Notebook : `GenAI/RAG-et-Memoire-Semantique/`


---


# Agents IA : au-delà du chatbot

- Un agent = un LLM + des outils + une boucle de raisonnement
- Le modèle décide quand utiliser un outil (code, web, API, fichier)
- Boucle **ReAct** : Raisonner → Agir → Observer → Raisonner…

```mermaid
%%{init: {"flowchart": {"nodeSpacing": 30, "rankSpacing": 35, "curve": "linear"}, "themeVariables": {"fontSize": "14px"}}}%%
graph LR
    A[Percevoir] --> B[Raisonner]
    B --> C[Agir]
    C --> D[Observer]
    D --> B
```

- Cas d'usage : recherche web, exécution de code, orchestration de tâches
- Le chatbot devient un **agent actif** qui accomplit des tâches

> Notebooks : `GenAI/SemanticKernel/` (20 notebooks)


---


# Vibe coding : programmer par intention

- Terme popularisé par Andrej Karpathy (2025)
- On décrit ce que l'on veut **en langage naturel**, l'IA écrit le code
- Le développeur devient architecte et relecteur plutôt que dactylographe
- Limite : il faut savoir **relire et tester** ce que l'IA produit

```mermaid
graph LR
    A[Idée en langage naturel] --> B[L'IA génère le code]
    B --> C[Exécution + tests]
    C --> D[Revue humaine]
    D --> B
```

> Curriculum : `GenAI/Vibe-Coding/`


---


# Vibe coding en pratique

<div class="grid grid-cols-[1.15fr_1fr] gap-6 mt-2">

<div>

- **Outils** : Claude Code, GitHub Copilot, Cursor, Windsurf
- **Bonnes pratiques**
  - `CLAUDE.md` : documenter le contexte et les règles du projet
  - Agents et skills spécialisés : déléguer les tâches répétitives
  - Itération serrée : petites tâches, vérification continue
- **Notre infrastructure** : un cluster d'agents (coordinateur + workers) qui
  explorent, produisent, reviewent et fusionnent des PRs

</div>

<div>

```mermaid
%%{init: {"flowchart": {"nodeSpacing": 14, "rankSpacing": 20, "curve": "linear"}, "themeVariables": {"fontSize": "11px"}}}%%
graph LR
    U[Utilisateur] --> C[Coordinateur]
    C --> W1[Worker 1]
    C --> W2[Worker 2]
    C --> W3[Worker 3]
    W1 --> R[PR + rapports]
    W2 --> R
    W3 --> R
    R --> U
```

</div>

</div>

<div class="text-sm text-slate-600 border-l-2 border-rose-800/40 pl-4 mt-2">
Ce qui fait tenir l'ensemble n'est pas la puissance des modèles, mais la <b>structure</b> :
des rôles séparés, un périmètre écrit pour chacun, et une <b>revue obligatoire</b> avant
intégration. Les mêmes mécanismes qu'une organisation emploie pour déléguer sans perdre
le contrôle — et ils échouent ici pour les mêmes raisons : périmètre flou, revue de complaisance.
</div>

> Curriculum : `GenAI/Vibe-Coding/Claude-Code/`


---


# Adapter un modèle de fondation

- Un modèle de fondation est générique : on l'**adapte** à un domaine
- **Fine-tuning** : ré-entraînement supervisé sur des données spécialisées
- **LoRA** : n'adapter qu'un petit nombre de paramètres (économie de calcul)
- **Quantization** (INT4, FP8) : réduire la mémoire pour l'inférence
- **DPO / RLHF** : aligner le comportement sur des préférences humaines

```mermaid
graph LR
    A[Modèle de fondation<br/>générique] --> B[Adaptation<br/>LoRA / fine-tuning]
    B --> C[Modèle spécialisé]
    C --> D[Quantization<br/>INT4 / FP8]
    D --> E[Inférence efficace]
```

> Notebooks : `GenAI/PostTraining/`, `GenAI/FineTuning/`


---


# Notre stack GenAI (self-hosted)

- Services Docker dédiés, orchestrés et validés sur nos machines
  - **ComfyUI** : workflows de génération d'images
  - **Qwen / Lumina / Z-Image** : modèles de fondation open-source
  - **Open-WebUI** : interface conversationnelle
- GPU avec allocation et idle management (quantization par service)
- La même stack alimente les notebooks `GenAI/{Image,Audio,Video}`

```mermaid
%%{init: {"flowchart": {"nodeSpacing": 25, "rankSpacing": 30, "curve": "linear"}, "themeVariables": {"fontSize": "13px"}}}%%
graph LR
    A[Notebooks GenAI] --> B[API commune]
    B --> C[ComfyUI]
    B --> D[Qwen / Lumina]
    B --> E[Open-WebUI]
    C --> F[(GPU)]
    D --> F
    E --> F
```

> Référence : `docs/genai/genai-services.md`


---
layout: section
---


# Retour d'expérience : une organisation d'agents

- Ce que change le passage de l'assistant à l'atelier
- L'organisation, les règles, les garde-fous
- Ce qui marche, ce qui ne marche pas


---


# De l'assistant à l'atelier

**L'assistant** : on pose une question, il répond. La valeur s'arrête quand on
ferme la fenêtre.

**L'atelier** : plusieurs agents travaillent en continu sur un dépôt, chacun
produit un livrable **relisable** (une *pull request*), un coordinateur relit et
intègre.

<div class="grid grid-cols-2 gap-4 mt-4">
<div>

**Le dépôt, au 17 août 2026**

| | |
|---|---|
| Contributions intégrées | **9 192** |
| Commits | **11 383** |
| Notebooks pédagogiques | **1 040** |
| Machines hébergeant des agents | **5** |
| Postes de travail (« lanes ») | **10** |

</div>
<div>

**Le rythme récent**

| | |
|---|---|
| Contributions / 30 jours | **3 464** |
| Contributions / 7 jours | **885** |
| Contributions / 24 h | **181** |

</div>
</div>

> Toutes tailles confondues : du correctif d'une ligne à la preuve formelle.
> Le chiffre qui compte n'est pas le volume, c'est qu'**aucune n'entre sans
> relecture**.


---


# L'organisation, trait pour trait

Le parallèle avec une entreprise n'est pas une métaphore : ce sont les mêmes
problèmes, et ils se résolvent avec les mêmes objets.

| Dans l'atelier d'agents | Dans une organisation |
|---|---|
| Un **coordinateur** distribue le travail et intègre | Direction / chef de projet |
| Des **spécialistes** par domaine (21 profils) | Métiers |
| Une **file de travail** par poste, jamais vide | Plan de charge |
| Un **jeton de réservation** posé sur la tâche | « Qui fait quoi » — anti-doublon |
| Une **revue obligatoire** avant intégration | Contrôle, double signature |
| Des **règles écrites** plutôt que des consignes orales | Procédures |

Aucun de ces objets n'a été conçu pour l'IA : ce sont ceux d'une direction
des opérations, transposés tels quels.

---

# L'organisation, à l'échelle

<div class="grid grid-cols-[1fr_1.1fr] gap-6 mt-2">

<div>

```mermaid
%%{init: {"flowchart": {"nodeSpacing": 12, "rankSpacing": 26, "curve": "linear"}, "themeVariables": {"fontSize": "12px"}}}%%
graph TD
    H["Direction — 1 personne"] --> C["Coordinateur — 1 agent"]
    C --> M1["Machine A<br/>2 postes"]
    C --> M2["Machine B<br/>2 postes"]
    C --> M3["Machines C-E<br/>6 postes"]
    M1 --> S["21 profils spécialistes<br/>appelés à la demande"]
    M2 --> S
    M3 --> S
```

</div>

<div>

| Niveau | Effectif | Disponibilité |
|---|---|---|
| Direction, arbitrage | **1 personne** | 1-2 h / jour |
| Coordination | **1 agent** | continue |
| Production | **10 postes** | continue |
| Spécialistes | **21 profils** | à la demande |

<div class="text-sm text-slate-600 mt-5">
<b>5 machines</b>, 2 périmètres de travail chacune :
un poste = une machine × un périmètre.
</div>

</div>

</div>

<div class="text-sm text-slate-600 border-l-2 border-rose-800/40 pl-4 mt-3">
Le chiffre à retenir n'est pas « 10 postes » : c'est le <b>rapport</b>. Une personne, une
à deux heures par jour d'arbitrage, tient une structure qui produit en continu. Ce n'est
pas un remplacement d'ETP — c'est un <b>changement de ce que fait l'ETP</b> : elle ne
produit plus, elle décide et elle relit.
</div>

---

# Quel agent, quel outil, pour quelle tâche

Un **seul** outil d'agent — *Claude Code*, celui déjà cité plus haut — décliné en **profils**.
Ce qui les distingue n'est pas le modèle : c'est le **jeu d'outils** que chacun reçoit.

<div class="text-sm mt-3">

| Profil | Les outils qu'il reçoit | Sa tâche |
|---|---|---|
| Exploration | lecture et recherche, **pas d'écriture** | Retrouver où vit une notion, sans rien modifier |
| Rédaction pédagogique | édition de *notebooks* | Écrire cours et exercices |
| Exécution | noyau Jupyter, Papermill | Faire tourner le cours et **capturer les sorties réelles** |
| Preuve formelle | Lean 4 / Lake | Vérifier un théorème, mesurer la dette de preuve |
| Entraînement | GPU, PyTorch, validation *walk-forward* | Entraîner et **falsifier** un modèle |
| Marchés | API QuantConnect | Lancer un *backtest*, relever Sharpe / drawdown |
| Génération d'images | ComfyUI + modèles auto-hébergés | Produire les illustrations du cours |
| Relecture visuelle | rendu de planches + vision | Vérifier qu'une planche ne déborde pas |
| Contrôle | tests, *build* — et le droit de **refuser** | Refuser ce qui ne passe pas |

</div>

<div class="text-sm text-slate-600 border-l-2 border-rose-800/40 pl-4 mt-2">
Un agent n'est pas « une IA » : c'est un <b>périmètre écrit</b> plus un <b>jeu d'outils
restreint</b>. Celui qui explore n'a pas le droit d'écrire ; celui qui exécute n'a pas le
droit de fusionner. La séparation des pouvoirs y fait le même travail que dans une
organisation — et elle est <b>plus facile à tenir</b>, parce qu'elle est déclarée dans un
fichier plutôt que rappelée en réunion.
</div>


---


# Le circuit d'une contribution

```mermaid
%%{init: {"theme": "base", "themeVariables": {"primaryColor": "#F5F5F5", "primaryTextColor": "#2C3E50", "primaryBorderColor": "#8B1A1A", "lineColor": "#7F8C8D", "fontSize": "15px", "fontFamily": "Segoe UI, Calibri, Arial, sans-serif"}, "flowchart": {"nodeSpacing": 26, "rankSpacing": 44, "curve": "linear"}}}%%
graph LR
    D[Direction] --> C[Coordinateur]
    C --> L1[Poste 1]
    C --> L2[Poste 2]
    C --> L3[Poste n]
    L1 --> P[Livrable relisable]
    L2 --> P
    L3 --> P
    P --> G{Revue + contrôles}
    G -->|conforme| M[Intégré]
    G -->|non conforme| C
```

Le **retour en arrière** est le trait décisif : une contribution non conforme
ne bloque personne, elle revient au poste qui l'a produite.

> Le jeton de réservation est né d'un incident : deux postes irréprochables ont
> livré **deux fois le même travail**. Ce n'était pas une faute d'exécution,
> c'était un **défaut de signal**.


---


# Écrire la règle plutôt que rappeler la consigne

Une leçon transposable telle quelle au management.

**Ce qui ne tient pas** : redire la consigne. Un agent — comme une équipe —
finit par contourner une règle qui n'est portée que par la vigilance.

**Ce qui tient** : un **organe** qui rend le manquement visible et bloquant.

<div class="grid grid-cols-2 gap-4 mt-2">
<div>

**Exemples vécus**

- « Ne jamais intégrer une remarque non traitée » → un contrôle qui refuse
  l'intégration tant que la remarque n'a pas reçu **une phrase** de réponse
- « Varier le travail » → un compteur qui plafonne les tâches faciles
- « Ne pas se marcher dessus » → le jeton de réservation

</div>
<div>

**La formulation qui a émergé**

> Une règle non appliquée demande un **organe**,
> pas davantage de vigilance.

Et son corollaire, plus dur à admettre :

> Un commit poussé après une remarque ne la lève pas.
> Ce qui lève une remarque, c'est **une phrase**.

</div>
</div>

> Un harnais de règles écrit, chargé automatiquement à chaque session — la
> plupart immédiatement, certaines à la demande selon le contexte. La
> documentation qui n'est pas chargée n'existe pas.


---


# Les garde-fous : on ne fusionne pas sur parole

**93 contrôles automatiques** s'exécutent sur chaque contribution. Ils ne
vérifient pas l'intention, ils vérifient le **livrable** :

- le notebook s'exécute-t-il vraiment de bout en bout ?
- la preuve formelle compile-t-elle, sans trou masqué ?
- le résultat annoncé est-il reproductible sur plusieurs tirages ?
- la contribution fait-elle **ce que son titre annonce**, rien de plus ?

**Le revers, mesuré aujourd'hui même.** Le contrôle unique qui protège la
branche principale a, pendant plusieurs heures, bloqué **78 contributions
saines** : le mécanisme censé le débloquer publiait un second verdict sous le
**même nom**, et la plateforme exige que **tous** les verdicts homonymes soient
au vert. Le sauvetage ne pouvait qu'ajouter une façon d'échouer.

> Un garde-fou est un actif **et** un risque d'exploitation. Celui-ci a été
> diagnostiqué en une requête — parce qu'il était instrumenté. Sans mesure, il
> serait passé pour « la file d'attente est saturée », et on aurait attendu.


---


# Ce qui ne marche pas

Le retour d'expérience utile n'est pas la liste des réussites.

**1. L'affirmation confiante et fausse.** Un agent annonce volontiers « fait,
vérifié ». Le remède n'est pas la défiance, c'est l'**exigence de preuve
citée** : le numéro de ligne, la sortie de commande, le lien vers l'exécution.

**2. L'instrument qui répond « rien trouvé » quand il veut dire « je n'ai pas
regardé ».** Neuf fois en une seule session de travail, une mesure a rendu un
chiffre **plus petit et plus propre que la vérité** — donc rassurant. C'est le
mode de panne le plus dangereux, parce qu'il ne lève aucune alerte.

**3. La monoculture du facile.** Laissée libre, une équipe d'agents converge
vers les tâches courtes et sûres, et le travail de fond ne sort jamais. Il a
fallu un quota explicite.

**4. Le coût de coordination est réel.** Il croît plus vite que le nombre
d'agents. Au-delà d'une dizaine de postes, ce n'est plus l'IA qu'on optimise,
c'est l'organisation.

> Aucun de ces quatre points n'est propre à l'IA. Ce sont des pathologies
> d'organisation, que l'IA rend simplement **plus rapides**.


---


# Ce qu'un comité de direction peut en retenir

**1. Le gain n'est pas la génération, c'est le débit relu.** Produire du texte
ou du code est devenu gratuit ; ce qui reste cher, c'est de **savoir ce qu'on
peut intégrer**. Investir dans la relecture automatisée, pas dans la génération.

**2. La vérification doit être mécanique.** Tout ce qui repose sur la vigilance
d'une personne finit par céder sous le volume. Ce qui est vérifié par un
programme tient.

**3. Ce qui n'est pas mesuré n'est pas su.** Les deux incidents les plus coûteux
de ce projet ont été des mesures fausses, pas des décisions fausses.

**4. L'organisation est le facteur limitant, pas le modèle.** Les modèles
progressent seuls ; la distribution du travail, la non-duplication et le
contrôle qualité, non.

**5. Commencer par un périmètre où l'erreur est rattrapable.** Un dépôt de code
a une propriété rare : tout y est réversible et tracé. Peu de processus
d'entreprise offrent ce filet — c'est le premier critère de choix d'un pilote.

> Un atelier d'agents ne remplace pas une équipe. Il déplace le travail de
> l'exécution vers la **spécification** et le **contrôle** — les deux endroits où
> une direction a le plus à dire.


---


# Enjeux : hallucinations, alignement, régulation

- **Hallucinations** : un LLM peut affirmer avec assurance une chose fausse
  - Atténuation : RAG, vérification, raisonnement pas à pas
- **Alignement** : s'assurer que le modèle suit l'intention humaine
  - RLHF, DPO, garde-fous, supervision
- **Régulation** : l'AI Act européen encadre les usages à risque
  - Transparence, documentation, obligations pour l'IA généraliste
- **Sécurité** : les clés et secrets vivent dans des fichiers protégés,
  jamais dans le code, les prompts ou les sorties

> Un outil puissant appelle une utilisation **responsable**


---


# Ce qui est un vrai risque — et ce qui n'en est pas un

<div class="grid grid-cols-2 gap-7 mt-3">

<div>

### Surestimé

- **Le remplacement.** Le goulot n'est pas la production, c'est la **relecture** — écrire dix fois plus réclame plus de relecteurs, pas moins.
- **L'autonomie du modèle.** Ni intention, ni mémoire entre deux appels. Le risque n'est pas qu'il décide : c'est qu'on le **laisse** décider sans vérifier.
- **L'hallucination comme fatalité.** Risque d'ingénierie, mesurable — atténué par le périmètre fermé, la source citée, la vérification.

</div>

<div>

### Sous-estimé

- **La fuite ordinaire.** Pas l'attaque : la pièce de dossier collée dans un service public gratuit. Premier risque réel, et **déjà là**.
- **La dépendance non arbitrée.** Un processus qui ne sait plus fonctionner sans le modèle — sans que personne l'ait décidé.
- **Le biais qui se durcit.** Appris sur l'historique, il reproduit la sélection passée. En souscription : discrimination indirecte, **opposable**.
- **L'absence de trace.** L'AI Act demande de documenter ; ce qui n'est pas tracé dès le pilote ne se reconstitue pas.

</div>

</div>

<div class="mt-6 text-slate-600 border-l-2 border-rose-800/40 pl-5 leading-relaxed">

Le partage utile n'est pas « risqué / pas risqué » : c'est **rattrapable / irrattrapable**.

</div>


---


# Où la valeur se trouve — et où elle ne se trouve pas encore

<div class="grid grid-cols-2 gap-7 mt-3">

<div>

### Mûr aujourd'hui
*l'erreur se voit, et se corrige*

- **Lire et structurer un document** : constat, pièce, conditions générales
- **Chercher dans un corpus fermé**, réponse rattachée à sa source
- **Pré-rédiger sous contrôle** : courrier, compte rendu, synthèse de dossier
- **Assister l'analyse** : code, données, exploration d'un portefeuille

</div>

<div>

### Pas encore
*l'erreur est silencieuse*

- **La décision autonome** sur un dossier
- **Le chiffre non vérifié.** Un modèle de langage ne calcule pas : il complète. Tarification et provisionnement passent par un **outil de calcul** qu'on appelle — jamais par le modèle lui-même.
- **Le jugement en zone grise**, là où la règle ne tranche pas et où c'est précisément le métier qui tranche

</div>

</div>

<div class="mt-8 text-slate-600 border-l-2 border-rose-800/40 pl-5 leading-relaxed">

**L'IA ne remplace pas le métier : elle réorganise le travail autour de lui.** Une nuance, et elle compte devant des actuaires — elle n'automatise pas le **calcul**, elle automatise ce qui l'entoure.

</div>


---


# Pour aller plus loin : Notebooks

Ce deck couvre tous les domaines de l'IA. Pour approfondir avec des exemples pratiques :

> **GenAI - IA Générative**
> `MyIA.AI.Notebooks/GenAI/`
> Transformers, diffusion, LLMs, génération d'images, audio, vidéo
> `GenAI/Vibe-Coding/` : programmation par intention (Claude Code)

> **Search - Recherche et Optimisation**
> `MyIA.AI.Notebooks/Search/`
> Algorithmes génétiques, A*, optimisation locale

> **ML - Machine Learning**
> `MyIA.AI.Notebooks/ML/`
> ML.NET, arbres de décision, classification, régression

> **SymbolicAI - IA Symbolique**
> `MyIA.AI.Notebooks/SymbolicAI/`
> RDF, Z3 SMT, Tweety, Lean, ontologies, web sémantique

> **Probas - Modèles Probabilistes**
> `MyIA.AI.Notebooks/Probas/`
> Infer.NET, réseaux bayésiens, inférence probabiliste

> **GameTheory - Théorie des Jeux**
> `MyIA.AI.Notebooks/GameTheory/`
> OpenSpiel, équilibres de Nash, jeux stratégiques


---
layout: end
---



# Merci

Jean-Sylvain Boige
jsboige@myia.org
