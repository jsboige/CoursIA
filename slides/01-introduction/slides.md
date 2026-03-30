---
theme: ../theme-ia101
title: "01 Introduction"
info: Cours Intelligence Artificielle
paginate: true
drawings:
  persist: false
transition: slide-left
mdc: true
layout: cover
---

# Intelligence Artificielle

Intelligence Artificielle -- I

**Jean-Sylvain Boige**

MRes CSAI, Sussex University, Brighton UK


Aricie -- DNN -- PKP -- My Intelligence Agency

---

# IA 101 -- Ressources et organisation

- **Ouvrage de référence**
  - *Artificial Intelligence: A Modern Approach* (Russell & Norvig)
  - 3e édition (2006) et 4e édition (2020, avec deep learning et IA moderne)
- **En classe**
  - Cours magistraux, corrections d'exercices, travaux pratiques
- **Projets trimestriels**
  - Equipes de 2-3 etudiants, travail transversal
  - Expose final en classe devant le groupe

---

# Sommaire

<img src="./images/img_001.jpg" style="position:absolute; top:72px; right:24px; height:210px; border-radius:4px; box-shadow:2px 2px 8px rgba(0,0,0,0.3);" alt="Russell &amp; Norvig" />

- Qu'est-ce que l'intelligence artificielle ?
- Racines, histoire et etat de l'art
- Structure des agents rationnels
<div v-click="1">
- Intelligence exploratoire
</div>
<div v-click="1">
  - Comment chercher la solution a un probleme ?
</div>
<div v-click="2">
- Intelligence Symbolique
</div>
<div v-click="2">
  - Comment utiliser le raisonnement et les mathematiques ?
</div>
<div v-click="3">
- Intelligence probabiliste
</div>
<div v-click="3">
  - Comment agir dans l'incertitude ?
</div>
<div v-click="4">
- Intelligence Multi-Agents
</div>
<div v-click="4">
  - Comment tenir compte des autres?
</div>
<div v-click="5">
- Apprentissage
</div>
<div v-click="5">
  - Comment utiliser les donnees et l'experience ?
</div>
<div v-click="6">
- Application: le langage naturel

---

# Sommaire

- Presentation du cursus
- Introduction
  - Qu'est-ce que l'intelligence artificielle?
  - Les domaines d'étude
  - Un peu d'histoire
  - L'etat de l'art
- Systèmes d'agents
  - Agents rationnels
  - Environnements taches
  - Types d'Agents
- Presentation des projets de groupe

---

# Objectifs du cours (1/2)

A l'issue de ce cours, vous serez capables de :

- **Comprendre les grands paradigmes de l'IA**
  - Identifier les principaux domaines et leurs applications
  - Disposer des bases pour approfondir chacun d'entre eux
- **Concevoir des programmes intelligents dans des domaines varies :**
  - Recherche de solutions et jeux strategiques
  - Représentation de connaissances et raisonnement logique
  - Modelisation probabiliste et prise de decision sous incertitude
  - Apprentissage automatique (supervise, non supervise, par renforcement)
  - Traitement du langage naturel

---

# Objectifs du cours (2/2)

- **Concevoir des systèmes intelligents en conditions reelles**
  - Integrer les differentes briques pour construire un système complet
  - Gerer les contraintes du monde reel : incertitude, temps de calcul, données imparfaites
- **BONUS : Mieux comprendre l'intelligence elle-meme**
  - Comment l'intelligence emerge-t-elle dans la nature ?
  - Comment fonctionne le cerveau humain, et en quoi l'IA s'en inspire ?
  - Comment definir et mesurer la rationalite ?

---

# Plan du cours

<ol class="roman-list">
<li>Introduction</li>
<li>Resolution de problemes</li>
<li>Bases de connaissances et logique</li>
<li>Raisonnement probabiliste</li>
<li>Theorie des jeux</li>
<li>Apprentissage</li>
<li>Traitement du langage naturel</li>
<li>Presentations des projets</li>
</ol>

---
layout: section
---

<h1 style="color: #F5F5F5 !important; border-bottom: 2px solid #F5F5F5 !important;">Questions?</h1>

---

# Introduction a l'intelligence artificielle

- Presentation du cursus
- **Introduction**
  - Qu'est-ce que l'intelligence artificielle?
  - Les domaines d'étude
  - Un peu d'histoire
  - L'etat de l'art
- Systèmes d'agents
  - Agents rationnels
  - Environnements taches
  - Types d'agents
- TP: Mise en place de l'environnement de travail
- Presentation des projets de groupe

---

# Qu'est-ce que l'intelligence artificielle ?

- **Des definitions multiples et un concept evolutif**
  - L'IA n'a pas de définition unique : elle recouvre des approches tres differentes
  - Concevoir un système intelligent n'implique pas de comprendre l'intelligence
- **Une définition qui évolue avec la technologie :**
  - Automates → Calculateurs → Algorithmes → Bases de connaissances → Systèmes experts → Apprentissage profond → IA generative

![](./images/img_002.png)

---

# Quatre visions de l'IA

**Quatre grandes approches structurent le domaine :**

<ColoredTable />

**Notre angle principal : « Agir de facon rationnelle »**
- Concevoir des agents qui prennent les meilleures decisions possibles
- Approche qui unifie les autres : un agent rationnel peut raisonner, apprendre et communiquer

---

# Les fondements de l'IA

L'IA est une discipline profondement interdisciplinaire :

- **Philosophie :** logique, raisonnement, nature de l'esprit
- **Mathematiques :** algorithmes, complexite, probabilites, decidabilite
- **Economie :** theorie de la decision, utilite, theorie des jeux
- **Biologie :** intelligence naturelle et animale, evolution
- **Neurosciences :** substrat physique de l'activite mentale
- **Psychologie :** perception, cognition, comportement
- **Informatique :** puissance de calcul, logiciel, architectures
- **Theorie du controle :** optimisation d'une fonction objective dans le temps
- **Linguistique :** grammaires, representation du sens

---
layout: image-right
image: ./images/img_004.png
---

# Histoire succincte (1/2)

**Les debuts (1943-1970)**
- **1943** : McCulloch & Pitts modélisent le cerveau comme un circuit logique
- **1950** : Turing pose la question "Can machines think?"
- **1956** : Conference de Dartmouth -- le terme "Artificial Intelligence" est ne
- **Années 50** : premiers programmes capables d'apprendre
  - Samuel (jeu de dames), Newell & Simon (theoricien logique)
  - Gelernter (geometrie), naissance de Lisp
- **1965** : Robinson propose un algorithme complet de raisonnement logique
- **1969-79** : age d'or des systèmes experts (bases de connaissances)

---

# Histoire succincte (2/2)

**Maturite et "hivers de l'IA" (1970-2010)**

- **1970s** : l'IA se heurte a la complexité calculatoire -- premier "hiver"
- **1980s** : l'IA devient une industrie (robotique, vision, systèmes experts)
- **1986** : retour des réseaux de neurones grace a la retropropagation
- **1990s** : l'IA se mathematise (probabilités, optimisation)
- **2000s** : data mining, apprentissage bayesien, web semantique

**Renaissance et explosion (2010-aujourd'hui)**

- **2012** : deep learning domine ImageNet -- la revolution commence
- **2017** : "Attention Is All You Need" -- naissance des Transformers
- **2020s** : GPT, DALL-E, ChatGPT, Claude, Gemini, DeepSeek, agents autonomes

---

# Etat de l'art (1/2)

**L'IA bat les champions (1997-2019)**

- **1997** : Deep Blue bat Kasparov aux echecs
- **2016** : AlphaGo bat Lee Sedol au Go (DeepMind)
- **2017** : Libratus domine les pros du poker
- **2018** : AlphaZero apprend seul Go, echecs et shogi par renforcement
- **2019** : StarCraft II, Pluribus (poker multi-joueurs)

**Applications dans le monde reel**

- Preuve de conjectures mathématiques (Robbins, 1996)
- Vehicules autonomes (vol, conduite, marche robotique)
- Logistique et planification militaire (guerre du Golfe) <img src="./images/img_005.jpg" style="display:inline; height:1.4em; vertical-align:middle;" />
- NASA : planification autonome de missions spatiales
- Trading algorithmique (85% du volume des marches en 2012)

---

# Etat de l'art (2/2)

**Deep Learning et NLP (2010-2019)**

- **2012** : deep learning domine ImageNet (reconnaissance d'images quasi humaine)
- **2014** : GANs -- les reseaux de neurones deviennent creatifs
- **2017** : Transformers (Google) -- revolution du traitement du langage
- **2018-19** : GPT-2, BERT, Watson -- un nouveau paradigme d'interaction

**L'ere de l'IA generative (2020-2026)**

- **2020** : GPT-3 (175 milliards de parametres)
- **2021** : DALL-E (images), AlphaFold (proteines)
- **2022** : ChatGPT (1M utilisateurs en 5 jours), Stable Diffusion
- **2023** : GPT-4, Claude, LLaMA, Gemini -- competition ouverte
- **2024** : modeles de reflexion (O1), agents LLM, open source (DeepSeek)
- **2025** : GPT-5, agents autonomes, MCP (interoperabilite)

---

# Qui fait de l'IA ?

**Recherche academique** : CMU, Stanford, Berkeley, MIT, Caltech, U Austin, IDSIA...

<div class="image-grid">
<img src="./images/img_007.png" alt="CMU">
<img src="./images/img_008.png" alt="MIT">
<img src="./images/img_009.png" alt="IDSIA">
<img src="./images/img_010.png" alt="Berkeley">
<img src="./images/img_011.jpg" alt="Stanford">
</div>

**Gouvernements et laboratoires prives** : NASA, NRL, NIST, IBM, AT&T, SRI, ISI, MERL...

**Beaucoup de societes** : Google, Microsoft, Facebook, Amazon, Honeywell, MITRE, Fujitsu...

<div class="image-grid">
<img src="./images/img_012.png" alt="Google">
<img src="./images/img_013.png" alt="Microsoft">
<img src="./images/img_014.png" alt="Honeywell">
<img src="./images/img_015.png" alt="BodyMedia">
<img src="./images/img_016.png" alt="MITRE">
<img src="./images/img_017.png" alt="Fujitsu">
<img src="./images/img_018.png" alt="Facebook">
<img src="./images/img_019.png" alt="Amazon">
</div>

---

# L'IA dans la vie de tous les jours

- **Banque et finance** : scoring de credit, detection de fraude, trading algorithmique
- **Service client** : chatbots, reconnaissance vocale, routage intelligent
- **Internet** : recommandation (Netflix, Spotify), detection de spam, publicite ciblee
- **Securite** : reconnaissance faciale, detection de plaques, videosurveillance
- **Transport** : navigation GPS, vehicules autonomes, optimisation logistique
- **Sante** : aide au diagnostic, analyse d'imagerie medicale, decouverte de medicaments
- **Quotidien** : assistants vocaux (Siri, Alexa), traduction automatique, filtres photo

---
layout: image-right
image: ./images/img_020.png
---

# Agir comme l'homme : le Test de Turing

**Alan Turing (1950)** propose un test operationnel : une machine est "intelligente" si un humain ne peut la distinguer d'un autre humain en conversant avec elle.

**Competences requises pour reussir le test :**
- Traitement du langage naturel
- Représentation de connaissances
- Raisonnement automatique
- Apprentissage

**« Total Turing » (+ camera)** ajoute la vision et la robotique.

**Ces competences definissent les grandes disciplines de l'IA** -- dont quatre seront detaillees dans ce cours.

---

# Penser comme l'homme : sciences cognitives

- **La "revolution cognitive" (années 1960)**
  - La psychologie commence a modeliser la pensee comme un traitement de l'information
- **Deux approches pour etudier le cerveau**
  - *Top-down* : modeliser le comportement humain observable
  - *Bottom-up* : observer directement l'activite neurologique (IRMf, EEG)
- **Pourquoi l'IA s'en distingue aujourd'hui**
  - Les humains sont souvent irrationnels (biais cognitifs)
  - Le reverse-engineering du cerveau reste extremement difficile
  - Le "hardware" biologique differe fondamentalement du silicium

---

# Penser de facon rationnelle : lois de la raison

- **Depuis Aristote : quels sont les arguments corrects ?**
  - La logique formelle fournit des regles de derivation rigoureuses
- **La logique au service de l'IA**
  - Representer les faits du monde sous forme formelle
  - Utiliser l'inference pour deduire de nouvelles connaissances
  - Exemple : prouveurs automatiques de théorèmes
- **Limites de l'approche purement logique**
  - Le monde reel est incertain (capteurs imparfaits, information incomplete)
  - Tout comportement intelligent ne releve pas d'une délibération logique
  - En pratique, il faut aussi definir des buts et évaluer des couts

---

# Agir de facon rationnelle : l'agent

- **Un comportement rationnel consiste a faire la bonne chose :**
  - Choisir l'action qui maximise les chances d'atteindre l'objectif, compte tenu de l'information disponible
- **Agir rationnellement n'implique pas forcement de penser**
  - Un reflexe (cligner des yeux) peut etre rationnel sans délibération
  - Mais la reflexion reste un outil puissant au service de l'action
- **Lien avec la theorie de la decision**
  - Évaluer les etats possibles et les actions disponibles
  - Maximiser l'utilite esperee, meme sous incertitude
- **C'est l'approche centrale de ce cours** : concevoir des agents rationnels

---
layout: section
---

<h1 style="color: #F5F5F5 !important; border-bottom: 2px solid #F5F5F5 !important;">Questions?</h1>

---

# Systemes d'agents

- Presentation du cursus
- Introduction
  - Qu'est-ce que l'intelligence artificielle?
  - Les domaines d'étude
  - Un peu d'histoire
  - L'etat de l'art
- **Agents rationnels**
- **Environnements taches**
- **Types d'agents**
- TP: Mise en place de l'environnement de travail
- Presentation des projets de groupe

---
layout: image-right
image: ./images/img_021.png
---

# Les agents

**Un agent est une entite autonome qui :**
- **Percoit** son environnement grace a des capteurs (cameras, micros, senseurs...)
- **Agit** sur cet environnement par des effecteurs (moteurs, ecrans, haut-parleurs...)

**Formalisation :**
- Un agent implemente une *fonction d'agent* : $f: \mathcal{P}^* \to \mathcal{A}$
- A partir de l'historique complet de ses percepts, il choisit une action

---

# Les agents rationnels

**Un agent rationnel choisit l'action qui maximise sa mesure de performance.**

- **Mesure de performance** : critere objectif et externe de succes
- **Decision basee sur** : la suite des percepts recus et les connaissances prealables
- **Rationnel ne signifie pas omniscient**
  - L'agent explore pour completer ses connaissances
  - Il s'adapte par l'expérience (apprentissage)
  - Il est reactif *et* proactif

---

# Rationalite limitee

- **La rationalite parfaite est rarement atteignable**
  - Ressources de calcul limitees, temps de decision contraint
  - Information incomplete sur l'environnement
- **Objectif realiste** : obtenir les meilleures performances possibles compte tenu des ressources disponibles
- **Herbert Simon (1955)** : concept de "satisficing" -- choisir une solution satisfaisante plutot qu'optimale

---

# Intelligences


**Procedurale** -- Automates, Algorithmes

**Intelligence exploratoire** -- Recherche de chemin, Exploration locale, Satisfaction de contraintes

**Intelligence symbolique** -- Raisonnement, Bases de connaissances, Plans

**Intelligence probabiliste** -- Inference Bayesienne, Recherche de politique, Analyse strategique

::right::

<div style="display: grid; grid-template-columns: 1fr 1fr; gap: 12px; align-items: center;">
<img src="./images/img_022.jpg" style="max-height: 140px; object-fit: contain;">
<img src="./images/img_023.png" style="max-height: 140px; object-fit: contain;">
<img src="./images/img_026.png" style="max-height: 140px; object-fit: contain;">
<img src="./images/img_027.jpg" style="max-height: 140px; object-fit: contain;">
</div>


---

# Intelligence de la recherche

<IntelligenceTaxonomy :rows="[
  {label:'Type', items:['Exploratoire']},
  {label:'Inférence', items:['Recherche de chemin','Exploration locale','Satisfaction de contraintes']},
  {label:'Modèles', items:['Cartes heuristiques','Modèles paramétriques','Modèles de contraintes']},
  {label:'Apprentissage', items:['Apprentissage de carte','Meta-learning','Descente de gradient','Algorithmes génétiques','Meta-heuristiques']},
  {label:'Agents', items:['Fondés sur des buts','Fondés sur un modèle','Agents Evolutifs']}
]" />

---

# Intelligence de la pensée logique

<IntelligenceTaxonomy :rows="[
  {label:'Type', items:['Symbolique']},
  {label:'Inférence', items:['Raisonnement']},
  {label:'Modèles', items:['Bases de connaissances','Plans','Smart-contracts']},
  {label:'Apprentissage', items:['Apprentissage inductif','Apprentissage déductif','Solveurs SMTs','Planificateur','Maintenance de la vérité']},
  {label:'Agents', items:['Fondés sur des connaissances','Fondés sur des hypothèses','Agents optimiseurs','Fondés sur des buts','Agents certifiants']}
]" />

---

# Intelligence de l'incertitude

<IntelligenceTaxonomy :rows="[
  {label:'Type', items:['Probabiliste']},
  {label:'Inférences', items:['Inférence Bayésienne','Recherche de politique','Analyse stratégique']},
  {label:'Modèles', items:['Modèles graphiques','Réseaux de décision','Processus de Markov','Modèles stratégiques']},
  {label:'Apprentissage', items:['Apprentissage Bayésien','Système expert','Apprentissage par renforcement','Minimisation de regret']},
  {label:'Agents', items:['Agents diagnostic','Fondés sur l\'utilité','Agents politiques','Agents stratégiques']}
]" />

---

# Environnement de tache

**Description PEAS:**
- **P**erformance (Mesure de)
- **E**nvironnement
- **A**ctuators (Effecteurs)
- **S**ensors (Capteurs)

**Exemple: Taxi**
- **Performance:**
  - Prudent, rapide, legal, confortable, rentable
- **Environnement:**
  - Route, trafic, pietons, clients, vehicule
- **Effecteurs:**
  - Volant, accelerateur, frein, clignotants, klaxon
- **Capteurs:**
  - Cameras, sonar, accelerometre, GPS, Lidar, clavier etc.

---

# Environnements de tache: exemples

<style>
table { font-size: 0.7em; }
</style>

| Agent | Performance | Environnement | Effecteurs | Capteurs |
|-------|------------|--------------|-----------|---------|
| Diagnostic | Patients gueris | Hopital | Tests, traitements | Symptomes |
| Satellites | Categorisation | Orbite | Scene classifiee | Pixels |
| Robot trieur | % correct | Tapis roulant | Bras articule | Camera |
| Raffinerie | Purete, securite | Raffinerie | Valves, pompes | Temp., pression |
| Repetiteur | Notes etudiants | Etudiants | Corrections | Clavier |

---

# Types d'environnement (1/2)

Chaque environnement de tache possede des propriétés qui influencent la conception de l'agent :

- **Completement vs partiellement observable**
  - L'agent a-t-il acces a l'etat complet de l'environnement ?
- **Deterministe vs stochastique**
  - L'etat suivant est-il entierement determine par l'etat courant et l'action ?
  - Cas particulier : *strategique* = déterministe sauf les actions des autres agents
- **Episodique vs séquentiel**
  - Les decisions sont-elles indépendantes ou liees entre elles ?
- **Statique vs dynamique**
  - L'environnement change-t-il pendant que l'agent delibere ?

---

# Types d'environnement (2/2)

<div v-click="1">

- **Discret vs continu**
  - Les etats, le temps, les percepts et les actions sont-ils denombrables ?

</div>
<div v-click="2">

- **Agent simple vs multiagent**
  - L'agent est-il seul ou en interaction (cooperation, competition) ?

</div>
<div v-click="3">

- **Connu vs inconnu**
  - L'agent connait-il les regles de l'environnement ?

</div>

**En pratique**, le monde reel combine les cas les plus difficiles : partiellement observable, stochastique, sequentiel, dynamique, continu, multiagent.

---

# Types d'environnement: exemples

<style>
table { font-size: 0.65em; }
</style>

| Tache | Obs. | Agents | Determ. | Epis. | Stat. | Discr. |
|-------|------|--------|---------|-------|-------|--------|
| Echecs | O | Multi | O | N | Semi | O |
| Poker | N | Multi | N | N | Stat. | O |
| Backgammon | O | Multi | N | N | Semi | O |
| Conduite | P | Multi | N | N | N | N |
| Diagnostic | P | Simple | N | N | N | N |
| Analyse img | O | Simple | O | O | Semi | N |
| Robot trieur | P | Simple | N | N | N | N |
| Raffinerie | P | Simple | N | N | N | N |
| Repetiteur | N | Multi | N | N | N | N |

---
layout: image-right
image: ./images/img_030.png
---

# Types d'agents

**f(agent) = Architecture physique + Programme**

Un agent naif pourrait stocker une table "percepts → action", mais cette approche est impraticable : la table serait gigantesque et impossible a construire.

**Cinq architectures d'agents, par ordre de généralité :**

1. Agent reflexe simple
2. Agent reflexe fonde sur un modele
3. Agent fonde sur des buts
4. Agent fonde sur l'utilite
5. Agent capable d'apprentissage

---
layout: two-cols
---

# Agent reflexe


**Caractéristiques:**

- Pas de mémoire
- Percepts courants
- Regles Conditions / Actions

**Exemples:**

<div v-click="1">

- Intelligence animale

</div>

- Behaviourism
- Artificial Life
- Cellular Automata

<img src="./images/img_033.png" width="80">

::right::

<img src="./images/img_031.png" width="420">

<img src="./images/img_032.png" width="350">


---
layout: two-cols
---

# Agent reflexe fonde sur un modele


**Caractéristiques:**

<div v-click="1">

- Etat du monde

</div>

- Historique des percepts
- Mémoire du changement

**Exemple: Subsomption (Brooks)**

- Modele non representatif
- Comportements simples
- Couches d'automates
- Emergence

<img src="./images/img_036.png" width="80">

::right::

<img src="./images/img_034.png" width="420">

<img src="./images/img_035.png" width="350">


---
layout: image-right
image: ./images/img_037.png
---

# Agent fonde sur des buts

**Du reactif au deliberatif** : l'agent ne reagit plus seulement a l'instant present, il anticipe le futur.

- Considere les consequences de ses actions
- Planifie des sequences d'actions pour atteindre un objectif
- Utilise la recherche (exploration) et la planification

---
layout: image-right
image: ./images/img_038.png
---

# Agent fonde sur l'utilite

**Quand plusieurs chemins menent au but, lequel choisir ?**

- Une **fonction d'utilite** U : Etat → R attribue un score a chaque etat
- L'agent choisit l'action qui maximise l'utilite esperee

**Permet d'arbitrer entre :**
- Probabilite de succes vs importance de l'objectif
- Risque vs recompense, urgence vs cout

---
layout: image-right
image: ./images/img_039.png
---

# Agent capable d'apprentissage

**Quatre composants internes :**

- **Element de performance** : choisit les actions
- **Element d'apprentissage** : ameliore la performance a partir de l'expérience
- **Critique** : evalue les resultats par rapport a un standard fixe
- **Generateur de problemes** : suggere des actions exploratoires

**Formes d'apprentissage :** supervise, par renforcement, non supervise

---

# Fonctionnement interne des agents

**La représentation de la connaissance est determinante**

Trois niveaux de representation des etats, du plus simple au plus expressif :

- **Atomique** : chaque etat est indivisible (ex: un noeud dans un graphe)
- **Factorise** : un etat est un ensemble de proprietes (ex: variables booleennes)
- **Structure** : un etat est un objet complexe avec des relations (ex: base de donnees)

**Compromis fondamental :** plus la representation est riche, plus l'agent est flexible -- mais plus le raisonnement est couteux.

<img src="./images/img_040.png" style="display:block; margin:8px auto; max-height:30vh;" alt="Representations: Atomique, Factorisee, Structuree" />

---

# Resume

- **Intelligence artificielle**
  - Quatre approches : penser/agir comme l'homme ou de facon rationnelle
  - Fondements interdisciplinaires : logique, decision, neurosciences, linguistique...
  - Une histoire ponctuee de "hivers" et de renaissances spectaculaires
- **Agents rationnels**
  - Un agent percoit son environnement et agit pour maximiser sa performance
  - La rationalite parfaite est un ideal ; en pratique, on vise le meilleur compromis
- **Architectures d'agents**
  - Reflexes (simples ou avec modele), fondes sur des buts ou l'utilite, apprenants
  - Les propriétés de l'environnement dictent le choix de l'architecture
  - La représentation des etats (atomique, factorisee, structuree) conditionne les capacites

---

# Plan du cours

<ol class="roman-list">
<li>Introduction</li>
<li>Resolution de problemes</li>
<li>Bases de connaissances et logique</li>
<li>Raisonnement probabiliste</li>
<li>Theorie des jeux</li>
<li>Apprentissage</li>
<li>Traitement du langage naturel</li>
<li>Presentations des projets</li>
</ol>

---

# Pour aller plus loin : Notebooks

Chaque chapitre du cours est accompagne de travaux pratiques sous forme de notebooks Jupyter :

- **Exploration** : `Search/`, `Sudoku/` -- CSP, algorithmes genetiques, optimisation
- **Logique** : `SymbolicAI/`, `Lean/` -- Z3, Tweety, Lean 4, argumentation
- **Probabilites** : `Probas/Infer/` -- inference bayesienne, réseaux de decision
- **Jeux** : `GameTheory/` -- equilibres de Nash, jeux bayesiens, MARL
- **Apprentissage** : `ML/`, `RL/` -- classification, regression, renforcement
- **IA Generative** : `GenAI/` -- DALL-E, Stable Diffusion, LLMs, RAG

> **Depot :** `github.com/jsboige/CoursIA` > dossier `MyIA.AI.Notebooks/`

---
layout: cover
---

# Merci

Jean-Sylvain Boige
jsboige@myia.org
