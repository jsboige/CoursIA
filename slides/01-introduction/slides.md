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

<img src="./images/img_001.jpg" style="position:absolute; top:90px; right:40px; height:340px; border-radius:4px; box-shadow:2px 2px 8px rgba(0,0,0,0.3);" alt="Russell &amp; Norvig - Intelligence artificielle" />

<div style="max-width:65%;">

- **Ouvrage de référence**
  - *Artificial Intelligence: A Modern Approach* (Russell & Norvig)
  - 3e édition (2006) et 4e édition (2020, avec deep learning et IA moderne)
- **En classe**
  - Cours magistraux, corrections d'exercices, travaux pratiques
- **Projets trimestriels**
  - Equipes de 2-3 etudiants, travail transversal
  - Expose final en classe devant le groupe

</div>

---

# Sommaire

<ul>
  <li>Qu'est-ce que l'intelligence artificielle ?
    <ul>
      <li>Racines, histoire et etat de l'art</li>
      <li>Structure des agents rationnels</li>
    </ul>
  </li>
  <li v-click>Intelligence exploratoire
    <ul><li>Comment chercher la solution a un probleme ?</li></ul>
  </li>
  <li v-click>Intelligence Symbolique
    <ul><li>Comment utiliser le raisonnement et les mathematiques ?</li></ul>
  </li>
  <li v-click>Intelligence probabiliste
    <ul><li>Comment agir dans l'incertitude ?</li></ul>
  </li>
  <li v-click>Intelligence Multi-Agents
    <ul><li>Comment tenir compte des autres ?</li></ul>
  </li>
  <li v-click>Apprentissage
    <ul><li>Comment utiliser les donnees et l'experience ?</li></ul>
  </li>
  <li v-click>Application : le langage naturel</li>
</ul>

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

<img src="./images/img_002.png" style="position:absolute; top:80px; right:20px; width:340px;" alt="Quatre definitions de l'IA" />

<div style="max-width:55%;">

- **Des definitions multiples et un concept evolutif**
  - L'IA n'a pas de définition unique : elle recouvre des approches tres differentes
  - Concevoir un système intelligent n'implique pas de comprendre l'intelligence
- **Une définition qui évolue avec la technologie :**
  - Automates → Calculateurs → Algorithmes → Bases de connaissances → Systèmes experts → Apprentissage profond → IA generative

</div>

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

# Histoire succincte (1/2)

<img src="./images/img_004.png" style="position:absolute; top:60px; right:20px; width:340px;" alt="Frise chronologique IA" />

<div style="max-width:55%;">

**Les debuts (1943-1970)**
- **1943** : McCulloch & Pitts modélisent le cerveau comme un circuit logique
- **1950** : Turing pose la question "Can machines think?"
- **1956** : Conference de Dartmouth -- le terme "Artificial Intelligence" est ne
- **Années 50** : premiers programmes capables d'apprendre
  - Samuel (jeu de dames), Newell & Simon (theoricien logique)
  - Gelernter (geometrie), naissance de Lisp
- **1965** : Robinson propose un algorithme complet de raisonnement logique
- **1969-79** : age d'or des systèmes experts (bases de connaissances)

</div>

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

# Agir comme l'homme : le Test de Turing

<img src="./images/img_020.png" style="position:absolute; top:60px; right:20px; width:300px;" alt="Test de Turing" />

<div style="max-width:60%;">

**Alan Turing (1950)** propose un test operationnel : une machine est "intelligente" si un humain ne peut la distinguer d'un autre humain en conversant avec elle.

**Competences requises pour reussir le test :**
- Traitement du langage naturel
- Représentation de connaissances
- Raisonnement automatique
- Apprentissage

**« Total Turing » (+ camera)** ajoute la vision et la robotique.

**Ces competences definissent les grandes disciplines de l'IA** -- dont quatre seront detaillees dans ce cours.

</div>

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

# Les agents

<img src="./images/img_021.png" style="position:absolute; top:60px; right:20px; width:320px;" alt="Schema agent" />

<div style="max-width:55%;">

**Un agent est une entite autonome qui :**
- **Percoit** son environnement grace a des capteurs (cameras, micros, senseurs...)
- **Agit** sur cet environnement par des effecteurs (moteurs, ecrans, haut-parleurs...)

**Formalisation :**
- Un agent implemente une *fonction d'agent* : $f: \mathcal{P}^* \to \mathcal{A}$
- A partir de l'historique complet de ses percepts, il choisit une action

</div>

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

<div style="position:absolute; top:70px; left:25px; right:25px; bottom:35px;">
  <!-- Procedurale (outermost) -->
  <div style="background:#c0522e; border-radius:20px; padding:12px 14px 10px; height:100%; position:relative; color:white; display:flex; flex-direction:column;">
    <div style="display:flex; align-items:center; gap:10px; margin-bottom:2px;">
      <span style="font-size:1.5em; font-weight:bold;">Procedurale</span>
      <img src="./images/img_023.png" style="height:60px; background:white; border-radius:6px; padding:2px; object-fit:contain;" />
    </div>
    <div style="position:absolute; top:12px; right:14px; display:flex; flex-direction:column; gap:4px;">
      <span style="background:white; color:#333; padding:3px 12px; border-radius:4px; font-size:0.7em;">Automates</span>
      <span style="background:white; color:#333; padding:3px 12px; border-radius:4px; font-size:0.7em;">Algorithmes</span>
    </div>
    <!-- Exploratoire -->
    <div style="background:#d07050; border:2px dashed rgba(255,255,255,0.5); border-radius:12px; padding:8px 12px; flex:1; position:relative; display:flex; flex-direction:column;">
      <div style="display:flex; align-items:center; gap:10px; margin-bottom:2px;">
        <span style="font-size:1.25em; font-weight:bold;">Exploratoire</span>
        <img src="./images/img_024.jpg" style="height:55px; border-radius:5px; object-fit:cover;" />
      </div>
      <div style="display:flex; gap:8px; flex:1;">
        <!-- Left column: Exploratoire items -->
        <div style="display:flex; flex-direction:column; gap:4px; min-width:110px; justify-content:center;">
          <span style="background:white; color:#333; padding:2px 8px; border-radius:4px; font-size:0.6em; white-space:nowrap;">Recherche de chemin</span>
          <span style="background:white; color:#333; padding:2px 8px; border-radius:4px; font-size:0.6em;">Escalades</span>
          <span style="background:white; color:#333; padding:2px 8px; border-radius:4px; font-size:0.6em;">Arbres de jeux</span>
          <span style="background:white; color:#333; padding:2px 8px; border-radius:4px; font-size:0.6em; white-space:nowrap;">Satisfaction de contraintes</span>
        </div>
        <!-- Symbolique -->
        <div style="flex:1; background:#d8886e; border:2px dashed rgba(255,255,255,0.5); border-radius:10px; padding:6px 10px; position:relative; display:flex; flex-direction:column;">
          <div style="display:flex; align-items:center; gap:8px; margin-bottom:2px;">
            <span style="font-size:1.1em; font-weight:bold;">Symbolique</span>
            <img src="./images/img_025.jpg" style="height:45px; border-radius:4px; object-fit:cover;" />
          </div>
          <div style="display:flex; gap:6px; flex:1;">
            <!-- Symbolique items -->
            <div style="display:flex; flex-direction:column; gap:3px; min-width:100px; justify-content:center;">
              <span style="background:white; color:#333; padding:2px 6px; border-radius:3px; font-size:0.55em;">Raisonnement</span>
              <span style="background:white; color:#333; padding:2px 6px; border-radius:3px; font-size:0.55em; white-space:nowrap;">Bases de connaissances</span>
              <span style="background:white; color:#333; padding:2px 6px; border-radius:3px; font-size:0.55em;">Solveurs</span>
              <span style="background:white; color:#333; padding:2px 6px; border-radius:3px; font-size:0.55em;">Planificateurs</span>
              <span style="background:white; color:#333; padding:2px 6px; border-radius:3px; font-size:0.55em;">Smart-contracts</span>
            </div>
            <!-- Probabiliste (innermost) -->
            <div style="flex:1; background:#dea08a; border:2px dashed rgba(255,255,255,0.5); border-radius:8px; padding:5px 8px; display:flex; flex-direction:column; justify-content:center; position:relative;">
              <div style="display:flex; align-items:center; gap:6px; margin-bottom:4px;">
                <div style="font-size:0.95em; font-weight:bold;">Probabiliste</div>
                <img src="./images/img_026.png" style="height:35px; background:white; border-radius:4px; padding:2px; object-fit:contain;" />
              </div>
              <div style="display:flex; flex-wrap:wrap; gap:4px; align-content:center;">
                <span style="background:white; color:#333; padding:2px 6px; border-radius:3px; font-size:0.55em;">Modeles graphiques</span>
                <span style="background:white; color:#333; padding:2px 6px; border-radius:3px; font-size:0.55em;">Reseaux de decision</span>
                <span style="background:white; color:#333; padding:2px 6px; border-radius:3px; font-size:0.55em; white-space:nowrap;">Politiques Markoviennes</span>
                <span style="background:#8b5cf6; color:white; padding:2px 6px; border-radius:3px; font-size:0.55em;">Theorie des jeux</span>
              </div>
            </div>
          </div>
        </div>
      </div>
    </div>
  </div>
</div>


---

<img src="./pptx-reference/slide-27.png" style="position:absolute; top:0; left:0; width:100%; height:100%; object-fit:contain;" alt="Intelligence de la recherche - taxonomie" />

---

<img src="./pptx-reference/slide-28.png" style="position:absolute; top:0; left:0; width:100%; height:100%; object-fit:contain;" alt="Intelligence de la pensée logique - taxonomie" />

---

<img src="./pptx-reference/slide-29.png" style="position:absolute; top:0; left:0; width:100%; height:100%; object-fit:contain;" alt="Intelligence de l'incertitude - taxonomie" />

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

<img src="./images/img_028.png" style="display:block; margin:8px auto; max-height:78vh;" alt="Tableau d'exemples d'environnements de tache" />

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

<div v-click="4">

**En pratique**, le monde reel combine les cas les plus difficiles : partiellement observable, stochastique, sequentiel, dynamique, continu, multiagent.

</div>

---

# Types d'environnement: exemples

<img src="./images/img_029.png" style="display:block; margin:8px auto; max-height:78vh;" alt="Tableau de types d'environnement" />

---

# Types d'agents

<img src="./images/img_030.png" style="position:absolute; top:75px; right:20px; width:380px; background:white; padding:6px; border-radius:4px;" alt="Pseudocode agent pilote par table" />

<div style="max-width:55%;">

**f(agent) = Architecture physique + Programme**

**Programme agent pilote par table**

- Taille ? Duree ? Autonomie ?

</div>

<div style="max-width:95%; margin-top:8px;">

Un agent naif pourrait stocker une table "percepts → action" : la table serait gigantesque et impossible a construire.

**Cinq architectures d'agents, par ordre de generalite :**

1. Agent reflexe simple
2. Agent reflexe fonde sur un modele
3. Agent fonde sur des buts
4. Agent fonde sur l'utilite
5. Agent capable d'apprentissage

</div>

---

# Agent reflexe

<img src="./images/img_031.png" style="position:absolute; top:60px; right:20px; width:380px; background:white; padding:4px; border-radius:4px;" alt="Schema agent reflexe" />

<img src="./images/img_032.png" style="position:absolute; bottom:30px; right:30px; width:340px; background:white; padding:4px; border-radius:4px;" alt="Pseudocode agent reflexe" />

<div style="max-width:48%;">

- **Pas de memoire**
- **Percepts courants**
- **Regles Conditions / Actions**

<div v-click="1">

**Intelligence animale**

- Behaviourism
- Artificial Life
- Cellular Automata

</div>

</div>

<img src="./images/img_033.png" v-click="1" style="position:absolute; bottom:30px; left:30px; width:90px;" alt="A New Kind of Science - Wolfram" />


---

# Agent reflexe fonde sur un modele

<img src="./images/img_034.png" style="position:absolute; top:60px; right:20px; width:380px; background:white; padding:4px; border-radius:4px;" alt="Schema agent modele" />

<img src="./images/img_035.png" style="position:absolute; bottom:30px; right:30px; width:320px; background:white; padding:4px; border-radius:4px;" alt="Pseudocode agent fonde sur un modele" />

<div style="max-width:48%;">

**Etat du monde**

- Historique des percepts
- Memoire du changement

<div v-click="1">

**Ex : Subsomption (Brooks)**

- Modele non representatif
- Comportements simples
- Couches d'automates
- Emergence

</div>

</div>

<img src="./images/img_036.png" v-click="1" style="position:absolute; bottom:30px; left:30px; width:90px;" alt="Robot Brooks" />


---

# Agent fonde sur des buts

<img src="./images/img_037.png" style="position:absolute; top:60px; right:20px; width:400px;" alt="Schema agent buts" />

<div style="max-width:55%;">

**Du reactif au deliberatif** : l'agent ne reagit plus seulement a l'instant present, il anticipe le futur.

- Considere les consequences de ses actions
- Planifie des sequences d'actions pour atteindre un objectif
- Utilise la recherche (exploration) et la planification

</div>

---

# Agent fonde sur l'utilite

<img src="./images/img_038.png" style="position:absolute; top:60px; right:20px; width:400px;" alt="Schema agent utilite" />

<div style="max-width:55%;">

**Quand plusieurs chemins menent au but, lequel choisir ?**

- Une **fonction d'utilite** U : Etat → R attribue un score a chaque etat
- L'agent choisit l'action qui maximise l'utilite esperee

**Permet d'arbitrer entre :**
- Probabilite de succes vs importance de l'objectif
- Risque vs recompense, urgence vs cout

</div>

---

# Agent capable d'apprentissage

<img src="./images/img_039.png" style="position:absolute; top:60px; right:20px; width:400px;" alt="Schema agent apprentissage" />

<div style="max-width:55%;">

**Quatre composants internes :**

- **Element de performance** : choisit les actions
- **Element d'apprentissage** : ameliore la performance a partir de l'experience
- **Critique** : evalue les resultats par rapport a un standard fixe
- **Generateur de problemes** : suggere des actions exploratoires

**Formes d'apprentissage :** supervise, par renforcement, non supervise

</div>

---

# Fonctionnement interne des agents

**La representation de la connaissance est determinante**

Trois niveaux de representation des etats, du plus simple au plus expressif :

<div v-click="1">

- **Atomique** : chaque etat est indivisible (ex: un noeud dans un graphe)

</div>
<div v-click="2">

- **Factorise** : un etat est un ensemble de proprietes (ex: variables booleennes)

</div>
<div v-click="3">

- **Structure** : un etat est un objet complexe avec des relations (ex: base de donnees)

</div>

**Compromis fondamental :** plus la representation est riche, plus l'agent est flexible -- mais plus le raisonnement est couteux.

<img src="./images/img_040.png" style="display:block; margin:8px auto; max-height:25vh;" alt="Representations: Atomique, Factorisee, Structuree" />

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

- **Exploration** : `Search/Part1-Foundations/` (11 notebooks), `Search/Part2-CSP/` (9 notebooks), `Sudoku/` (16 notebooks) -- recherche, CSP, algorithmes genetiques, optimisation
- **Logique** : `SymbolicAI/` -- Z3, Tweety, Lean 4, argumentation, smart-contracts
- **Probabilites** : `Probas/Infer/` -- inference bayesienne, réseaux de decision (Infer.NET)
- **Jeux** : `GameTheory/` -- equilibres de Nash, jeux bayesiens, MARL (OpenSpiel)
- **Apprentissage** : `ML/` -- classification, regression, renforcement (ML.NET)
- **IA Generative** : `GenAI/` -- Image (19 notebooks), Audio (16), Video (16), Texte (10)
- **Trading** : `QuantConnect/` -- 28 notebooks + 67 strategies backtestees

> **Depot :** `github.com/jsboige/CoursIA` > dossier `MyIA.AI.Notebooks/`

---
layout: cover
---

# Merci

Jean-Sylvain Boige
jsboige@myia.org
