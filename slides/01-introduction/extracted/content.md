<!-- Slide number: 1 -->
# Intelligence artificielle
1
Enseignant: Jean-Sylvain Boige

MRes CSAI, Sussex University, Brighton UK
Aricie - DNN - PKP
My Intelligence Agency
IA 101

### Notes:

<!-- Slide number: 2 -->
# IA 101
2
Livres
Intelligence artificielle, 3e éditionS. Russell & P. Norvig, Pearson (Pdf)
Classe
Corrections / Projets
Cours
TPs
Projets trimestriels
Equipes de 2-3
Travail transversal
Exposé final en classe

IA 101

### Notes:

<!-- Slide number: 3 -->
# Sommaire
3
Qu’est-ce que l’intelligence artificielle ?
Racines, histoire et état de l’art
Structure des agents rationnel
Intelligence exploratoire
Comment chercher la solution à un problème ?
Intelligence Symbolique
 Comment utiliser le raisonnement et les mathématiques ?
Intelligence probabiliste
 Comment agir dans l’incertitude ?
Intelligence Multi-Agents
Comment tenir compte des autres?
Apprentissage
Comment utiliser les données et l’expérience ?
Application: le langage naturel

![Intelligence artificielle](Picture6.jpg)
Intelligence(s)

### Notes:
Timing?

<!-- Slide number: 4 -->
# Sommaire
4
Présentation du cursus
Introduction
Qu’est-ce que l’intelligence artificielle?
Les domaines d’étude
Un peu d’histoire
L’état de l’art
Systèmes d’agents
Agents rationnels
Environnements tâches
Types d’Agents
Présentation des projets de groupe
IA 101

### Notes:
Timing?

<!-- Slide number: 5 -->
# Objectifs du cours
5
A la fin de ce cours vous pourrez:
Comprendre et utiliser des modèles informatiques de l’intelligence artificielle.
Principaux domaines
Pouvoir approfondir
Concevoir des programmes dans des domaines comme:
La recherche de solutions et les jeux
La représentation de connaissance et le raisonnement
Les systèmes probabilistes
Différentes formes d’apprentissage
Le traitement du langage naturel
Concevoir des systèmes intelligents.
Conditions réelles
Système complet
BONUS: Connaître un peu mieux notre monde
Comment émerge l’intelligence
Comment fonctionne le cerveau humain
Comment réfléchir et agir de façon rationnelle
IA 101

### Notes:
Objectifs ambitieux
Investissement -> réalistes

<!-- Slide number: 6 -->
# Plan du cours
6
Introduction
Résolution de problèmes
Bases de connaissances et logique
Raisonnement probabiliste
Théorie des jeux
Apprentissage
Traitement du langage naturel
Présentations des projets
IA 101

### Notes:
Quid de la semaine de battement en février

<!-- Slide number: 7 -->
# Questions?
7
IA 101

### Notes:

<!-- Slide number: 8 -->
# Introduction à l’intelligence artificielle
8
Présentation du cursus
Introduction
Qu’est-ce que l’intelligence artificielle?
Les domaines d’étude
Un peu d’histoire
L’état de l’art
Systèmes d’agents
Agents rationnels
Environnements tâches
Types d’agents
TP: Mise en place de l’environnement de travail
Présentation des projets de groupe
IA 101

### Notes:

<!-- Slide number: 9 -->
# Qu’est-ce que l’intelligence artificielle?
9
Définitions multiples de l’intelligence et de l’IA
Concevoir != comprendre

![](Image1.jpg)
Définition mouvante:
Automates  Calculateur  Algorithmes  Bases de connaissances  Systèmes experts  Systèmes probabilistes  Apprentissage profond  Generatif ?

IA 101

### Notes:
Comprendre et construire
Période actuelle effervescente
 Grande diversité d’approches

<!-- Slide number: 10 -->
# Qu’est-ce que l’intelligence artificielle?
10
4 types d’approches:

Notre angle principal: « Agir de façon rationnelle »
  Conception d’agents
| Penser comme l’homme | Penser de façon rationnelle |
| --- | --- |
| Agir comme l’homme | Agirde façon rationnelle |
IA 101

### Notes:
Comprendre et construire
Période actuelle effervescente
 Grande diversité d’approches

<!-- Slide number: 11 -->
# Les fondements de l’IA
11
Philosophie	Logique, méthodes de raisonnement, esprit 				physique, apprentissage, langage, raison
Maths 		Représentation formelle et preuve, 					algorithmes, calcul, (in)décidabilité, 					complexité, probabilités
Economie	Utilité, théorie des jeux, la décision, agents 					économiques rationnels
Biologie		Intelligence naturelle et animale
Neurosciences	Substrat physique de l’activité mentale
Psychologie	Comportement, Perception cognition, contrôle 			moteur, techniques expérimentales
Informatique	Origines, ordinateurs puissants et logiciels
Théorie du 	Maximiser une fonction objective        		contrôle	dans le temps
Linguistique	Représentation de connaissances, grammaire

![](Image1.jpg)
IA 101

### Notes:

<!-- Slide number: 12 -->
# Histoire succincte
12
1943     	McCulloch & Pitts: le cerveau comme un circuit logique
1950     	Turing "Computing Machinery and Intelligence"
1956		Rencontre de Dartmouth : "Artificial Intelligence"
1950 - 70	Enthousiasme des débuts
1950s		Premiers programmes, Samuel (jeu de dames) 				Newell & Simon (théoricien logique), 		Gelernter (moteur géométrique), Lisp (Clojure: 2007)
1965		Robinson:  Algorithme complet de raisonnement
1970s	L’IA découvre la complexité calculatoire		La recherche sur les réseaux de neurones calle
1969—79	Systèmes à base de connaissance (s. experts)
1980s 	L’IA devient une industrie (robotique, vision)
1986	 	Retour des réseaux de neurones (rétropropagation)
1990s	L’IA devient une science (neats vs scruffies, Maths)
1995		L’émergence d’agents intelligents, diagnostic, GAs
2000s 	Data mining, reconnaissances, apprentissage bayésien, web 			sémantique
2010s 	Big data, deep learning, chatbots, smart contracts, 			cloud, architectures hybrides

![turing](Picture4.jpg)
IA 101

### Notes:

<!-- Slide number: 13 -->
# Etat de l’art
13
1997 : Echecs - Deep Blue bat Garry Kasparov
Preuve de conjectures mathématiques irresolues (Robbins)
Vol / Conduite / marche autonome
Systèmes de gestion logistique et de planification (guerre du Golfe)
NASA: système embarqué de planification des opérations des vaisseaux
2007: Jeu de dames résolu, Backgammon également
Trading algorithmique (85% du volume en 2012)
2010: Explosion du deep-learning
ImageNet: performances quasi humaines
2014 : GANS - Les réseaux de neurones deviennent imaginatifs
2016 : Jeu de Go - AlphaGo bat Lee Sedol (Google)
TPUs (Google, Nvidia etc.)
2018 : Alpha zero - apprentissage par renforcement (Go/Echecs/Shogi)
2017 : Poker - Libratus bat les joueurs professionnels, puis Deep CRM
2019 : Deepmind: Starcraft 2, Pluribus
2010 : Traitement du langage naturel
LinkedData: sémantisation du web
Raisonneurs et bases de connaissance (IBM Watson, Maths etc.)
Proverb: expert en mots croisés, arg techs,
Transformers: OpenAI: GPT2, Google: Bert
Bots conversationnels: Un nouveau paradigme UX

![](Image10.jpg)

![http://image-net.org/index_files/logo.jpg](Picture16.jpg)
IA 101

### Notes:

<!-- Slide number: 14 -->
# Qui fait de l’IA
14
Recherche académique
CMU, Stanford, Berkeley, MIT, Caltech, U Austin, IDSIA…

Gouvernements et laboratoires privés
NASA, NRL, NIST, IBM, AT&T, SRI, ISI, MERL…

Beaucoup de sociétés
Google, Apple, Microsoft, Facebook, Amazon, Honeywell, Teknowledge, SAIC, MITRE, Fujitsu, Global InfoTek, BodyMedia…

![](Image1.jpg)

![Seal of The University of Texas at Austin](Picture14.jpg)

![The University of California, Berkeley](Picture16.jpg)

![carnegie-mellon-logo](Picture10.jpg)

![About this site](Picture12.jpg)

![bodymedia](Picture7.jpg)

![Google](Picture4.jpg)

![](Image16.jpg)

![Honeywell](Picture6.jpg)

![FUJITSU](Picture9.jpg)

![MITRE](Picture8.jpg)

![](Image4.jpg)

![Microsoft](Picture5.jpg)
IA 101

### Notes:

<!-- Slide number: 15 -->
# Dans la vie de tous les jours
15
Poste
Reconnaissance des adresses et tri du courrier
Banque
Lecture des chèques et vérification des signatures
Evaluation des demandes de crédits
Trading
Service client
Synthèse et reconnaissance vocale, agents conversationnels
Internet
Identification du visiteur / marketing /segmentation
Détection de spam, de fraude
Sécurité
Détection de plaques d’immatriculations et de visages
Jeux
Personnages / adversaires intelligents

IA 101

### Notes:

<!-- Slide number: 16 -->
# Agir comme l’homme: le Test de Turing
16
Turing (1950)
Précis
Compétences
Langage
Représentationde connaissances
Raisonnement
Apprentissage
« Total Turing » (+ caméra)
Vision
Robotique
 Principales disciplines de l’IA
Dont 4 détaillées dans ce cours
Dnn + Portal Keeper: plateforme web d’agents

![turing](Picture4.jpg)
IA 101

### Notes:
Prediction qu’en 2000, une machine aurait 30% de chance de tromper un humain pendant 5 minutes.
Mais cf vols  vs oiseaux, imitation à ses limites

<!-- Slide number: 17 -->
# Penser comme l’homme: sciences cognitives
17
« Révolution cognitive » (1960s): Psychologie comme traitement de l’information
Théories scientifique de l’activité du cerveau humain
Modèles du comportement humain (top-down)
Observation de l’activité neurologique (bottom-up)
Deux approches aujourd’hui distinctes de l’IA.
Les hommes sont souvent irrationnels
Le reverse-engineering est difficile à faire
Le « hardware » est différent de ce qu’offre l’informatique
IA 101

### Notes:
Introspection, experiences psychologiques, et imagerie

<!-- Slide number: 18 -->
# Penser de façon rationnelle: lois de la raison
18
Aristote: Quels sont les arguments corrects?
Règles de dérivations pour la pensée
En lien par les maths et la philosophie (Logique) à l’IA
Représentation des faits du monde
Inférence logique pour raisonner sur ces faits
Ex: prouveurs de théorèmes
Problèmes:
Incertitude du monde (capteurs)
Tout comportement intelligent n’est pas le résultat d’une délibération logique
Quelles sont de « bonnes » pensée? Monde réel  Définir des buts, évaluer des coûts…
IA 101

### Notes:
Several Greek schools developed various forms of logic: notation and rules of derivation for thoughts; may or may not have proceeded to the idea of mechanization

<!-- Slide number: 19 -->
# Agir de façon rationnelle: l’agent
19
Comportement rationnel: faire la bonne chose:
Celle dont on espère qu’elle maximisera les chances d’atteindre l’objectif, compte tenu de l’information disponible.
N’implique pas forcément de penser (ex. clignement, réflexes)
mais penser sert la rationalité de l’action
Théorie de la décision / Economie
Evaluation des états et des actions possibles
Maximisation de l’utilité des états résultants
Utilité espérée si incertaine
IA 101

### Notes:

<!-- Slide number: 20 -->
# Questions?
20
IA 101

### Notes:

<!-- Slide number: 21 -->
# Systèmes d’agents
21
Présentation du cursus
Introduction
Qu’est-ce que l’intelligence artificielle?
Les domaines d’étude
Un peu d’histoire
L’état de l’art
Systèmes d’agents
Agents rationnels
Environnements tâches
Types d’agents
TP: Mise en place de l’environnement de travail
Présentation des projets de groupe
IA 101

### Notes:

<!-- Slide number: 22 -->
# Les agents
22
Un agent est une entité qui
perçoit son environnement par des capteurs
et agit sur lui par des effecteurs.
Abstraction:
Fonction d’agent: de l’historique des perceptions (percepts)  vers les actions:	[f: P*  A]

![](Image6.jpg)
Intelligence(s)

### Notes:
 design best program for given machine resources

<!-- Slide number: 23 -->
# Les agents rationnels
23
« La bonne action »: celle qui maximise le succès.
Mesure de la performance
Critère objectif de succès.
Maximisation de la mesure de performance
A partir de la suite de percepts et de l’état de connaissance.
Rationnel != omniscient
Réactivité, Proactivité
Exploration =  modification des percepts
Interaction, Autonomie
Comportement issu de l’expérience
Environnement limité:
la rationalité parfaite n’est souvent pas atteignable.
Objectif = les meilleures performances
(compte tenu des ressources disponibles)
Intelligence(s)

### Notes:
 design best program for given machine resources

<!-- Slide number: 24 -->
# Les agents rationnels
24
« La bonne action »: celle qui maximise le succès.
Mesure de la performance
Critère objectif de succès.
Maximisation de la mesure de performance
A partir de la suite de percepts et de l’état de connaissance.
Rationnel != omniscient
Réactivité, Proactivité
Exploration =  modification des percepts
Interaction, Autonomie
Comportement issu de l’expérience
Environnement limité:
la rationalité parfaite n’est souvent pas atteignable.
Objectif = les meilleures performances
(compte tenu des ressources disponibles)
Intelligence(s)

### Notes:
 design best program for given machine resources

<!-- Slide number: 25 -->
# Intelligences
25
Procédurale

![](Image20.jpg)
Automates
Algorithmes

![Une image contenant texte, carte Description générée automatiquement](Image22.jpg)

![Une image contenant texte Description générée automatiquement](Image15.jpg)

![](Image18.jpg)
Intelligences

### Notes:

<!-- Slide number: 26 -->
Intelligences
Procédurale

![](Image9.jpg)
Automates
Algorithmes

![Une image contenant texte, carte Description générée automatiquement](Image14.jpg)

![Une image contenant texte Description générée automatiquement](Image12.jpg)

![](Image13.jpg)

<!-- Slide number: 27 -->
# Intelligence de la recherche
27
Intelligences

<!-- Slide number: 28 -->
# Intelligence de la pensée logique
28
Intelligences

<!-- Slide number: 29 -->
# Intelligence de l’incertitude
29
Intelligences

<!-- Slide number: 30 -->
# Environnement de tâche
30
Description PEAS:
Mesure de Performance
Environnement
Effecteurs (Actuators)
Capteurs (Sensors)
Exemple: Taxi
Performance:
 Prudent, rapide, légal, confortable, rentable
Environnement:
Route, trafic, piétons, clients, véhicule
Effecteurs:
Volant, accélérateur, frein, clignotants, klaxon
Capteurs:
caméras, sonar, accéléromètre, GPS, Lidar, clavier etc.
Intelligence(s)

### Notes:
 design best program for given machine resources

<!-- Slide number: 31 -->
# Environnements de tâche: exemples
31

![](Image1.jpg)
IA 101

### Notes:
 design best program for given machine resources

<!-- Slide number: 32 -->
# Types d’environnement
32
Complètement vs partiellement observable
Etats de l’environnement
Déterministe vs stochastique
Evolution complètement déterminée par l’état précédent et les actions
Déterministe sauf actions des autres = stratégique
Episodique vs séquentiel
Episodes atomiques indépendants
Statique vs Dynamique
Change pendant la délibération (score = semi-dynamique)
Discret vs continu
Atomicité des états, du temps, des percepts, des actions
Agent simple vs multiagent
Concurrentiel vs coopératif
Communication vs aléatoire
Connu vs inconnu
Monde réel  cas complexes
IA 101

### Notes:
 design best program for given machine resources

<!-- Slide number: 33 -->
# Types d’environnement: exemples
33

![](Image1.jpg)
IA 101

### Notes:
 design best program for given machine resources

<!-- Slide number: 34 -->
# Types d’agents
34
f (agent) = Architecture physique + Programme
Programme agent piloté par table

Taille?
Durée?
Autonomie?
Types dans l’ordre de généralité:
Agent réflexe
Agent réflexe fondés sur un modèle
Agent fondé sur des buts
Agent fondé sur l’utilité
+ Agent apprenant

![](Image1.jpg)
IA 101

### Notes:
 design best program for given machine resources

<!-- Slide number: 35 -->
# Agent réflexe
35
Pas de mémoire
Percepts courants
Règles
Conditions / Actions
Intelligence animale
Behaviourism
Artificial Life
Cellular Automata

![](Image8.jpg)

![](Image10.jpg)

![](Image9.jpg)
IA 101

### Notes:
 design best program for given machine resources

<!-- Slide number: 36 -->
# Agent réflexe fondé sur un modèle
36
Etat du monde
Historique des percepts
Mémoire du changement
Ex: Subsomption (Brooks)
Modèle non représentatif
Comportements simples
Couches d’automates
Emergence

![](Image4.jpg)

![](Image6.jpg)

![](Image8.jpg)
IA 101

### Notes:
 design best program for given machine resources

<!-- Slide number: 37 -->
# Agent fondé sur des buts
37
Réactif  Délibératif
Considération du Futur, séquences d’actions
Exploration, planification

![](Image1.jpg)
IA 101

### Notes:
 design best program for given machine resources

<!-- Slide number: 38 -->
# Agent fondé sur l’utilité
38

Alternatives ?
Niveau de succès
Quantitatif
Fonction U
Etat  R
Arbitrages
Chance de succès
Important
Urgent
…

![](Image3.jpg)
IA 101

### Notes:
 design best program for given machine resources

<!-- Slide number: 39 -->
# Agent capable d’apprentissage
39

Modules
Performance
Apprentissage
Critique
Générateur de problème
Plusieurs formes
Direct
Récompense
Non supervisé

![](Image1.jpg)
IA 101

### Notes:
 design best program for given machine resources

<!-- Slide number: 40 -->
# Fonctionnement interne des agents
40
Représentation de la connaissance importante

Niveau de représentation des Etats
Atomique
Indivisible
Factorisé
Propriétés
Structurée
Modèle / DB

Compromis
Flexibilité vs complexité

![](Image3.jpg)
IA 101

### Notes:
 design best program for given machine resources

<!-- Slide number: 41 -->
# Résumé
41
Intelligence artificielle
Plusieurs approches / objectifs
Nombreux fondements
Logique, décision, comportement, langage, adaptation etc.
Histoire à rebondissements
Progrès récents pratiques et théoriques
Agents
Perçoit et Agit dans un Environnement
Rationnel  Succès  Performance
Types d’environnements de tâches
Agents réflexes, simple ou basé sur un modèle
Agents fondés sur des buts (qualitatif) ou l’utilité (quantitatif)
Capables d’apprentissage (+ critique et générateur de problème)
Etats atomiques, factorisés, structurés

IA 101

### Notes:
 design best program for given machine resources

<!-- Slide number: 42 -->
# Plan du cours
42
Introduction
Résolution de problèmes
Bases de connaissances et logique
Raisonnement probabiliste
Apprentissage
 Traitement du langage naturel
Présentations projets
IA 101

### Notes:

<!-- Slide number: 43 -->
# Merci
43
Jean-Sylvain Boige
jsboige@myia.org
IA 101

### Notes: