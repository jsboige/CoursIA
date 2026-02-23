<!-- Slide number: 1 -->
# Intelligence(s)
1
Jean-Sylvain Boige

jsboige@myia.org

Telecom Bretagne
Cogs, Brighton UK
Aricie - DNN - PKP

![](Image6.jpg)

![DNN.png](Picture6.jpg)

![](Image5.jpg)
Intelligence(s)

### Notes:

<!-- Slide number: 2 -->
# Sommaire
2
Qu’est-ce que l’intelligence artificielle ?
Racines, histoire et état de l’art
Structure des agents rationnel
Intelligence exploratoire
Comment chercher la solution à un problème ?
Intelligence Symbolique
 Comment utiliser le raisonnement et les mathématiques ?
Intelligence probabiliste
 Comment agir dans l’incertitude ?
Apprentissage
Comment utiliser les données et l’expérience ?
Application: le langage naturel

![](Image1.jpg)
Intelligence(s)

### Notes:
Timing?

<!-- Slide number: 3 -->
# Intelligence artificielle
3
Introduction
Agents rationnels
Intelligences

Intelligence(s)

### Notes:

<!-- Slide number: 4 -->
# Qu’est-ce que l’intelligence artificielle?
4
Définitions multiples

Notre angle :
« Agir de façon rationnelle »
 Conception d’agents

Fondements
Philosophie
Maths
Economie
Biologie
Neurosciences

Psychologie
Informatique
Théorie du contrôle
Linguistique
| Penser comme l’homme | Penser de façon rationnelle |
| --- | --- |
| Agir comme l’homme | Agirde façon rationnelle |

![](Image17.jpg)
Intelligence(s)

### Notes:
Définitions multiples de l’intelligence et de l’IA
Concevoir != comprendre
Définition mouvante:
Automates  Calculateur  Algorithmes  Bases de connaissances  Systèmes experts  Apprentissage profond  ?
4 types d’approches:
Notre angle principal: « Agir de façon rationnelle »
Conception d’agents
Philosophie	Logique, méthodes de raisonnement, esprit physique, apprentissage, langage, raison
Maths 		Représentation formelle et preuve, algorithmes, calcul, (in)décidabilité, complexité, probabilités
Economie	Utilité, théorie des jeux, la décision, agents économiques rationnels
Biologie		Intelligence naturelle et animale
Neurosciences	Substrat physique de l’activité mentale
Psychologie	Comportement, Perception cognition, contrôle moteur, techniques expérimentales
Informatique	Origines, ordinateurs puissants et logiciels
Théorie du 	Maximiser une fonction objective contrôle	dans le temps
Linguistique	Représentation de connaissances, grammaire

<!-- Slide number: 5 -->
# Développement
5
Histoire succincte
Etat de l’art
1997 : Echecs - Deep Blue
2000s: Prouveurs
Maths, logistique, planification,
Navigation/ marche autonome
2007: Jeu de dames
Backgammon
Algotrading: 95% des échanges
2010s: Explosion du deep-learning
2014 : GANS
2016 : AlphaGo
2018 :Alpha zero
2017 : Libratus
2019 : Starcraft 2, Pluribus
Traitement du langage naturel
LinkedData, Raisonneurs
Bots conversationnels
Transformers, Large Language Models
1940 - 70 Enthousiasme des débuts
McCulloch & Pitts: cerveau = circuit logique
Turing "Computing Machinery and Intelligence"
Rencontre de Dartmouth : "Artificial Intelligence"
Samuel (jeu de dames), Newell & Simon (logique), Gelernter (géométriie), Lisp, Robinson (raisonneur)
1970s - Complexité calculatoire
La recherche sur les réseaux de neurones calle
Systèmes à base de connaissance (s. experts)
1980s - L’IA devient une industrie
Robotique, vision
1986 - Retour des réseaux de neurones (rétropropagation)
1990s - L’IA devient une science
Neats vs scruffies, Maths
1995 - Agents intelligents, diagnostic, GAs
2000s - Data mining, reconnaissances, apprentissage bayésien, web sémantique
2010s 	L’IA explose
Big data, deep learning,
Chatbots, smart contracts,
Cloud, architectures hybrides

![](Image9.jpg)

![turing](Picture4.jpg)

![http://image-net.org/index_files/logo.jpg](Picture16.jpg)
IA 101

### Notes:
Ne pas passer trop de temps sur les jeux (pas des gamers)

<!-- Slide number: 6 -->
# Dans la vie de tous les jours
6

Poste

Banque

Médecine

Service client

Transport

Internet

Transport

Industrie

Image numérique

Jeux

Données…
Intelligence(s)

### Notes:
Poste
Reconnaissance des adresses et tri du courrier
Banque
Lecture des chèques et vérification des signatures
Evaluation des demandes de crédits
Médecine
Diagnostic
Prescriptions, procédures
Suivi, prévention
Service client
Synthèse et reconnaissance vocale
Chatbots
Internet
Identification du visiteur / marketing
Détection de spam, de fraude
Transport
Détection de plaques d’immatriculations, de véhicules
Conduite autonome
Industrie
Conception, fabrication, exploitation
Image numérique
Détection de visages, mise au point, compression
Jeux
Personnages / adversaires intelligents
Données…

<!-- Slide number: 7 -->
# Les agents
7
Définition
L’agent rationnel
Entité qui
perçoit par des capteurs
agit par des effecteurs.
Dans un environnement

Fait la bonne action
Maximise son succès.
Pas omniscient
Réactif, proactif, interactif, autonome
Limitations
ressources disponibles

![](Image6.jpg)
Intelligence(s)

### Notes:
« La bonne action »: celle qui maximise le succès.
Mesure de de la performance
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
 Objectif = les meilleures performances
Compte tenu des ressources disponibles
Rationalité humaine
Normatif (logique)  Conséquentialiste (succès cognitif)

<!-- Slide number: 8 -->
# Conception d’agents
8
Environnement de tâche
Agent réflexe
Description PEAS
Pas de mémoire
Percepts courants
Règles
Conditions / Actions

![](Image8.jpg)

![](Image7.jpg)
Intelligence(s)

### Notes:
Insister sur le cas pratique (e.g. Elon Musk)
 design best program for given machine resources

<!-- Slide number: 9 -->
# Quiz
9
Taxi autonome:
Description Peas
Intelligences

<!-- Slide number: 10 -->
# Agent réflexe fondé sur un modèle
10
Agent réflexe avec modèle
Fonctionnement interne
Etat du monde

Niveau de représentation

Compromis
Flexibilité vs complexité

![](Image6.jpg)

![](Image9.jpg)
Intelligence(s)

### Notes:
(virer?)
 design best program for given machine resources

<!-- Slide number: 11 -->
# Intelligences
11
Procédurale

![](Image20.jpg)
Automates
Algorithmes

![Une image contenant texte, carte Description générée automatiquement](Image22.jpg)

![Une image contenant texte Description générée automatiquement](Image15.jpg)

![](Image18.jpg)
Intelligences

<!-- Slide number: 12 -->
# Questions?
12
Intelligence(s)

### Notes:

<!-- Slide number: 13 -->
# Intelligence exploratoire
13

Recherches non informée et informée
Jeux
Problèmes à satisfaction de contraintes
Intelligence(s)

### Notes:

<!-- Slide number: 14 -->
# Agent explorateur
14
Agent fondé sur des buts
Résolution de problèmes
Réactif  Délibératif
Exploration, plan

Objectif ?
Actions ?
Représentation ?

![](Image7.jpg)

Etat
Final
EtatInitial
Actions
Intelligence(s)

### Notes:
 design best program for given machine resources

<!-- Slide number: 15 -->
# Formulation de problèmes
15
Itinéraire
Abstractions

![romania-distances](Picture4.jpg)
Assemblage robotique

Problèmes jouets

![stanford-arm+blocks](Picture4.jpg)
Etat initial, test de but
Transitions
Etats, Actions
Coût de chemin
Solution = Séquence

![](Image14.jpg)

![](Image11.jpg)
Intelligence(s)

### Notes:

<!-- Slide number: 16 -->
# Arbre d’exploration
16
Idée de base
Exemple: Enigme

![Une image contenant texte Description générée automatiquement](Image4.jpg)
Développement
des états successeur
Choix des nœuds= Stratégie d’exploration
Missionnaires et cannibales
Barque de 2 places
Jamais + de cannibales

![](Image13.jpg)

![](Image1.jpg)
Intelligence(s)

<!-- Slide number: 17 -->
# Quiz
17
Missionnaires et cannibales
Intelligences

<!-- Slide number: 18 -->
# Stratégies d’exploration
18
Non informées
Informées
En largeur

En profondeur

Ex: Où sont mes clefs ?
Bidirectionnelle

Evaluation des états
Heuristique
Estimation du coût restant
Ex: Distance à vol d’oiseau

Par le meilleur d’abord
Exploration gloutonne
Algorithme A*
Demo Pathfinding.js
Exploration locale

![](Image10.jpg)

![f-circles](Picture4.jpg)

![](Image11.jpg)

![](Image12.jpg)
Intelligence(s)

<!-- Slide number: 19 -->
# Exploration locale
19
Si seule la solution compte
pas le chemin
Modification d’un seul état
Espaces plus complexes

Paysage de l’espace des états
Optimisation d’une fonction
Escalade, descente de gradient

Problèmes :
Bloqué sur un optimum local
Solutions:
Recuit simulé
Ex: le carton de babioles
Exploration en faisceaux
Ex: Perdus en foret
Sélection naturelle = combinaison
Algorithmes génétiques

![4queens-sequence](Picture4.jpg)

![genetic](Picture4.jpg)

![](Image4.jpg)

![8queens-crossover](Picture4.jpg)

### Notes:
Démo GeneticSharp

<!-- Slide number: 20 -->
# Jeux
20
Jeux vs Exploration
Arbre de jeu
Environnements
multi-agents, concurrentiels
Classe la plus étudiées
Alternés, déterministes
A somme nulle (h1 = -h2)
A information parfaite
Difficulté
Arbre d’exploration impraticable
 Performance critique: temps
Stochastiques, information imparfaite
Libratus (poker), Starcraft 2
Arbre Minimax
Actions joueurs Max et Min + utilité terminale

Techniques
Minimax, Alpha-Beta
Avec arrêt + évaluation heuristique
Techniques probabilistes
Expectiminimax
Méthodes de Monte-Carlo

![tictactoe](Picture4.jpg)
Intelligences

<!-- Slide number: 21 -->
# Problèmes à satisfaction de contraintes
21
Définition CSPs
Techniques
Jusqu’ici: représentation atomique

CSP = Etat factorisé
Etat = variables  sur des domaines
Test de but = contraintes sur les variables
Bonnes méthodes générales
Meilleures que l’exploration standard
Exemple
Coloration de carte
Exploration avec heuristiques
H1 ?
H2 ?
H3 ?
Ex: le coffre de voiture
Inférence
Mise en cohérence des domaines
Ex: Sudoku
Structure des problèmes
Sous-problèmes
Arbres
Structure des valeurs
Symétrie (rupture de)

![Une image contenant texte Description générée automatiquement](Image16.jpg)

![](Image7.jpg)

![](Image13.jpg)

![australia-most-constrained-variable](Picture4.jpg)

![australia-most-constraining-variable](Picture4.jpg)

![australia-least-constraining-value](Picture4.jpg)
Intelligence(s)

### Notes:
Se concentrer sur le coffre de voitureMinimum de valeurs restantes
Variable la + contraignante
Valeur la – contraignante

<!-- Slide number: 22 -->
# Questions?
22
Intelligence(s)

### Notes:

<!-- Slide number: 23 -->
# Intelligence symbolique
23

Logique propositionnelle
Logique du premier ordre
Agents fondés sur la connaissance
Planification

Intelligence(s)

### Notes:
Faire 1 slide des 3 suivants, se concentrer sur les exemples

<!-- Slide number: 24 -->
# Représentation et logique
24
Bases de connaissances
Raisonnement

![](Image3.jpg)
Inférence

Propriétés
correction, consistance, complétude

![](Image4.jpg)
Enoncés
Langage
Syntaxe
Sémantique
Types de logiques

Modale

Logiques non-monotones
Logiques polyvalentes
Temporelle

Logiques probabilistes
d’ordre supérieur
Logique du Premier ordre
Logique floue
Logique Propositionnelle
Intelligence(s)

### Notes:

<!-- Slide number: 25 -->
# Logique propositionnelle
25
Inférence logique
Règles cohérentes
Ex: Modus ponens
Preuve déductive

Procédures
Chainages
Résolution
DPLL
WalkSAT

Solveurs SAT
Problèmes NP-complets
Syntaxe

Sémantique
Tables de vérité

![](Image2.jpg)

![](Image11.jpg)

![](Image12.jpg)

![img19](Picture3.jpg)

![](Image3.jpg)
Intelligence(s)

<!-- Slide number: 26 -->
# Logique du premier ordre (FOL)
26
Modélise
Objets, Propriétés
Relations, Fonctions

Quantificateurs:
Il existe x - x
Pour chaque x - x
Sémantiques multiples
 de base de données
Exemple: investigation
« la loi stipule que c’est un crime pour un américain de vendre des armes à des nations hostiles. La Corée du Nord, un ennemi de l’Amérique, possède des missiles et tous ses missiles lui ont été vendus par le colonel West, qui est américain »

![](Image9.jpg)
Missile(x) ET Possède(Corée, x) => Vend(West, x ,Corée)
Missile(x) => Arme(x)
Enemy(x,America) => Hostile(x)
Américain(x) ET Arme(y) ET Vend(x,y,z) ET Hostile(z) => Criminel(x)
Intelligence(s)

<!-- Slide number: 27 -->
# Application: argumentation
27
Code de conduite
Qu’est-ce qu’un argument?
Standards
procédural efficace
éthique important
Principes de conduite intellectuelle
Faillibilité
Recherche de la vérité
Clarté
Charge de la preuve
Charité
Structure, Pertinence, Acceptabilité, Suffisance, Réfutation
Suspension du jugement
Résolution
Une proposition (conclusion) supportée par
D’autres proposition (Prémisses)
Le raisonnement
Argument =/= Opinion
Déduction vs Induction
Déduction  nécessité logique
Induction  Corroboration
Prémisses particulières
Argument Moral  principe
Légal  loi, jurisprudence etc.
Esthétique  critère
Intelligence(s)

<!-- Slide number: 28 -->
# Analyse rhétorique
28
Un bon argument
Un argument fallacieux
Respecte 5 critères
Structure bien formée
Prémisse pertinentes
pour la vérité de la conclusion
Prémisses acceptables
par une personne raisonnable
Prémisses suffisantes
à démontrer la conclusion
Fournissant une réfutation effective
des critiques anticipées
Renforcer un argument
Balayer ces 5 critères
Viole l’un des critères
Taxonomie

Comment le dénoncer
Reconstruction standard
Contre-exemple absurde
Fair-play

![Une image contenant objet Description générée avec un niveau de confiance élevé](Image8.jpg)

![Une image contenant texte Description générée automatiquement](Image9.jpg)
Intelligence(s)

### Notes:
Ne pas passer trop de temps sur la taxonomie, passer sur le Jeu rapidement

<!-- Slide number: 29 -->
# Application: Planification
29
Expression de problème
Approches
Langage formel

But à atteindre
Listes des opérations
Exploration des états, plans
Heuristiques ?
Calcul situationnel
Théorèmes en FOL
Planification par contraintes
Planification à Ordre partiel
Décomposition hiérarchique

![Une image contenant texte Description générée automatiquement](Image12.jpg)

![](Image10.jpg)

![fig12](Picture3.jpg)

![](Image8.jpg)

![](Image11.jpg)
Intelligence(s)

### Notes:
Zapper

<!-- Slide number: 30 -->
# Autres Applications
30
Systèmes à maintenance de vérité (TMS)
Révision des croyances
JTMS, ATMS: justice
Générateurs d’hypothèses
Smart-contracts
Cryptographie
Blockchain
Non-divulgation
Solveurs Modulo Théorie
SAT + Quantificateurs
+ Théories arithmétiques
+ Optimiseurs
Ingénierie de connaissances
Triplets, Ontologies
Web sémantique
W3C

Linked Data

![](Picture4.jpg)

![Résultat de recherche d'images pour "smart contract"](Picture2.jpg)

![Résultat de recherche d'images pour "linked data"](Picture4.jpg)
CS 405

### Notes:
Simplifier pour le public, Passer vite sur les formats de l’ingénierie de connaissance
insister sur smart-contracts

<!-- Slide number: 31 -->
# Questions?
31
Intelligence(s)

### Notes:

<!-- Slide number: 32 -->
# Intelligence probabiliste
32

Quantification de l’incertitude
Raisonnement probabiliste
Prise de décision
Théorie des jeux

Intelligence(s)

### Notes:

<!-- Slide number: 33 -->
# Agir dans l’incertitude
33
Le monde est incertain
Agent fondé sur l’utilité
Entrées incertaines
Données manquantes,  bruitées
Connaissance incertaine
Causalités complexes
Environnement stochastique
Sorties incertaines
Abduction, induction
Inférence incomplète
Raisonnement probabiliste
Résultats probabilistes
Alternatives
Niveau de succès espéré

![](Espaceréservéducontenu5.jpg)
Intelligence(s)

### Notes:
Exemple Rainman

<!-- Slide number: 34 -->
# Probabilité
34
Fondements
Programmation probabiliste
Résument
Paresse
Ignorance
Probabilités subjectives
Changent % observations
Règle de Bayes
Diagnostic
P(Cause | Effet) = P(Effet | Cause) x P(Cause) / P(Effet)

Réseau Bayésien naïf
Attributs indépendants

Modèles graphiques
Indépendance conditionnelle

Facteurs de distributions continues

![naive-bayes](Picture4.jpg)

![burglary2](Picture4.jpg)

![](Image13.jpg)
Intelligence(s)

### Notes:
Faire 1 slide avec le suivant (exemple météo, ne pas rentrer dans le détail Markov & co)

<!-- Slide number: 35 -->
# Réseaux bayésiens dynamiques
35
Chaînes de Markov
Applications
Traitement du langage naturel
Classification
Extraction
Reconnaissance
Traduction
Google 1.0: Page rank
Suivi de trajectoire
Météo, radars, économie etc.
Filtres de Kalman

Apprentissage
Indépendance conditionnelle
Passé
Futur

Modèle de transition
Probabiliste
Distributionstationnaire

Chaînes de Markov cachées
Observations bruitées

![](Picture2.jpg)

![](Picture2.jpg)

![Une image contenant texte Description générée automatiquement](Image30.jpg)

![](Image32.jpg)

![Une image contenant texte Description générée automatiquement](Image3.jpg)
B
E

A

C

Inducteur

![](Picture2.jpg)

<!-- Slide number: 36 -->
# Prise de décision
36
Théorie de la décision
Que faire?
Théorie des probabilités
Que croire ?
Théorie de l’utilité
Que vouloir ?
Utilité de l’argent
Goût du risque ?
Prime
Utilité espérée
biaisée (malédiction)
+ Humains pas rationnel
Prise de décision simple
Réseaux de décision

Décision complexe
Processus de Markov
Politique optimale

![](Image12.jpg)

![Une image contenant texte Description générée automatiquement](Image7.jpg)

![](Image11.jpg)

![](Image13.jpg)

![](Image14.jpg)

![Une image contenant texte Description générée automatiquement](Image6.jpg)
Intelligence(s)

### Notes:
Insister sur les exemples.Ordonnancement
Transitivité
Continuité
Substituabilité
Monotonie
Décomposabilité
Effet de certitude,
Régression fallacieuse,
évitement d’ambiguïté,
effet de cadrage
effet d’ancrage

<!-- Slide number: 37 -->
# Théorie des jeux
37
Environnement multi-agents
Analyse stratégique

![](Image10.jpg)
Jeux simultanés
Matrice de gains
Dominance
Equilibres de Nash
Purs et mixtes (2n+1)
Topologie
Jeux séquentiels
Plusieurs manches
Forme extensive
Crédibilité
Punitions
Menaces
Promesses
Induction
avant/arrière

Interdépendances stratégiques

Design d’agent
Quelle stratégie?
Design de mécanisme
Quelles règles?
Optimisation de stratégies
Solution = profil de stratégies
Pures (déterministes)
Mixtes (probabilistes)
Utilité espérée

![](Image15.jpg)

![Une image contenant texte Description générée automatiquement](Image11.jpg)

![](Image6.jpg)

![](Image13.jpg)
CS 405

### Notes:
Aller plus vite, se concentrer sur les exemples

<!-- Slide number: 38 -->
# Extensions
38
Extensions
Algorithmes
Espaces infinis
Hotelling
Jeux Bayésiens
Information incomplète
Jeux de signalisation
Jeux différentiels
Equilibres approchés
ε-équilibres
Minimisation de regret contrefactuel
Cepheus
Libratus
Deepstack

![](Image6.jpg)

![Une image contenant ciel, lumière Description générée automatiquement](Image15.jpg)

![](Image12.jpg)
Intelligences

### Notes:
Faire 1 slide des 3 avec Exemple de Bayrou

<!-- Slide number: 39 -->
# Conception de mécanismes
39
Concepts
Résultats
Théorie des jeux inverse
Quelles bonnes règles ?
Max d’une utilité globale?

Principe de révélation
Mécanismes manipulables
Non-stratégiques
Enchères de Vickrey
Tragédie des communs
Taxe carbone
Conditions byzantines
Bitcoin
Stratégies sociétales
Evolution de la confiance

![Une image contenant texte Description générée automatiquement](Image8.jpg)

![Une image contenant texte, carte Description générée automatiquement](Image9.jpg)

![](Image12.jpg)
Intelligence(s)

<!-- Slide number: 40 -->
# Décisions collectives
40
Théorie du choix social
Théorie de la négociation

![](Image9.jpg)
Théorie des votes
Résultats négatifs
Critère de Condorcet
Electeur médian
Méthodes de Condorcet
Schulze
Autres bon Scrutins
Vote par assentiment
Jugement majoritaire
Scrutin bipartipludique

![Une image contenant texte Description générée automatiquement](Image10.jpg)
Intelligences

### Notes:

<!-- Slide number: 41 -->
# Quiz
41
Présidentielles: vainqueur de Condorcet
Intelligences

<!-- Slide number: 42 -->
# Questions?
42
Intelligence(s)

### Notes:

<!-- Slide number: 43 -->
# Apprentissage
43

Apprentissage supervisé
Arbres de décision
Deep learning
Modèles non-paramétriques
Apprentissage et connaissances
Apprentissage par renforcement

Intelligence(s)

### Notes:

<!-- Slide number: 44 -->
# Apprentissage
44
Enjeux
Structure d’agent
Environnements inconnus
Méthode de conception de systèmes
Améliorer la prise de décision
Les performances
Modules
Performance
Apprentissage
Critique
Générateur de problème

![](Image10.jpg)
Intelligence(s)

### Notes:
En parler au début (chatpGPT & co), diminuer de moitié les slides

<!-- Slide number: 45 -->
# Caractéristiques
45
Composants d’apprentissage
Apprentissage inductif
Nature affectée par
Environnement / données
Connaissance a priori / modèles
Feedback pour apprendre
Type d’apprentissage
Inductif
Déductif
Type de feedback:
Supervisé: les réponses correctes
Non-supervisé: clusters
Par renforcement: récompenses
On construit une hypothèse
h consistante avec les données

Ensemble de sortie
Classification
Régression
Rasoir d’Occam
Parcimonie
Entraînement
Validation
Méthodes d’ensemble
 Boosting

![curve-fitting1c](Picture4.jpg)

![curve-fitting5c](Picture2.jpg)

![curve-fitting4c](Picture6.jpg)

![](Image11.jpg)
Intelligence(s)

### Notes:
Passer vite

<!-- Slide number: 46 -->
# Arbres de décision
46
Principe
Techniques
Attributs  Décision

A partir d’exemples

Ordre des attributs
Gain entropique

Compacité
Elagage
Régression
Quantisation
Random forest
Ensemble

![](Image8.jpg)

![](Image12.jpg)

![Une image contenant texte, carte Description générée automatiquement](Image14.jpg)

![](Image9.jpg)
Intelligence(s)

### Notes:

<!-- Slide number: 47 -->
# Classification
47
Utilisation de dimensions supérieures
Classification linéaire

![](Espaceréservéducontenu3.jpg)

![](Image4.jpg)

<!-- Slide number: 48 -->
# Réseaux de neurones artificiels
48
Inspiration biologique

Neurone artificiel
Fonctions d’activation

Multi-couches

Expressivité croissante

![](Image11.jpg)

![](Image3.jpg)

![](Image6.jpg)

![](Espaceréservéducontenu5.jpg)

![](Image7.jpg)

![](Image8.jpg)

<!-- Slide number: 49 -->
# Apprentissage profond
49
Réseaux convolués
Noyaux de convolution

Sous-échantillonnage
Réseaux profonds
Multicouche traditionnel classifier

Hiérarchies naturelles
Pixel, bord, teston, motif, partie, objet
Caractère, mot, groupe, clause, phrase, histoire

![](Image16.jpg)

![](Image14.jpg)

![](Image17.jpg)

![](Image15.jpg)

<!-- Slide number: 50 -->
# Extensions 2010+
50
Réseaux récurrents

Mémoire à court terme

Réseaux LSTM
MAJ d’un état de cellule

Réseaux résiduels
Réinjection des entrées

GANs
Réseaux adversériaux

![](Image6.jpg)

![](Image9.jpg)

![](Image8.jpg)

![](Image12.jpg)

![](Picture2.jpg)

![](Image7.jpg)
CS 405

<!-- Slide number: 51 -->
# Extensions 2015+
51
Réseaux attentionnels
Economiede ressources
Séquences

Transformers
Multi-têtes
Semi-supervisé
Transfert
LLMs
Bert, GPT
Modèles Bayésiens
Régularisation
Ex: Auto-encodeurs Var.

Graph Neural Networks
Généralisation géométrique

Agrégation de voisinage

![Une image contenant herbe, extérieur, jeune, champ Description générée automatiquement](Image6.jpg)

![](Image9.jpg)

![](Image7.jpg)

![](Image16.jpg)

![](Image12.jpg)

![](Image14.jpg)
Intelligences

<!-- Slide number: 52 -->
# Extensions 2020+
52
Modèles multimodaux
E.g Texte+Image
Datasets

Encodeurs
Rapprochement des plongements
Modèles de diffusion
Prédiction d’un bruit

Diffusion latente
Autoencodeur Variationnel
Conditionnement multimodal
Mécanisme attentionnel

![](Image8.jpg)

![](Image6.jpg)

![](Image9.jpg)

![](Image7.jpg)
Intelligences

<!-- Slide number: 53 -->
# Apprentissage non paramétrique
53
Principes
Machines à vecteurs de support
Jusque là, paramétrique
Arbres de décisions, NNs
Ici, par les instances
Les données servent à prédire
K Plus proches voisins
Noyaux de pondérations

Séparateurs à marge maximale

Astuce du noyau

![](Image11.jpg)

![](Image10.jpg)

![](Image6.jpg)

![Une image contenant texte, carte Description générée automatiquement](Image12.jpg)
Intelligences

<!-- Slide number: 54 -->
# Apprentissage et connaissances
54
Utilisation de la connaissance
Passé + futur
Construction d’un énoncé en FOL
Exploration: Version Space learning
Apprentissage par explication
Ex: brochette
 Explanation Based Learning
Fondé sur la pertinence
Ex: langue du pays
 Relevance Based learning
Fondé sur des connaissances
Ex: Interne médical
 Knowledge Based Inductive Learning
Programmation logique inductive (Prolog)

![](Image5.jpg)

![Une image contenant texte Description générée automatiquement](Image7.jpg)
Intelligences

<!-- Slide number: 55 -->
# Apprentissage par renforcement
55
Pas d’exemple
Feedback = bon ou mauvais
Processus de décision de Markov
Récompense à apprendre
Possibilité de Shaping
3 architectures
Basé sur l’utilité
Q-learning (utilité/action)
Agent réflex = apprentissage de politique
2 familles
Passif (politique fixée)
Actif  nécessité d’explorer
Approximations
Modèles paramétriques
Deep Q-learning

![](Image5.jpg)

![](Image7.jpg)
Intelligences

<!-- Slide number: 56 -->
# Questions?
56
Intelligence(s)

### Notes:

<!-- Slide number: 57 -->
# Langage naturel (NLP)
57

Modèle du langage
Communication
Agents conversationnels (chatbots)
Intelligence(s)

### Notes:

<!-- Slide number: 58 -->
# Modèles du langage
58
N-grams
Modèles de Markov

Traitements
 lissage, perplexité
Utilisation

Classification, catégorisation
Langue, genre, spam
Analyse de sentiments
Recherche d’information
Indexation
+ traitement requêtes
+ score  résultats
Extraction d’information
Automates à états finis:
Regexs, Transducteurs
Modèles probabilistes
Extraction d’ontologie
Machine reading

![](Image10.jpg)

![](Image7.jpg)

![](Espaceréservéducontenu8.jpg)
Intelligences

<!-- Slide number: 59 -->
# Grammaires
59
Caractéristiques
Analyse du langage

![](Image9.jpg)
Communication
Echange d’information
Modèles de communication
= grammaires + sémantique
Formalismes
Classes  de Chomsky
Catégories = Part Of Speech
Grammaires probabilistes
Sans contexte (PCFGs)
Syntaxique
Apprentissages
Grammaires augmentées
Avec contexte
Sémantiques
Interpréteurs
Modèles sémantiques
 Ambiguités
 Modèles imbriqués

![](Image7.jpg)
Intelligences

<!-- Slide number: 60 -->
# Speech/Text to Text/Speech
60

![](Image10.jpg)
Traduction automatisée
Modèles statistiques
Reconnaissance de la parole
Modèles acoustiques + langage
Modèles profonds
Réseaux récurrents / Transformers
Résumé, analyse syntaxique
Modèles sémantiques profonds

![](Image9.jpg)

![](Image7.jpg)

![](Image8.jpg)
Intelligences

<!-- Slide number: 61 -->
# Agents conversationnels
61
Agents algorithmiques couplé au NLP

Modèles de langage
Intentions = tâches
Entités = objets et propriétés
Instances = exemples
Architecture
Connecteurs à des canaux
Contextes de dialogues

Conception
Développement hors ligne
Actions, KBs
Modèles du langage
Bootstrap
Entraînement en ligne

![](Image9.jpg)

![](Image7.jpg)

![](Image8.jpg)
Intelligences

<!-- Slide number: 62 -->
# Applications des chatbots
62
Processus de création
Exemples
Définition des objectifs
Fonctions, besoins etc.
Définition du processus
Arborescence narrative
Spécifications
Périmètre
Identifier / rassembler les données
FAQ, DB, KB
Budgétisation
10000 à 500K€
Choix des canaux
Mobile, réseaux sociaux etc.
Choix technologique
Pile technologique + prestataires
Réalisation
Développement + entrainement
Communication
Mise en production
Amélioration
Métriques, Affinage des modèles, de l’arborescence, des fonctions
Hôtels et transports
SNCF
Achats en ligne
Amazon
Télécoms
Verizon
Finance
Orange
Médias
CNN
Ami virtuel
Replika
Support juridique interne
ADP
Intelligences

<!-- Slide number: 63 -->
# Intelligence conversationnelle
63

![](Image9.jpg)
Connaissances

![](Image7.jpg)
Probabiliste

![](Image30.jpg)
Modèles

![](Espaceréservéducontenu8.jpg)

![Une image contenant texte Description générée automatiquement](Image6.jpg)
Symbolique

![Une image contenant texte, carte Description générée automatiquement](Image10.jpg)
Exploratoire

![](Image46.jpg)
Argumentation

![](Image5.jpg)
Procédurale

Dialogue
Intelligences

<!-- Slide number: 64 -->
# Merci
64
Jean-Sylvain Boige
jsboige@myia.org
Intelligence(s)

### Notes: