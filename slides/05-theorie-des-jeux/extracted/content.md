<!-- Slide number: 1 -->
# Théorie des jeux
1
Intelligence Artificielle - V

Analyse stratégique
Jeux Bayésiens
Théorie des mécanismes
Jeux différentiels

IA 101

### Notes:

<!-- Slide number: 2 -->
# Plan du cours
2
Introduction
Résolution de problèmes
Bases de connaissances et logique
Incertitude et modèles probabilistes
Théorie des jeux
Apprentissage
Traitement du langage naturel
Présentation projets
IA 101

### Notes:

<!-- Slide number: 3 -->
# Théorie des jeux
3
Environnement multi-agent
Un seul Décideur
Planification / Synchronisation
Multi-Effecteurs / Multi-corps (découplage)
Centralisé (state = pool) vs décentralisé
Décideurs multiples  théorie des jeux
But commun / buts propres
d’adversité et/ou collaboratif
Information parfaite / imparfaite
A un tour: Joueurs, actions, récompenses
Ex: Morra (2 doigts)
Etudes des interdépendances stratégiques
Objectif double
Design d’agent: Quelle est la meilleure stratégie?
Design de mécanisme: Quelles sont les bonnes règles?
Justifications
Les maths deviennent compliquées
Fournit des outils de comptabilité
Identifier les situations analogues
Compréhension des schémas habituels
Optimisation de stratégies
Pure / mixte (randomisée)
Solution = profil rationnel = assignation de stratégies
Von Neumann  Maximin
Jeux à somme nulle
Changement de règles  séquence UE,O ≤ U ≤ UO,E
Ex: Morra: p = 7/12, U(E)= -1/12

![](Image5.jpg)
CS 405

<!-- Slide number: 4 -->
# Analyse stratégique
4

![](Image7.jpg)
Jeux simultanés
Matrice de gains
Dilemme du prisonnier
Parler ou se taire
Stratégie pure strictement dominante (stable)
Mais Pareto dominée (global mais instable)
IESDS
Elimination itérative des stratégies strictement dominées
Réduction progressive de la matrice
Equilibre de Nash:
optimum local dans l’espace des politiques
Ex: chasse au cerf
Aucun agent n’a de motivation à changer de stratégie
=Une loi que personne n’enfreint sans la police (Feu rouge)
Garanti d’exister / importance de la Coordination
Meilleure réponse
Etant donnée les autres choix.
Equilibre de Nash = meilleure réponse pour tous

![](Image6.jpg)

![](Image11.jpg)

![](Image10.jpg)
CS 405

<!-- Slide number: 5 -->
# Stratégies mixtes
5

![](Image5.jpg)

![](Image6.jpg)

![](Image7.jpg)
CS 405

<!-- Slide number: 6 -->
# Equilibres de stratégie mixte
6

![](Image5.jpg)

![](Image7.jpg)

![](Image8.jpg)

![](Image10.jpg)
CS 405

<!-- Slide number: 7 -->
# Jeux séquentiels
7
Jeux à tours successifs:
Conflits, négociations etc.
Jeu de la guerre des prix (in/out)
Accept, out = équilibres
Matrice = cf. dominance faible
Mais différence = menace crédible?
Equilibre parfait de sous-jeu (SPE)
Sous-jeu Firm 2  accept
« out » plus en équilibre  q des menaces crédibles
Induction arrière
Ex: Jeu de l’escalade à la guerre
On démarre par la fin
Les sous-jeux finaux éclairent les premiers
 « Accept » stratégie optimale
Equilibres parfait de sous-jeu
Importance de repérer tous les chemins / nœuds de décision
<Accept, War>; <Escalade>
Equilibres de sous-jeu parfaits multiples (rare)
Sous-jeu du bas   cf simultané : mixte  EU(1) = -1/3  mixte infini

![](Image5.jpg)

![](Image7.jpg)

![](Image9.jpg)
CS 405

<!-- Slide number: 8 -->
# Jeux à étapes
8
Plusieurs manches
Sous-jeux simultanés, Gains indépendants, connaissance du passé
Difficile à dessiner (exponentiel)
Théorèmes:
Dernière étape  Equilibre de Nash (passé pas modifiable)
Autres: jouer équilibres de Nash = 1 équilibre de sous-jeu
Mais Autres équilibres de sous-jeu possibles (coopération)
Stratégies de punition
Ex: Prisonnier puis Argent gratuit
 équilibre faible (0,0) = menace de punition
 meilleur équilibre
Menaces « crédibles » importantes
Se lier les mains
Ex: brûler le pont derrière soi
 Pas de possibilités de retraite
 Rend la menace crédible
Problèmes d’engagement
Ex: fouille: superficielle, complète, chien
Pb = pas d’engagement crédible
Induction arrière K9
 l’ordre est important
Problèmes de l’induction arrière
Ex: le millepattes
Equilibre pessimiste, pas constaté dans la pratique
Hypothèses  Maths  conclusions
Pb ici: hypothèses: rationalité limitée
Induction avant
Induction arrière = futur rationnel
Induction avant = passé rationnel
Ex: « pub hunt »  supprime un équilibre
Mais parfois solutions controversées
Version sociétale: dilemmes répétés
Punition perpétuelle, œil pour œil etc.
Evolution de la confiance

![](Image8.jpg)

![](Image5.jpg)

![](Image6.jpg)

![](Image7.jpg)

![](Image10.jpg)

![](Image9.jpg)
CS 405

<!-- Slide number: 9 -->
# Formes stratégiques avancées
9

![](Image6.jpg)

![](Image5.jpg)

![](Image9.jpg)

![](Image8.jpg)

![](Image7.jpg)

![](Image11.jpg)

![](Image12.jpg)
CS 405

<!-- Slide number: 10 -->
# Espaces de stratégies infinis
10
Jeux sans équilibre
Jusqu’ici, nombre fini de stratégies pures
Matrices + théorèmes de Nash
Certains jeux ont une infinité de stratégies pures
 pas de matrice et pas forcément d’équilibre de Nash
Ex: Joueur 1: x>0, Joueur 2: y>0, gain xy pour les deux
Duels
100 m, 2 balles, se rapprochent, peuvent tirer quand ils souhaitent
Précisions différentes mais 0% à 100m, 100% à 0m
  Equilibre = même distance
(preuve par contradiction)
Ex: date de sortie de produits concurrents
Loi de Hotelling et l’électeur médian
2 vendeurs de glace sur la plage, choix de l’emplacement
Equilibre = les deux au milieu.
Principe important en politique: théorèmes de l’électeur médian
Vainqueur de Condorcet (cf Choix social)

![](Image9.jpg)

![](Image7.jpg)

![](Image8.jpg)
CS 405

<!-- Slide number: 11 -->
# Jeux Bayésiens
11

![](Image6.jpg)

![](Image8.jpg)

![](Image7.jpg)
CS 405

<!-- Slide number: 12 -->
# Equilibres Bayésiens parfaits (PBE)
12

![](Image5.jpg)

![](Image6.jpg)

![](Image7.jpg)
CS 405

<!-- Slide number: 13 -->
# Questions?
13
IA 101

### Notes:

<!-- Slide number: 14 -->
# Jeux coopératifs
14
CS 405

<!-- Slide number: 15 -->
# Conception de mécanismes
15
CS 405

<!-- Slide number: 16 -->
# Allocation de ressources par les enchères
16

![](Image2.jpg)
CS 405

<!-- Slide number: 17 -->
# Allocation par les votes
17
CS 405

<!-- Slide number: 18 -->
# Critère de Condorcet
18
Condition du vainqueur de Condorcet
La meilleure aux autres options prises paire à paire
Exemple: Uninominal à 2 tours: Bayrou vainqueur de Condorcet mais pas au 2è tour
Théorème: Indifférence aux petits candidats: Vainqueur de Condorcet stable aux changements
Mais paradoxe de Condorcet: pas de garantie d’existence
Théorèmes de l’électeur médian
1er théorème: Gauche – droite  existence du vainqueur  électeur médian
2è théorème: Gauche – droite + valeur intrinsèque
Si pas de vainqueur de Condorcet
Méthodes de Condorcet
 résolution si pas de vainqueur
Une ou deux méthodes
Exemple à une méthode: Méthode Minimax
Celui qui fait le mieux au pire
Mais très stratégique (ex: anarchistes)
 Méthode de Schulze:
Elimination itérative des derniers du peloton de tête
robuste à la manipulation (électeurs raisonnables)

![](Image6.jpg)

![Une image contenant texte, horloge, périphérique Description générée automatiquement](Image7.jpg)

![](Image5.jpg)
CS 405

<!-- Slide number: 19 -->
# Procédures de votes connues
19
Référendum:
2 options  méthode de la majorité robuste à la manipulation et c’est la seule
Vote pluraliste uninominal (n candidats)
 critiqué (vote utile + pas de préférences)
Vote à second-tour instantané: Préférences
Si pas de majorité, élimination du dernier et second tour  pas de critère de Condorcet
Méthode de Condorcet: vote à règle de vrai majorité:
Préférences complètes, puis comparaisons paires à paires
 bons résultats mais ne marche pas tout le temps (paradoxe de Condorcet)
 Méthodes de Condorcet  Shulze
Méthodes utilitaristes:
Compte de Borda  préférences, score = ordre
Manipulable
Vote par assentiment  élimination, majorité d’approbation
Théorème de robustesse au mensonge: suffrage sincère stratégique
Scrutin au jugement majoritaire:
Médiane des scores
Seule procédure vérifiant
majorité d’une même note validée
et monotonie au changement individuel
Scrutins stochastiques
Scrutin Stochocratique:
Option préférée puis tirage au sort
Théorème d’Hylland de « la dictature aléatoire »:
Seul méthode avec critère d’unanimité non stratégique
Méthode de Condorcet randomisée:
Loterie pondérée dans le peloton de tête:
Pondération selon équilibre de Nash
Ex: Shifumi
Critère de Condorcet et Non stratégique (seul)
Comparaison détaillée
Articles et démonstrations

![](Image5.jpg)

![Une image contenant table Description générée automatiquement](Image10.jpg)

![Une image contenant texte Description générée automatiquement](Image6.jpg)

![Une image contenant table Description générée automatiquement](Image12.jpg)

![Une image contenant texte, vert, équipement électronique Description générée automatiquement](Image8.jpg)

![Une image contenant table Description générée automatiquement](Image14.jpg)
CS 405

<!-- Slide number: 20 -->
# Allocation par la négociation
20

![](Image6.jpg)
CS 405

<!-- Slide number: 21 -->
# Théorie de la négociation
21
Démarche
Hypothèses
 Modèles de jeux
 Equilibres et pouvoirs de négociation
Sources du pouvoir de négociation
Pouvoir de proposition
Patience
Options alternatives
Connaissance de l’autre utilité
Monopole
Réputation
Engagement crédible
Signalement coûteux

CS 405

<!-- Slide number: 22 -->
# Questions?
22
IA 101

### Notes:

<!-- Slide number: 23 -->
# Jeux différentiels
23
CS 405

<!-- Slide number: 24 -->
# Equilibres différentiels
24

![](Image7.jpg)
Contexte
Equilibres de Nash pour jeux à somme nulle
J1(u1,u2) + J2(u1,u2) = 0
Equilibres de point de selle
P1 maximise, P2 minimise
  Equilibre ssi point de selle existe
Equilibres de Stackelberg
Le « leader » annonce
En tenant compte du fait que les autres maximisent leur réponse
Jeux Coopératifs/compétitifs
Possibilité de dialogue maximisation commune
Division en partie coopérative et partie compétitive: valeur co-co
Equilibres en boucle ouverte
Equilibre de Nash
u* est un équilibre ssi
J1, J2  2 optimisations conditions d’existence et de calcul
+ Equilibre de Stackelberg: conditions d’existence et de calcul
Ex: croissance économique                                         avec u1 taxe sur le capital et u2 consommation
Equilibre de S avec gouvernement leader.
Equilibres Markovien
Equilibre de Nash
σ* est un équilibre ssi
Résolution d’équations différentielles partielles
Cas général  Solutions non hyperboliques
Jeux à somme nul ou dimension 1  système hyperbolique
Jeux linéaires quadratiques
Dynamique linéaire, récompense quadratique  solution

![](Image5.jpg)

![](Image8.jpg)

![](Image6.jpg)
CS 405

<!-- Slide number: 25 -->
# Méthodes calculatoires
25
Méthodes directes
Formulation du programme mathématique et résolution
Méthodes indirectes
Utilisation d’équations différentielles partielles
Méthode d’échantillonnage incrémental
Ex: poursuite évasion:
Temps terminal T, récompense L(Ue,Up) –T
RRT exploration d’arbre
convergence avec nombre d’échantillons suffisant
 similaire au filtrage particulaire
Pour aller plus loin
Détails mathématiques

![](Image5.jpg)

![](Image6.jpg)
CS 405

<!-- Slide number: 26 -->
# Questions?
26
IA 101

### Notes:

<!-- Slide number: 27 -->
# Plan du cours
27
Introduction
Résolution de problèmes
Bases de connaissances et logique
Incertitude et modèles probabilistes
Théorie des jeux
Apprentissage
Traitement du langage naturel
Présentation projets
IA 101

### Notes:

<!-- Slide number: 28 -->
# Projets de groupe
28
Moteur de recherche augmenté par le raisonnement et le langage naturel
Grammaire et sémantique des contenus et des requêtes. Lucene.Net, OpenNLP, SharpRDF, FOL
Conception de bots de services sur réseaux sociaux
Chat Bots, AIML, Reddit et agents de service, NLP, RDF, APIs
Conception d'un modèle d'inférence pour l’analyse de sentiment
Conception d’un modèle probabiliste, Infer.Net, démarche expérimentale, Reddit
Création d'une plateforme sémantique LDP à partir d'un index structuré.
Structuration et ouverture des données = Linked Data. Lucene.Net, SharpRDF
Résolution de Captchas par deep learning
Apprentissage via un Adapteur DNN, Réseaux de dernières génération. TensorFlow, CNTK, Encog
Entrainement de stratégies de trading algorithmiques sur crypto monnaies.
Expérience DNN Bitcoin, Encog et machine learning
Amélioration par l'apprentissage d'un agent joueur de Go simple
Le Go et l’IA, Récentes avancées. Go Traxx
Evolution de vaisseaux spatiaux par algorithmes génétiques dans le jeu de la vie.
Approches évolutionnistes, automates cellulaires, Bac a sable. Golly, Encog
Pilotage d'un cluster de cache distribué pour le portage d’applications  dans le Cloud
Caches distribués, scaling, stratégies et clustering. Redis
IA 101

### Notes:

<!-- Slide number: 29 -->
# Merci
29
Jean-Sylvain Boige
jsboige@myia.org
IA 101

### Notes: