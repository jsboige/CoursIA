---
theme: ../theme-ia101
title: "Intelligence Artificielle - Théorie des jeux"
info: IA 101 - Théorie des jeux, analyse stratégique, mécanismes
paginate: true
drawings:
  persist: false
transition: slide-left
mdc: true
layout: cover
---

# Théorie des jeux

INTELLIGENCE ARTIFICIELLE -- V

**Analyse stratégique**

- Jeux Bayesiens
- Théorie des mécanismes
  - Jeux differentiels

---
layout: section
---

# Plan du cours

---
layout: default
---

# Sommaire

- I. Introduction
- II. Resolution de problemes
- III. Bases de connaissances et logique
- IV. Incertitude et modèles probabilistes
- **V. Théorie des jeux**
- VI. Apprentissage
- VII. Traitement du langage naturel
- VIII. Presentation projets

---
layout: dense
---

# Théorie des jeux

## Environnement multi-agent

- Un seul Decideur
  - Planification / Synchronisation
  - Multi-Effecteurs / Multi-corps (decouplage)
    - Centralise (state = pool) vs decentralise
- Decideurs multiples -> théorie des jeux
  - But commun / buts propres, adversite et/ou collaboratif
  - Information parfaite / imparfaite
  - A un tour: Joueurs, actions, recompenses

## Études des interdependances stratégiques

- Objectif double
  - Design d'agent: Quelle est la meilleure stratégie?
  - Design de mécanisme: Quelles sont les bonnes règles?
- Optimisation de stratégies: pure / mixte (randomisee)
- Von Neumann -> Maximin: Jeux a somme nulle

<img src="./images/img_001.png" alt="Environnement multi-agent : plusieurs decideurs en interaction, exemple du jeu de Morra" style="display:block; margin:4px auto 0; max-height:88px; width:auto; max-width:100%; object-fit:contain;">

---
layout: section
---

# Analyse stratégique

---
layout: dense
---

# Analyse stratégique

## Jeux simultanes

- Matrice de gains
- Dilemme du prisonnier: Parler ou se taire
  - Stratégie pure strictement dominante (stable)
  - Mais Pareto dominee (global mais instable)

## IESDS

- Elimination iterative des stratégies strictement dominees
- Reduction progressive de la matrice

## Equilibre de Nash

- Optimum local dans l'espace des politiques
- Aucun agent n'a de motivation a changer de stratégie
  - = Une loi que personne n'enfreint sans la police
- Garanti d'exister / importance de la Coordination

## Meilleure reponse

- Etant donnée les autres choix
- Equilibre de Nash = meilleure reponse pour tous

<div style="display:grid; grid-template-columns:repeat(4,1fr); gap:6px; align-items:center;">
<img src="./images/img_002.png" alt="Matrice de gains du dilemme du prisonnier" style="width:100%; height:28px; object-fit:contain;">
<img src="./images/img_003.png" alt="Elimination iterative des strategies strictement dominees (IESDS)" style="width:100%; height:28px; object-fit:contain;">
<img src="./images/img_004.png" alt="Equilibre de Nash dans la matrice de gains" style="width:100%; height:28px; object-fit:contain;">
<img src="./images/img_005.png" alt="Meilleure reponse aux strategies des autres joueurs" style="width:100%; height:28px; object-fit:contain;">
</div>

---
layout: dense
---

# Stratégies mixtes

## Occurrences

- Ex: Penalty, pile ou face -- Jeux a somme nulle
- Distribution probabiliste de stratégies pures
- Theoreme de Nash: 1 equilibre doit exister

## Algorithme de stratégie mixte

- Utilites esperees -> equations pour l'indifference a l'equilibre
  - `EU_L = sigma_u(-3) + (1-sigma_u)(1) = EU_R = sigma_u(2) + (1-sigma_u)(0)` -> `sigma_u = 1/6`
  - `EU_U = sigma_L(3) + (1-sigma_L)(-2) = EU_D = sigma_L(-1) + (1-sigma_L)(0)` -> `sigma_L = 1/3`

## Calcul des gains esperes

- Somme ponderee par les probabilités individuelles
- Ex: Bataille des sexes (boxe vs ballet): 2 equilibres purs + mixte 1/3 vs 2/3 -> gain 2/3

<div style="display:grid; grid-template-columns:repeat(3,1fr); gap:6px; align-items:center;">
<img src="./images/img_006.png" alt="Distribution probabiliste de strategies pures : exemple du penalty" style="width:100%; height:130px; object-fit:contain;">
<img src="./images/img_007.png" alt="Algorithme de strategie mixte : equations d'indifference a l'equilibre" style="width:100%; height:130px; object-fit:contain;">
<img src="./images/img_008.png" alt="Calcul des gains esperes : bataille des sexes" style="width:100%; height:130px; object-fit:contain;">
</div>

---
layout: dense
---

# Equilibres de stratégie mixte

## Stratégie mixte dominant strictement une pure

- Ex: 3 lignes, milieu dominee, calcul des probas

## Dominance faible

- Domine ou indifferente (>=)
- Elimination iterative, mais reste autres equilibres

## Equilibres infinis

- Ex: equilibres partiellement mixtes

## Règle impaire

- Presque tous les jeux ont un nombre impair d'equilibres
- Nombre infini ou pair généralement lie a la dominance faible
  - Ex nombre pair: l'argent gratuit
  - Sinon verifier si on n'a pas oublie une mixte

<div style="display:grid; grid-template-columns:repeat(4,1fr); gap:6px; align-items:center;">
<img src="./images/img_009.png" alt="Strategie mixte dominant strictement une strategie pure : calcul des probabilites" style="width:100%; height:120px; object-fit:contain;">
<img src="./images/img_010.png" alt="Dominance faible : elimination iterative" style="width:100%; height:120px; object-fit:contain;">
<img src="./images/img_011.png" alt="Equilibres infinis : equilibres partiellement mixtes" style="width:100%; height:120px; object-fit:contain;">
<img src="./images/img_012.png" alt="Regle impaire : nombre d'equilibres d'un jeu" style="width:100%; height:120px; object-fit:contain;">
</div>

---
layout: dense
---

# Jeux séquentiels

## Jeux a tours successifs

- Conflits, negociations etc.
- Jeu de la guerre des prix (in/out)
  - Accept, out = equilibres
  - Différence = menace credible?
- Equilibre parfait de sous-jeu (SPE)
  - Sous-jeu Firm 2 -> accept
  - "out" plus en equilibre -> question des menaces credibles

## Induction arriere

- Ex: Jeu de l'escalade a la guerre
- On demarre par la fin
  - Les sous-jeux finaux eclairent les premiers

## Equilibres parfaits de sous-jeu

- Importance de reperer tous les chemins / noeuds de decision
- Equilibres de sous-jeu parfaits multiples (rare)

<div style="display:grid; grid-template-columns:repeat(3,1fr); gap:6px; align-items:center;">
<img src="./images/img_013.png" alt="Jeu de la guerre des prix : arbre a tours successifs" style="width:100%; height:72px; object-fit:contain;">
<img src="./images/img_014.png" alt="Induction arriere : jeu de l'escalade a la guerre" style="width:100%; height:72px; object-fit:contain;">
<img src="./images/img_015.png" alt="Equilibre parfait de sous-jeu (SPE) : menaces credibles" style="width:100%; height:72px; object-fit:contain;">
</div>

---
layout: dense
---

# Jeux a étapes

## Plusieurs manches

- Sous-jeux simultanes, Gains independants, connaissance du passe
- Difficile a dessiner (exponentiel)
- Theoremes:
  - Dernière étape -> Equilibre de Nash (passe non modifiable)
  - Autres: jouer equilibres de Nash = 1 equilibre de sous-jeu
  - Mais autres equilibres de sous-jeu possibles (cooperation)

## Stratégies de punition

- Ex: Prisonnier puis Argent gratuit -> equilibre faible (0,0) = menace de punition
- Menaces "credibles" importantes

<img src="./images/img_016.png" alt="Strategies de punition : jeu du prisonnier puis argent gratuit" style="display:block; margin:6px auto 2px; max-height:90px; width:auto; max-width:100%; object-fit:contain;">

## Se lier les mains

- Ex: bruler le pont derriere soi -> Rend la menace credible

<img src="./images/img_017.png" alt="Se lier les mains : bruler le pont rend la menace credible" style="display:block; margin:6px auto 2px; max-height:90px; width:auto; max-width:100%; object-fit:contain;">

## Problemes de l'induction arriere

- Ex: le millepattes -- equilibre pessimiste, pas constate en pratique
- Hypotheses -> Maths -> conclusions (problème: rationalite limitee)
- Induction avant = passe rationnel (supprime un equilibre)

<div style="display:grid; grid-template-columns:repeat(2,1fr); gap:6px; align-items:center;">
<img src="./images/img_018.png" alt="Jeu du mille-pattes : equilibre pessimiste de l'induction arriere" style="width:100%; height:90px; object-fit:contain;">
<img src="./images/img_019.png" alt="Induction arriere : les sous-jeux finaux eclairent les premiers" style="width:100%; height:90px; object-fit:contain;">
</div>

## Dilemmes repetes

- Punition perpetuelle, oeil pour oeil etc. -- Evolution de la confiance

<div style="display:grid; grid-template-columns:repeat(2,1fr); gap:6px; align-items:center;">
<img src="./images/img_020.png" alt="Dilemmes repetes : arbre de jeu multi-manches" style="width:100%; height:90px; object-fit:contain;">
<img src="./images/img_021.png" alt="Jeux repetes : punition perpetuelle et evolution de la confiance" style="width:100%; height:90px; object-fit:contain;">
</div>

---
layout: dense
---

# Formes stratégiques avancees

## Raisonner avec des variables

- Ex: bataille des sexes, A>B>C, algorithme de stratégie mixte
  - `sigma_u = (b-c)/(a+b-2c)` et `0 < sigma_u < 1`
- Ex: Topologie complete 2x2

<div style="display:grid; grid-template-columns:repeat(3,1fr); gap:6px; align-items:center;">
<img src="./images/img_022.png" alt="Bataille des sexes avec variables A>B>C" style="width:100%; height:100px; object-fit:contain;">
<img src="./images/img_023.png" alt="Topologie complete des jeux 2x2" style="width:100%; height:100px; object-fit:contain;">
<img src="./images/img_024.png" alt="Algorithme de strategie mixte avec variables" style="width:100%; height:100px; object-fit:contain;">
</div>

## Equilibre de lame de couteau

- X>0 -> Up, Left vs x<0 -> down, right, x=0 -> tous
- Instable autour de x=0, probabilité faible -> ignore

<img src="./images/img_025.png" alt="Equilibre de lame de couteau : instabilite autour de x=0" style="display:block; margin:4px auto; width:100%; max-height:36px; object-fit:contain;">

## Modèles causaux

- Proprietes causales des inputs -> Statiques comparees
  - Calcul des gradients aux equilibres
- Ex: Football penalty: `sigma_KL = 1/(1+x)`, `sigma'_KL = -1/(1+x^2) < 0`
  - -> il tire davantage son cote faible (compense)

<img src="./images/img_026.png" alt="Modele causal du penalty au football : gradients aux equilibres" style="display:block; margin:6px auto 2px; max-height:95px; width:auto; max-width:100%; object-fit:contain;">

## Pierre, papier, ciseaux

- Pas de stratégie pure -> cycle
- Support des stratégies mixtes, EU egales dans le support
- Theoreme: 2 joueurs, symetrique a somme nulle -> EU = 0
- Resolution: indifference `sigma_L = 1/4` (ciseaux pour compenser)

<div style="display:grid; grid-template-columns:repeat(2,1fr); gap:6px; align-items:center;">
<img src="./images/img_027.png" alt="Pierre-papier-ciseaux : matrice de gains a somme nulle" style="width:100%; height:100px; object-fit:contain;">
<img src="./images/img_028.png" alt="Resolution de pierre-papier-ciseaux : support des strategies mixtes" style="width:100%; height:100px; object-fit:contain;">
</div>

---
layout: default
---

# Espaces de stratégies infinis

## Jeux sans equilibre

- Nombre fini de stratégies pures -> Matrices + theoremes de Nash
- Certains jeux ont une infinite de stratégies pures
  - Pas de matrice, pas forcement d'equilibre de Nash

<img src="./images/img_029.png" alt="Jeu sans equilibre de Nash en strategies pures" style="display:block; margin:4px auto; width:100%; max-height:32px; object-fit:contain;">

## Duels

- 100 m, 2 balles, precisions différentes (0% a 100m, 100% a 0m)
- Equilibre = même distance (preuve par contradiction)
- Ex: date de sortie de produits concurrents

<img src="./images/img_030.png" alt="Duel : equilibre a meme distance" style="display:block; margin:4px auto; width:100%; max-height:28px; object-fit:contain;">

## Loi de Hotelling et l'electeur median

- 2 vendeurs de glace sur la plage, choix de l'emplacement
  - Equilibre = les deux au milieu
- Principe important en politique: theoreme de l'electeur median
  - Vainqueur de Condorcet (cf Choix social)

<img src="./images/img_031.png" alt="Loi de Hotelling : les deux vendeurs se placent au milieu" style="display:block; margin:4px auto; width:100%; max-height:28px; object-fit:contain;">

---
layout: section
---

# Jeux Bayesiens

---
layout: dense
---

# Jeux Bayesiens

## Information incomplete

- Sur les autres joueurs (ex: recompenses)
- Representation = Distribution de probabilité sur les types de joueurs
  - Information imparfaite -> Analyse probabiliste

## Formalisation

`G = <N, Omega, <A_i, u_i, T_i, tau_i, p_i, C_i>>`

- N joueurs, Omega etats de la nature, A_i actions du joueur i
- T_i type du joueur i, U_i recompense, p_i distribution des types
- Stratégies pures: `S_i = {s_i: T_i -> A_i}`

<img src="./images/img_032.png" alt="Formalisation Bayesienne : joueurs, etats, types et croyances" style="display:block; margin:4px auto; max-height:30px; width:auto; max-width:100%; object-fit:contain;">

## Equilibres de Nash Bayesien

- Objectif = maximisation de la recompense esperee
- De nombreux equilibres sans restrictions supplementaires

<img src="./images/img_033.png" alt="Equilibre de Nash Bayesien : maximisation de la recompense esperee" style="display:block; margin:4px auto; max-height:70px; width:auto; max-width:100%; object-fit:contain;">

## Ex: Dilemme du Sheriff

- Criminel (p) vs civil (1-p), tirer ou pas
- Stratégies dominantes: tirer pour criminel, pas pour civil
- Pour le Sheriff: `E(tirer) = p-1`, `E(pas) = -2p`
  - p>1/3 = tirer

<img src="./images/img_034.png" alt="Dilemme du Sheriff : seuil p>1/3 pour tirer" style="display:block; margin:4px auto; max-height:70px; width:auto; max-width:100%; object-fit:contain;">

---
layout: dense
---

# Equilibres Bayesiens parfaits (PBE)

## Jeux séquentiels

- Rappel SPE -> equilibres non plausibles (menaces non credibles)
- Systèmes de croyance: assignations de probabilités sur les types
  - "Consistant" -> Probabilités par application des stratégies (Bayes)
- Rationalite séquentielle: recompense esperee maximale

<img src="./images/img_035.png" alt="Jeu de signalisation : arbre avec systeme de croyances" style="display:block; margin:4px auto; max-height:70px; width:auto; max-width:100%; object-fit:contain;">

## Definition PBE

- Profile stratégique et système de croyance consistant tels que les stratégies sont sequentiellement rationnelles

## Jeux de signalisation

- Emetteur S (connait son type) -> message m, Recepteur R -> action a
- 3 catégories de PBE:
  - **Pooling**: emetteurs choisissent le même message (pas de signal)
  - **Separating**: messages toujours différents -> croyance déterministe
  - **Semi-separation** (partial-pooling): mixte

<img src="./images/img_036.png" alt="Arbre extensive d'un jeu de signalisation" style="display:block; margin:4px auto; max-height:100px; width:auto; max-width:100%; object-fit:contain;">

## Exemples

- Jeu de reputation (guerre des prix): pooling ou separating
- Jeu d'education: doue ou pas, diplome ou pas (signal) -> PBE de separation
- Biere-quiche: P=0.9 -> pooling, P=0.2 -> stratégies mixtes

<img src="./images/img_037.png" alt="Exemples de PBE : pooling, separating et semi-separation" style="display:block; margin:4px auto; max-height:90px; width:auto; max-width:100%; object-fit:contain;">

---
layout: section
---

# Questions?

---
layout: section
---

# Jeux cooperatifs

---
layout: dense
---

# Jeux cooperatifs

## Jeux d'assistance

- 2 joueurs, recompense theta incertaine pour l'assistant
- Ex: Jeu du trombone
  - Nash -> meilleure reponse myope incrementale
- Cas general similaire a un POMDP + theta

## Théorie des jeux cooperatifs

- Utilite transferable de coalition: `G = {N, v}`, `V(C) >= 0`
- Partitions = Structures de Coalitions CS(N)
- **Imputation**: `sum x_i = v(N)`, `x_i > v({i})`
- **Noyau**: imputations x telles que `x(C) > v(C)` pour tout C
- **Valeur de Shapley**: contribution marginale moyennee sur toutes les permutations
  - `phi_i(G) = 1/n! * sum mc_i(p_i)`
  - Axiomes: Efficace, joueur nul, symetrie, additivite -> unique

## Calculs

- Reseaux de contribution marginale (representation compacte)
  - `phi_i(R) = sum x/|C|` pour les coalitions contenant i
- Structures de coalition optimales: NP-Hard
  - Bons résultats avec exploration du graphe de structure

---
layout: section
---

# Conception de mécanismes

---
layout: dense
---

# Conception de mécanismes

## Théorie des jeux inverse

- Si les agents sont rationnels, quelles sont les bonnes règles?
- Dans le cadre Bayesien d'information imparfaite
  - Le "principal" souhaite inciter a reveler la vraie utilite

## Formalisme

- Le principal choisit la structure de recompense `y()`
- Les agents declarent `theta_hat` (et peuvent mentir)
- Fonction de choix social `f(theta)` a implementer par `y(theta_hat)`

## Principe de revelation

- Mécanisme incitatif verace (IC): non manipulable, revelateur
  - `theta_hat(theta) = theta`
- S'il existe un mécanisme y implementant f, alors il existe une version IC
- 2 versions:
  - **DSIC**: Implementation en stratégies dominantes
  - **BNIC**: Equilibre de Nash Bayesien (plus faible)

---
layout: dense
---

# Allocation de ressources par les encheres

## Encheres individuelles

- Valeur privee v_i de l'objet par l'individu i
- Enchere anglaise (ascendante): Efficace mais risque de collusion
- Enchere de Vickrey (second prix)
  - Equilibre DSIC = chacun declare la valeur "honnete"
  - Très repandu: eBay, AdWords etc.
- Theoreme d'equivalence de revenue

## Bien commun

- Tragedie des communs (ex: pollution)
  - Stratégie de pollution dominante mais pas optimale (Pareto)
  - Necessite d'expliciter les externalites (ex: taxe carbone)

## Mécanisme de Vickrey-Clarke-Groves (VCG)

- N Encherisseurs declarent utilite de M ressources
- Allocation maximisant la somme des utilites
- Taxe: `T_i = U_max(sans i) - U_max(sans i, sans ressource j)`

<img src="./images/img_038.png" alt="Taxe VCG : T_i = U_max(sans i) - U_max(sans i, sans ressource j)" style="display:block; margin:6px auto 2px; max-height:68px; width:auto; max-width:100%; object-fit:contain;">

---
layout: dense
---

# Allocation par les votes

## Théorie du choix social

- Préférences individuelles rationnelles -> Ordre de préférence social
- Proprietes d'une bonne fonction de choix social:
  1. Condition de Pareto / critere d'unanimite
  2. Indépendance des alternatives non pertinentes
  3. Pas de dictature

## Résultats negatifs

- **Paradoxe de Condorcet**: A,B,C -> 2/3 de mecontents
- **Theoreme de Arrow**: Impossible de satisfaire 1, 2 et 3 simultanement (>= 3 options)
- **Theoreme de Gibbard-Satterthwaite**: Toute FCS déterministe avec Pareto et >2 choix est manipulable ou dictatoriale

---
layout: dense
---

# Critere de Condorcet

## Condition du vainqueur de Condorcet

- La meilleure aux autres options prises paire a paire
  - Ex: Uninominal a 2 tours: Bayrou vainqueur de Condorcet mais pas au 2e tour
- **Indifference aux petits candidats**: vainqueur stable aux changements
- Paradoxe de Condorcet: pas de garantie d'existence

<img src="./images/img_039.png" alt="Comparaisons par paires : recherche du vainqueur de Condorcet" style="display:block; margin:4px auto; max-height:85px; width:auto; max-width:100%; object-fit:contain;">

## Theoremes de l'electeur median

- 1er theoreme: Gauche-droite -> existence du vainqueur -> electeur median
- 2e theoreme: Gauche-droite + valeur intrinseque

<img src="./images/img_040.png" alt="Theoremes de l'electeur median : resultats de vote" style="display:block; margin:4px auto; max-height:80px; width:auto; max-width:100%; object-fit:contain;">

## Si pas de vainqueur de Condorcet

- Méthode **Minimax**: celui qui fait le mieux au pire
  - Mais très stratégique (ex: anarchistes)
- Méthode de **Schulze**: elimination iterative des derniers du peloton de tete
  - Robuste a la manipulation (electeurs raisonnables)

<img src="./images/img_041.png" alt="Methodes Minimax et Schulze en l'absence de vainqueur de Condorcet" style="display:block; margin:4px auto; width:100%; max-height:36px; object-fit:contain;">

---
layout: dense
---

# Procedures de votes connues

- **Referendum**: 2 options -> méthode de la majorite robuste (la seule)
- **Vote pluraliste uninominal** (n candidats): critique (vote utile)
- **Vote a second-tour instantane**: Préférences, elimination du dernier
  - Pas de critere de Condorcet
- **Méthode de Condorcet**: comparaisons paires a paires -> Schulze

## Méthodes utilitaristes

- **Compte de Borda**: préférences, score = ordre (manipulable)
- **Vote par assentiment**: elimination, majorite d'approbation
  - Theoreme de robustesse au mensonge
- **Scrutin au jugement majoritaire**: mediane des scores
  - Seule procedure avec majorite d'une même note validee + monotonie

<div style="display:grid; grid-template-columns:repeat(3,1fr); gap:6px; align-items:center;">
<img src="./images/img_042.png" alt="Compte de Borda : score selon l'ordre des preferences" style="width:100%; height:90px; object-fit:contain;">
<img src="./images/img_043.png" alt="Vote par assentiment : majorite d'approbation" style="width:100%; height:90px; object-fit:contain;">
<img src="./images/img_044.png" alt="Scrutin au jugement majoritaire : mediane des scores" style="width:100%; height:90px; object-fit:contain;">
</div>

## Scrutins stochastiques

- **Scrutin Stochocratique**: option preferee puis tirage au sort
  - Theoreme d'Hylland: seule méthode avec unanimite non stratégique
- **Condorcet randomisee**: loterie ponderee dans le peloton de tete
  - Ponderation selon equilibre de Nash -- critere de Condorcet + non stratégique

<div style="display:grid; grid-template-columns:repeat(3,1fr); gap:6px; align-items:center;">
<img src="./images/img_045.png" alt="Scrutin Stochocratique : option preferee puis tirage au sort" style="width:100%; height:80px; object-fit:contain;">
<img src="./images/img_046.png" alt="Theoreme d'Hylland : unanimite non strategique" style="width:100%; height:80px; object-fit:contain;">
<img src="./images/img_047.png" alt="Condorcet randomisee : loterie ponderee dans le peloton de tete" style="width:100%; height:80px; object-fit:contain;">
</div>

---
layout: default
---

# Allocation par la negociation

## Modèle des offres alternees

- Si pas d'accord: Accord de conflit -> fenêtre de negociation
- Nombre de manches:
  - 1 manche: Ultimatum (J1 a tout le pouvoir)
  - 2 manches: J2 a tout le pouvoir
  - N manches: JN a le pouvoir
- Agents impatients: facteurs de discompte `0 <= gamma_i < 1`
  - Offre a l'equilibre: `A_1 = (1-gamma_2)/(1-gamma_1*gamma_2)`

<img src="./images/img_048.png" alt="Negociation a offres alternees : fenetre d'accord et partage a l'equilibre" style="display:block; margin:10px auto; max-height:200px; width:auto; max-width:100%; object-fit:contain;">

## Domaines orientes tâches

- Offres (T1, T2) de repartitions de tâches parmi T
- Protocole de concession monotone

## Stratégie de Zeuthen

- Mesure de l'aversion au risque de conflit
- Le risque plus faible concede, sinon tirage au sort

---
layout: default
---

# Théorie de la negociation

## Demarche

- Hypotheses -> Modèles de jeux -> Equilibres et pouvoirs de negociation

## Sources du pouvoir de negociation

- Pouvoir de proposition
- Patience
- Options alternatives
- Connaissance de l'autre utilite
- Monopole
- Reputation
- Engagement credible
- Signalement couteux

---
layout: section
---

# Questions?

---
layout: section
---

# Jeux differentiels

---
layout: dense
---

# Jeux differentiels

## Théorie des jeux + théorie du contrôle

- Interdependance: agents economiques, pollution, marches
- Dynamique: habitudes, technologies, accumulations, traffic
- Comportement stratégique: buts antagonistes, choix

## Definitions

- Joueurs M={1,...,m}, Vecteur de contrôle `u_j(t)`
- Vecteur d'etat `x(t)`, equation d'etat: `x'(t) = f(x(t), u(t), t)`
- Fonction de gain: `J_j = S_j(x(T)) - integral g_j dt` -> Minimisation de L

## Structure de l'information

- **Boucle ouverte**: conditions initiales + temps: `u_j(t) = mu_j(x_0, t)`
- **Markovienne**: `u_j(t) = sigma_j(t, x(t))` (lineaire, quadratique, seuil)
- Non Markovienne: utilisation de l'historique
- **Hiérarchique**: le leader annonce sa stratégie

---
layout: dense
---

# Equilibres differentiels

## Equilibres de Nash pour jeux a somme nulle

- `J_1 + J_2 = 0`, equilibres de point de selle
- P1 maximise, P2 minimise -> equilibre ssi point de selle existe

<img src="./images/img_049.png" alt="Point de selle d'un jeu differentiel a somme nulle" style="display:block; margin:4px auto; width:100%; max-height:26px; object-fit:contain;">

## Equilibres de Stackelberg

- Le "leader" annonce en tenant compte des reponses des autres
- Ex: croissance economique (taxe sur le capital + consommation)

## Jeux cooperatifs/competitifs

- Possibilite de dialogue -> maximisation commune
- Division en partie cooperative et partie competitive (valeur co-co)

## Equilibres en boucle ouverte

- u* est un equilibre de Nash ssi aucun joueur ne peut ameliorer seul
- Resolution: 2 optimisations -> conditions necessaires

<img src="./images/img_050.png" alt="Equilibres en boucle ouverte : conditions necessaires" style="display:block; margin:4px auto; width:100%; max-height:26px; object-fit:contain;">

## Equilibres Markoviens

- Resolution d'equations differentielles
- Jeux lineaires quadratiques -> solution analytique

<div style="display:grid; grid-template-columns:1fr 1fr; gap:6px; align-items:center;">
<img src="./images/img_051.png" alt="Equilibres Markoviens : jeux lineaires quadratiques" style="width:100%; height:75px; object-fit:contain;">
<img src="./images/img_052.png" alt="Solution analytique des jeux lineaires quadratiques" style="width:100%; height:75px; object-fit:contain;">
</div>

---
layout: default
---

# Méthodes calculatoires

## Méthodes directes

- Formulation du programme mathematique et resolution

## Méthodes indirectes

- Utilisation d'equations differentielles partielles

## Méthode d'echantillonnage incremental

- Ex: poursuite evasion
- RRT -> exploration d'arbre
  - Convergence avec nombre d'echantillons suffisant
  - Similaire au filtrage particulaire

<img src="./images/img_053.png" alt="Echantillonnage incremental : convergence avec le nombre d'echantillons" style="display:block; margin:2px auto 0; max-height:20px; width:auto; max-width:100%; object-fit:contain;">
<img src="./images/img_054.png" alt="Poursuite-evasion : exploration par arbre RRT, similaire au filtrage particulaire" style="display:block; margin:4px auto; max-height:28px; width:auto; max-width:100%; object-fit:contain;">

## Pour aller plus loin

- Details mathematiques dans les references du cours

---
layout: section
---

# Questions?

---
layout: section
---

# Plan du cours

---
layout: default
---

# Sommaire (suite)

- I. Introduction
- II. Resolution de problemes
- III. Bases de connaissances et logique
- IV. Incertitude et modèles probabilistes
- V. Théorie des jeux
- **VI. Apprentissage**
- VII. Traitement du langage naturel
- VIII. Presentation projets

---
layout: dense
---

# Projets de groupe

1. Moteur de recherche augmente par le raisonnement et le langage naturel
2. Conception de bots de services sur reseaux sociaux
3. Conception d'un modèle d'inference pour l'analyse de sentiment
4. Création d'une plateforme sémantique LDP
5. Resolution de Captchas par deep learning
6. Entrainement de stratégies de trading algorithmiques sur crypto monnaies
7. Amelioration par l'apprentissage d'un agent joueur de Go simple
8. Evolution de vaisseaux spatiaux par algorithmes génétiques dans le jeu de la vie
9. Pilotage d'un cluster de cache distribue pour le portage d'applications dans le Cloud

---
layout: end
---

# Merci

**Jean-Sylvain Boige**

jsboige@myia.org
