---
theme: ../theme-ia101
title: "Intelligence Artificielle - Theorie des jeux"
info: IA 101 - Theorie des jeux, analyse strategique, mecanismes
paginate: true
drawings:
  persist: false
transition: slide-left
mdc: true
layout: cover
---

# Theorie des jeux

INTELLIGENCE ARTIFICIELLE -- V

**Analyse strategique**

- Jeux Bayesiens
- Theorie des mecanismes
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
- IV. Incertitude et modeles probabilistes
- **V. Theorie des jeux**
- VI. Apprentissage
- VII. Traitement du langage naturel
- VIII. Presentation projets

---
layout: dense
---

# Theorie des jeux

## Environnement multi-agent

- Un seul Decideur
  - Planification / Synchronisation
  - Multi-Effecteurs / Multi-corps (decouplage)
    - Centralise (state = pool) vs decentralise
- Decideurs multiples -> theorie des jeux
  - But commun / buts propres, adversite et/ou collaboratif
  - Information parfaite / imparfaite
  - A un tour: Joueurs, actions, recompenses

## Etudes des interdependances strategiques

- Objectif double
  - Design d'agent: Quelle est la meilleure strategie?
  - Design de mecanisme: Quelles sont les bonnes regles?
- Optimisation de strategies: pure / mixte (randomisee)
- Von Neumann -> Maximin: Jeux a somme nulle

---
layout: section
---

# Analyse strategique

---
layout: dense
---

# Analyse strategique

## Jeux simultanes

- Matrice de gains
- Dilemme du prisonnier: Parler ou se taire
  - Strategie pure strictement dominante (stable)
  - Mais Pareto dominee (global mais instable)

## IESDS

- Elimination iterative des strategies strictement dominees
- Reduction progressive de la matrice

## Equilibre de Nash

- Optimum local dans l'espace des politiques
- Aucun agent n'a de motivation a changer de strategie
  - = Une loi que personne n'enfreint sans la police
- Garanti d'exister / importance de la Coordination

## Meilleure reponse

- Etant donnee les autres choix
- Equilibre de Nash = meilleure reponse pour tous

---
layout: dense
---

# Strategies mixtes

## Occurrences

- Ex: Penalty, pile ou face -- Jeux a somme nulle
- Distribution probabiliste de strategies pures
- Theoreme de Nash: 1 equilibre doit exister

## Algorithme de strategie mixte

- Utilites esperees -> equations pour l'indifference a l'equilibre
  - `EU_L = sigma_u(-3) + (1-sigma_u)(1) = EU_R = sigma_u(2) + (1-sigma_u)(0)` -> `sigma_u = 1/6`
  - `EU_U = sigma_L(3) + (1-sigma_L)(-2) = EU_D = sigma_L(-1) + (1-sigma_L)(0)` -> `sigma_L = 1/3`

## Calcul des gains esperes

- Somme ponderee par les probabilites individuelles
- Ex: Bataille des sexes (boxe vs ballet): 2 equilibres purs + mixte 1/3 vs 2/3 -> gain 2/3

---
layout: dense
---

# Equilibres de strategie mixte

## Strategie mixte dominant strictement une pure

- Ex: 3 lignes, milieu dominee, calcul des probas

## Dominance faible

- Domine ou indifferente (>=)
- Elimination iterative, mais reste autres equilibres

## Equilibres infinis

- Ex: equilibres partiellement mixtes

## Regle impaire

- Presque tous les jeux ont un nombre impair d'equilibres
- Nombre infini ou pair generalement lie a la dominance faible
  - Ex nombre pair: l'argent gratuit
  - Sinon verifier si on n'a pas oublie une mixte

---
layout: dense
---

# Jeux sequentiels

## Jeux a tours successifs

- Conflits, negociations etc.
- Jeu de la guerre des prix (in/out)
  - Accept, out = equilibres
  - Difference = menace credible?
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

---
layout: dense
---

# Jeux a etapes

## Plusieurs manches

- Sous-jeux simultanes, Gains independants, connaissance du passe
- Difficile a dessiner (exponentiel)
- Theoremes:
  - Derniere etape -> Equilibre de Nash (passe non modifiable)
  - Autres: jouer equilibres de Nash = 1 equilibre de sous-jeu
  - Mais autres equilibres de sous-jeu possibles (cooperation)

## Strategies de punition

- Ex: Prisonnier puis Argent gratuit -> equilibre faible (0,0) = menace de punition
- Menaces "credibles" importantes

## Se lier les mains

- Ex: bruler le pont derriere soi -> Rend la menace credible

## Problemes de l'induction arriere

- Ex: le millepattes -- equilibre pessimiste, pas constate en pratique
- Hypotheses -> Maths -> conclusions (probleme: rationalite limitee)
- Induction avant = passe rationnel (supprime un equilibre)

## Dilemmes repetes

- Punition perpetuelle, oeil pour oeil etc. -- Evolution de la confiance

---
layout: dense
---

# Formes strategiques avancees

## Raisonner avec des variables

- Ex: bataille des sexes, A>B>C, algorithme de strategie mixte
  - `sigma_u = (b-c)/(a+b-2c)` et `0 < sigma_u < 1`
- Ex: Topologie complete 2x2

## Equilibre de lame de couteau

- X>0 -> Up, Left vs x<0 -> down, right, x=0 -> tous
- Instable autour de x=0, probabilite faible -> ignore

## Modeles causaux

- Proprietes causales des inputs -> Statiques comparees
  - Calcul des gradients aux equilibres
- Ex: Football penalty: `sigma_KL = 1/(1+x)`, `sigma'_KL = -1/(1+x^2) < 0`
  - -> il tire davantage son cote faible (compense)

## Pierre, papier, ciseaux

- Pas de strategie pure -> cycle
- Support des strategies mixtes, EU egales dans le support
- Theoreme: 2 joueurs, symetrique a somme nulle -> EU = 0
- Resolution: indifference `sigma_L = 1/4` (ciseaux pour compenser)

---
layout: default
---

# Espaces de strategies infinis

## Jeux sans equilibre

- Nombre fini de strategies pures -> Matrices + theoremes de Nash
- Certains jeux ont une infinite de strategies pures
  - Pas de matrice, pas forcement d'equilibre de Nash

## Duels

- 100 m, 2 balles, precisions differentes (0% a 100m, 100% a 0m)
- Equilibre = meme distance (preuve par contradiction)
- Ex: date de sortie de produits concurrents

## Loi de Hotelling et l'electeur median

- 2 vendeurs de glace sur la plage, choix de l'emplacement
  - Equilibre = les deux au milieu
- Principe important en politique: theoreme de l'electeur median
  - Vainqueur de Condorcet (cf Choix social)

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
- Representation = Distribution de probabilite sur les types de joueurs
  - Information imparfaite -> Analyse probabiliste

## Formalisation

`G = <N, Omega, <A_i, u_i, T_i, tau_i, p_i, C_i>>`

- N joueurs, Omega etats de la nature, A_i actions du joueur i
- T_i type du joueur i, U_i recompense, p_i distribution des types
- Strategies pures: `S_i = {s_i: T_i -> A_i}`

## Equilibres de Nash Bayesien

- Objectif = maximisation de la recompense esperee
- De nombreux equilibres sans restrictions supplementaires

## Ex: Dilemme du Sheriff

- Criminel (p) vs civil (1-p), tirer ou pas
- Strategies dominantes: tirer pour criminel, pas pour civil
- Pour le Sheriff: `E(tirer) = p-1`, `E(pas) = -2p`
  - p>1/3 = tirer

---
layout: dense
---

# Equilibres Bayesiens parfaits (PBE)

## Jeux sequentiels

- Rappel SPE -> equilibres non plausibles (menaces non credibles)
- Systemes de croyance: assignations de probabilites sur les types
  - "Consistant" -> Probabilites par application des strategies (Bayes)
- Rationalite sequentielle: recompense esperee maximale

## Definition PBE

- Profile strategique et systeme de croyance consistant tels que les strategies sont sequentiellement rationnelles

## Jeux de signalisation

- Emetteur S (connait son type) -> message m, Recepteur R -> action a
- 3 categories de PBE:
  - **Pooling**: emetteurs choisissent le meme message (pas de signal)
  - **Separating**: messages toujours differents -> croyance deterministe
  - **Semi-separation** (partial-pooling): mixte

## Exemples

- Jeu de reputation (guerre des prix): pooling ou separating
- Jeu d'education: doue ou pas, diplome ou pas (signal) -> PBE de separation
- Biere-quiche: P=0.9 -> pooling, P=0.2 -> strategies mixtes

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

## Theorie des jeux cooperatifs

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
  - Bons resultats avec exploration du graphe de structure

---
layout: section
---

# Conception de mecanismes

---
layout: dense
---

# Conception de mecanismes

## Theorie des jeux inverse

- Si les agents sont rationnels, quelles sont les bonnes regles?
- Dans le cadre Bayesien d'information imparfaite
  - Le "principal" souhaite inciter a reveler la vraie utilite

## Formalisme

- Le principal choisit la structure de recompense `y()`
- Les agents declarent `theta_hat` (et peuvent mentir)
- Fonction de choix social `f(theta)` a implementer par `y(theta_hat)`

## Principe de revelation

- Mecanisme incitatif verace (IC): non manipulable, revelateur
  - `theta_hat(theta) = theta`
- S'il existe un mecanisme y implementant f, alors il existe une version IC
- 2 versions:
  - **DSIC**: Implementation en strategies dominantes
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
  - Tres repandu: eBay, AdWords etc.
- Theoreme d'equivalence de revenue

## Bien commun

- Tragedie des communs (ex: pollution)
  - Strategie de pollution dominante mais pas optimale (Pareto)
  - Necessite d'expliciter les externalites (ex: taxe carbone)

## Mecanisme de Vickrey-Clarke-Groves (VCG)

- N Encherisseurs declarent utilite de M ressources
- Allocation maximisant la somme des utilites
- Taxe: `T_i = U_max(sans i) - U_max(sans i, sans ressource j)`

---
layout: dense
---

# Allocation par les votes

## Theorie du choix social

- Preferences individuelles rationnelles -> Ordre de preference social
- Proprietes d'une bonne fonction de choix social:
  1. Condition de Pareto / critere d'unanimite
  2. Independance des alternatives non pertinentes
  3. Pas de dictature

## Resultats negatifs

- **Paradoxe de Condorcet**: A,B,C -> 2/3 de mecontents
- **Theoreme de Arrow**: Impossible de satisfaire 1, 2 et 3 simultanement (>= 3 options)
- **Theoreme de Gibbard-Satterthwaite**: Toute FCS deterministe avec Pareto et >2 choix est manipulable ou dictatoriale

---
layout: dense
---

# Critere de Condorcet

## Condition du vainqueur de Condorcet

- La meilleure aux autres options prises paire a paire
  - Ex: Uninominal a 2 tours: Bayrou vainqueur de Condorcet mais pas au 2e tour
- **Indifference aux petits candidats**: vainqueur stable aux changements
- Paradoxe de Condorcet: pas de garantie d'existence

## Theoremes de l'electeur median

- 1er theoreme: Gauche-droite -> existence du vainqueur -> electeur median
- 2e theoreme: Gauche-droite + valeur intrinseque

## Si pas de vainqueur de Condorcet

- Methode **Minimax**: celui qui fait le mieux au pire
  - Mais tres strategique (ex: anarchistes)
- Methode de **Schulze**: elimination iterative des derniers du peloton de tete
  - Robuste a la manipulation (electeurs raisonnables)

---
layout: dense
---

# Procedures de votes connues

- **Referendum**: 2 options -> methode de la majorite robuste (la seule)
- **Vote pluraliste uninominal** (n candidats): critique (vote utile)
- **Vote a second-tour instantane**: Preferences, elimination du dernier
  - Pas de critere de Condorcet
- **Methode de Condorcet**: comparaisons paires a paires -> Schulze

## Methodes utilitaristes

- **Compte de Borda**: preferences, score = ordre (manipulable)
- **Vote par assentiment**: elimination, majorite d'approbation
  - Theoreme de robustesse au mensonge
- **Scrutin au jugement majoritaire**: mediane des scores
  - Seule procedure avec majorite d'une meme note validee + monotonie

## Scrutins stochastiques

- **Scrutin Stochocratique**: option preferee puis tirage au sort
  - Theoreme d'Hylland: seule methode avec unanimite non strategique
- **Condorcet randomisee**: loterie ponderee dans le peloton de tete
  - Ponderation selon equilibre de Nash -- critere de Condorcet + non strategique

---
layout: default
---

# Allocation par la negociation

## Modele des offres alternees

- Si pas d'accord: Accord de conflit -> fenetre de negociation
- Nombre de manches:
  - 1 manche: Ultimatum (J1 a tout le pouvoir)
  - 2 manches: J2 a tout le pouvoir
  - N manches: JN a le pouvoir
- Agents impatients: facteurs de discompte `0 <= gamma_i < 1`
  - Offre a l'equilibre: `A_1 = (1-gamma_2)/(1-gamma_1*gamma_2)`

## Domaines orientes taches

- Offres (T1, T2) de repartitions de taches parmi T
- Protocole de concession monotone

## Strategie de Zeuthen

- Mesure de l'aversion au risque de conflit
- Le risque plus faible concede, sinon tirage au sort

---
layout: default
---

# Theorie de la negociation

## Demarche

- Hypotheses -> Modeles de jeux -> Equilibres et pouvoirs de negociation

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

## Theorie des jeux + theorie du controle

- Interdependance: agents economiques, pollution, marches
- Dynamique: habitudes, technologies, accumulations, traffic
- Comportement strategique: buts antagonistes, choix

## Definitions

- Joueurs M={1,...,m}, Vecteur de controle `u_j(t)`
- Vecteur d'etat `x(t)`, equation d'etat: `x'(t) = f(x(t), u(t), t)`
- Fonction de gain: `J_j = S_j(x(T)) - integral g_j dt` -> Minimisation de L

## Structure de l'information

- **Boucle ouverte**: conditions initiales + temps: `u_j(t) = mu_j(x_0, t)`
- **Markovienne**: `u_j(t) = sigma_j(t, x(t))` (lineaire, quadratique, seuil)
- Non Markovienne: utilisation de l'historique
- **Hierarchique**: le leader annonce sa strategie

---
layout: dense
---

# Equilibres differentiels

## Equilibres de Nash pour jeux a somme nulle

- `J_1 + J_2 = 0`, equilibres de point de selle
- P1 maximise, P2 minimise -> equilibre ssi point de selle existe

## Equilibres de Stackelberg

- Le "leader" annonce en tenant compte des reponses des autres
- Ex: croissance economique (taxe sur le capital + consommation)

## Jeux cooperatifs/competitifs

- Possibilite de dialogue -> maximisation commune
- Division en partie cooperative et partie competitive (valeur co-co)

## Equilibres en boucle ouverte

- u* est un equilibre de Nash ssi aucun joueur ne peut ameliorer seul
- Resolution: 2 optimisations -> conditions necessaires

## Equilibres Markoviens

- Resolution d'equations differentielles
- Jeux lineaires quadratiques -> solution analytique

---
layout: default
---

# Methodes calculatoires

## Methodes directes

- Formulation du programme mathematique et resolution

## Methodes indirectes

- Utilisation d'equations differentielles partielles

## Methode d'echantillonnage incremental

- Ex: poursuite evasion
- RRT -> exploration d'arbre
  - Convergence avec nombre d'echantillons suffisant
  - Similaire au filtrage particulaire

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
- IV. Incertitude et modeles probabilistes
- V. Theorie des jeux
- **VI. Apprentissage**
- VII. Traitement du langage naturel
- VIII. Presentation projets

---
layout: dense
---

# Projets de groupe

1. Moteur de recherche augmente par le raisonnement et le langage naturel
2. Conception de bots de services sur reseaux sociaux
3. Conception d'un modele d'inference pour l'analyse de sentiment
4. Creation d'une plateforme semantique LDP
5. Resolution de Captchas par deep learning
6. Entrainement de strategies de trading algorithmiques sur crypto monnaies
7. Amelioration par l'apprentissage d'un agent joueur de Go simple
8. Evolution de vaisseaux spatiaux par algorithmes genetiques dans le jeu de la vie
9. Pilotage d'un cluster de cache distribue pour le portage d'applications dans le Cloud

---
layout: end
---

# Merci

**Jean-Sylvain Boige**

jsboige@myia.org
