<!-- Slide number: 1 -->
# Résolution de problèmes
1
Intelligence Artificielle - II

Explorations non informée et informée
Jeux
Problèmes à satisfaction de contraintes
IA 101

### Notes:

<!-- Slide number: 2 -->
# Plan du cours
2
Introduction
Résolution de problèmes
Bases de connaissances et logique
Raisonnement probabiliste
Apprentissage
Traitement du langage naturel
TP final projets trimestriels
IA 101

### Notes:

<!-- Slide number: 3 -->
# Sommaire
3
Agents de résolution de problèmes
Résolution de problèmes par exploration
Exploration non informée
Heuristiques et exploration informée
Exploration en situation d’adversité: les jeux
Minimax et Alpha-Bêta
Décisions imparfaites
Problèmes à satisfaction de contraintes
Backtracking
Exploration locale
Structure des problèmes
TP: Mise en œuvre de l’exploration et de la satisfaction de contrainte dans un contexte ludique
IA 101

### Notes:

<!-- Slide number: 4 -->
# Agent fondé sur des buts
4
Réactif  Délibératif
Exploration du Futur, séquences d’actions
Recherche, planification

![](Image1.jpg)
Intelligence(s)

### Notes:
 design best program for given machine resources

<!-- Slide number: 5 -->
# Résolution de problèmes
5
Quel est l’objectif à atteindre ?
Quelles sont les actions possibles ?
Quel est la représentation de l’état courant?

Actions
EtatInitial
Etat
Final
Intelligence(s)

### Notes:

<!-- Slide number: 6 -->
# Agents de résolution de problèmes
6

![](Image2.jpg)
IA 101

### Notes:

<!-- Slide number: 7 -->
# Exemple: Itinéraire
7

En vacances en Roumanie; actuellement à Arad.
Le vol part demain de Bucharest
Formuler le but:
Etre à Bucharest
Formuler le problème:
Etats: plusieurs villes
Actions: conduire d’une ville à l’autre
Trouver la solution:
Séquence de villes e.g., Arad, Sibiu, Fagaras, Bucharest

![romania-distances](Picture4.jpg)
IA 101

### Notes:

<!-- Slide number: 8 -->
# Types de problèmes
8

Déterministes, complètement observables   problème à état simple
L’agent sait exactement dans quel état il sera; la solution est une séquence
Non-observable  problème sans capteur dit conformant
L’agent peut ne pas savoir où il est, la solution est une séquence
Non déterministe et / ou partiellement observable  problème de contingence
Les percepts fournissent une nouvelle information à propos de l’état courant
Entrelacement {calcul, action}
Espaces d’états inconnu  problèmes d’exploration en ligne
IA 101

### Notes:

<!-- Slide number: 9 -->
# Formulation de problèmes
9
Un problème est défini par les éléments suivants:

Etat initial e.g., “à Arad"
Actions ou fonction successeur S(x) = ensemble de paires actions - état
e.g., S(Arad) = {<Arad  Zerind, Zerind>, … }
AIMA : ActionsFunction et ResultFunction = modèle de transition
1+2 = Espace des états -> graphe -> chemins
Test de but, qui peut être
explicite, e.g. x = “à Bucharest"
implicite, e.g. EchecEtMat(x)
Coût de chemin (optionnel, additif)
e.g., Somme des distances, Nombre d’actions exécutées, etc.
c(x,a,y) est le coût d’étape, (≥ 0)
Une solution est une séquence d’actions (chemin) qui condition de l’état initial à un état but
Optimale = coût minimum

IA 101

### Notes:

<!-- Slide number: 10 -->
# Sélection d’un espace des états
10
Le monde réel est très complexe
L’espace des états doit faire l’objet d’une abstraction
Etat (abstrait) = ensemble d’états réels
Action (abstraite) = combinaison complexe d’action réelles
e.g. « Arad -> Zerind » représente un ensemble de routes, détours, pauses etc.
Pour une réalisation garantie, chaque état réel « à Arad » doit conduire à un état réel « à Zerind »
Solution (abstraite) = ensemble de chemins réels qui sont solutions dans le monde réel
Chaque action abstraite doit être plus « facile » que dans le problème réel.
Problème jouet: Expérimenter avec les méthodes de résolution
IA 101

### Notes:

<!-- Slide number: 11 -->
# Exemple Abstraction: Assemblage robotique
11

Etats: Coordonnées réelles des joints du robot et des objets
Test de but: Objet assemblé
Etat initial: Pièces détachées, bras au repos
Actions: Mouvement continu des joints du bras robotique
Cout de chemin: temps d’exécution

![stanford-arm+blocks](Picture4.jpg)

<!-- Slide number: 12 -->
# Problème jouet: Le taquin
12

Etats: Position des 8 pièces + case vide
Test de but: Etat == { 0, 1, 2, 3, 4, 5, 6, 7, 8 }
Etat initial: La moitié des états possible
Actions: case vide  gauche, droite, haut, bas
Cout de chemin: 1 par étape
[Note: puzzle à glissement de pièces: problèmes NP-complet (durs)]

![](Image1.jpg)

<!-- Slide number: 13 -->
# Problème jouet: Les 8 reines
13

Etats: Disposition de 0-8 reines
Test de but: 8 reines sont présentes, et aucune n’est menacée
Etat initial: Echiquier vide
Actions: Poser une reine
Cout de chemin: N.A / 1 par étape
Note: Meilleure formulation: une reine par colonne, de gauche à droite, légale.
1,8* 10^14 positions  (dur)  2057 positions (facile)

![](Image2.jpg)

<!-- Slide number: 14 -->
# Questions?
14
IA 101

### Notes:

<!-- Slide number: 15 -->
# Sommaire
15
Agents de résolution de problèmes
Résolution de problèmes par exploration
Exploration non informée
Exploration informée (heuristiques)
Exploration en situation d’adversité: les jeux
Minimax et Alpha-Bêta
Décisions imparfaites
Problèmes à satisfaction de contraintes
Backtracking
Exploration locale
Structure des problèmes
TP: Mise en œuvre de l’exploration et de la satisfaction de contrainte dans un contexte ludique
IA 101

### Notes:

<!-- Slide number: 16 -->
# Arbre d’exploration
16
Idée de base:
Exploration simulée (hors ligne) de l’espace des états en générant les successeurs des états déjà explorés (Développement des états)
Ensemble des Nœuds feuilles = Frontière d’exploration
Choix des nœuds à développer = Stratégie d’exploration

![](Image1.jpg)
IA 101

<!-- Slide number: 17 -->
# Arbre d’exploration: exemple
17

![search-map3c](Picture4.jpg)
IA 101

<!-- Slide number: 18 -->
# Exploration de graphe
18
Idée de base:
Etats répétés  chemins avec boucle
Solution : mémoire = ensemble exploré
Frontière: sépare espace exploré et espace inconnu

![](Image2.jpg)
IA 101

<!-- Slide number: 19 -->
# Infrastructure: Etats vs Nœuds
19
Etats != Noeud
Un Etat est une représentation de la configuration réelle
Un Nœud est une structure de données constitutive d’une exploration
Inclut l’état, le nœud parent, l’action, le coup d’étape g(x), la profondeur
La fonction de développement crée de nouveaux nœuds, et utilise la fonction successeurpour déterminer les états enfants

![](Image4.jpg)

![](Image3.jpg)
IA 101

<!-- Slide number: 20 -->
# Stratégies d’exploration
20
Une stratégie d’exploration définit l’ordre de développement des nœuds.
Critères d’évaluation
Complétude: Garantie d’obtenir une solution si elle existe
Optimalité: Garantie d’obtenir une solution de coût minimal
Complexité en temps: ~ nombre de nœuds développés
Complexité en espace: ~ nombre max de nœuds en mémoire
Complexités en temps et en espace s’évaluent selon:
b: Facteur maximal de branchement dans l’arbre de recherche
d: (depth)  profondeur de la solution de moindre coût
m: profondeur maximale de l’espace d’états (souvent ∞)
IA 101

<!-- Slide number: 21 -->
# Stratégies d’exploration non informée
21
Les stratégies non informée (aveugle) utilisent uniquement la définition du problème
Stratégies d’exploration en largeur
En largeur d’abord (BFS: Breadth First Search)
A coût uniforme (UCS: Uniform Cost Search)
Stratégies d’exploration en profondeur
En profondeur d’abord (DFS: Depth First Search)
En profondeur limitée (DLS: Depth Limited Search)
Itérative en profondeur (IDS: Iterative Depth Search)
Variantes
Bidirectionnelle
IA 101

<!-- Slide number: 22 -->
# Exploration en largeur d’abord (BFS)
22
Développe les nœuds les moins profonds en premier

La frontière est une queue (File ou FIFO)

![](Image2.jpg)

![](Image1.jpg)
IA 101

<!-- Slide number: 23 -->
# Propriétés de l’exploration en largeur
23
Complet ? Oui (si b est finit)
Complexité en temps ?
1+b+b2+b3+… +bd + b(bd-1) = O(bd+1)
Complexité en espace ?
O(bd+1) chaque nœud est gardé en mémoire
Optimale? Oui si coût d’étape = 1
L’espace est le plus gros problème

![](Image3.jpg)
IA 101

<!-- Slide number: 24 -->
# Exploration à coût uniforme (UCS)
24
Développe les nœuds les moins coûteux en premier
La frontière est une queue triée par coût de chemin
Equivaut à l’exploration en largeur d’abord si le coût d’étapes est uniforme
En théorie de graphes = algorithme de Dijkstra
Caractéristiques
Complet? Oui, si coût d’étape ≥ ε
Complexité en temps et en espace: O(bplafond(C*/ ε)) avec C* le coût d’une solution optimale
Optimal ? Oui: les nœuds sont développés dans l’ordre des coût de chemin
IA 101

<!-- Slide number: 25 -->
# Exploration en profondeur d’abord (DFS)
25
Développe les nœuds les plus profonds en premier
La frontière est une Pile (LIFO)
Les branches déjà explorés ne sont pas conservées en mémoire

Caractéristiques:
Complet ? Non: échoue dans les espaces de profondeur infinie
ou avec des boucles -> exploration de graphe
Complexité en temps: O(bm) terrible si m beaucoup plus grand que d
mais si les solutions sont dense, plus rapide qu’en largeur
Complexité en espace: O(bm), linéaire en espace !
Optimal: Non
Variante: Exploration avec retour arrière (backtracking):
On développe 1 seul successeur à la fois  O(m) en espace
+ Optimisation en modifiant les états plutôt qu’en les copiant (retour arrière = annulation)

![](Image2.jpg)
IA 101

<!-- Slide number: 26 -->
# Exploration en profondeur limitée (DLS)
26
= Exploration en profondeur d’abord avec une profondeur limite l
Les nœuds de profondeur l n’ont pas de successeur
Complet si l ≥ d= diamètre des l’espace des états
Implémentation récursive:

![](Image1.jpg)
IA 101

<!-- Slide number: 27 -->
# Exploration itérative en profondeur (IDS)
27
On augmente graduellement l

Coût du même ordre que l’exploration en profondeur limitée
Pour b = 10, d= 5: ~+10% (contre intuitif)
NDLS = 1 + 10 + 100 + 1,000 + 10,000 + 100,000 = 111,111
NIDS = 6 + 50 + 400 + 3,000 + 20,000 + 100,000 = 123,456
 Caractéristiques
Complet: Oui
Complexité en temps: O(bd)
Complexité en espace: O(bd)
Optimale: Oui si coût d’étape = 1
De façon analogue pour l’exploration à coût uniforme:
Exploration itérative par allongement (ILS)

![](Image2.jpg)
IA 101

<!-- Slide number: 28 -->
# Exploration Bidirectionnelle
28
Quand on connait l’état but
Double exploration vers l’aval et vers l’amont
Intérêt: O(bd/2) + O(bd/2) est très inférieur à O(bd)
Exemple courant
Logiciel de navigation GPS

Difficultés:
Nécessite une fonction Prédécesseurs
Contrôle de l’intersection
maintient de la frontière, même en profondeur + hachage pour comparaison
+ Solution non optimale même en largeur  continuer pour trouver les raccourcis
Etats buts complexes:
Plusieurs états buts  Etat but fictif en l’aval des états buts
Description implicite (ex: 8 reines)  difficile

![](Image1.jpg)
IA 101

<!-- Slide number: 29 -->
# Résumé Exploration non informée
29
Nécessité d’une abstraction du monde réel
Variété des stratégies non informées
En largeur = Queue
En profondeur = Pile
Compromis complexité espace vs temps
Présence de cycles  exploration de graphe
Comparaison des explorations non informées:

![](Espaceréservéducontenu2.jpg)
IA 101

<!-- Slide number: 30 -->
# Les missionnaires et cannibales
30
Les missionnaires et cannibales doivent traverser la rivière
Pas plus de 2 personnes en même temps sur la barque
Si + de cannibales que de missionnaires d’un côté ou l’autre
 ils se font manger

![](Image5.jpg)
Intelligence(s)

<!-- Slide number: 31 -->
# Questions?
31
IA 101

### Notes:

<!-- Slide number: 32 -->
# TP
32
exploration non informée
Services Web PKP: Search
Librairie js : PathFinding.js

Aima javascript
IA 101

### Notes:

<!-- Slide number: 33 -->
# Sommaire
33
Agents de résolution de problèmes
Résolution de problèmes par exploration
Exploration non informée
Exploration informée (heuristiques)
Exploration en situation d’adversité: les jeux
Minimax et Alpha-Bêta
Décisions imparfaites
Problèmes à satisfaction de contraintes
Backtracking
Exploration locale
Structure des problèmes
TP: Mise en œuvre de l’exploration et de la satisfaction de contrainte dans un contexte ludique
IA 101

### Notes:

<!-- Slide number: 34 -->
# Stratégies d’exploration informée
34
Les stratégies informées utilisent des connaissances du problème en plus de sa définition
Exploration par le meilleur d’abord
Exploration gloutonne (GBF: Greedy Best-First)
Exploration A étoile (A*: A-Star)
Stratégies d’exploration locale
Exploration par escalade (HC: Hill-Climbing)
Exploration par recuit simulé (SA: Simulated Annealing)
Exploration locale en faisceau (LBS: Local Beam Search)
Algorithmes génétiques (GAs: Genetic Algorithms)
IA 101

<!-- Slide number: 35 -->
# Exploration par le meilleur d’abord
35
Idée: utiliser une fonction d’évaluation f(n) pour chaque nœud.
Estimation de la « désirabilité »
On développe les nœuds non explorés les plus désirables
Implémentation
On tri les nœuds dans la frontière en ordre décroissant de désirabilité
Cas spéciaux:
Exploration gloutonne
Exploration A étoile
IA 101

<!-- Slide number: 36 -->
# Exploration gloutonne
36
f(n) = h(n) =Heuristique = estimation du coût depuis n au but
Ex: hSLD(n) = distance à vol d’oiseau de n à Bucarest (straight-line distance)
Développe le nœud qui semble êtrele plus proche du but
Caractéristiques:
Complet:
Arbre: Non, Possibilité de boucle (cf Iasi  Fagaras)
Graphe: Oui pour espaces finis
Complexité en temps: O(bm)
mais une bonne heuristique donne de bons résultats
Complexité en espace: O(bm) :
on garde tous les nœuds en mémoire
 Optimal? Non

![](Image1.jpg)

![](Image4.jpg)
IA 101

<!-- Slide number: 37 -->
# Heuristiques admissibles et consistantes
37
Une heuristique h(n) est dit admissible si pour chaque nœud n, h(n) ≤ h*(n), où h*(n) est le vrai coût pour rejoindre l’état but depuis n
Une heuristique admissible ne surestime jamais le coût pour atteindre le but: elle est optimiste
Exemple hSLD(n) ne surestime jamais la distance routière
Une heuristique est consistante (ou monotone) si pour chaque nœud n, et chaque successeur n’ de n généré par une action a: h(n) ≤ c(n,a,n') + h(n')
≈ inégalité triangulaire
Consistante  admissible

![consistency](Picture4.jpg)
IA 101

<!-- Slide number: 38 -->
# Exploration A*
38
Idée: éviter de développer les nœuds déjà coûteux
Minimisation du coût total estimé de la solution
Fonction d’évaluation f(n) = g(n) + h(n)
g(n) = coût pour atteindre n
h(n) = coût estimé de n au but
f(n) = coût total estimé du chemin au but en passant par n
Identique à UCS avec g+h au lieu de g
Théorèmes:
 Si h(n) est admissible, A* est optimal en exploration d’arbre
Démonstration par l’absurde en développant
Si h(n) est consistante, A* est optimal en exploration de graphe
Démonstration: f est monotone  puis par l’absurde en développant
IA 101

<!-- Slide number: 39 -->
# Caractéristiques de A*
39

![f-circles](Picture4.jpg)
Optimalité de A*
Ajoute graduellement des « f-contours » de nœuds
Le contour i a tous les nœuds avec f=fi où fi < fi+1
Propriétés de A*
Complet: Oui
Sauf s’il existe une infinité de nœuds avec f ≤ f(G)
Complexité en temps: Exponentielle
Complexité en espace: Idem
 Optimal? Oui (cf. théorèmes)
+ optimalement efficace pour toute heuristique consistante donnée
Limites
Nombre d’états dans l’espace d’exploration des contours souvent exponentiel.
Souvent, le principal problème est la mémoire
Démos itinéraires
IA 101

<!-- Slide number: 40 -->
# Variations
40
Exploration heuristique à mémoire limitée
A* avec approfondissement itératif (IDA*)
Coupure: coût f le plus faible parmi les nœuds en dépassement
Exploration récursive par le meilleur d’abord (RBFS)
Espace en mémoire linéaire: valeur f du meilleur chemin alternatif
Récursion avec valeur rapportée: meilleur valeur f des enfants oubliés
Mais excès inverse: trop peu de mémoire et trop de « redéveloppements »
Utilisation de toute la mémoire disponible
MA* (A* sous contrainte de mémoire)
SMA* (simplified MA*)
On oublie quand plus de place disponible, le nœud le plus mauvais
Exploration avec apprentissage
Espace des états de métaniveau = états de l’algorithme d’exploration (nœuds, arbres etc.)
Techniques d’apprentissage au métaniveau  compromis entre coût de calcul et coût de chemin
IA 101

<!-- Slide number: 41 -->
# Effet de l’exactitude de l’heuristiques
41
Efficacité fonction de l’erreur absolue ou relative de l’heuristique
Δ = h* - h et ε = (h* - h)/ h*
Complexité en O(bΔ) ou O(bεd) à coût d’étape constant
Facteur de branchement effectif b*
Facteur de branchement pour une exploration équivalente (même nombre de développements) sans heuristique (exploration à coût uniforme)
Bonne indication de l’utilité globale de l’heuristique
Dominance:
Si h1 et h2 sont admissibles et h2(n) ≥ h1(n) ∀ n, h2 domine h1
 si h2 domine h1, h2 est meilleure
IA 101

<!-- Slide number: 42 -->
# Production d’heuristiques
42
Problèmes relaxés
Problème avec moins de restrictions sur les actions = problème relaxé
Coût exact d’une solution optimale pour une problème relaxé = heuristique admissible
Exemple du Taquin
Une pièce peut bouger n’importe où  h1 (nb pièces mal placées)
Une pièce peut bouger sur toute case adjacente  h2 (distance Manhattan)
Sous-problèmes
Exemple du taquin: pièces 1,2,3 et 4 uniquement à placer
Bases de données de motifs
Coût exact de solutions de sous-problèmes = Heuristique pour le problème général
Motifs disjoints
Question de l’additivité des heuristiques admissibles
Apprentissage d’heuristiques
Utilisation de l’expérience sur des solutions connues
Apprentissage inductif à partir des caractéristiques pertinentes
Approche classique: h(n) = c1 x1 (n) + c2 x2(n)
Domaine vaste: Apprentissage = machine learning
IA 101

<!-- Slide number: 43 -->
# Algorithmes d’exploration locale
43
Souvent, le chemin ne compte pas, le but est la solution
Espace des états = ensemble de configurations complètes
Trouver une configuration satisfaisant des contraintes (ex 8 reines)
On peut utiliser un algorithme d’exploration locale
On conserve un simple état « courant », qu’on tente d’améliorer
Avantages:
Consomme peu de mémoire
Peut fonctionner dans des espaces de grande taille ou infinis
Exemple: 8 reines

![4queens-sequence](Picture4.jpg)
IA 101

<!-- Slide number: 44 -->
# Paysage de l’espace des états
44
Problèmes d’optimisation :
Objectif = trouver le meilleur état selon une fonction objectif
Utilité du paysage de l’espace des états
On recherche un maximum (f = -h)
Complet
 On trouve toujours un but
 Optimal
On trouve toujours un maximum global

![](Image1.jpg)
IA 101

<!-- Slide number: 45 -->
# Exploration par escalade (HCS)
45
Escalade par la plus forte pente:

Exploration locale « gloutonne »
Maxima locaux
Crêtes, plateaux, paliers
Solution: déplacement latéraux
Mais nécessité de limites
Escalade stochastique du premier choix, mais toujours incomplets
Escalade avec reprise aléatoire (complet)

![](Image2.jpg)

![8queens-local-minimum](Picture4.jpg)

![](Image3.jpg)
IA 101

<!-- Slide number: 46 -->
# Exploration par recuit simulé (SA)
46
Idée: échapper des maxima locaux:
en autorisant de mauvais déplacement
mais en diminuant progressivement leur fréquence

Fréquence  température T
Si T diminue suffisamment doucement, la probabilité de trouver un optimum global approche 1
Très utilisé dans l’agencement de circuits, l’ordonnancement
Exemple: le carton de babioles

![](Image1.jpg)
IA 101

<!-- Slide number: 47 -->
# Exploration locale en faisceau (LBS)
47
Idée: on suit simultanément k états plutôt qu’un seul
On démarre avec k états aléatoires
A chaque itération, tous les successeurs sont générés
On sélectionne les k meilleurs successeurs de la liste complète
Exemple: Perdus en foret
Transfère progressif des ressources vers les explorations fructueuses
Mais parfois, transfère trop rapide vers une petite région
Variante: exploration en faisceau stochastique
Analogue à l’escalade stochastique
k choisis au hasard, avec probabilité fonction de leur valeur
Analogue à la sélection naturelle  GAs
IA 101

<!-- Slide number: 48 -->
# Algorithmes génétiques (GAs)
48
Variante de l’exploration en faisceau stochastique
Successeurs issus de combinaisons (≈ reproduction)
Population
Individus
Taille constante
Gènes
Points de recombinaison
Mutationsaléatoires
Phénotype
Fonction d’adaptation:fitness function

![](Image1.jpg)
IA 101

<!-- Slide number: 49 -->
# Algorithme génétique pour les 8 reines
49
Génétique

Phénotype

![](Image2.jpg)

![](Image3.jpg)
IA 101

<!-- Slide number: 50 -->
# TP
50
exploration informée et locale
Services Web PKP: Search
Librairie js : PathFinding.js
IA 101

### Notes:

<!-- Slide number: 51 -->
# Exploration locale d’espaces continus
51
Etats définis par des variables réelles
Problèmes de discontinuités
Une solution = Discrétisation des voisinages
Pente pour l’escalade = gradient du paysage
Parfois résolution analytique de ∇ f = 0 (rare)
Si valable localement: x  x + α∇ f où α est le pas de l’étape
Si pas analytique: gradient empirique
Exploration linaire
α trop petit ou trop grand  on double le pas jusqu’à observer une diminution
Méthode de Newton-Raphson
Formule de Newton pour trouver g(x) = 0 : x  x – g(x) / g’(x)
En prenant pour g le gradient de f: x  x – Hf-1(x) ∇ f(x)
avec H matrice Hessienne des dérivées secondes de f
Méthodes modernes (RMSProp, ADAM)

Efficacité et optimisation des méthodes par gradient
Condition de Polyak-Lojasiewicz
Optimisation sous contrainte
Contraintes sur les variables
Programmation linéaire
 inégalités formant ensemble convexe (pas de trous)
Très étudié  complexité polynomiale

![Une image contenant texte, équipement électronique, graphiques vectoriels Description générée automatiquement](Image3.jpg)
IA 101

<!-- Slide number: 52 -->
# Exploration avec actions non déterministes
52
Cf. cours précédent  utilité des percepts
Solution != séquence  plan contingent ou stratégie
Arbres Et-Ou: entrelacement de nœuds
Nœuds Ou = Choix d’exploration classique
Nœuds Et = « Choix » de l’environnement
solutions cycliques  possibilité d’étiquettes (tant que…)
Ex: Aspirateur glissant
Où l’action de déplacement peut échouer

![](Image1.jpg)
IA 101

<!-- Slide number: 53 -->
# Exploration avec observations partielles
53
Cf. cours précédent  Etat pas situé précisément
Analogue à non déterministe
Etat de croyance: états physiques possibles
Exploration sans observation: problème conformant
Parfois parfaitement soluble. Ex: positionnement de pièces
Idée  contraindre le monde
N états physiques  2N états de croyances
Modèle de transition  étape de prévision
Exploration incrémentale
 Arbres Et-Ou complets
Exploration avec observation
Etape de prévision d’observations
Etape de mise à jour

![](Image2.jpg)
IA 101

<!-- Slide number: 54 -->
# Exploration en ligne
54
Entrelacement calcul et action
Problèmes de découverte
Ratio de compétitivité
En temps, vis-à-vis d’un espace connu
Il y a parfois des impasses
sinon l’espace est explorable sans risque
Algorithmes
DFS, Escalade avec reprise aléatoire
Mémoire  estimation H de l’heuristique h
 LRTA* (learning real time A*)
Apprentissage
De la « carte » (Etats)
Du coût d’étape
Des règles (transitions)

![](Image2.jpg)
IA 101

<!-- Slide number: 55 -->
# Résumé Exploration Informée
55
Heuristiques
Admissibles
Consistantes
Meilleur d’abord
Exploration Gloutonne (h)
A* (g+h) + variantes limitées en mémoire
Exploration Locale
Paysage de l’espace d’états
Escalade, Recuit simulé
Exploration en Faisceau, stochastique, algorithmes génétiques
Extensions
Espaces continus  gradients, programmation linéaire
Actions Non déterministe  Arbres Et-Ou
Observations partielles  prévisions, exploration en ligne
IA 101

### Notes:

<!-- Slide number: 56 -->
# Questions?
56
IA 101

### Notes:

<!-- Slide number: 57 -->
# Sommaire
57
Agents de résolution de problèmes
Résolution de problèmes par exploration
Exploration non informée
Exploration informée (heuristiques)
Exploration en situation d’adversité: les jeux
Minimax et Alpha-Bêta
Décisions impafaites
Problèmes à satisfaction de contraintes
Backtracking
Exploration locale
Structure des problèmes
TP: Mise en œuvre de l’exploration et de la satisfaction de contrainte dans un contexte ludique
IA 101

### Notes:

<!-- Slide number: 58 -->
# Jeux vs Exploration
58
Environnements:
multi-agents
concurrentiels
Classe de jeux la plus étudiée (échecs, Go)
Alternés
Déterministes
A somme nulle (h1 = -h2)
A information parfaite
Difficulté
Imprédictibilité  arbre d’exploration complet
Impraticable, solution optimale impossible
 Performance critique: temps  victoire
IA 101

<!-- Slide number: 59 -->
# Arbre de jeu
59
Ex: Morpion
Etat initial S0
Joueurs(s)
Max, Min
Actions(s)
Coups
Résultat(s,a)
Modèle de transition
Test-Terminal(s)
Fin de partie
Utilité(s,p)
Score final de p

![tictactoe](Picture4.jpg)
IA 101

<!-- Slide number: 60 -->
# Minimax
60

![minimax](Picture4.jpg)
IA 101

<!-- Slide number: 61 -->
# Algorithme Minimax
61
Faire « remonter » les valeurs Minimax
Propriétés
Complet? Oui
si l’arbre est fini
Optimal? Oui
avec adversaire optimal
Complexité en temps
O(bm)
Complexité en espace
O(bm) (DFS)
Echecs: b ≈ 35, m ≈ 100
 complètement infaisable
Mais c’est la base de:
l’analyse mathématique des jeux
meilleurs algorithmes
Cadre Multi-joueurs:
Même approche
Vecteurs Utilité
Souvent, alliances naturelles

![](Image3.jpg)
IA 101

<!-- Slide number: 62 -->
# Elagage Alpha-Bêta
62

![alpha-beta-progress4c](Picture4.jpg)
IA 101

<!-- Slide number: 63 -->
# Décisions imparfaites
63
Approche
Utilité Fonction d’évaluation heuristique Eval(s) sur des états non terminaux
Test de terminaison  Test d’arrêt Cutoff(s) pour savoir quand appliquer l’évaluation (ex: profondeur limite dlim)
Fonction d’évaluation
Cf. Humains  attributs d’un état
Classe d’équivalence  valeur attendue (utilité pondérée)
Mais trop de classes  valeur matérielle  fonction linéaire pondérée
Eval(s) = w1 f1(s) + w2 f2(s) + … + wn fn(s)
Mais non indépendance des attributs  fonction non linéaire
Si pas d’expérience, possibilité d’apprentissage (1 fou = 3 pions !)
Exploration avec arrêt
Alpha Beta Itératif pour respecter une limite de temps (+ ordre des coups)
Problème des situation instables au cutoff (prise au prochain tour)
Solution = recherche de stabilité (« quiescence », ex: pas de prise)
Problème plus subtile: Effet d’horizon
Un évènement peut être retardé au-delà du cutoff
Solution = extension de singularité (ex: prises)
IA 101

<!-- Slide number: 64 -->
# Techniques avancées
64
Elagage avant (forward pruning)
Dangereux (pas de considération des nœuds élagués)
Exploration en faisceau (n-meilleurs coups par tour)
ProbCut  probabilité que le nœuds soit hors [Alpha,Beta]
Exploration vs Consultation
Ex: Echecs: début et fin de partie documentés
Début de partie:
Consultation de tables plutôt qu’exploration
Livres d’ouverture + statistiques de bases de données de parties
Fin de partie:
Utilisation d’une Politique (correspondance directe du coup optimal)
Exploration rétrograde
IA 101

<!-- Slide number: 65 -->
# Exploration d’arbre de Monte-Carlo
65
Rollouts
Pas d’heuristique d’évaluations
Replacée par des rollouts
= simulations statistiques
Algorithme complet
Sélection
Guidé par une politique de sélection
Compromis exploration/exploitation
Expansion
Simulations = rollouts
Rétropropagation: Nœuds parents incrémentés
Politique de sélection
Intervalle de confiance supérieur UCB1=
C empirique ou modèle appris (Alpha Go)
Combinaison avec heuristique
Critère de terminaison avancée
Apprentissage par renforcement

![](Graphique7.jpg)
CS 405

<!-- Slide number: 66 -->
# Classes de Jeux complexes
66

![](Image7.jpg)

![](Image9.jpg)

![](Image10.jpg)
IA 101

<!-- Slide number: 67 -->
# Résumé Jeux
67
Décisions optimales
Arbre de jeu (états, actions, résultats, test terminal, utilité)
Minimax (valeur optimale, algorithme)
Alpha Beta (élagage)
Décisions imparfaites
Fonction d’évaluation heuristique
Test d’arrêt (compliqué  stabilité, horizon)
Elagage avant (faisceaux mais dangereux)
Consultation, Politiques (début et fin de parties)
Classes complexes
Jeux stochastiques (valeur minimax espérée)
Jeux partiellement observables (état de croyance)
IA 101

### Notes:

<!-- Slide number: 68 -->
# Questions?
68
IA 101

### Notes:

<!-- Slide number: 69 -->
# Sommaire
69
Agents de résolution de problèmes
Résolution de problèmes par exploration
Exploration non informée
Exploration informée (heuristiques)
Exploration en situation d’adversité: les jeux
Minimax et Alpha-Bêta
Décisions imparfaites
Problèmes à satisfaction de contraintes
Backtracking
Exploration locale
Structure des problèmes
Contraintes modernes et hybridation
TP: Mise en œuvre de l’exploration et de la satisfaction de contrainte dans un contexte ludique
IA 101

### Notes:

<!-- Slide number: 70 -->
# Problèmes à satisfaction de contraintes (CSPs)
70
Problème standard d’exploration
L’état est une « boite noire », toute structure qui implémente:
la fonction successeur
la fonction heuristique
le test de but
CSP:
Etat défini par des variables Xi à valeurs dans le domaine Di
Test de but défini par un ensemble de contraintes spécifiant les combinaisons de valeurs acceptables pour des sous-ensembles de variables
Exemple simple d’un langage de représentation formelle
Permet l’utilisation de méthodes générales
plus puissantes que les algorithmes standards d’exploration

![](Image7.jpg)
IA 101

<!-- Slide number: 71 -->
# Exemple: coloration de carte
71

![australia](Picture5.jpg)
Contexte:
Coloration:
Contraintes: les régions adjacentes doivent avoir descouleurs différentes
Théorie des graphes
Théorème des 4 couleurs (épique !)
Ici: 3 couleurs
Définition:
Variables : WA, NT, Q, NSW, V, SA, T
Domaines : Di = {rouge, vert, bleu}
Contraintes :
WA ≠ NT
ou (WA,NT) dans {(rouge, vert),(rouge, bleu),(vert, rouge), (vert, bleu),(bleu, rouge),(bleu, vert)}
+ les autres paires de regions adjacentes…
IA 101

### Notes:

<!-- Slide number: 72 -->
# Solutions d’un CSP
72
Etat = Assignation de variables
Solutions = Assignations complètes et consistantes
Exemple: {WA=rouge, NT=vert, Q=rouge, NSW=vert, V = rouge, SA=bleu, T = vert}
Assignation partielle: certaines variables seulement

![australia-solution](Picture4.jpg)
IA 101

### Notes:

<!-- Slide number: 73 -->
# Techniques de résolution des CSPs
73
Méthodes traditionnelles :
Backtracking + heuristiques,
Propagation de contraintes, Forward checking
Exploration locale (min-conflicts)
Backjumping
Contraintes modernes et Hybridation
Intégration CP/SAT/SMT
Utilisation de techniques telles que Lazy Clause Generation pour apprendre des conflits
Exemple: Le seolver CP-SAT de Google OR-Tools
Hybridation avec métaheuristiques
Combinaison d’exploration locale (min-conflicts) avec des phases de réparation par CP (Large Neighborhood Search)

CS 405

<!-- Slide number: 74 -->
# Domaines des CSP
74
Variables discrètes
Domaines finis
n variables, taille de domaine d  O(dn) assignations complètes
Domaines infinis
Entiers, chaines de caractères etc.
Ex: planification de cours
Besoin d’un langage de contraintes
 DébutCours1 +5 ≤ DébutCours2
Variables continues
Exemple: Planifications des observation du Télescope Hubble
Contraintes linéaires solubles en temps polynomial par la programmation linéaire
IA 101

<!-- Slide number: 75 -->
# Graphe de contraintes
75
CSP Binaire: chaque contrainte relie 2 variables
Graphe de contraintes:
Les nœuds sont les variables
Les arcs sont les contraintes
Exemple Coloration:

![australia-csp](Picture4.jpg)
IA 101

### Notes:

<!-- Slide number: 76 -->
# Types de contraintes
76
Unaires: contraintes à 1 variable
Ex: SA ≠ vert
Binaires: contraintes impliquant 1 paire de variables
Ex: SA ≠ WA
Globale ou d’ordre supérieur: contraintes avec 3 variables ou plus
Ex: problèmes cryptaritmétiques
Variables: F T U W R O X1 X2 X3
Domaines: {0,1,2,3,4,5,6,7,8,9}
Contraintes: Alldiff (F,T,U,W,R,O)
O + O = R + 10 · X1
X1 + W + W = U + 10 · X2
X2 + T + T = O + 10 · X3
X3 = F, T ≠ 0, F ≠ 0
Représentation = hypergraphe des contraintes
Xi  sont des variables auxiliaires
Possible de réduire à des contraintes binaires (ex: Graphe Biparti)
Contraintes de préférences
CSP  contraintes absolues
 Problèmes à optimisation de contraintes (COP)

![cryptarithmetic](Picture5.jpg)
IA 101

<!-- Slide number: 77 -->
# CSPs courants
77
Problèmes d’assignation
Dits de « mariage »
E.g. Quels classes / projets sont attribués?
Problème de répartition
E.g. Quelle classe est enseignée quand et où?
Logistique
Planification d’usines
Les problèmes en conditions réels impliquent souvent des variables continues
CS 405

<!-- Slide number: 78 -->
# Formulation standard d’exploration
78
On commence par une formulation simple, puis on l’améliore
Les états sont définis par les valeurs assignées
Etat initial: l’assignation vide {}
Fonction successeur:
on assigne une valeur aux variables non assignées compatible avec l’assignation courante
 Echec si pas d’assignation légale
Test de but: l’assignation est complète
Identique pour tous les CSPs
Chaque solution arrive à la profondeur n avec n variables
Exploration en profondeur d’abord (DFS)
Le chemin n’est pas important
Facteur de branchement b = (n-p).d à la profondeur p
soit n!dn feuilles

IA 101

<!-- Slide number: 79 -->
# Propagation de contraintes
79
IA 101

<!-- Slide number: 80 -->
# Contraintes globales
80
AllDiff:
réduction de la cardinalité des domaines
 rapide (ex: Sudoku)
AtMost:
somme des valeurs minimales, considération max vs mins
Domaines  considérés par leurs bornes et propagation des limites
 limite-cohérence
Contraintes de sommes, cricuits

CS 405

<!-- Slide number: 81 -->
# Exploration avec backtracking des CSPs
81

![backtrack-progress4c](Picture4.jpg)
IA 101

<!-- Slide number: 82 -->
# Ordre des variables et des valeurs
82
Objectif: Détecter les incohérences au plus tôt et éviter les cul de sacs
Variables la plus contrainte
Variable avec le moins de valeurs légales restantes
  Heuristique du minimum des valeurs restantes (MRV)

En cas d’égalité: Heuristique des degrés:
 Variable la plus contraignante pour les autres

Ordonnancement des domaines: Heuristique de la valeur la moins contraignante (LCV)
Celle qui exclut le moins de choix par la suite.

Weighted Degree Heuristic
Priorise les variables impliquées dans de nombreux conflits.
Backjumping dynamique & nogood learning
Pour éviter de revisiter des branches déjà invalidées.

![australia-least-constraining-value](Picture4.jpg)

![australia-most-constrained-variable](Picture4.jpg)

![australia-most-constraining-variable](Picture4.jpg)
IA 101

<!-- Slide number: 83 -->
# Vérification avant et examen en amont
83
Forward checking: application de l’inférence pendant l’exploration
On identifie les valeurs légales pour les variables non assignées
Terminaison quand une variable n’a plus de valeur légale
Mais toutes les incohérencesne sont pas détectées (ex ligne 3)
Maintien de la cohérence d’arc (MAC)
Propagation des contraintes
Backtracking intelligent
Problème: reprise à variables qui ne résout rien (ex: Tasmanie)
Solution: Backjumping orienté conflits
Retour vers assignation la plus récente dans l’ensemble de conflit
Apprentissage de contraintes:
Sous-ensemble minimal de l’ensemble de conflit: variables inutiles

![forward-checking-progress4c](Picture4.jpg)
IA 101

<!-- Slide number: 84 -->
# Exploration locale pour les CSPs
84
Algorithmes très efficaces
Quand les solutions sont denses
Formulation par états complets
Modification d’une variable à la fois
Elimination des contraintes violées
Heuristique Min-Conflits:
Choix d’une valeur qui minimise le nombre de conflits
N-reines: Nombre d’étapes quasi constant: solutions denses
Autre avantage: changement du problème à la volée
Ex: trafic aérien et météo
Modification rapide et minimale

Mais de nombreux plateaux
Techniques pour déplacements latéraux vues précédemment
+ Exploration taboue
Pondération de contraintes
Les contraintes reçoivent un poids
On essaie de minimiser le poids
Les poids sont mis à jour à chaque étape
Hybridation CP + Métaheuristiques
Large Neighborhood Search (LNS)
Relâchement partiel de la solution suivie d’une phase de réparation par CP.
Combinaison d’une recherche locale stochastique et de la propagation de contraintes.
IA 101

<!-- Slide number: 85 -->
# Structure des problèmes
85
Idée: décomposition d’un problème en sous-problèmes
Composantes connexes du graphe: sous-problèmes indépendant
Ex: Tasmanie vs Australie continentale
Complexité: si c variables par sous problème, O(dcn/c)
Exponentielle  linéaire en n
Rare mais structure d’arbre également linéaire
Cohérence d’arc dirigé (DAC)
Tri topologique de l’arbre puis DAC en O(nd2)
Puis assignation sans retour arrière  résolveur arbre
Du coup idée = faire apparaitre l’arbre
Assignation des bonnes variables: Australie méridionale
Choix d’un ensemble coupe-cycle (cutset)
Coupe cycle minimal NP-complet : Ex: graphes petit-monde
Mais bonnes heuristiques. Méthode complète: conditionnement du coupe cycle
Ou bien: décomposition en arbre de sous problèmes connexes
Résolution d’arbre sur les variables partagées
Taille des sous-problèmes minimale
 largeur d’arbre w d’une décomposition= taille max, O(ndw+1)
Problème NP-complet mais bonnes heuristiques
Structure des domaines également intéressante
Ex: coloration: n! permutations équivalentes  symétrie de valeurs
 Contrainte de rupture de symétrie
ex: ordre alphabétique: NT<SA<WA

![](Image3.jpg)

![](Image1.jpg)
IA 101

<!-- Slide number: 86 -->
# Solveurs modernes - intégrations
86
Principaux solveurs actuels :
MiniZinc : Langage de modélisation indépendant et front-end pour divers solveurs.
Google OR-Tools (CP‑SAT) : Solveur hybride CP/SAT avec API pour Python, C#, Java et C++.
Choco Solver et Gecode : Alternatives open-source en Java et C++ respectivement.
Z3 : Solveur SMT pour contraintes logiques complexes.

Interopérabilité multi-langages :
Bindings natifs : OR-Tools et Z3 offrent des interfaces officielles pour plusieurs langages.
Ponts technologiques :
pythonnet pour intégrer Python et .NET.
IKVM pour utiliser des librairies Java en C#.
JPype pour appeler du code Java depuis Python.
CS 405

<!-- Slide number: 87 -->
# Applications et cas d’usage modernes
87
Planification et ordonnancement :
Emplois du temps, scheduling industriel, allocation de ressources.
Logistique et transport :
Problèmes de tournées de véhicules (VRP), gestion d’entrepôts.
Optimisation combinatoire :
Puzzles (Sudoku, n‑queens), coloriage de graphes, configuration de produits.
Planification en IA :
Planification de missions robotiques, satellites, et autres systèmes autonomes.
CS 405

<!-- Slide number: 88 -->
# Résumé CSPs
88
Problèmes à satisfaction de contraintes
Variables, domaines
+ Graphes (binaires) ou hypergraphes de contraintes
Techniques d’inférences
Cohérence de nœuds, arcs, K-cohérence
Exploration avec Backtracking
En profondeur d’abord: Couplage Inférence + exploration
Heuristiques choix de variables, de valeurs
Forward checking et Backjumping orienté conflit accélèrent aussi
Exploration locale
Min conflits est très efficace mêmes avec de nombreuses variables
Structure des problèmes: complexité des problèmes
Coupe cycle idéal pour réduire à un arbre
Décomposition en arbre pratique courante
Symétrie des valeurs importantes
IA 101

### Notes:

<!-- Slide number: 89 -->
# Questions?
89
IA 101

### Notes:

<!-- Slide number: 90 -->
# TP
90

PKP service web CSPs
IA 101

### Notes:

<!-- Slide number: 91 -->
# Sommaire
91
Agents de résolution de problèmes
Résolution de problèmes par exploration
Exploration non informée
Heuristiques et exploration informée
Exploration en situation d’adversité: les jeux
Minimax et Alpha-Bêta
Décisions imparfaites
Problèmes à satisfaction de contraintes
Backtracking
Exploration locale
Structure des problèmes
IA 101

### Notes:

<!-- Slide number: 92 -->
# Plan du cours
92
Introduction
Résolution de problèmes
Bases de connaissances et logique
Raisonnement probabiliste
Apprentissage
Traitement du langage naturel
Présentations projets trimestriels
IA 101

### Notes:

<!-- Slide number: 93 -->
# Merci
93
Jean-Sylvain Boige
jsboige@myia.org
IA 101

### Notes: