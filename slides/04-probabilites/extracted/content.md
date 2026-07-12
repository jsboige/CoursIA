<!-- Slide number: 1 -->
# Incertitude et modèles probabilistes
1
Intelligence Artificielle - IV

Quantification de l’incertitude
Raisonnement probabiliste
Prise de décision

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
# Sommaire
3
Quantification de l’incertitude
Incertitude
Probabilités
Syntaxe et sémantique
Inférence
Indépendance et règle de Bayes
Raisonnement probabiliste
Raisonnement probabiliste temporel
TP: Inférence avec des modèles probabilistes simples et temporels
Théorie de la décision
Prise de décision simple
Prise de décision complexe
IA 101

### Notes:

<!-- Slide number: 4 -->
# Incertitude
4
At = partir pour l’aéroport t minutes avant le vol.Est-ce que At me permettra d’avoir mon vol?
Problèmes
Observabilité partielle (état de la route, plans des autres etc.)
Capteurs bruités (Bison Futé)
Incertitude sur les résultats des actions (pneu crevé, etc.)
Complexité de la modélisation et la prévision du trafic
Une approche purement logique
Risque d’être incorrecte (A25 devrait suffire …)
Conduira à des conclusions trop faibles pour la prise de décision
A25 suffira s’il n’y a pas d’accident sur le pont et il ne pleut pas et mes pneus ne crèvent pas etc. = problème de la qualification logique
A1500 conduira raisonnablement au but, mais il me faudra dormir à l’aéroport
IA 101

### Notes:

<!-- Slide number: 5 -->
# Méthodes face à l’incertitude
5
Logique par défaut ou non monotone
On suppose que ma voiture n’a pas de pneu crevé
On suppose que A25 fonctionne à moins d’une indication contradictoire
Problèmes:
Quelles sont les suppositions raisonnables?
Comment gérer la contradiction?
Règles avec facteurs vague
A25 |→0.3 devrait suffir
Arroseur |→ 0.99 Herbe Mouillée
Herbe Mouillée |→ 0.7 Pluie
Problèmes: combinaisons (e.g, l’arroseur cause la pluie ?)
Probabilités:
Représente le degré de croyance de l’agent
 Etant donné les observations disponibles, A25  devrait me permettre d’avoir mon avion avec la probabilité 0.04
IA 101

### Notes:

<!-- Slide number: 6 -->
# Probabilité
6
Les assertions probabilistes résument les effets de:
La paresse: on n’énumère pas toutes les exceptions, qualifications etc.
L’ignorance théorique et pratique: Il nous manque des faits pertinents, les conditions initiales etc.
Probabilités subjectives:
Elles concernent les propositions de l’état de connaissance de l’agent.
P(A25 | pas d’incident rapporté) = 0.06
Ce ne sont pas des assertions sur le monde
Les probabilités des propositions changent avec de nouvelles observations.
P(A25 | pas d’incident rapporté, 05h00) = 0.15
CS 405

<!-- Slide number: 7 -->
# Prendre des décisions dans l’incertitude
7
Supposons que je crois :
P(A25 j’arrive à temps | …) 	= 0.04
P(A90 j’arrive à temps | …) 	= 0.70
P(A120 j’arrive à temps | …) 	= 0.95
P(A1440 j’arrive à temps | …) 	= 0.9999
Quelles actions choisir
Dépend des préférences entre rater le vol et attendre
La théorie de l’utilité peut représenter et inférer les préférences
théorie de la décision = probabilités + théorie de l’utilité
CS 405

<!-- Slide number: 8 -->
# Syntaxe
8
Elément de base: La variable aléatoire
Des mondes possibles leur donnent des assignations (cf logique propositionnelle)
Domaines:
Variables aléatoires Booléennes:
E.g. Carie (est-ce que j’ai une carie?)
Variables discrètes:
E.g. Le Temps est un parmi <ensoleillé, nuageux, pluvieux, neigeux>
valeurs des domaines exhaustives et mutuellement exclusives
Propositions:
Proposition élémentaire construites par assignation
E.g. Temps = ensoleillé, Carie = faux ( Carie)
Proposition complexe formée par élémentaires + connecteurs logiques
E.g. Temps = ensoleillé  Carie = faux
Evènement atomique: spécification complète de l’état incertain
Ex pour 2 variables aléatoires:
Carie = false  MalDeDent = true
Mutuellement exclusifs et exhaustifs
CS 405

<!-- Slide number: 9 -->
# Axiomes des probabilités
9
Pour toutes propositions A, B,
0 ≤ P(A) ≤ 1
P(vrai) = 1 and P(faux) = 0
P(A  B) = P(A) + P(B) - P(A  B)

![axiom3-venn](Picture4.jpg)
CS 405

<!-- Slide number: 10 -->
# Probabilités a priori
10
Probabilités inconditionnelles ou a priori de propositions
E.g. P(Carie = vrai) et P(Temps =ensoleillé) = 0.72
= état de croyance a priori en l’absence d’observation
La distribution de probabilité donne les valeurs pour toutes les assignations:
P(Temps) = <0.72,0.1,0.08,0.1> (normalisées, i.e. la somme vaut 1)
Distribution de probabilités conjointe
 Pour des variables aléatoires, la probabilité de chacun de leurs évènements atomiques
P(Temps, Carie) = une matrice 4 x 2

	Temps =	Soleil	Pluie	Nuages	Neige
	Carie = true 	0.144	0.02 	0.016 	0.02
	Carie = false	0.576	0.08 	0.064 	0.08
Chaque question sur un domaine peut être répondue par la distribution conjointe.

CS 405

<!-- Slide number: 11 -->
# Probabilités des variables continues
11

![](Image5.jpg)

![](Image6.jpg)
CS 405

<!-- Slide number: 12 -->
# Probabilités conditionnelles
12
Probabilités conditionnelles ou a posteriori
E.g. P(Carie | MalDeDent) = 0.8
i.e. « sachant uniquement» Mal De Dent
Notation pour distributions conditionnelles:
 P(Carie | MalDeDent) =vecteur à 2 elts de vecteurs à 2 elts
Si l’on sait plus
P(Carie | MalDeDent, Carie) = 1
Des observations peuvent être non pertinentes
Permettent la simplification
P(Carie | MalDeDent, ensoleillé) = P(Carie | MalDeDent) = 0.8
Règle du produit
P(a  b) = P(a | b) P(b) = P(b | a) P(a) soit P(a | b) = P(a  b) / P(b) si  P(b) > 0
P(Temps , Carie) = P(Temps| Carie) P( Carie) produit terme à terme, pas matriciel
Règle de chainage = dérivation successive
P(X1, …,Xn) 	= P(X1,...,Xn-1) P(Xn | X1,...,Xn-1)
                 	= P(X1) P(X2 | X1)… P(Xn-1 | X1,...,Xn-2) P(Xn | X1,...,Xn-1)
                  	= …
                  	= πi= 1^n P(Xi | X1, … ,Xi-1)
CS 405

<!-- Slide number: 13 -->
# Inférence par énumération
13
Probabilités conjointe:

Proposition φ -> sommer les évts atomiques où elle est vraie
P(φ) = Σω:ω╞φ P(ω)
P(MalDeDents) = 0.108 + 0.012 + 0.016 + 0.064 = 0.2
Conditionnelles
P(Carie | MalDeDents)  = P(Carie  MalDeDents) / P(MalDeDents)
	= (0.016+0.064) / (0.108 + 0.012 + 0.016 + 0.064)
	= 0.4

![dentist-joint1](Picture9.jpg)

![dentist-joint3](Picture6.jpg)
CS 405

<!-- Slide number: 14 -->
# Normalisation
14
Dénominateur = constante de normalisation α
P(Carie | MalDeDents) = α P(Carie,MalDeDents), α = 1/ P(MalDeDents)
= α [P(Carie,MalDeDents,Croche) + P(Carie,MalDeDents, Croche)]
= α [<0.108,0.016> + <0.012,0.064>]
= α <0.12,0.08> = <0.6,0.4>
Idée générale: calculer la distribution
sur la variable de requête Y
en fixant les variables d’observations E
en sommant sur les variables cachées H
Distribution a posteriori conjointe
P(Y | E = e) = αP(Y,E = e) = αΣhP(Y,E= e, H = h)
Problèmes:
Complexité au pire en O(dn) où d est la plus grande arité (nb d’arguments)
Complexité en espace en O(dn) pour stocker la distribution conjointe
Comment trouver les nombres pour O(dn) entrées?

![dentist-joint4](Picture6.jpg)
CS 405

<!-- Slide number: 15 -->
# Indépendance
15
A et B sont indépendants si et seulement si
P(A|B) = P(A)    ou P(B|A) = P(B)     ou P(A, B) = P(A) P(B)

P(MalDeDent, Croche, Carie, Temps)= P(MalDeDent, Croche, Carie) P(Temps)
Pour n lancés de pièces indépendants : O(2n) →O(n)
Puissant mais rare
Ex du dentiste: des centaines de variables dépendantes

![weather-independence](Picture4.jpg)
CS 405

<!-- Slide number: 16 -->
# Indépendance conditionnelle
16
Croche est conditionnellement indépendant de Mal De Dents:
(1) P(Croche | MalDeDent, Carie) = P(Croche | Carie)
(2) P(Croche | MalDeDent,Carie) = P(Croche | Carie)
P(Croche | MalDeDent,Carie) = P(Croche | Carie)
P(MalDeDent | Croche, Carie) = P(MalDeDent | Carie)
P(MalDeDent, Croche | Carie) = P(MalDeDent | Carie) *P(Croche | Carie)
Utilisation de la règle de chaînage:
P(MalDeDent, Croche, Carie)= P(MalDeDent | Carie) P(Croche | Carie) P(Carie)
Réduction de la complexité:
Peut réduire depuis la distribution conjointe de O(2n) à O(n)
Notre connaissance la plus basique et robuste en environnement incertain.

CS 405

<!-- Slide number: 17 -->
# Règle de Bayes
17
Règle du produit:
 P(ab) = P(a | b) P(b) = P(b | a) P(a)
 règle de Bayes
P(a | b) = P(b | a) P(a) / P(b)
Sous forme de distribution:
P(Y|X) = P(X|Y) P(Y) / P(X) = αP(X|Y) P(Y)
Utile pour déterminer les probabilités de diagnostic depuis les probabilités causales.
P(Cause | Effet) = P(Effet | Cause) P(Cause) / P(Effet)
Ex: méningite, nuque douloureuse:
P(m|s) = P(s|m) P(m) / P(s) = 0.8 × 0.0001 / 0.1 = 0.0008
La probabilité a postériori est encore très faible

CS 405

<!-- Slide number: 18 -->
# Bayes et indépendance conditionnelle
18
Exemple:
	P(Carie | MalDeDents  croche)
= αP(MalDeDents  croche | Carie) P(Carie)
= αP(MalDeDent | Carie) P(Croche | Carie) P(Carie)
C’est un exemple de modèle Bayesien naïf
P(Cause,Effet1, … ,Effetn) = P(Cause) πiP(Effeti|Cause)

Le nombre de paramètres est linéaire en n

![naive-bayes](Picture4.jpg)
CS 405

<!-- Slide number: 19 -->
# Résumé
19
Les probabilités sont un formalisme rigoureux pour la connaissance incertaine
La distribution conjointe de probabilité spécifie la probabilité de chaque évènement atomique
Les questions peuvent être répondues en sommant sur les évènements atomiques
Pour des domaines non triviaux, on doit trouver un moyen de réduire la taille conjointe
L’indépendance et l’indépendance conditionnelle fournissent de bons outils
CS 405

<!-- Slide number: 20 -->
# Questions?
20
IA 101

### Notes:

<!-- Slide number: 21 -->
# Sommaire
21
Quantification de l’incertitude
Raisonnement probabiliste
Réseaux Bayésiens
Domaines experts simples
Raisonnement probabiliste temporel
Prise de décision simple
Prise de décision complexe
TP: Inférence avec des modèles probabilistes simples et temporels
IA 101

### Notes:

<!-- Slide number: 22 -->
# Réseaux Bayesiens
22
Une notation simple, graphique
pour les assertions d’’indépendance conditionnelle,
et pour la spécification compacte d’une distribution conjointe complète.
Syntaxe:
Un ensemble de nœuds, un par variable
Un graphe dirigé acyclique (lien ≈ “influences directes")
Une distribution conditionnelle pour chaque nœud, étant donné ces parents:
P (Xi | Parents (Xi))

Dans la cas le plus simple, une distribution conditionnelle est représentée par:
une table de probabilités conditionnelles (CPT)
donnant la distribution en Xi pour chaque combinaison de valeur parente

<!-- Slide number: 23 -->
# Example
23
La topologie du réseau encode les assertions d’indépendance conditionnelle:

Weather est indépendant des autres variables
Toothache et Catch sont conditionnellement indépendants, étant donné Cavity

![dentist-network](Picture4.jpg)

<!-- Slide number: 24 -->
# Exemple
24
Mise en situation:
« Au travail, mon voisin John m’appelle pour me prévenir que mon alarme sonne, mais ma voisine Marie n’appelle pas. Parfois elle est déclanchée par de petits tremblements de terre. Y a-t’il un voleur? »
Variables: Burglary, Earthquake, Alarm, JohnCalls, MaryCalls

La topologie de réseau reflate la connaissance "causale" :
A burglar can set the alarm off
An earthquake can set the alarm off
The alarm can cause Mary to call
The alarm can cause John to call

<!-- Slide number: 25 -->
# Example (suite)
25

![burglary2](Picture4.jpg)

<!-- Slide number: 26 -->
# Compacité
26
Un CPT pour les booléens  Xi avec k Booleéns parents a 2k lignes pour les combinaisons de valeurs parents

Chaque ligne nécessite un nombre p pour Xi = true(le nombre pour Xi = false est juste 1-p)

Si chaque variable n’a pas plus de k parents, le réseau complet nécessite O(n · 2k) nombres

I.e., croit linéairement en n, vs. O(2n) pour la distribution conjointe complète

Pour le réseau burglary, 1 + 1 + 4 + 2 + 2 = 10 nombres (vs. 25-1 = 31)

![burglary-small](Picture4.jpg)

<!-- Slide number: 27 -->
# Sémantiques
27
La distribution conjointe complète est définie par la produit des distributions conditionnelles locales:

		P (X1, … ,Xn) = πi = 1 P (Xi | Parents(Xi))

e.g., P(j  m  a  b  e)

	= P (j | a) P (m | a) P (a | b, e) P (b) P (e)

![burglary-small](Picture4.jpg)
n

<!-- Slide number: 28 -->
# Construction de réseaux Bayésiens
28
1. On choisit un ordre de variables X1, … ,Xn
2. De i = 1 à n
On ajoute Xi au réseau
On sélectionne les parents de X1, … ,Xi-1 tells que
	P (Xi | Parents(Xi)) = P (Xi | X1, ... Xi-1)

Ce choix de parents garantit:

P (X1, … ,Xn) 	= πi =1 P (Xi | X1, … , Xi-1)
(règle de chaine)
			= πi =1P (Xi | Parents(Xi))
(par construction)
n
n

<!-- Slide number: 29 -->
# Exemple
29
Supposons qu’on choisisse l’ordre M, J, A, B, E

P(J | M) = P(J)?

![burglary-make1c](Picture6.jpg)

<!-- Slide number: 30 -->
# Exemple
30
Supposons qu’on choisisse l’ordre M, J, A, B, E

P(J | M) = P(J)?
Non
P(A | J, M) = P(A | J)? P(A | J, M) = P(A)?

![burglary-make2c](Picture6.jpg)

<!-- Slide number: 31 -->
# Exemple
31
Supposons qu’on choisisse l’ordre M, J, A, B, E

P(J | M) = P(J)?
Non
P(A | J, M) = P(A | J)? P(A | J, M) = P(A)? Non
P(B | A, J, M) = P(B | A)?
P(B | A, J, M) = P(B)?

![burglary-make3c](Picture6.jpg)

<!-- Slide number: 32 -->
# Exemple
32
Supposons qu’on choisisse l’ordre M, J, A, B, E

P(J | M) = P(J)?
No
P(A | J, M) = P(A | J)? P(A | J, M) = P(A)? No
P(B | A, J, M) = P(B | A)? Yes
P(B | A, J, M) = P(B)? No
P(E | B, A ,J, M) = P(E | A)?
P(E | B, A, J, M) = P(E | A, B)?

![burglary-make4c](Picture6.jpg)

<!-- Slide number: 33 -->
# Exemple
33
Supposons que nous choisissons l’ordre M, J, A, B, E

P(J | M) = P(J)?
No
P(A | J, M) = P(A | J)? P(A | J, M) = P(A)? No
P(B | A, J, M) = P(B | A)? Yes
P(B | A, J, M) = P(B)? No
P(E | B, A ,J, M) = P(E | A)? No
P(E | B, A, J, M) = P(E | A, B)? Yes

![burglary-make5c](Picture6.jpg)

<!-- Slide number: 34 -->
# Example contd.
34

Décider de l’indépendance conditionnelle est difficile dans les directions non causales
(Les modèles causaux et d’indépendance conditionnelle semble cablés pour les humains!)
Le réseau est moins compacte : 1 + 2 + 4 + 2 + 4 = 13 nombres nécessaires

![burglary-make5c](Picture5.jpg)

<!-- Slide number: 35 -->
# Représentation efficace
35
Relations d’indépendance conditionnelle
Indépendante conditionnelle aux non-descendants, étant donné les parents (a)
Couverture de Markov: Indépendance au reste du réseau (b)
Etant données parents, enfants et parents des enfants
Distribution canonique
Tables de probabilités conditionnelles fastidieux
O(2^k) nombres dans le cas pessimiste
 Schéma standard plus simple
Ex simple: Nœuds déterministes: Enfants spécifiés par parents
Ex: Canadien vs US & Mexico  Nord Américain (disjonction)
Ex: Concessionnaires  Meilleur prix (Min)
Ex: débits entrant et sortant  Niveau d’un lac (différence)
Relation « OU-bruité »
+Incertitude causale Parents/Enfants  Relation inhibée par un bruit
Couverture des clauses de la disjonction  ajout d’un nœud de fuite
Hypothèse d’indépendance causale des bruits
Formulation générale:

Ex: Fièvre vs Maladies  3 chiffres suffisent

![](Image5.jpg)

![](Image6.jpg)

![](Image7.jpg)
CS 405

<!-- Slide number: 36 -->
# Variables continues
36
Concerne de nombreux problèmes (hauteur, masse, devise, température etc.)
1ère possibilité: Discrétisation  intervalles fixes
Mais parfois peu précis
Meilleur: définition d’une distribution de probabilités
Paramétrique: ex: Gaussienne  moyenne et variance
Non paramétrique: Définition implicite par l’exemple
Réseau bayésien hybride
Paramètres discrets + continus
Variables continues: Probabilité linéaire Gaussienne
Ex: Coût  Q récolte (h) + subventions
2 distributions sommées

Somme de distributions linéaires gaussienne
distribution conjointe = Distribution gaussienne multivariée
Distribution a posteriori = distribution gaussienne conditionnelle
Variables discrètes avec parents continus
Seuil doux : Ex: acheter / coût
Possibilité = intégrale de la distribution normale
= Distribution Probit
Alternative = fonction sigmoïde = distribution logit
Distribution Apriori conjuguée
Quelle distribution utiliser?
Posterieur = même famille de distribution
Exemples:
Gaussienne: moyenne  Gaussienne, précision  Gamma
https://en.wikipedia.org/wiki/Conjugate_prior

![](Image6.jpg)

![](Image5.jpg)

![](Image7.jpg)

![](Image10.jpg)

![Une image contenant tasse, orange, table Description générée automatiquement](Image12.jpg)

![](Image8.jpg)
CS 405

<!-- Slide number: 37 -->
# Inférence exacte dans les réseaux Bayésiens
37

![](Image5.jpg)

![](Image6.jpg)
CS 405

<!-- Slide number: 38 -->
# Inférence approchée dans les RB
38

![](Image5.jpg)

![](Image6.jpg)
CS 405

<!-- Slide number: 39 -->
# Modèles relationnels du premier ordre
39
Modèles bayésiens = propositionnel
FOL  relations entre objets
Ex: évaluations livres: pb de partialité
 Impartial(c), Indulgent(c), Mérite(l) prédicats du premier ordre
Mondes possibles
Assignations de variables  mondes possibles
Sémantique de base de données (limite la taille du problème)
Modèles probabilistes relationnels
Syntaxe de FOL  Variables aléatoires = assignations possibles
Distributions et dépendances (Tables de Pr Cond.)
Indépendance contextuelle
= branchement ex: si Impartial(c), si Fan(c, Auteur(l))
Inférence: ex dépliement  Assemblage complet
 grand réseau + variables inconnues  nombreux nœuds parents: ex auteur?
Mais si sémantique de DB:
mise en cache + indépendance contextuelle + techniques MCMC efficaces
= propositionnalisation  améliorée en FOL par lifting  De même lifting ici
Modèles relativistes en univers ouvert
Sémantique standard  incertitude d’existence et d’identité des objets (e.g. IDs: Sibyl attacks)
 MPUOs
Ex: NbClient: Si honête, exactement 1, sinon distribution LogNormal[6,9,2,3]

![](Image5.jpg)
CS 405

<!-- Slide number: 40 -->
# Résumé réseaux bayésiens
40
Les réseaux Bayésiens fournissent une représentation naturelle pour les indépendance conditionnelles (induites par causalité)
Topologie + CPTs = représentation compacte d’une distribution jointe
Généralement facile à construire pour un expert d’un domaine
Représentation efficace/compacte:
Distributions canonique, distributions paramétriques (Gaussiennes etc.)
Inférence = calcul de variables de requêtes
Exacte: énumération, élimination, clustering
 Efficace dans les polyarbres
Approximée:
Echantillonage a priori, par rejet, par vraissemblence
Méthodes de Monte-Carlo(Gibbs)
Modèles relationnels
Combinaison avec FOL = Modèles probabilistes relationnels (MPR)
+ Incertitude d’existence et d’identité = MP en Univers Ouvert

<!-- Slide number: 41 -->
# Questions?
41
IA 101

### Notes:

<!-- Slide number: 42 -->
# Sommaire
42
Quantification de l’incertitude
Raisonnement probabiliste
Raisonnement probabiliste temporel
Chaînes de Markov
Modèles de Markov Cachés
Réseaux Bayésiens dynamiques
Filtrage particulaire
Prise de décision simple
Prise de décision complexe
TP: Inférence avec des modèles probabilistes simples et temporels
IA 101

### Notes:

<!-- Slide number: 43 -->
# Raisonner dans le temps ou l’espace
43
Souvent, nous souhaitons raisonner à propos d’une séquence d’observations
Reconnaissance de la parole
Localisation d’un robot
Attention d’un utilisateur
Monitoring médical
Suivi radar
Besoin d’introduire le temps (ou l’espace) dans nos modèles

<!-- Slide number: 44 -->
# Modèles de Markov
44

![](Picture2.jpg)

<!-- Slide number: 45 -->
# Distribution de probabilités
45

![](Picture2.jpg)

<!-- Slide number: 46 -->
# Indépendance conditionnelle
46

Indépendance conditionnelle basique:
Passé et future indépendants conditionnellement au  présent
Chaque étape dépend uniquement de la précédente
On l’appelle la propriété de Markov (du premier ordre)
On note que la chaine est simplement un Réseau bayésien (extensible) : On peut toujours utiliser le raisonnement des RB classiques si on tronque la chaine à une longueur donnée.

![](Picture2.jpg)

<!-- Slide number: 47 -->
# Exemple: Chaîne de Markov
47

![](Picture2.jpg)
0.3
0.7

<!-- Slide number: 48 -->
# Inférence sur chaînes de Markov
48

![](Picture2.jpg)

<!-- Slide number: 49 -->
# Distribution conjointe de modèle de Markov
49

![](Picture2.jpg)

<!-- Slide number: 50 -->
# Récapitulatif modèles de Markov
50

![](Picture2.jpg)

<!-- Slide number: 51 -->
# Algorithme Mini-Forward
51

![](Picture2.jpg)

<!-- Slide number: 52 -->
# Exemple d’exécution Mini-Forward
52
Depuis une observation initial d’ensoleillement:

Depuis une observation initial de pluie:

Depuis une autre distribution initiale P(X1):

![](Picture4.jpg)

![](Picture5.jpg)

![](Picture2.jpg)

<!-- Slide number: 53 -->
# Distributions stationnaires
53

<!-- Slide number: 54 -->
# Exemple: distribution stationnaire
54
Question: Quel est P(X) au temps t = infini?

![](Picture2.jpg)

![](Picture2.jpg)

![](Picture3.jpg)

<!-- Slide number: 55 -->
# Application : Analyse des liens web

![](Picture2.jpg)
55
PageRank sur un graphe du web
Chaque page est un état
Distribution initiale: uniforme sur les pages
Transitions:
Avec la prob. c, saut uniforme vers une pageAléatoire (lignes pointillées)
Avec prob. 1-c, suivre un lien sortant aléatoire (lignes pleines)
Distribution stationnaire:
On passera plus de temps sur les pages hautement accessibles
E.g. Plein de façon d’arriver sur la page de téléchargement d’Acrobat Reader
Relativement robuste au spam de liens
Google 1.0
Renvoyait la liste de pages contenant vos mots clés par ordre décroisant de page rank, maintenant tous les moteurs de recherche utilisent l’analyse de lien avec d’autres facteurs (le page rank devient en fait de moins en moins important)

<!-- Slide number: 56 -->
# Hidden Markov Models
56
Markov chains not so useful for most agents
Eventually you don’t know anything anymore
Need observations to update your beliefs
Hidden Markov models (HMMs)
Underlying Markov chain over states S
You observe outputs (effects) at each time step
As a Bayes’ net:

![](Picture2.jpg)

<!-- Slide number: 57 -->
# Example
57

![](Picture2.jpg)

<!-- Slide number: 58 -->
# Hidden Markov Models
58

![](Picture2.jpg)

<!-- Slide number: 59 -->
# HMM Computations
59
Given
parameters
evidence E1:n =e1:n
Inference problems include:
Filtering, find P(Xt |e1:t) for all t
Smoothing, find P(Xt |e1:n) for all t
Most probable explanation, find x*1:n = argmax x1:n P(x1:n|e1:n)

<!-- Slide number: 60 -->
# Real HMM Examples
60
Speech recognition HMMs:
Observations are acoustic signals (continuous valued)
States are specific positions in specific words (so, tens of thousands)

![](Picture2.jpg)

<!-- Slide number: 61 -->
# Real HMM Examples
61
Machine translation HMMs:
Observations are words (tens of thousands)
States are translation options

![](Picture2.jpg)

<!-- Slide number: 62 -->
# Real HMM Examples
62
Robot tracking:
Observations are range readings (continuous)
States are positions on a map (continuous)

![](Picture2.jpg)

<!-- Slide number: 63 -->
# Conditional Independence
63
HMMs have two important independence properties:
Markov hidden process, future depends on past via the present

![](Picture2.jpg)

<!-- Slide number: 64 -->
# Conditional Independence
64
HMMs have two important independence properties:
Markov hidden process, future depends on past via the present
Current observation independent of all else given current state

![](Picture2.jpg)

<!-- Slide number: 65 -->
# Conditional Independence
65
HMMs have two important independence properties:
Markov hidden process, future depends on past via the present
Current observation independent of all else given current state

Quiz: does this mean that observations are independent given no evidence?

![](Picture2.jpg)

### Notes:
§ [No, correlated by the hidden state]

<!-- Slide number: 66 -->
# HMM Notation
66

<!-- Slide number: 67 -->
# HMM Problem 1
67
EvaluationConsider the problem where we have a number of HMMs (that is, a set of (,A,B) triples) describing different systems, and a sequence of observations. We may want to know which HMM most probably generated the given sequence.
Solution: Forward Algorithm

<!-- Slide number: 68 -->
# HMM Problem 2
68
Decoding: Finding the most probable sequence of hidden states given some observations
Find the hidden states that generated the observed output.
In many cases we are interested in the hidden states of the model since they represent something of value that is not directly observable
Solution:
Backward Algorithm
or Viterbi Algorithm

<!-- Slide number: 69 -->
# HMM Problem 3
69
Learning: Generating a HMM from a sequence of observations
Solution: Forward-Backward Algorithm

![](Image5.jpg)

<!-- Slide number: 70 -->
# Exhaustive Search Solution
70
Sequence of observations for seaweed state:
Dry
Damp
Soggy

![](Picture3.jpg)

<!-- Slide number: 71 -->
# Exhaustive Search Solution
71
Pr(dry,damp,soggy | HMM) = Pr(dry,damp,soggy | sunny,sunny,sunny) + Pr(dry,damp,soggy | sunny,sunny ,cloudy) + Pr(dry,damp,soggy | sunny,sunny ,rainy) + . . . . Pr(dry,damp,soggy | rainy,rainy ,rainy)

![](Picture3.jpg)

<!-- Slide number: 72 -->
# A better solution: dynamic programming
72
We can calculate the probability of reaching an intermediate state in the trellis as the sum of all possible paths to that state.

![](Picture2.jpg)

<!-- Slide number: 73 -->
# A better solution: dynamic programming
73
t ( j )= Pr( observation | hidden state is j ) x Pr(all paths to state j at time t)

![](Picture2.jpg)

<!-- Slide number: 74 -->
# A better solution: dynamic programming
74

![](Picture2.jpg)

<!-- Slide number: 75 -->
# A better solution: dynamic programming
75

![](Picture2.jpg)

<!-- Slide number: 76 -->
# Filtres de Kalman
76

![](Image5.jpg)

![](Image6.jpg)

![](Image7.jpg)

![](Image8.jpg)

![](Image9.jpg)

![](Image10.jpg)

![](Image11.jpg)

![](Image12.jpg)

![](Image13.jpg)
CS 405

<!-- Slide number: 77 -->
# Réseaux bayésiens dynamiques
77
Généralisation HMM, Kalman etc.
Modèle probabiliste temporel
Variables Xt d’état et Et d’observations, dans des coupes arbitraires
Cf transformation HMM RBD (vecteur multidimensionnel)
Modèle (beaucoup) plus parcimonieux
Construction d’un RBD
Distribution a priori , modèle de transition, de capteur
Ex: Robot: jauge de batterie
 Modèle de défaillance temporaire
 Modèle de défaillance persistante  « Jauge cassée »
Inférence exacte
Possibilité: dépliement de suffisamment de coupes
Puis élimination, clustering
Utilité du fonctionnement récursif (sommations partielles)
mais résultat pas factorisable
 Souvent, méthodes approximatives uniquement
Inférence approchée
Pondération par vraisemblance et méthodes MCMC adaptables
Ex: Filtrage particulaire: on rejette les échantillons trop faibles et on duplique les autres parmi N
Suivre de nombreux objet (jusqu’ici: une trajectoire)
Incertitude d’identité  pb d’association des données  Méthodes approximatives
Ex: plus proche voisin, max. de la probabilité des observations, filtrage particulaire, MCMC

![](Image5.jpg)

![](Image6.jpg)

![](Image7.jpg)
CS 405

<!-- Slide number: 78 -->
# Résumé raisonnement temporel
78
Variables aléatoires temporelles
Propriété de Markov, stationnarité
Modèles de transition, de capteur
Inférence
Filtrage (forward), prédiction, lissage (backward), explication vraissemblance
Familles de modèles temporels
Modèles de Markov cachés, filtres de Kalman, Réseaux bayésiens dynamiques
Inférence exacte souvent difficile mais méthodes approchées efficaces
Filtrage particulaire
+ Problème de l’association des données
CS 405

<!-- Slide number: 79 -->
# Questions?
79
IA 101

### Notes:

<!-- Slide number: 80 -->

# Programmation probabiliste
80
Principales librairies
Infer.Net (c# / .Net)
Pyro (Python / Pytorch)
Tensorflow Probability (Python /Tensorflow)
PyMC (Python / Aesara, Jax)
Stan (C++ /Wrappers)
Tutoriels Infer.Net
Prise en main (en français)
Tutoriels (en anglais)
Guide utilisateur
CS 405

<!-- Slide number: 81 -->
# Sommaire
81
Quantification de l’incertitude
Raisonnement probabiliste
Raisonnement probabiliste temporel
Prise de décision simple
Théorie de l’utilité
Réseaux de décision
Systèmes experts
Prise de décision complexe
Théorie des jeux
TP: Inférence avec des modèles probabilistes simples et temporels
IA 101

### Notes:

<!-- Slide number: 82 -->
# Agent fondé sur l’utilité
82

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

<!-- Slide number: 83 -->
# Prise de décision
83
Théorie des probabilités
Ce qu’un agent devrait croire en s’appuyant sur l’observation
Théorie de l’utilité
Ce que l’agent veut
 Théorie de la décision synthétise les deux
Ce que l’agent devrait faire.
Considérer toutes les actions possibles
 viser le meilleur résultat: maximiser l’utilité espérée
 Agent rationnel
Préférence entre les loteries: L = [p1, S1; p2, S2; . . . pn, Sn]
Axiomes simples d’utilité
Prise de décision simple
Problèmes épisodiques

![](Image5.jpg)

![](Image6.jpg)
CS 405

<!-- Slide number: 84 -->
# Théorie de l’utilité
84

![](Image6.jpg)

![](Image8.jpg)

![](Image5.jpg)

![](Image7.jpg)

![](Image9.jpg)

![](Image10.jpg)
CS 405

<!-- Slide number: 85 -->
# Fonctions d’utilité
85

![](Image5.jpg)

![](Image6.jpg)

![](Image7.jpg)

![](Image8.jpg)

![](Image9.jpg)
CS 405

<!-- Slide number: 86 -->
# Réseaux de décision

![](Image5.jpg)
86

![](Image6.jpg)

![](Image7.jpg)

![](Image8.jpg)
CS 405

<!-- Slide number: 87 -->
# Système expert
87

![](Espaceréservéducontenu5.jpg)
CS 405

<!-- Slide number: 88 -->
# Questions?
88
IA 101

### Notes:

<!-- Slide number: 89 -->
# Sommaire
89
Quantification de l’incertitude
Raisonnement probabiliste
Raisonnement probabiliste temporel
Prise de décision simple
Prise de décision complexe
Politiques, Processus de décision de Markov
Théorie de jeux
Design de mécanismes
Jeux différentiels
TP: Inférence avec des modèles probabilistes simples et temporels
IA 101

### Notes:

<!-- Slide number: 90 -->
# Prise de décision complexe
90
Problèmes de décision séquentiels
Planification = cas particulier
Entièrement observables
Processus de décision de Markov (MDP)
Etats s, Actions(s)
Modèle de transition P(s’|s,a)
Récompense R(s)
Ex: +1;-1 (terminal) ; -0,04 (vitesse)
Solution = Politique optimale (π*)
Fournit l’utilité espérée maximale
EUh([s0, s1, . . . , sn])
Horizon fini  π* non-stationnaire
Préférences Stationnaires  récompenses
Additives: Uh([s0, s1, s2, . . .]) = R(s0) + R(s1) + R(s2) + ...
Besoin d’une politique appropriée (garantie de finir)
Ou escomptées : Uh([s0, s1, s2, . . .]) = R(s0) + γ R(s1) + γ² R(s2)
 U bornée, Empirique, monétaire, uncertitude, stationarité
Sinon, récompense moyenne

![](Image5.jpg)

![](Image8.jpg)

![](Image6.jpg)

![](Image7.jpg)
CS 405

<!-- Slide number: 91 -->
# Evaluation des politiques
91

![](Image5.jpg)

![Une image contenant texte Description générée automatiquement](Image10.jpg)

![Une image contenant texte Description générée automatiquement](Image12.jpg)

![](Image14.jpg)

![](Image16.jpg)
CS 405

<!-- Slide number: 92 -->
# Méthodes itératives
92

![](Image6.jpg)

![](Image8.jpg)

![](Image10.jpg)
CS 405

<!-- Slide number: 93 -->
# Autres méthodes
93
Programmation linéaire
Bellman  sommes et max  problème d’optimisation
Minimisation U(s) avec
Mais souvent complexité mauvaise (nombreux états/actions)
Algorithmes itératifs en ligne
Méthodes offline souvent impraticables (cf. jeux)
Ex: Expectiminimax: Arbre minimax + nœuds de chance
Profondeur bornée (via γ) ainsi que branchement (via sampling)
Programmation dynamique en temps réel (RTDP)
(décomposition en sous problèmes  Graphe = sous-MPD)
Grands espaces  méthodes de Monte-Carlo
Problèmes de bandits manchots
Machines à sous à n bras aux probabilités de gains distinctes (MAP ≈MDP)
 Compromis Exploration/Exploitation
Ex: traitements covid-19
Coefficient de Gittins
une seule machine à sous: Comparaison avec récompense stationnaire λ
 stopping time T
Calcul: Cas simple: utilisation d’un Restart MDP (indifférence à T)
Approximations (MPD tronqué)

![](Image6.jpg)

![](Image8.jpg)
CS 405

<!-- Slide number: 94 -->
# PDMPOs / POMDPs
94

![](Image5.jpg)

![](Image7.jpg)

![](Image6.jpg)
CS 405

<!-- Slide number: 95 -->
# Questions?
95
IA 101

### Notes:

<!-- Slide number: 96 -->
# Plan du cours
96
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

<!-- Slide number: 97 -->
# Projets de groupe
97
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

<!-- Slide number: 98 -->
# Merci
98
Jean-Sylvain Boige
jsboige@myia.org
IA 101

### Notes: