---
theme: ../theme-ia101
title: "Intelligence Artificielle - Resolution de problemes"
info: IA 101 - Resolution de problemes
paginate: true
drawings:
  persist: false
transition: slide-left
mdc: true
layout: cover
---

# Resolution de problemes

INTELLIGENCE ARTIFICIELLE -- II

- Explorations non informee et informee
  - Jeux
  - Problemes a satisfaction de contraintes

---

# Plan du cours

<ol class="roman-list">
<li>Introduction</li>
<li><strong>Resolution de problemes</strong></li>
<li>Bases de connaissances et logique</li>
<li>Raisonnement probabiliste</li>
<li>Apprentissage</li>
<li>Traitement du langage naturel</li>
<li>TP final projets trimestriels</li>
</ol>

---

# Sommaire

- **Agents de resolution de problemes**
- **Resolution de problemes par exploration**
  - Exploration non informee
  - Heuristiques et exploration informee
- **Exploration en situation d'adversite : les jeux**
  - Minimax et Alpha-Beta
  - Decisions imparfaites
- **Problemes a satisfaction de contraintes**
  - Backtracking
  - Exploration locale
  - Structure des problemes
- **TP** : Mise en oeuvre de l'exploration et de la satisfaction de contrainte dans un contexte ludique

---
layout: section
---

# Agents de resolution de Problemes
---

# Agent fonde sur des buts

<img src="./images/img_001.png" style="position:absolute; top:80px; right:30px; height:340px;" alt="Agent fonde sur des buts" />

- **Reactif → Deliberatif**
  - Exploration du Futur, sequences d'actions
  - Recherche, planification

- **Composants :**
  - Etats, Buts, Capteurs, Effecteurs
- **Questions cles :**
  - "Comment le monde evolue-t-il ?"
  - "Quel est l'impact de mes actions ?"
  - "A quoi ressemble le monde maintenant ?"
  - "Quelle action entreprendre maintenant ?"

---

# Resolution de problemes

- Quel est **l'objectif** a atteindre ?
- Quelles sont les **actions** possibles ?
- Quelle est la **representation** de l'etat courant ?

---

# Agents de resolution de problemes

## Fonction Agent-Simple-Resolution-Probleme

```
fonction Agent-Simple-Resolution-Probleme(percept) retourne une action
  persistante: seq (sequence d'actions, initialement vide)
               etat (description de l'etat courant du monde)
               but (initialement vide)
               probleme (formulation du probleme)
  etat <- Actualiser-Etat(etat, percept)
  si seq est vide alors
    but <- Formuler-But(etat)
    probleme <- Formuler-Probleme(etat, but)
    seq <- Explorer(probleme)
    si seq = echec alors retourner une action vide
  action <- Premier(seq)
  seq <- Reste(seq)
  retourner action
```

---

# Exemple: Itineraire

<img src="./images/img_003.png" style="position:absolute; top:60px; right:20px; width:420px;" alt="Carte de Roumanie" />

- En vacances en Roumanie; actuellement a Arad.
- Le vol part demain de Bucharest
- **Formuler le but :**
  - Etre a Bucharest
- **Formuler le probleme :**
  - **Etats** : plusieurs villes
  - **Actions** : conduire d'une ville a l'autre
- **Trouver la solution :**
  - Sequence de villes e.g., Arad, Sibiu, Fagaras, Bucharest

---

# Types de problemes

- **Deterministes, completement observables** → **probleme a etat simple**
  - L'agent sait exactement dans quel etat il sera ; la solution est une sequence
- **Non-observable** → **probleme sans capteur** dit conformant
  - L'agent peut ne pas savoir ou il est, la solution est une sequence
- **Non deterministe et/ou partiellement observable** → **probleme de contingence**
  - Les percepts fournissent une **nouvelle** information a propos de l'etat courant
  - Entrelacement &#123;calcul, action&#125;
- **Espaces d'etats inconnu** → **problemes d'exploration en ligne**

---

# Formulation de problemes

Un **probleme** est defini par les elements suivants :

1. **Etat initial** e.g., "a Arad"
2. **Actions** ou **fonction successeur** S(x) = ensemble de paires actions - etat
   - e.g., S(Arad) = &#123;(Arad → Zerind, Zerind), ... &#125;
   - AIMA : ActionsFunction et ResultFunction = **modele de transition**
   - 1+2 = Espace des etats → graphe → chemins
3. **Test de but**, qui peut etre
   - *explicite*, e.g. x = "a Bucharest"
   - *implicite*, e.g. EchecEtMat(x)
4. **Cout de chemin** (optionnel, additif)
   - e.g., Somme des distances, Nombre d'actions executees, etc.
   - c(x,a,y) est le **cout d'etape**, (>= 0)

- Une **solution** est une sequence d'actions (chemin) qui conduit de l'etat initial a un etat but
  - **Optimale** = cout minimum

---

# Selection d'un espace des etats

- Le monde reel est tres complexe
  - L'espace des etats doit faire l'objet d'une **abstraction**
- **Etat** (abstrait) = ensemble d'etats reels
- **Action** (abstraite) = combinaison complexe d'actions reelles
  - e.g. "Arad → Zerind" represente un ensemble de routes, detours, pauses etc.
  - Pour une realisation garantie, chaque etat reel "a Arad" doit conduire a un etat reel "a Zerind"
- **Solution** (abstraite) = ensemble de chemins reels qui sont solutions dans le monde reel
  - Chaque action abstraite doit etre plus "facile" que dans le probleme reel
- **Probleme jouet** : experimenter avec les methodes de resolution

---

# Exemple Abstraction: Assemblage robotique

<img src="./images/img_004.png" style="position:absolute; top:60px; right:30px; width:380px;" alt="Bras robotique" />

- **Etats** : Coordonnees reelles des joints du robot et des objets
- **Test de but** : Objet assemble
- **Etat initial** : Pieces detachees, bras au repos
- **Actions** : Mouvement continu des joints du bras robotique
- **Cout de chemin** : temps d'execution

---

# Probleme jouet: Le taquin

<img src="./images/img_005.png" style="position:absolute; top:60px; right:30px; width:350px;" alt="Le taquin 8-puzzle" />

- **Etats** : Position des 8 pieces + case vide
- **Test de but** : Etat == &#123; 0, 1, 2, 3, 4, 5, 6, 7, 8 &#125;
- **Etat initial** : La moitie des etats possibles
- **Actions** : case vide → gauche, droite, haut, bas
- **Cout de chemin** : 1 par etape
- Note : puzzle a glissement de pieces : problemes NP-complet (durs)

---

# Probleme jouet: Les 8 reines

<img src="./images/img_006.png" style="position:absolute; top:60px; right:30px; width:280px;" alt="Les 8 reines" />

- **Etats** : Disposition de 0-8 reines
- **Test de but** : 8 reines sont presentes, et aucune n'est menacee
- **Etat initial** : Echiquier vide
- **Actions** : Poser une reine
- **Cout de chemin** : N.A / 1 par etape
- Meilleure formulation: une reine par colonne, de gauche a droite, legale. 1,8* 10^14 positions (dur) -> 2057 positions (facile)

---
layout: section
---

# Resolution de Problemes par Exploration
---

# Arbre d'exploration

## Idee de base

- Exploration simulee (hors ligne) de l'espace des etats en generant les successeurs des etats deja explores (**developpement** des etats)
- Ensemble des noeuds feuilles = **frontiere** d'exploration
- Choix des noeuds a developper = **strategie** d'exploration

## Fonction EXPLORER-ARBRE

```
fonction EXPLORER-ARBRE(probleme) retourne une solution, ou echec
  initialiser la frontiere avec l'etat initial de probleme
  faire en boucle
    si la frontiere est vide alors retourner echec
    choisir un noeud feuille et l'enlever de la frontiere
    si le noeud contient un etat but alors retourner la solution correspondante
    developper le noeud choisi, en ajoutant les noeuds obtenus a la frontiere
```

---

# Arbre d'exploration: exemple

<img src="./images/img_003.png" style="display:block; margin:12px auto; max-height:60vh;" alt="Arbre d'exploration - Itineraire Roumanie" />

Arbre de recherche avec la racine **Arad** : developpement des successeurs Sibiu, Timisoara, Zerind, puis de leurs propres successeurs.

---

# Exploration de graphe

## Idee de base

- Etats repetes → chemins avec boucle
- **Solution** : memoire = ensemble explore
- **Frontiere** : separe espace explore et espace inconnu

## Fonction EXPLORER-GRAPHE

```
fonction EXPLORER-GRAPHE(probleme) retourne une solution, ou echec
  initialiser la frontiere avec l'etat initial de probleme
  initialiser l'ensemble des noeuds explores a vide
  faire en boucle
    si la frontiere est vide alors retourner echec
    choisir un noeud feuille et l'enlever de la frontiere
    si le noeud contient un etat but alors retourner la solution correspondante
    ajouter le noeud a l'ensemble des noeuds explores
    developper le noeud choisi, en ajoutant les noeuds obtenus a la frontiere
    seulement si ils ne sont ni dans la frontiere, ni dans l'ensemble explores.
```

---

# Infrastructure: Etats vs Noeuds

<img src="./images/img_010.png" style="position:absolute; top:60px; right:20px; width:360px;" alt="Structure d'un noeud" />

## Etats != Noeuds

- Un **Etat** est une representation de la configuration reelle
- Un **Noeud** est une structure de donnees constitutive d'une exploration
  - Inclut l'etat, le noeud parent, l'action, le cout g(x), la profondeur

## Fonction NOEUD-FILS

```
fonction NOEUD-FILS(probleme, parent, action) retourne un noeud
  retourner un noeud avec
    ETAT = probleme.Resultat(parent.Etat, action),
    PARENT = parent, ACTION = action,
    COUT-CHEMIN = parent.COUT-CHEMIN
                + probleme.COUT-ETAPE(parent.Etat, action)
```

---

# Strategies d'exploration

Une strategie d'exploration definit l'ordre de developpement des noeuds.

## Criteres d'evaluation

- **Completude** : garantie d'obtenir une solution si elle existe
- **Optimalite** : garantie d'obtenir une solution de cout minimal
- **Complexite en temps** : ~ nombre de noeuds developpes
- **Complexite en espace** : ~ nombre max de noeuds en memoire

## Complexites s'evaluent selon

- **b** : facteur maximal de branchement dans l'arbre de recherche
- **d** : (depth) profondeur de la solution de moindre cout
- **m** : profondeur maximale de l'espace d'etats (souvent infini)

---
layout: section
---

# Exploration Non Informee
---

# Strategies d'exploration non informee

Les strategies non informees (aveugle) utilisent uniquement la definition du probleme.

## Strategies d'exploration en largeur

- **BFS** : En largeur d'abord (Breadth First Search)
- **UCS** : A cout uniforme (Uniform Cost Search)

## Strategies d'exploration en profondeur

- **DFS** : En profondeur d'abord (Depth First Search)
- **DLS** : En profondeur limitee (Depth Limited Search)
- **IDS** : Iterative en profondeur (Iterative Depth Search)

## Variantes

- Bidirectionnelle

---

# Exploration en largeur d'abord (BFS)

<img src="./images/img_011.png" style="position:absolute; top:60px; right:20px; width:480px;" alt="Expansion BFS" />

- Developpe les noeuds les **moins profonds** en premier
- La frontiere est une **queue** (File ou FIFO)

---

# Proprietes de l'exploration en largeur

<img src="./images/img_013.png" style="position:absolute; top:60px; right:20px; width:440px;" alt="Tableau complexite BFS" />

- **Complet** ? Oui (si b est fini)
- **Complexite en temps** ? O(b^(d+1))
- **Complexite en espace** ? O(b^(d+1))
  - chaque noeud est garde en memoire
- **Optimale** ? Oui si cout d'etape = 1
- L'**espace** est le plus gros probleme

---

# Exploration a cout uniforme (UCS)

- Developpe les noeuds les moins couteux en premier
  - La frontiere est une queue triee par cout de chemin
- Equivaut a l'exploration en largeur d'abord si le cout d'etapes est uniforme
- En theorie de graphes = algorithme de Dijkstra

## Caracteristiques

- Complet? Oui, si cout d'etape >= epsilon
- Complexite en temps et en espace: O(b^(1+plafond(C*/epsilon)))
  - avec C* le cout d'une solution optimale
- Optimal ? Oui: les noeuds sont developpes dans l'ordre des cout de chemin

---

# Exploration en profondeur d'abord (DFS)

<img src="./images/img_014.png" style="position:absolute; top:60px; right:20px; width:480px;" alt="Expansion DFS" />

- Developpe les noeuds les **plus profonds** en premier
  - La frontiere est une **Pile** (LIFO)
  - Les branches deja explorees ne sont pas conservees en memoire

## Caracteristiques

- Complet ? Non: echoue dans les espaces de profondeur infinie
  - ou avec des boucles -> exploration de graphe
- Complexite en temps: O(b^m) terrible si m beaucoup plus grand que d
  - mais si les solutions sont denses, plus rapide qu'en largeur
- Complexite en espace: O(b^m), lineaire en espace !
- Optimal: Non

## Variante: Exploration avec retour arriere (backtracking)

- On developpe 1 seul successeur a la fois -> O(m) en espace
- + Optimisation en modifiant les etats plutot qu'en les copiant (retour arriere = annulation)

---

# Exploration en profondeur limitee (DLS)

= Exploration en profondeur d'abord avec une profondeur limite l

- Les noeuds de profondeur l n'ont pas de successeur
- Complet si l >= d = diametre de l'espace des etats

## Implementation recursive

```
fonction Exploration-Profondeur-Limitee(probleme, limite) retourne une solution, ou echec/arret
  retourner EPL-Recursive(Creer-Noeud(probleme.Etat-Initial), probleme, limite)

fonction EPL-Recursive(noeud, probleme, limite) retourne une solution, ou echec/arret
  si probleme.Test-But(noeud.Etat) alors retourner Solution(noeud)
  sinon si limite = 0 alors retourner coupure
  sinon
    arret_rencontre? <- faux
    pour chaque action dans probleme.Actions(noeud.Etat) faire
      fils <- Noeud-Fils(probleme, noeud, action)
      resultat <- EPL-Recursive(fils, probleme, limite - 1)
      si resultat = coupure alors arret_rencontre? <- vrai
      sinon si resultat != echec alors retourner resultat
    si arret_rencontre? alors retourner coupure sinon retourner echec
```

---

<style scoped>
.slidev-layout { font-size: 0.85em; }
h2 { font-size: 1.1em !important; margin-top: 0.3em !important; margin-bottom: 0.1em !important; }
</style>

# Exploration iterative en profondeur (IDS)

On augmente graduellement l

```
fonction Exploration-Iterative-Profondeur(probleme) retourne une solution, ou echec
  pour profondeur = 0 jusqu'a l'infini faire
    resultat <- EXPLORATION-LIMITEE-PROFONDEUR(probleme, profondeur)
    si resultat != arret alors retourner resultat
```

## Cout du meme ordre que l'exploration en profondeur limitee

- Pour b = 10, d = 5: ~+10% (contre intuition)
  - N_DLS = 1 + 10 + 100 + 1,000 + 10,000 + 100,000 = 111,111
  - N_IDS = 6 + 50 + 400 + 3,000 + 20,000 + 100,000 = 123,456

## Caracteristiques

- Complet: Oui | Temps: O(b^d) | Espace: O(b*d) | Optimale: Oui si cout d'etape = 1

**Analogue :** Exploration iterative par allongement (ILS) pour cout uniforme

---

# Exploration Bidirectionnelle

<img src="./images/img_017.png" style="position:absolute; top:60px; right:20px; width:360px;" alt="Recherche bidirectionnelle" />

## Quand on connait l'etat but

- Double exploration vers l'aval et vers l'amont
- Interet : O(b^(d/2)) + O(b^(d/2)) est tres inferieur a O(b^d)

## Exemple courant

- Logiciel de navigation GPS

## Difficultes

- Necessite une fonction Predecesseurs
- Controle de l'intersection
  - maintient de la frontiere, meme en profondeur + hachage pour comparaison
  - + Solution non optimale meme en largeur -> continuer pour trouver les raccourcis
- Etats buts complexes
  - Plusieurs etats buts -> Etat but fictif en l'aval des etats buts
  - Description implicite (ex: 8 reines) -> difficile

---

# Resume Exploration non informee

## Necessite d'une abstraction du monde reel

## Varie des strategies non informees

- En largeur = Queue
- En profondeur = Pile
- Compromis complexite espace vs temps
- Presence de cycles -> exploration de graphe

## Comparaison des explorations non informees

| Critere | Largeur d'abord | Cout uniforme | Profondeur d'abord | Profondeur limitee | Profondeur iterative | Bidirectionnelle |
|--------|-----------------|---------------|--------------------|--------------------|-----------------------|------------------|
| Complete? | Oui | Oui | Non | Oui (si l>=d) | Oui | Oui |
| Temps | O(b^(d+1)) | O(b^(1+C*/epsilon)) | O(b^m) | O(b^l) | O(b^d) | O(b^(d/2)) |
| Espace | O(b^(d+1)) | O(b^(1+C*/epsilon)) | O(b^m) | O(b^l) | O(b^d) | O(b^(d/2)) |
| Optimal? | Oui (cout=1) | Oui | Non | Non | Oui (cout=1) | Oui |

---

# Les missionnaires et cannibales

<img src="./images/img_019.png" style="position:absolute; top:60px; right:20px; width:360px;" alt="Missionnaires et cannibales" />

- Les missionnaires et cannibales doivent traverser la riviere
- Pas plus de 2 personnes en meme temps sur la barque
- Si + de cannibales que de missionnaires d'un cote ou de l'autre → ils se font manger

---
layout: section
---

# Exploration Informee
---

# Exploration gloutonne

<img src="./images/img_020.png" style="position:absolute; top:60px; right:20px; width:340px;" alt="Valeurs heuristiques h(n)" />

## Idee

- Utiliser une **heuristique** h(n) = cout estime pour atteindre le but depuis n
  - f(n) = g(n) + h(n)
  - Developpe le noeud avec le plus petit f(n)

## Caracteristiques

- Complet? Non, peut etre piege dans un maximum local
- Temps? O(b^m) mais un bon heuristique donne des bons resultats
- Espace? O(b^m)
- Optimal? Non

---

# Exploration A*

<img src="./images/img_022.png" style="position:absolute; top:60px; right:20px; width:160px;" alt="Triangle consistance A*" />

## Idee

- Eviter de developper les noeuds deja couteux
  - Minimisation du cout total estime de la solution

## Fonction d'evaluation f(n) = g(n) + h(n)

- g(n) = cout pour atteindre n
- h(n) = cout estime de n au but
- f(n) = cout total estime du chemin au but en passant par n

## Identique a UCS avec g+h au lieu de g

## Theoremes

- Si h(n) est admissible, A* est optimal en exploration d'arbre
  - Demonstration par l'absurde en developpant
- Si h(n) est consistante, A* est optimal en exploration de graphe
  - Demonstration: f est monotone puis par l'absurde en developpant

---

# Caracteristiques de A*

<img src="./images/img_023.png" style="position:absolute; top:60px; right:20px; width:400px;" alt="Contours A* sur carte Roumanie" />

## Optimalite de A*

- Ajoute graduellement des "f-contours" de noeuds
- Le contour i a tous les noeuds avec f=f_i ou f_i < f_(i+1)

## Proprietes de A*

- Complet: Oui
  - Sauf s'il existe une infinite de noeuds avec f <= f(G)
- Complexite en temps: Exponentielle
- Complexite en espace: Idem
- Optimal? Oui (cf. theoremes)
  - + optimalement efficace pour toute heuristique consistante donnee

## Limites

- Nombre d'etats dans l'espace d'exploration des contours souvent exponentiel.
- Souvent, le principal probleme est la memoire

---

# Variations

## Exploration heuristique a memoire limitee

- A* avec approfondissement iteratif (IDA*)
  - Coupe: cout f le plus faible parmi les noeuds en depassement
- Exploration recursive par le meilleur d'abord (RBFS)
  - Espace en memoire lineaire: valeur f du meilleur chemin alternatif
  - Recursion avec valeur rapportee: meilleure valeur f des enfants oublies
  - Mais exces inverse: trop peu de memoire et trop de "redeveloppements"
- Utilisation de toute la memoire disponible
  - MA* (A* sous contrainte de memoire)
  - SMA* (simplified MA*)
    - On oublie quand plus de place disponible, le noeud le plus mauvais

## Exploration avec apprentissage

- Espace des etats de metaniveau = etats de l'algorithme d'exploration (noeuds, arbres etc.)
- Techniques d'apprentissage au metaniveau -> compromis entre cout de calcul et cout de chemin

---

# Effet de l'exactitude de l'heuristique

## Efficacite fonction de l'erreur absolue ou relative de l'heuristique

- Delta = h* - h, epsilon = (h* - h)/h*
- Complexite en O(b^epsilon*d) ou O(b^(epsilon*d)) a cout d'etape constant

## Facteur de branchement effectif b*

- Facteur de branchement equivalent sans heuristique (exploration a cout uniforme)
- Bonne indication de l'utilite globale de l'heuristique

## Dominance

- Si h1 et h2 admissibles et h2(n) >= h1(n) pour tout n, h2 domine h1
- Si h2 domine h1, h2 est meilleure

---

# Production d'heuristiques

## Problemes relaxes

- Probleme avec moins de restrictions = **probleme relaxe**
- Cout exact = heuristique admissible
- Exemple du Taquin: h1 (nb pieces mal placees), h2 (distance Manhattan)

## Sous-problemes

- Exemple: taquin (pieces 1,2,3,4)
- **Bases de donnees de motifs**: cout exact sous-problemes = heuristique generale
- **Motifs disjoints**: question de l'additivite des heuristiques admissibles

## Apprentissage d'heuristiques

- Utilisation de l'experience sur solutions connues
- Apprentissage inductif (ex: h(n) = c1*x1(n) + c2*x2(n))
- Domaine vaste: apprentissage = machine learning

---
layout: section
---

# Algorithmes d'Exploration Locale
---

# Algorithmes d'exploration locale

## Objectif: but = solution (chemin secondaire)

- Espace etats = configurations completes (ex: 8 reines)

## Algorithme d'exploration locale

- Conserve un etat "courant" a ameliorer

## Avantages

- Peu de memoire
- Fonctionne dans espaces grands/infinis

## Exemple: 8 reines

---

# Paysage de l'espace des etats

<img src="./images/img_025.png" style="display:block; margin:12px auto; max-height:55vh;" alt="Paysage espace des etats" />

## Problemes d'optimisation

- Objectif = meilleur etat selon **fonction objectif**

## Utilite du paysage

- Recherche maximum (f = -h)
- **Complet**: trouve toujours un but
- **Optimal**: trouve maximum global

---

# Exploration par escalade (HCS)

<img src="./images/img_028.png" style="position:absolute; top:60px; right:20px; width:200px;" alt="8 reines escalade" />

## Escalade par la plus forte pente

```python
retourne maximum local
  boucle courant <- voisin max valeur
  si voisin <= courant, retourner courant
```

## Exploration locale "gloutonne"

- Maxima locaux, cretes, plateaux, paliers

## Solution: deplacement lateraux

- Necessite de limites

## Escalade stochastique: premier choix aleatoire (incomplet)

## Escalade reprise aleatoire (complet)

---

# Exploration par recuit simule (SA)

<img src="./images/img_027.png" style="position:absolute; top:60px; right:20px; width:120px;" alt="Courbes temperature SA" />

## Idee : echapper aux maxima locaux

- Autoriser mauvais deplacements, diminuer leur frequence progressivement

## Code

```python
boucle t -> infini
  si T=1 retourner courant
  sinon -> voisin aleatoire
  DeltaE = voisin - courant
  suivant si DeltaE > 0
  sinon courant avec proba e^(DeltaE/T)
```

## Frequence <- temperature T

- T diminue doucement -> proba optimum global -> 1
- Utilise dans circuits, ordonnancement (ex: carton de babioles)

---

# Exploration locale en faisceau (LBS)

## Idee: suivre k etats (ex: *Perdus en foret*)

- k etats aleatoires, generation tous succes, selection k meilleurs

## Transfere progressif ressources

- Risque: transfert trop rapide vers une petite region

## Variante: exploration en faisceau stochastique

- Analogue escalade stochastique; k choix aleatoire (proba = valeur)
- Analogue selection naturelle -> GAs

---

# Algorithmes genetiques (GAs)

## Variante faisceau stochastique

- Successeurs = combinaisons (approx reproduction)

## Population (individus, taille constante)

## Genes (recombinaison, mutations aleatoires)

## Phenotype (fonction d'adaptation: *fitness function*)

## Code

```
algorithme genetique (selection, reproduction, mutation, retour meilleur individu)
```

---

# Algorithme genetique pour les 8 reines

<img src="./images/img_031.png" style="display:block; margin:8px auto; max-height:35vh;" alt="Algorithme genetique: population, fitness, selection, crossover, mutation" />

<img src="./images/img_032.png" style="display:block; margin:8px auto; max-height:20vh;" alt="Croisement 8 reines" />

## Phenotype

- Diagramme: 3 echiquiers (addition de deux, resultat)

---
layout: section
---

# Exploration Locale - Espaces Continus
---

# Exploration locale d'espaces continus

<img src="./images/img_033.gif" style="position:absolute; top:60px; right:20px; width:300px;" alt="Trajectoires optimiseurs SGD" />

## Etats definis par des variables reelles

## Problemes de discontinuites

- Une solution = Discretisation des voisinages

## Pente pour l'escalade = gradient du paysage

- Parfois resolution analytique de nabla f = 0 (rare)
- Si valable localement: x <- x + alpha*nabla f ou alpha est le pas de l'etape
- Si pas analytique: gradient empirique
  - Exploration lineaire
    - alpha trop petit ou trop grand -> on double le pas jusqu'a observer une diminution
  - Methode de Newton-Raphson
    - Formule de Newton pour trouver g(x) = 0 : x <- x - g(x) / g'(x)
    - En prenant pour g le gradient de f: x <- x - H^-1(x) nabla f(x)
      - avec H matrice Hessienne des derivees secondes de f
    - Methodes modernes (RMSProp, ADAM)

## Optimisation sous contrainte

- Contraintes sur les variables
- Programmation lineaire
  - <- inegalites formant ensemble convexe (pas de trous)
  - Tres etudie -> complexite polynomiale

---
layout: section
---

# Extensions
---

# Exploration avec actions non deterministes

## Cf. cours precedent -> utilite des percepts

- Solution != sequence -> plan contingent ou strategie

## Arbres Et-Ou: entrelacement de noeuds

- Noeuds Ou = Choix d'exploration classique
- Noeuds Et = "Choix" de l'environnement
- solutions cycliques -> possibilite d'etiquettes (tant que...)

## Ex: Aspirateur glissant

- Ou l'action de deplacement peut echouer

---

# Exploration avec observations partielles

## Cf. cours precedent -> Etat pas situe precisement

- Analogue a non deterministe
- Etat de croyance: etats physiques possibles

## Exploration sans observation: probleme conformant

- Parfois parfaitement soluble. Ex: positionnement de pieces
- Idee -> contraindre le monde
- N etats physiques -> 2^N etats de croyance
- Modele de transition -> etape de prevision

## Exploration incrementale

- -> Arbres Et-Ou complets

## Exploration avec observation

- Etape de prevision d'observations
- Etape de mise a jour

---

# Exploration en ligne

## Entrelacement calcul et action

- Problemes de decouverte

## Ratio de competitivite

- En temps, vis-a-vis d'un espace connu

## Il y a parfois des impasses

- sinon l'espace est explorablesans risque

## Algorithmes

- DFS, Escalade avec reprise aleatoire
- Memoire -> estimation H de l'heuristique h
  - LRTA* (learning real time A*)

## Apprentissage

- De la "carte" (Etats)
- Du cout d'etape
- Des regles (transitions)

---

# Resume Exploration Informee

## Heuristiques

- Admissibles
- Consistantes

## Meilleur d'abord

- Exploration Gloutonne (h)
- A* (g+h) + variantes limitees en memoire

## Exploration Locale

- Paysage de l'espace d'etats
- Escalade, Recuit simule
- Exploration en Faisceau, stochastique, algorithmes genetiques

## Extensions

- Espaces continus -> gradients, programmation lineaire
- Actions Non deterministe -> Arbres Et-Ou
- Observations partielles -> previsions, exploration en ligne

---
layout: section
---

# Jeux vs Exploration
---

# Jeux vs Exploration

## Environnements

- multi-agents
- concurrentiels

## Classe de jeux la plus etudiee (echecs, Go)

- Alternes
- Deterministes
- A somme nulle (h1 = -h2)
- A information parfaite

## Difficulte

- Impr edictibilite -> arbre d'exploration complet
- Impraticable, solution optimale impossible
- Performance critique: temps -> victoire

---

# Arbre de jeu

<img src="./images/img_037.png" style="position:absolute; top:50px; right:10px; width:500px;" alt="Arbre de jeu morpion" />

## Ex : Morpion

- **Etat initial** S0
- **Joueurs** : Max, Min
- **Actions** : Coups
- **Resultat**(s,a) : Modele de transition
- **Test-Terminal**(s) : Fin de partie
- **Utilite**(s,p) : Score final de p

---

# Minimax

## Decisions optimales

- Espace Non deterministe
  - Strategie contingente
  - Arbre Et-Ou
- 1 tour = 2 coups (Max, Min)

## Valeur Minimax

- Strategie theorique optimale
- Les 2 joueurs jouent au mieux

## Formules Minimax

```
Minimax(s) = { Utilite(s) si Test-Terminal(s)
              max_a dans Actions(s) Minimax(Resultat(s,a)) si Joueur(s) = Max
              min_a dans Actions(s) Minimax(Resultat(s,a)) si Joueur(s) = Min
```

---

# Algorithme Minimax

<img src="./images/img_038.png" style="position:absolute; top:60px; right:20px; width:380px;" alt="Arbre Minimax" />

## Faire "remonter" les valeurs Minimax

## Proprietes

- Complet? Oui (si l'arbre est fini)
- Optimal? Oui (avec adversaire optimal)
- Complexite en temps: O(b^m)
- Complexite en espace: O(b^m) (DFS)
- Echecs: b ~ 35, m ~ 100
  -> completement infaillable

## Mais c'est la base de

- l'analyse mathematique des jeux
- meilleurs algorithmes

## Cadre Multi-joueurs

- Meme approche
- Vecteurs Utilite
- Souvent, alliances naturelles

---

# Elagage Alpha-Beta

<img src="./images/img_040.png" style="position:absolute; top:60px; right:20px; width:380px;" alt="Elagage Alpha-Beta" />

## Idee : Diminuer le nombre d'etats a examiner

- Sans perdre l'optimalite
- Les branches mauvaises sont ignorees (elaguees)
  - alpha = meilleur coup pour Max
  - beta = meilleur coup pour Min

## L'ordre d'evaluation des coups est important

- Si l'ordre est "parfait":
  - la complexite devient O(b^(m/2))
  - facteur de branchement effectif sqrt(b)
  - profondeur double

## Approfondissement iteratif: Heuristiques des coups de maitre

## Permutations

- Certaines sequences distinctes sont equivalentes
- Maintiennent une table de transposition

## Exemple raisonnement au metaniveau

- Ex: raisonnement oriente buts ou autres types d'IA

---

# Decisions imparfaites

<img src="./images/img_042.png" style="position:absolute; top:60px; right:20px; width:400px;" alt="Formule ExpectiMinimax" />

## Approche

- Utilite -> Fonction d'evaluation heuristique Eval(s) sur des etats non terminaux
- Test de terminaison -> Test d'arret Cutoff(s) pour savoir quand appliquer l'evaluation (ex: profondeur limite d_lim)

## Fonction d'evaluation

- Cf. Humains <- attributs d'un etat
- Classe d'equivalence -> valeur attendue (utilite ponderee)
- Mais trop de classes -> valeur materielle -> fonction lineaire ponderee
  - Eval(s) = w1*f1(s) + w2*f2(s) + ... + wn*fn(s)
- Mais non independance des attributs -> fonction non lineaire
- Si pas d'experience, possibilite d'apprentissage (1 fou = 3 pions!)

## Exploration avec arret

- Alpha Beta Iteratif pour respecter une limite de temps (+ ordre des coups)
- Probleme des situation instables au cutoff (prise au prochain tour)
  - Solution = recherche de stabilite ("quiescence", ex: pas de prise)

---
layout: section
---

# Problemes a Satisfaction de Contraintes
---

# Problemes a satisfaction de contraintes (CSPs)

<img src="./images/img_047.png" style="position:absolute; top:50px; right:10px; width:320px;" alt="Carte Australie coloree" />

## Definition

- **Variables** X1, ..., Xn
- **Domaines** D1, ..., Dn
- **Contraintes** C1, ..., Cm

## Exemple : Coloration de carte

- Variables : WA, NT, Q, NSW, V, T, SA
- Domaines : &#123;rouge, vert, bleu&#125;
- Contraintes : WA != NT, NT != Q, SA != NSW, NSW != V, V != SA

## Objectif

- Trouver une assignation complete satisfaisant toutes les contraintes

---

# CSP: Exemple cryptarithme

<img src="./images/img_049.png" style="position:absolute; top:60px; right:20px; width:280px;" alt="Graphe contraintes TWO+TWO=FOUR" />

## Variables

- F, T, U, W, R, O, X1, X2, X3

## Domaines

- &#123;0, 1, 2, 3, 4, 5, 6, 7, 8, 9&#125;

## Contraintes

- Alldiff(F,T,U,W,R,O)
  - O + O = R + 10
  - X1 + W + W = U + 10
  - X2 + T + T = O + 10
  - X3 + F + F = W + 10
- X1 != X2 != X3

## Recherche

- Essayer les valeurs pour F,T,U,W,R,O

---

# Resolution de CSPs: Generation et test

## Approche la plus simple

1. Generer une assignation complete aleatoire
2. Tester si elle satisfait toutes les contraintes
3. Recommencer jusqu'a succes

## Probleme

- Nombre d'assignations: produit des domaines
  - Ex: coloration 7 pays -> 3^7 = 2187
  - Ex: 8 reines -> 64^8 = 2.8 * 10^14

---

# CSPs: Exploration avec backtracking

<img src="./images/img_050.png" style="position:absolute; top:50px; right:10px; width:440px;" alt="Arbre backtracking CSP Australie" />

## Principe

- Etendre progressivement une assignation partielle
- Des qu'une contrainte est violee → retour en arriere (backtrack)

## Fonction BACKTRACK

```
fonction BACKTRACK(csp, assignation) retourne solution ou echec
  si assignation est complete alors retourner assignation
  var <- variable non assignee
  pour chaque valeur dans var.domaine faire
    si valeur consistante avec assignation alors
      ajouter var=valeur a assignation
      resultat <- BACKTRACK(csp, assignation)
      si resultat != echec alors retourner resultat
      retirer var=valeur de assignation
  retourner echec
```

---

# CSPs: Propagation de contraintes

<img src="./images/img_053.png" style="position:absolute; top:50px; right:10px; width:440px;" alt="Forward Checking Australie" />

## Idee

- Reduire les domaines avant developpement
- Si domaine vide -> echec immediat

## Techniques

- **Forward Checking**: Apres assignation, eliminer les valeurs incompatibles des variables non assignees
- **Arc Consistency (AC)**: Pour chaque contrainte binaire (X,Y), eliminer les valeurs de X qui n'ont pas de support dans Y

## Algorithme AC-3

- Propage la coherence d'arc a travers le reseau de contraintes
- Tres efficace mais complexe

---

# CSPs: Heuristiques de variables et valeurs

<img src="./images/img_054.png" style="position:absolute; top:50px; right:10px; width:380px;" alt="Reduction domaines AC" />

<div style="max-width:55%;">

## Choix de variable (MRV, LCV)

- **Most Constrained Variable**: Variable avec le plus petit domaine
- **Least Constraining Value**: Valeur qui elimine le moins de choix pour les autres variables

</div>

## Choix de valeur (LCV)

- Choisir la valeur qui laisse le plus d'options aux voisins
- Maximise les chances de succes

---

# CSPs: Structure des problemes

<img src="./images/img_055.png" style="position:absolute; top:60px; right:20px; width:250px;" alt="Decomposition arbre contraintes" />

## Graphe de contraintes

- Noeuds = variables
- Arcs = contraintes binaires

## Composantes connexes

- Sous-ensembles de variables interconnectees
- Resolution independante possible

## Clusters et arbres

- Structure en arbres -> resolution en temps lineaire O(n)
- Graphe complet -> NP-complet

---

# CSPs: Exploration locale

## Min-conflicts

- Choisir la variable qui viole le plus de contraintes
- Changer sa valeur pour minimiser les conflits
- Tres efficace pour les problemes avec de nombreuses variables

## Example: 8 reines

- Chaque reine sur une colonne differente
- Deplacer la reine qui a le plus de conflits

---

# Techniques de resolution des CSPs

## Methodes traditionnelles

- Backtracking + heuristiques
- Propagation de contraintes, Forward checking
- Exploration locale (min-conflicts)
- Backjumping

## Contraintes modernes et Hybridation

- Integration CP/SAT/SMT: Utilisation de techniques telles que Lazy Clause Generation pour apprendre les conflits
  - Exemple: Le solver CP-SAT de Google OR-Tools

- Hybridation avec metaheuristiques: Combinaison d'exploration locale (min-conflicts) avec des phases de reparation par CP
  - Large Neighborhood Search

---

# Domaines des CSPs

## Variables discretes

- Domaines finis: n variables, taille de domaine d -> O(d^n) assignations completes
- Domaines infinis: Entiers, chaines de caracteres etc.
  - Ex: planification de cours
  - Besoin d'un langage de contraintes (DebutCours1 + 5 <= DebutCours2)

## Variables continues

- Exemple: Planifications des observation du Telescope Hubble
- Contraintes lineaires solubles en temps polynomial par la programmation lineaire

---

# Graphe de contraintes

<img src="./images/img_048.png" style="position:absolute; top:60px; right:20px; width:300px;" alt="Graphe contraintes Australie" />

## CSP Binaire: chaque contrainte relie 2 variables

## Graphe de contraintes

- Les noeuds sont les variables
- Les arcs sont les contraintes

## Exemple coloration

- Graphe avec noeuds (WA, NT, SA, Q, NSW, V, T)
- Arcs entre noeuds adjacents (e.g., WA-NT, NT-SA, SA-Q, etc.)

---

# Types de contraintes

## Unaires

- Contraintes a 1 variable (Ex: SA != vert)

## Binaires

- Contraintes impliquant 1 paire de variables (Ex: SA != WA)

## Globales ou d'ordre superieur

- Contraintes avec 3 variables ou plus
- Ex: problemes cryptarithmetiques
  - Variables: F T U W R O x X1 X2 X3
  - Domaines: &#123;0,1,2,3,4,5,6,7,8,9&#125;
  - Contraintes: Alldiff(F,T,U,W,R,O), O + O = R + 10, etc.

## Representation

- Hypergraphe des contraintes
  - Xi sont des variables auxiliaires
  - Possible de reduire a des contraintes binaires (ex: Graphe Biparti)
  - Contraintes de preferences
    - CSP -> contraintes absolues
    - -> Problemes a optimisation de contraintes (COP)

---

# CSPs courants

## Principaux solveurs actuels

- MiniZinc: Langage de modelisation independant et front-end pour divers solveurs
- Google OR-Tools: Solveur hybride CP/SAT avec API pour Python, C#, Java et C++
- Choco Solver: Alternative open-source en Java et C++ respectivement
- Z3: Solveur SMT pour contraintes logiques complexes

## Interoperabilite multi-langages

- Bindings natifs OR-Tools et Z3 offrent des interfaces officielles pour plusieurs langages

## Ponts technologiques

- pythonnet pour integration Python et .NET
- IKVM pour utiliser des bibliotheques Java en C#
- JPype pour appeler du code Java depuis Python

---

# Applications et cas d'usage modernes

## Planification et ordonnancement

- Emploi du temps, scheduling industriel, allocation de ressources

## Logistique et transport

- Problemes de tournees de vehicules (VRP), gestion d'entrepots

## Optimisation combinatoire

- Puzzles (Sudoku, n-queens, coloriage de graphes, configuration de produits)

## Planification en IA

- Planification de missions robotiques, satellites, et autres systemes autonomes

---

# Resume CSPs

## Problemes a satisfaction de contraintes

- Variables, domaines
- + Graphes (binaires) ou hypergraphes des contraintes

## Techniques d'inference

- Coherence de noeuds, arcs, K-coherence

## Exploration avec Backtracking

- En profondeur d'abord
- Couplage Inference + exploration
- Heuristiques choix de variables, de valeurs
- Forward checking et Backjumping orientent conflit accerent aussi
- Exploration locale
  - Min-conflicts est tres efficace memes avec de nombreuses variables

## Structure des problemes: complexite des problemes

  - Coupe cycle ideal pour reduire a un arbre
  - Decomposition en arbre pratique, nombre de sous-ensembles connexes
  - Symetrie des valeurs important

---
layout: section
---

# TP
---

# TP

## PKP service web CSPs

---
layout: end
---

# Merci

Jean-Sylvain Boige
JSBOIGE@myia.ORG
