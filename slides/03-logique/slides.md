---
theme: ../theme-ia101
title: "Intelligence Artificielle - Bases de connaissances et Logique"
info: IA 101 - Logique propositionnelle et du premier ordre
paginate: true
drawings:
  persist: false
transition: slide-left
mdc: true
layout: cover
---

# Bases de connaissances et Logique

INTELLIGENCE ARTIFICIELLE -- III

**Logique propositionnelle**

- Logique du premier ordre
  - Planification

- Representation des connaissances

---
layout: section
---

# Plan du cours

---
layout: default
---

# Sommaire

- Agents fondes sur la connaissance
- Logique propositionnelle
- Logique du premier ordre
- Planification
- Representation de connaissances
- TP: Mise en oeuvre de l'infrence en logique propositionnelle et en logique du premier ordre

---
layout: section
---

# Agents fondes sur les connaissances
---
layout: default
---

# Agents fondes sur les connaissances

## Fonction KB-AGENT

```
fonction KB-AGENT(percept) retourne une action
  persistante: KB, une base de connaissances
               t, un compteur, initialement a 0, qui indique le temps

  Tell(KB, Creer-Enonce-Percept(percept, t))
  action <- Ask(KB, Creer-Requete-Action(t))
  Tell(KB, Creer-Enonce-Action(action, t))
  t <- t + 1
  retourner action
```

## Composants

- Une base de connaissance (KB), composee d'enonces formules dans un langage formel de representation des connaissances
- Un systeme d'infrence (raisonnement) qui produit de nouveaux enonces pour prendre des decisions

## Fonctions principales

- Tell (-> KB) : Ajouter des connaissances
- Ask (<- KB) : Interroger la base

## Niveaux de l'architecture

- Connaissances (formulation naturelle)
- Logique (formulation en enonces)
- Implementation (representation physique des enonces)

---
layout: default
---

# Exemple: le monde du Wumpus

<img src="./images/img_003.png" style="position:absolute; top:50px; right:10px; height:320px;" alt="Grille du monde du Wumpus" />

## Jeu de role simpliste

### Environnement

- Grille 4x4 de salles a explorer

### But/Performance

- Trouver l'or et sortir sans dommages

### Actions

- Avancer, tourner, saisir, tirer, sortir

### Percepts

- Odeur, brise, lueur, choc, cri
  -> Vecteur

## Symboles

- A = Agent
- B = Brise
- L = Lueur/Or
- OK = Case sure
- P = Puits
- O = Odeur
- V = Visite
- W = Wumpus

---
layout: default
---

# Representation et logique

<img src="./images/img_007.png" style="position:absolute; top:60px; right:20px; width:300px;" alt="Relation semantique enonces et monde reel" />

## Syntaxe

- Definit les enonces possibles dans le langage

## Semantique

- Definit le sens des enonces
- Relation entre les enonces et le monde reel

## Proposition logique

- Un enonce qui peut etre vrai ou faux

## Connecteurs logiques

- NON (negation)
- ET (conjonction)
- OU (disjonction)
- IMPLIQUE (implication)
- EQUIVAUT (equivalence)

---
layout: section
---

# Logique Propositionnelle
---
layout: default
---

# Enonces propositionnels

## Proposition

- Un enonce atomique qui peut etre vrai ou faux
- Ex: "Il pleut", "Le Wumpus est en [1,2]"

## Enonces complexes

- Combinaisons de propositions avec des connecteurs logiques
- Ex: "Il pleut ET il fait froid"

## Connecteurs logiques

- P ET Q : vrai si P et Q sont vrais
- P OU Q : vrai si au moins un est vrai
- NON P : vrai si P est faux
- P => Q : vrai si P est faux ou Q est vrai
- P <=> Q : vrai si P et Q ont meme valeur de verite

---
layout: default
---

# Syntaxe de la logique propositionnelle

<img src="./images/img_008.png" style="position:absolute; top:50px; right:10px; width:380px;" alt="Grammaire BNF logique propositionnelle" />

## Symboles

- Propositions: P, Q, R, ...
- Connecteurs: ET, OU, NON, =>, <=>
- Parentheses: (, )

## Formules bien formees (FBF)

1. Toute proposition est une FBF
2. Si P est une FBF, NON P est une FBF
3. Si P et Q sont des FBF, (P ET Q), (P OU Q), (P => Q), (P <=> Q) sont des FBF
4. Rien d'autre n'est une FBF

---
layout: default
---

# Semantique de la logique propositionnelle

## Interpretation

- Attribution d'une valeur de verite (Vrai/Faux) a chaque proposition

## Tables de verite

| P | Q | P ET Q | P OU Q | P => Q | P <=> Q |
|---|---|--------|--------|--------|---------|
| V | V | V      | V      | V      | V       |
| V | F | F      | V      | F      | F       |
| F | V | F      | V      | V      | F       |
| F | F | F      | F      | V      | V       |

## Satisfaction

- Une interpretation satisfait une formule si la formule est vraie sous cette interpretation
- Une formule est **satisfaisable** s'il existe au moins une interpretation qui la satisfait
- Une formule est **valide** (tautologie) si elle est satisfaite par toute interpretation

---
layout: default
---

# Infrence propositionnelle

## Entailment (consequence semantique)

- KB |= alpha : "KB entraine alpha"
- Alpha est vrai dans tous les modeles ou KB est vrai

## Theoreme de deduction

- KB |= alpha si et seulement si (KB => alpha) est valide

## Demonstration d'infrence

1. **Methodes de verification de modele**
   - Enumerer toutes les interpretations
   - Verifier que alpha est vrai quand KB est vrai

2. **Methodes de preuve**
   - Deriver alpha a partir de KB en utilisant des regles d'infrence

---
layout: default
---

# Regles d'infrence

<img src="./images/img_011.png" style="position:absolute; top:50px; right:10px; width:380px;" alt="Equivalences logiques" />

## Modus Ponens

- Si P est vrai et P => Q est vrai, alors Q est vrai
- P, P => Q |- Q

## Et-introduction

- Si P est vrai et Q est vrai, alors P ET Q est vrai
- P, Q |- P ET Q

## Et-elimination

- Si P ET Q est vrai, alors P est vrai et Q est vrai
- P ET Q |- P
- P ET Q |- Q

## Ou-introduction

- Si P est vrai, alors P OU Q est vrai
- P |- P OU Q

## Double negation

- NON(NON P) equivaut a P

---
layout: default
---

# Resolution

<img src="./images/img_012.png" style="position:absolute; top:50px; right:20px; width:200px;" alt="Arbre de resolution" />

## Clause

- Disjonction de litteraux: P1 OU P2 OU ... OU Pn OU NON Q1 OU ... OU NON Qm

## Clause de Horn

- Au plus un litteral positif: P OU NON Q1 OU ... OU NON Qm
- Equivaut a: (Q1 ET Q2 ET ... ET Qm) => P

## Regle de resolution

- Deux clauses avec des litteraux complementaires peuvent etre combinees
- (P OU Q), (NON P OU R) |- (Q OU R)

## Resolution unitaire

- Si une clause a un seul litteral: P, (NON P OU Q) |- Q

## Algorithme de resolution

1. Convertir KB en CNF (forme normale conjonctive)
2. Ajouter NON alpha a l'ensemble de clauses
3. Appliquer la resolution jusqu'a obtenir la clause vide (contradiction) ou ne plus pouvoir progresser

---
layout: default
---

# Forward et Backward Chaining

<img src="./images/img_013.png" style="position:absolute; top:60px; right:20px; width:180px;" alt="Clauses Forward Chaining" />

## Forward Chaining (chaine avant)

- Partir des faits connus
- Appliquer les regles pour deduire de nouveaux faits
- Continuer jusqu'a ce que le but soit atteint ou plus aucun fait nouveau

## Backward Chaining (chaine arriere)

- Partir du but
- Chercher les regles dont le but est la conclusion
- Recursivement chercher a prouver les premisses

## Comparaison

- Forward: mieux quand les faits sont peu nombreux et les buts nombreux
- Backward: mieux quand les buts sont peu nombreux et les faits nombreux

---
layout: default
---

# Proprietes des systemes d'infrence

## Correctitude (Soundness)

- Si KB |- alpha, alors KB |= alpha
- Tout ce qui est prouvable est vrai

## Completude

- Si KB |= alpha, alors KB |- alpha
- Tout ce qui est vrai peut etre prouve

## Decidabilite

- Existe-t-il un algorithme qui peut toujours determiner si KB |= alpha ?

## Complexite

- Logique propositionnelle: NP-complet pour la satisfiabilite
- Mais les clauses de Horn: temps lineaire

---
layout: section
---

# Logique du Premier Ordre
---
layout: default
---

# Limites de la logique propositionnelle

## Exemple: Monde du Wumpus

- "Il y a une odeur dans toutes les cases adjacentes au Wumpus"
- En logique propositionnelle:
  - O1,1 <=> (W1,1 OU W1,2 OU W2,1)
  - O1,2 <=> (W1,1 OU W1,2 OU W1,3 OU W2,2)
  - ...
- Besoin d'une regle par case!

## Logique du premier ordre

- Permet d'exprimer des generalites
- "Pour tout x, s'il y a du Wumpus en x, alors il y a une odeur dans toutes les cases adjacentes"
- Une seule formule pour toutes les cases

---
layout: default
---

# Syntaxe de la logique du premier ordre

<img src="./images/img_019.png" style="position:absolute; top:50px; right:10px; width:320px;" alt="Grammaire BNF FOL" />

## Termes

- Constantes: Jean, Marie, A, B, ...
- Variables: x, y, z, ...
- Fonctions: Pere(Jean), Position(Agent), ...

## Formules atomiques

- Predicats: P(x), Q(x, y), R(Jean, Marie)
- Egalite: x = y

## Formules complexes

- Combinaisons avec connecteurs propositionnels
- Quantificateurs:
  - Quel que soit (pour tout): ∀x P(x)
  - Il existe: ∃x P(x)

---
layout: default
---

# Semantique de la logique du premier ordre

## Interpretation

- Domaine: ensemble non vide d'objets
- Interpretation des constantes: elements du domaine
- Interpretation des fonctions: applications du domaine vers le domaine
- Interpretation des predicats: relations sur le domaine

## Satisfaction

- Une interpretation satisfait ∀x P(x) si P(x) est vrai pour tout element du domaine
- Une interpretation satisfait ∃x P(x) si P(x) est vrai pour au moins un element

## Modele

- Une interpretation qui satisfait une formule

---
layout: default
---

# Quantificateurs

## Quantificateur universel (∀)

- ∀x P(x) : "Pour tout x, P(x)"
- Ex: ∀x (Humain(x) => Mortel(x))

## Quantificateur existentiel (∃)

- ∃x P(x) : "Il existe un x tel que P(x)"
- Ex: ∃x (Humain(x) ET Philosophe(x))

## Equivalences

- ∀x P(x) equivaut a NON ∃x NON P(x)
- ∃x P(x) equivaut a NON ∀x NON P(x)

## Portee des quantificateurs

- Les variables liees par un quantificateur sont locales a la formule

---
layout: default
---

# Axiomes et ingenierie des donnees

## Axiomes de base

- Enonces consideres comme vrais sans demonstration
- Fondements de la base de connaissances

## Ingenierie des donnees

- Processus de formalisation des connaissances
- Identifier les objets, relations et proprietes pertinentes
- Formuler les axiomes corrects

## Exemple: Monde du Wumpus

- "Toutes les cases adjacentes au Wumpus sentent mauvais"
  - ∀x (Wumpus(x) => ∀y (Adjacent(y,x) => Odeur(y)))
- "Il n'y a pas de Wumpus dans la case de depart"
  - NON Wumpus([1,1])

---
layout: default
---

# Infrence en logique du premier ordre

## Propositionalisation

- Convertir en logique propositionnelle
- Remplacer les variables par toutes les constantes possibles
- Probleme: explosion combinatoire

## Unification

- Trouver une substitution qui rend deux termes identiques
- Ex: unifier P(x, Jean) et P(Marie, y) -> &#123;x/Marie, y/Jean&#125;

## Modus Ponens generalise

- Si P et (P => Q) sont vrais, alors Q est vrai
- Avec substitution appropriee

---
layout: default
---

# Unification

## Definition

- Substitution: ensemble de paires variable/terme
- Unificateur: substitution qui rend deux atomes identiques
- Unificateur le plus general (MGU): unificateur minimal

## Exemples

- Unifier P(x, Jean) et P(Marie, y)
  - MGU: &#123;x/Marie, y/Jean&#125;
  - Resultat: P(Marie, Jean)

- Unifier P(x, x) et P(Jean, Marie)
  - Echec: impossible d'unifier

## Algorithme d'unification

- Comparer recursivement les termes
- Remplacer les variables par des termes plus specifiques

---
layout: default
---

# Forward chaining en FOL

## Principe

1. Partir des faits connus
2. Pour chaque regle, trouver les substitutions qui satisfont les premisses
3. Ajouter les conclusions correspondantes
4. Repeter jusqu'a ce que le but soit atteint

## Exemple

- Faits: Humain(Socrate)
- Regle: ∀x (Humain(x) => Mortel(x))
- Substitution: &#123;x/Socrate&#125;
- Nouveau fait: Mortel(Socrate)

---
layout: default
---

# Backward chaining en FOL

<img src="./images/img_022.png" style="position:absolute; top:50px; right:10px; width:400px;" alt="Arbre backward chaining Criminal(West)" />

## Principe

1. Partir du but
2. Chercher les regles dont le but est la conclusion
3. Pour chaque regle, chercher les substitutions et prouver les premisses
4. Recursivement

## Exemple

- But: Mortel(Socrate)
- Regle: ∀x (Humain(x) => Mortel(x))
- Substitution: &#123;x/Socrate&#125;
- Nouveau but: Humain(Socrate)
- Fait connu: Humain(Socrate) -> Succes!

---
layout: default
---

# Resolution en FOL

## Conversion en forme normale conjonctive (CNF)

1. Eliminer => et <=>
2. Deplacer NON vers l'interieur
3. Standardiser les variables
4. Skolemiser (eliminer ∃)
5. Eliminer ∀
6. Distribuer ET sur OU

## Resolution generalisee

- Unifier des clauses complementaires
- (P(x) OU Q(x)), (NON P(Jean) OU R(y))
- Substitution: &#123;x/Jean&#125;
- Resolvante: (Q(Jean) OU R(y))

---
layout: default
---

# Applications

## Agents fondes sur la connaissance

- Representation explicite des connaissances
- Raisonnement automatique

## Systemes experts

- Base de connaissances + Moteur d'infrence
- Domaines: medecine, diagnostic, configuration

## Web semantique

- RDF, OWL: representation des connaissances sur le web
- SPARQL: interrogation des connaissances

## Planification automatique

- Representation des actions et des etats
- Raisonnement sur les plans

---
layout: section
---

# Planification
---
layout: default
---

# Planification

## Probleme de planification

- Trouver une sequence d'actions qui permettent d'atteindre un objectif a partir d'un etat initial
- Donner la liste des instances d'operations, qui, executees a partir de l'etat initial, vont modifier l'etat du monde a un etat qui satisfait le but

## Planification et resolution de probleme

- Souvent memes types de problemes
- Planification plus expressive
- Exploration de l'espace de plan en plus de l'espace d'etats
- Sous-objectifs independants reduisent la complexite

---
layout: default
---

# Definition d'un domaine de planification

<img src="./images/img_025.png" style="position:absolute; top:50px; right:10px; width:380px;" alt="Domaine PDDL Air Cargo" />

## Planning Domain Definition Language (PDDL)

- Similaire a la logique du premier ordre (FOL)
- Etat: At(Truck1, Melbourne) ET At(Truck2, Sydney)
- Chaque etat est appele un fluent
- Semantique de DB (ce qui n'est pas explicite est presume faux)
- Les enonces sont fermes, sans fonction

## Schema d'action

- Noms: ex: Go
- Liste de variables (here, there)
- Preconditions: At(here), Path(here, there)
- Effets: At(there), NON At(here)

## Application d'une action

- Les preconditions doivent etre satisfaites
- S' = (S - Del(a)) ∪ Add(a)
- Add(a): Litteraux positifs dans les effets
- Del(a): Litteraux negatifs dans les effets

---
layout: default
---

# Exemple PDDL: Transport logistique

```
Init(At(C1, SFO) ET At(C2, JFK) ET At(P1, SFO) ET At(P2, JFK)
    ET Cargo(C1) ET Cargo(C2) ET Plane(P1) ET Plane(P2)
    ET Airport(JFK) ET Airport(SFO))
Goal(At(C1, JFK) ET At(C2, SFO))

Action(Load(c, p, a))
  PRECOND: At(c, a) ET At(p, a) ET Cargo(c) ET Plane(p) ET Airport(a)
  EFFECT: NON At(c, a) ET In(c, p))

Action(Unload(c, p, a))
  PRECOND: In(c, p) ET At(p, a) ET Cargo(c) ET Plane(p) ET Airport(a)
  EFFECT: At(c, a) ET NON In(c, p))

Action(Fly(p, from, to),
  PRECOND: At(p, from) ET Plane(p) ET Airport(from) ET Airport(to)
  EFFECT: NON At(p, from) ET At(p, to))
```

---
layout: default
---

# Approches de planification

## Exploration de l'espace des etats et des plans

- STRIPS, chainage avant, etc.

## Planification a ordre partiel

- Construction des sous-plans
- Ordre reconcilie par application de contraintes

## Decomposition hierarchique

- Distinction des buts a decomposer
- Primitives atomiques pour les atteindre

## Planification par contraintes

- Utilisation des CSP

## Calcul situationnel

- Logique du premier ordre
- Utilisation de theoremes pour prouver les bonnes sequences

---
layout: default
---

# Exploration de l'espace des etats

<img src="./images/img_027.png" style="position:absolute; top:50px; right:10px; width:380px;" alt="Graphe espace etats planification" />

## Complexite de la planification classique

- PlanSAT: Y-a-t-il un plan? -> PSPACE > NP
- PlanSAT "borne": Y-a-t-il un plan de longueur <k? -> PSPACE
- Pour de nombreux domaines (e.g. logistique):
  - PlanSAT borne NP-Complet (optimalite difficile)
  - PlanSAT dans P (suboptimalite plus facile)

## Algorithmes

- Planificateur progressif (avant)
- Planificateur regressif (arriere)
  - Recherche des etats pertinents
- Explorations bidirectionnelles

---
layout: default
---

# Heuristiques pour la planification

## Probleme relache

- Ignorer les preconditions
- Ignorer les delete lists

## Abstraction

- Ignorer les fluents non pertinents

## Decomposition

- Diviser le probleme en sous-problemes independants

## Landmarks

- Faits qui doivent etre vrais a un moment donne

---
layout: default
---

# Graphes de planification

<img src="./images/img_031.png" style="position:absolute; top:50px; right:10px; width:500px;" alt="Graphe de planification Have/Eat/Bake Cake" />

## Structure de donnees

- Generee a partir d'un probleme de planification
- Divisee en niveaux:
  - Niveaux d'etats Si: Les fluents peuvent etre vrais au niveau i
  - Niveaux d'actions Ai: Les actions applicables a l'etape i

## Construction

- Ai = actions avec preconditions satisfaites par Si
- Si = fluents rendus vrais par effets des actions Ai-1
- + NO-OP passe les fluents vrais de Si a Si+1

## Liens

- Fluents -> Preconditions
- Effets -> Fluents
- Mutexes: actions incompatibles, fluents incompatibles

---
layout: default
---

# Algorithme GraphPlan

<img src="./images/img_030.png" style="position:absolute; top:50px; right:10px; width:400px;" alt="Algorithme GraphPlan" />

```
fonction GRAPHPLAN(probleme) retourne solution ou echec
  graph <- INITIAL-PLANNING-GRAPH(probleme)
  goals <- CONJUNCTS(probleme.Goal)
  nogoods <- table de hachage vide
  pour t = 0 a l'infini faire
    si goals tous non-mutex dans St de graph alors
      solution <- EXTRACT-SOLUTION(graph, goals, NUMLEVELS(graph), nogoods)
      si solution != echec alors retourner solution
    si graph et nogoods ont tous les deux level-off alors retourner echec
    graph <- EXPAND-GRAPH(graph, probleme)
```

---
layout: default
---

# Planification par contraintes

## SatPlan

- La planification comme une satisfiabilite Booleenne
- Propositionalisation des actions, des buts
- Ajout des axiomes d'etats successeurs
- Ajout des axiomes de preconditions
- Utilisation de l'algorithme WalkSat

## Formulation comme CSP

- Plan a "k" actions
- Variables: Action unique pour chaque etape, Fluent
- Contraintes: decrivent les effets + etat initial et but

---
layout: default
---

# Calcul situationnel

<img src="./images/img_024.png" style="position:absolute; top:50px; right:10px; width:350px;" alt="Sequence etats Wumpus S0-S3" />

<style scoped>
.slidev-layout { font-size: 0.85em; }
h2 { margin-top: 0.3em !important; margin-bottom: 0.1em !important; }
</style>

<div style="max-width:58%;">

## Limitations de PDDL

- Pas de quantificateur (deplacer "tout le chargement" etc.)
- Logique propositionnelle: le temps est lie aux fluents

## Alternative: utiliser la FOL avec branches de situations

- Raisonner a propos du changement a travers ces branches
- Utilisation de theoremes pour prouver qu'un plan fonctionne

## Etat initial

- Phrase logique a propos de la situation S0
- At(Home, S0) ET NON Have(Milk, S0) ET NON Have(Bananas, S0) ET NON Have(Drill, S0)

## Etat but

- (∃s) At(Home, s) ET Have(Milk, s) ET Have(Bananas, s) ET Have(Drill, s)

</div>

---
layout: default
---

# Axiomes du calcul situationnel

## Preconditions -> Axiomes de Possibilite

## Operateurs: descriptions de comment le monde change

- ∀(a,s) Have(Milk, Result(a,s)) <=> ((a=Buy(Milk) ET At(Grocery,s)) OU (Have(Milk, s) ET a≠Drop(Milk)))

## Axiomes d'action unique

## Situations resultant du plan d'actions p

- Result(p, S0)
- (∀s) Result([], s) = s
- (∀a,p,s) Result([a|p], s) = Result(p, Result(a, s))

## Solution

- At(Home, Result'(p, S0)) ET Have(Milk, Result'(p, S0)) ET Have(Bananas, Result'(p, S0)) ET Have(Drill, Result'(p, S0))

---
layout: default
---

# Planification a ordre partiel

<style scoped>
.slidev-layout { font-size: 0.88em; }
h2 { margin-top: 0.3em !important; margin-bottom: 0.1em !important; }
</style>

## Planificateur non lineaire

- Construit une liste d'etapes avec des contraintes temporelles

## Raffinement du plan partiellement ordonne

- Par ajout d'etapes
- Par ajout de contraintes

## Engagement minimal

- On ne garde que le necessaire
- Pas d'engagement a l'avance

## Plan non lineaire

- Etapes &#123;S1, S2, S3...&#125;
  - Description d'operateurs + pre et post-conditions
- Liens causaux &#123;... (Si, C, Sj) ...&#125;
- Contraintes d'ordre &#123;... Si &lt; Sj ...&#125;

## Plan complet

- Toutes les etapes sont incluses
- Chaine de causalite
- Validite temporelle

---
layout: default
---

# Decomposition hierarchique

## Conditions reelles plus difficiles

- Gestion des ressources, du temps, des abstractions
- Planning -> scheduling
- Actions conditionnelles, incertaines, dynamiques

## Planifier =/= Programmer un evenement

- Allouer des ressources, respecter des contraintes
- Planifier -> raisonnement
- Programmer -> CSPs

## Decomposition hierarchique

- Operateurs abstraits -> vers les Buts intermediaires
- Primitives de bas niveau: Executable
- Operateurs non primitifs: Buts, actions abstraites

---
layout: default
---

# Resume planification

## Approches

- Recherche dans l'espace d'etats (STRIPS, chainage avant, etc.)
- Dans l'espace des plans (planification partiellement ordonnees, HTN, etc.)
- Base sur les contraintes (GraphPlan, SATPlan etc.)
- Calcul situationnel
- Planification hierarchique

## Strategies d'exploration

- Planification progressive
- Regression des buts
- Planification retrograde
- Moindre engagement
- Planification non lineaire

---
layout: section
---

# Representation de Connaissances
---
layout: default
---

# Ontologies

<img src="./images/img_020.png" style="position:absolute; top:50px; right:10px; width:280px; max-height:400px;" alt="Ontologie - graphe de connaissances" />

<style scoped>
.slidev-layout { font-size: 0.88em; }
h2 { margin-top: 0.3em !important; margin-bottom: 0.1em !important; }
</style>

<div style="max-width:65%;">

## Objectifs

- Representation des connaissances a grande echelle
- Lier les domaines specialises du savoir
- Couvrir la diversite des connaissances

## Besoins de categorisation

- Reification: predicats et constantes
  - BallonDeBasket(b) -> Membre(b, BallonsDeBasket)
- Hierarchie: taxonomies (sous-classes), heritage
- Partitions: Disjoints + decomposition exhaustive
- Composition: PartieDe(x,y)
- Mesure: Unites (Centimetre, Pouces)

## Objets mentaux

- Connaissances sur les croyances
- Logique modale: mondes possibles

</div>

---
layout: default
---

# Web semantique

<img src="./images/img_042.jpg" style="position:absolute; top:60px; right:20px; width:200px;" alt="dotNetRDF" />

## Resource Description Framework (RDF)

- Communaute KR: AAAI, W3C, Berners-Lee
- RDF: triplets (faits), classes / sous-classes
- Triplet (sujet, predicat, objet)

## RDFS et OWL

- Classes definies
- Contraintes

## SPARQL

- Requetes sur "Triple Stores"

## Linked Data

- SOA (Service Oriented Architecture)
- Donnees connectees sur le web

---
layout: default
---

# Systemes de raisonnement

## Reseaux semantiques

- Proche des formalismes UML/Merise
- Infrence par navigation, heritage, reification
- Valeurs par defaut et heritage

## Logiques de descriptions

- Notations elaborees pour FOL
- Subsomption (sous-ensemble), classification, coherence
- And, All, AtLeast, AtMost, Fills, SameAs, OneOf...

## Logiques non monotones

- Monde clos: proposition pas mentionnee fausse par defaut
- Nouveaux faits peuvent invalider etat de croyance
- Circonscription, logique par defaut

---
layout: default
---

# Systemes a maintenance de verite

<style scoped>
.slidev-layout { font-size: 0.88em; }
h2 { margin-top: 0.3em !important; margin-bottom: 0.1em !important; }
</style>

## Revision des croyances

- Statut par defaut -> revision des faits infenes faux
- Tell(KB, not P) -> Retract(KB, P)
- Probleme: si P->Q doit-on annuler Q?

## Fondes sur la justification (JTMS)

- Les enonces sont associes a leurs justifications
- Suppression soft: in/out

## Fondes sur les hypotheses (ATMS)

- Envisager simultanement plusieurs hypotheses
- Chaque enonce comporte les hypotheses qui peuvent le rendre vrai

## Generateurs d'explications

- Hypotheses = explications raisonnables
- Explications minimales (Ockham)

---
layout: default
---

# Resume representation des connaissances

## Ontologies

- Meta-modeles de donnees

## Web semantique

- Representation de faits
- Pile semantique du W3C

## Systemes de raisonnement

- Maintenance de la verite

## Smart Contracts

- Signatures, chiffrement et Preuves
- Divulgation partielle et contractualisee

---
layout: section
---

# TP
---
layout: default
---

# Projets de groupe

- Moteur de recherche augmente par le raisonnement et le langage naturel
  - Grammaire et semantique des contenus et des requetes. Lucene.Net, OpenNLP, SharpRDF, FOL

- Conception de bots de services sur reseaux sociaux
  - Chat Bots, AIML, Reddit et agents de service, NLP, RDF, APIs

- Conception d'un modele d'infrence pour l'analyse de sentiment
  - Modele probabiliste, Infer.Net, demarche experimentale, Reddit

- Creation d'une plateforme semantique LDP a partir d'un index structure
  - Linked Data. Lucene.Net, SharpRDF

- Resolution de Captchas par deep learning
  - TensorFlow, CNTK, Encog

---
layout: end
---

# Merci

Jean-Sylvain Boige
JSBOIGE@myia.ORG
