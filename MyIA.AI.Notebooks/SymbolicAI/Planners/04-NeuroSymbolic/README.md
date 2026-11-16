# Partie 4 — Neuro-Symbolique

[← Partie 3 — Avancée](../03-Advanced/README.md) | [↑ Planification](../README.md)

## Ouverture — ce que cette partie enseigne (Découverte)

Les trois parties précédentes construisent des solveurs que l'on *conçoit* : un modèle, un algorithme de recherche, une heuristique écrite à la main. Cette dernière partie regarde ce qui change quand on *apprend* à planifier. Le geste reste identique — un état, un but, une séquence d'actions — mais l'agent qui cherche n'est plus un programme dont on a fixé les règles : c'est un modèle de langage, ou un réseau entraîné sur des plans résolus.

Trois numéros et un palier, dans cet ordre : le LLM employé directement comme planificateur, avec ses variantes de raisonnement et ses échecs mesurés ; une interface qui rend un modèle PDDL portable d'un moteur à l'autre, seul moyen honnête de comparer ; puis *Learning to Plan*, où la politique et l'heuristique sortent de l'entraînement plutôt que d'une règle. Le palier 10b prend le contrepied : le LLM n'y résout rien, il **réduit** l'espace que le solveur déterministe explorera — et la mesure montre ce que cette division du travail achète.

Le fil de la série tient : la structure symbolique persiste sous l'apprentissage. Un plan reste une suite d'actions dont la validité se vérifie ; ce qui change est l'origine de la recherche. C'est cette structure, et non le moteur qui la produit, que l'on emporte au-delà de Planners.

**À qui elle s'adresse.** Un lecteur qui a suivi les parties 1 à 3 — modélisation PDDL, recherche heuristique, contraintes et temps — et qui veut voir ce que l'apprentissage apporte, ou n'apporte pas, à ce cadre. Les prérequis exacts sont en [Installation](#installation).

## Comment lire ce README (Découverte)

Un README de série se lit à plusieurs vitesses : le parcours principal par les numéros nus, l'approfondissement par les lettres, la recherche en cours par la section « Pour aller plus loin ». Le principe est exposé à la racine du dépôt, dans [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture).

- **Vous suivez le cœur de la partie** : la table du parcours principal, de haut en bas (les numéros 10, 11, 12).
- **Vous creusez un palier** : le palier lettré 10b, accroché au numéro 10, en [Approfondissements](#approfondissements-découverte).
- **Vous cherchez la recherche en cours** : allez directement à [« Pour aller plus loin »](#pour-aller-plus-loin--niveau-recherche).

## Parcours principal (Découverte)

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 10 | [Planners-10-LLM-Planning](Planners-10-LLM-Planning-Python.ipynb) | Le LLM comme planificateur direct : état, actions et prompt, puis les variantes de raisonnement — Chain-of-Thought, et Tree-of-Thought qui retient ici un plan sur les 3 branches explorées. Traduction langage naturel → PDDL, validation du domaine généré en 4 étapes, plan repair, et le LLM employé comme **heuristique** plutôt que comme solveur | Découverte | [Palier 10b](#approfondissements-découverte) : le LLM comme réducteur d'espace |
| 11 | [Planners-11-Unified-Planning](Planners-11-Unified-Planning-Python.ipynb) | L'interface `unified-planning` : un problème décrit une fois (types, fluents, actions), résolu par plusieurs moteurs. Sur le même problème, `pyperplan` rend un plan de 6 actions en 0,008 s là où `fast-downward` rend le même plan en 0,294 s. Actions duratives, fluents numériques et coûts (version optimisante face à la version satisfaisante), export et import PDDL | Découverte | [Partie 3 — Avancée](../03-Advanced/README.md) : les paradigmes que ces moteurs implémentent |
| 12 | [Planners-12-LOOP](Planners-12-LOOP-Python.ipynb) | *Learning to Plan* (framework LOOP) : encoder un état PDDL, réseaux de politique et de valeur, boucle d'entraînement — la perte passe de 14,02 à 2,12 sur 50 époques — puis un banc jouet mesuré à l'exécution, où l'imitation apprise couvre 60,0 % de 15 instances inédites contre 33,3 % pour une politique aléatoire et 100 % pour le BFS exact. Encodage par graphe (GNN) et fonctions de noyau (KRCL) en complément | Découverte | [Partie 2 — Classique](../02-Classical/README.md) : les heuristiques que l'on cherche ici à apprendre |

Cette partie ne porte pas de jumeau C# : les quatre carnets sont en Python, et deux d'entre eux (10, 10b) interrogent un service LLM externe plutôt qu'une bibliothèque locale.

**Ce que vous saurez faire à l'issue de cette partie :**

1. **Conduire** un LLM sur une tâche de planification — prompt direct, chaîne de raisonnement, arbre de pensée — et lire ses échecs plutôt que son éloquence ;
2. **Traduire** un énoncé en domaine et problème PDDL, puis **valider** le résultat avant de s'y fier ;
3. **Abstraire** un problème avec `unified-planning` pour porter le même modèle d'un solveur à l'autre et comparer les moteurs à modèle constant ;
4. **Entraîner** une politique ou une heuristique (LOOP) et mesurer sa coverage contre un planificateur classique, sur des instances inédites ;
5. **Décider** où placer le LLM — solveur, heuristique, ou simple réducteur d'espace — en fonction de ce que la mesure montre.

## Approfondissements (Découverte)

**10b — Le LLM comme réducteur d'espace de recherche** ([Planners-10b-LLM-Space-Reducer](Planners-10b-LLM-Space-Reducer-Python.ipynb)). Le contrepied du numéro 10, et la vue la plus utile de la partie pour qui doit choisir une architecture. Sur un mini-DSL de 8 primitives typées agissant sur des grilles, avec 115 instances par emplacement, l'espace des programmes de profondeur ≤ 4 vaut `115 + 115² + 115³ + 115⁴`, soit 176 434 840 programmes. Trois bras sont mesurés sur les mêmes trois tâches : la recherche exhaustive bornée, qui trouve les deux premières (400 puis 2 071 nœuds) et **dépasse le budget** sur la troisième à 15 001 nœuds et 0,284 s ; le LLM-direct ; et le LLM-réducteur, qui ne résout rien mais désigne les primitives à essayer, ramenant l'espace à 8 372, 132 et 1 884 programmes — des réductions de ×21 074, ×1 336 628 et ×93 649 — avant que le même moteur déterministe n'y trouve les trois solutions. Le débit mesuré (49 914 nœuds/seconde) permet d'extrapoler l'espace complet à 3 535 s ; c'est ce chiffre, et non une intuition, qui situe l'intérêt du réducteur.

## Sous-séries (Découverte)

Cette partie n'en contient pas. Elle est elle-même une **sous-série** de [Planification](../README.md), dont le README porte la vue d'ensemble de l'arc et l'escalier entre les parties.

## Installation

- **Parties 1 à 3 maîtrisées** : modélisation PDDL, planification classique, contraintes, temps et hiérarchie (notebooks 1-9).
- **Notebooks 10 et 10b** : une clé d'API LLM (OpenAI, Anthropic ou OpenRouter) dans l'environnement, et le goût du prompt. Les cellules d'appel échouent proprement sans clé ; la lecture du raisonnement reste possible, l'exécution des appels non.
- **Notebook 11** : `unified-planning` avec au moins deux moteurs (`pyperplan`, `fast-downward`). C'est l'installation la plus lourde de la série après le HTN.
- **Notebook 12** : PyTorch — tenseurs, modules, boucle d'entraînement — et les notions de réseau de neurones (perte, rétropropagation) sans lesquelles la section 4 se lit sans se comprendre.

## Pour aller plus loin — niveau Recherche

**Formalisations Lean.** Cette partie ne porte pas de formalisation propre : ce qu'elle ajoute — un modèle appris, une sortie de LLM — n'est pas de nature à être prouvé dans un assistant. Le lake `planning_lean` reste la formalisation de référence de la série et vit en [Partie 2 — Classique](../02-Classical/README.md), avec les paliers 5b et 5c ; son inventaire (modules, pins, mesure de `sorry`) est tenu dans [`LEAN_INVENTORY.md`](../LEAN_INVENTORY.md) et n'est pas recopié ici.

**Le fil de recherche.** Trois questions restent ouvertes et ce sont elles que la partie rend manipulables : à quelle condition un LLM est-il un planificateur plutôt qu'un générateur de texte plausible ; que mesure exactement une coverage apprise face à un solveur complet ; et où placer la frontière entre ce qu'on apprend et ce qu'on vérifie. La position défendue par le palier 10b — l'apprentissage réduit, le déterministe vérifie — est un point de départ argumenté, pas un résultat. Les statuts de maturité et les notes techniques de la série sont tenus dans le README parent.

## Ressources

- [Partie 3 — Avancée](../03-Advanced/README.md) : CP-SAT, PDDL temporel, HTN — les paradigmes que `unified-planning` unifie.
- [Partie 2 — Classique](../02-Classical/README.md) : Fast Downward, théorie des heuristiques, paliers 5b/5c.
- [Planification — README de la série](../README.md) : l'arc complet, l'inventaire Lean.
- [Choisir sa vitesse de lecture](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) : le principe des parcours à plusieurs vitesses, à la racine du dépôt.
