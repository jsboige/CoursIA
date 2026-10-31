# Partie 3 — Approches Avancées

[← Partie 2 — Classique](../02-Classical/README.md) | [↑ Planification](../README.md) | [Partie 4 — Neuro-Symbolique →](../04-NeuroSymbolic/README.md)

## Ouverture — ce que cette partie enseigne (Découverte)

La planification classique « épuise ses limites » dès que les problèmes deviennent trop grands pour l'exploration d'états. Cette partie présente **trois paradigmes complémentaires** qui contournent l'explosion combinatoire en changeant de point de vue : raisonner en *contraintes* (CP-SAT), raisonner en *temps continu* (PDDL 2.1 temporel), ou raisonner en *tâches hiérarchiques* (HTN). Aucun ne remplace Fast Downward ; chacun ouvre une classe de problèmes que la planification classique sait à peine aborder — ordonnancement sous contraintes de capacité, actions duratives et parallèles, décomposition d'un but complexe en sous-buts réutilisables.

Le fil conducteur : chaque notebook introduit un changement de représentation — les états deviennent des variables soumises à des contraintes (CP-SAT), des intervalles temporels (Temporal), ou des tâches à décomposer (HTN). C'est le geste par excellence de la planification moderne : changer de point de vue pour rendre un problème tractable. Le notebook 13 referme la boucle en mesurant, plans optimaux à l'appui, ce que vaut une bonne heuristique.

**À qui elle s'adresse.** Un lecteur qui a suivi les parties 1 et 2 — modélisation PDDL, recherche heuristique — et qui se demande que faire quand l'exploration d'états explose. Les prérequis exacts sont en [Installation](#installation).

## Comment lire ce README (Découverte)

Un README de série se lit à plusieurs vitesses : le parcours principal par les numéros nus, l'approfondissement par les lettres, la recherche en cours par la section « Pour aller plus loin ». Le principe est exposé à la racine du dépôt, dans [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture).

- **Vous suivez le cœur de la partie** : la table du parcours principal, de haut en bas (les numéros 7, 8, 9, puis 13).
- **Vous creusez un palier** : cette partie ne porte pas de palier lettré ; les deux paliers de la série (5b, 5c) vivent en [Partie 2 — Classique](../02-Classical/README.md#approfondissements-découverte).
- **Vous cherchez la recherche en cours** : allez directement à [« Pour aller plus loin »](#pour-aller-plus-loin--niveau-recherche).

## Parcours principal (Découverte)

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 7 | [Planners-7-OR-Tools](Planners-7-OR-Tools.ipynb) — jumeau [C#](Planners-7-OR-Tools-Csharp.ipynb) | Programmation par contraintes avec CP-SAT (Google OR-Tools) : all-different, cumulative, table ; scheduling ; optimisation multi-objectif. Le jumeau C# refait un solveur CP à propagation et backtracking *from-scratch* sur Job-Shop, sans OR-Tools, puis résout le même exemple job-shop via Google.OrTools CP-SAT (paquet NuGet `Google.OrTools`) (See #4956) | Découverte | — |
| 8 | [Planners-8-Temporal](Planners-8-Temporal.ipynb) — jumeau [C#](Planners-8-Temporal-Csharp.ipynb) | PDDL 2.1 : durées d'actions, parallélisme, contraintes temporelles simples et denses, ordonnancement de tâches. Le jumeau C# construit *from-scratch* l'algèbre d'Allen, un réseau temporel simple (STN) et un RCPSP-lite, puis résout le RCPSP via Google.OrTools CP-SAT (paquet NuGet `Google.OrTools`) (See #4956) | Découverte | — |
| 9 | [Planners-9-HTN](Planners-9-HTN.ipynb) — jumeau [C#](Planners-9-HTN-Csharp.ipynb) | Planification hiérarchique (Hierarchical Task Networks) : tâches primitives/abstraites, méthodes de décomposition, HDDL, solveur inspiré de SHOP2. Le jumeau C# réécrit un solveur HTN inspiré de SHOP2 *from-scratch* (décomposition de tâches en .NET 9), puis attaque le même problème via unified_planning + aries par pont .NET vers CPython (paquet NuGet `pythonnet` 3.0.5, paquets Python `unified-planning` et `up-aries`) (See #4956) | Découverte | [Partie 4 — Neuro-Symbolique](../04-NeuroSymbolic/README.md) |
| 13 | [Planners-13-Mesure-Qualite-Plans](Planners-13-Mesure-Qualite-Plans-Python.ipynb) | **Mesurer la qualité des plans** : 5 configurations Fast Downward sur une tour de 4 blocs — A* avec heuristiques blind, hmax, lmcut et fast-forward (les quatre trouvent le plan optimal de 6 actions, en évaluant de 22 à 121 états selon l'heuristique), plus une recherche greedy qui s'en écarte (10 actions, 20 états) ; recherche naïve BFS en Python en contrepoint | Découverte | [Partie 2 — Classique (théorie des heuristiques)](../02-Classical/README.md) |

Les jumeaux partagent la ligne de leur numéro : même arc, deux langages. Le C# se lit seul — sa première tranche (from-scratch, .NET 9) ne demande ni service ni Docker — et sa seconde tranche suppose l'environnement décrit en [Installation](#installation).

**Ce que vous saurez faire à l'issue de cette partie :**

1. **Modéliser** un problème de scheduling en contraintes CP-SAT et le résoudre avec OR-Tools ;
2. **Étendre** un domaine PDDL au temporel (PDDL 2.1) — actions duratives, parallélisme ;
3. **Décomposer** un but en réseaux de tâches hiérarchiques (HTN/HDDL, SHOP2) ;
4. **Choisir** le paradigme adapté à la structure du problème (états vs contraintes vs hiérarchie).

## Approfondissements (Découverte)

Cette partie ne porte pas de palier lettré : ses notebooks sont tous des numéros nus du parcours principal. Les deux paliers lettrés de la série — 5b (preuve formelle de l'admissibilité de la relaxation dans le lake `planning_lean`) et 5c (différentiel d'atteignabilité) — sont accrochés au numéro 5 et vivent en [Partie 2 — Classique](../02-Classical/README.md#approfondissements-découverte).

## Sous-séries (Découverte)

Cette partie n'en contient pas. Elle est elle-même une **sous-série** de [Planification](../README.md), dont le README porte la vue d'ensemble de l'arc et l'escalier entre les parties.

## Installation

- **Parties 1 et 2** maîtrisées : modélisation PDDL, planification classique (notebooks 1-6).
- **Notebook 7 (OR-Tools)** : goût pour la programmation par contraintes (variables, domaines, contraintes).
- **Notebooks 8-9** : connaissance de PDDL (domaines, problèmes), étendue à HDDL pour le HTN.
- **Jumeaux C# (7-9)** : .NET 9 Interactive. Les tranches 2 tirent des paquets NuGet (`Google.OrTools` pour 7 et 8, `pythonnet` 3.0.5 pour 9), donc un accès réseau à NuGet. Le jumeau 9 exige en plus un Python avec `unified-planning` et `up-aries` (chargeur `Config/PythonNetLoader.cs`). Aucun jumeau 7-9 n'utilise Docker.

Si un paquet manque, la lecture théorique reste accessible : seules les exécutions des cellules concernées sont sautées. Pour les jumeaux C#, la tranche 1 (from-scratch) s'exécute toujours ; seule la tranche 2 suppose son paquet.

## Pour aller plus loin — niveau Recherche

**Formalisations Lean.** Cette partie ne porte pas de formalisation propre ; le lake `planning_lean` (admissibilité de la relaxation sans-delete) reste la formalisation de référence de la série — il est consommé par les paliers 5b et 5c en [Partie 2](../02-Classical/README.md), et son inventaire (modules, pins, mesure de `sorry`) vit dans [`LEAN_INVENTORY.md`](../LEAN_INVENTORY.md), qui n'est pas recopié ici.

**Le fil de recherche.** La limite que cette partie révèle — trois paradigmes pour contourner l'explosion combinatoire, mais toujours des moteurs et des heuristiques conçus à la main — est précisément ce que la partie 4 retourne en changeant *qui cherche* : d'un algorithme conçu à la main vers une heuristique ou une politique *apprise*. Les statuts de maturité et les notes techniques de la série sont tenus dans le README parent.

## Ressources

- [Partie 2 — Classique](../02-Classical/README.md) : Fast Downward, théorie des heuristiques, paliers 5b/5c.
- [Planification — README de la série](../README.md) : l'arc complet, l'inventaire Lean.
- [Partie 4 — Neuro-Symbolique](../04-NeuroSymbolic/README.md) : LLM planning, unified-planning, Learning to Plan (LOOP).
- [Choisir sa vitesse de lecture](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) : le principe des parcours à plusieurs vitesses, à la racine du dépôt.
