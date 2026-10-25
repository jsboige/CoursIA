# Partie 1 — Fondations de la planification

[← Setup (00-Environment)](../00-Environment/Planners-0-Setup.ipynb) | [↑ Planification](../README.md) | [Partie 2 — Classique →](../02-Classical/README.md)

## Ouverture — ce que cette partie enseigne (Découverte)

Cette partie pose le **vocabulaire formel** de la planification automatique. Avant de résoudre un problème, il faut savoir le *décrire* : qu'est-ce qu'un état, une action, un but ? Comment représenter un monde assez précisément pour qu'une machine puisse y chercher une suite d'actions ? Les notebooks de cette partie construisent progressivement ce cadre conceptuel, du triptyque État-Action-But jusqu'à la constatation qui motive toute la suite de la série : la recherche aveugle dans l'espace d'états explose combinatoirement.

Le fil conducteur est le passage du problème *informel* (« je veux empiler ces blocs ») au modèle *formel* (un domaine PDDL, un état initial, un but). C'est cette traduction qui rend le problème soluble par un algorithme — et qui révèle, au dernier notebook, pourquoi un algorithme naïf ne suffit pas.

**À qui elle s'adresse.** Un lecteur qui sait programmer (Python, ou C# pour les jumeaux) et qui n'a jamais fait de planification. Les concepts sont introduits depuis zéro ; les prérequis exacts sont en [Installation](#installation).

## Comment lire ce README (Découverte)

Un README de série se lit à plusieurs vitesses : le parcours principal par les numéros nus, l'approfondissement par les lettres, la recherche en cours par les sous-séries et la section « Pour aller plus loin ». Le principe est exposé à la racine du dépôt, dans [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture).

- **Vous découvrez la planification** : suivez la table du parcours principal, de haut en bas.
- **Vous creusez un palier** : cette partie n'en porte aucun (voir [Approfondissements](#approfondissements-découverte)) ; les paliers commencent à la partie 2.
- **Vous cherchez la recherche en cours** : allez directement à [« Pour aller plus loin »](#pour-aller-plus-loin--niveau-recherche) et aux formalisations Lean.

## Parcours principal (Découverte)

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 1 | [Planners-1-Introduction](Planners-1-Introduction.ipynb) — jumeau [C#](Planners-1-Introduction-Csharp.ipynb) | Triptyque État-Action-But, hypothèses STRIPS (1971), taxonomie des paradigmes de planification. Le jumeau C# refait la même introduction *from-scratch* (BFS et états STRIPS en C# pur, sans dépendance), puis branche un moteur de production (Fast Downward via l'API Docker) | Découverte | [Le vocabulaire PDDL du 2](#parcours-principal-découverte) |
| 2 | [Planners-2-PDDL-Basics](Planners-2-PDDL-Basics.ipynb) — jumeau [C#](Planners-2-PDDL-Basics-Csharp.ipynb) | Syntaxe PDDL : domaines, problèmes, types, prédicats, actions, préconditions, effets. Le jumeau C# implémente un planificateur STRIPS complet (modèle typé, grounding, BFS forward) sur Logistics et Gripper, puis compare au même moteur industriel | Découverte | [L'explosion combinatoire du 3](#parcours-principal-découverte) |
| 3 | [Planners-3-State-Space](Planners-3-State-Space.ipynb) — jumeau [C#](Planners-3-State-Space-Csharp.ipynb) | Recherche dans l'espace d'états, explosion combinatoire en $O(2^n)$, nécessité des heuristiques. Le jumeau C# oppose BFS, DFS, Greedy et A* sur un terrain uniforme puis pondéré, avec QuikGraph puis Fast Downward en processus local | Découverte | [Partie 2 — Planification classique](../02-Classical/README.md) |

Les jumeaux partagent la ligne de leur numéro : même arc, deux langages. Le C# se lit seul — sa première tranche ne demande ni service ni Python — et sa seconde tranche suppose l'environnement décrit en [Installation](#installation).

**Ce que vous saurez faire à l'issue de cette partie :**

1. **Définir** ce qu'est la planification automatique et la distinguer de l'apprentissage supervisé ;
2. **Modéliser** un problème en PDDL — domaine, problème, actions avec préconditions et effets ;
3. **Représenter** l'espace d'états d'un problème et mesurer son explosion combinatoire ;
4. **Justifier** pourquoi la recherche aveugle ne suffit pas — et donc pourquoi les heuristiques de la partie 2 sont indispensables.

## Approfondissements (Découverte)

Cette partie **ne porte aucun approfondissement lettré** : la gradation de la série ouvre les paliers à partir de la partie 2, où chaque lettre ajoute un cas ou une variante à son numéro porteur. Rien n'est donc perdu ici — il n'y a rien à replier.

Les jumeaux C# ne sont pas des approfondissements : ce sont les mêmes numéros dans un autre langage, ils figurent donc sur la ligne de leur numéro dans la table du parcours principal. Le détail de leurs deux tranches (from-scratch, puis moteur SOTA) est décrit dans la colonne « Ce qu'on y apprend ».

## Sous-séries (Découverte)

Cette partie n'en contient pas. Elle est elle-même une **sous-série** de [Planification](../README.md), dont le README porte la vue d'ensemble de l'arc et l'escalier entre les parties.

## Installation

- **Python 3.9+** : programmation orientée objet, types, dataclasses. Le notebook de setup de la partie précédente ([`00-Environment`](../00-Environment/Planners-0-Setup.ipynb)) installe `unified-planning` et vérifie l'environnement ; il s'exécute une fois avant d'attaquer cette partie.
- **Algorithmique de base** : graphes, parcours en largeur et en profondeur.
- **Logique propositionnelle** : prédicats, connecteurs.
- **.NET 9 (jumeaux C# uniquement)** : les notebooks `-Csharp` s'exécutent sous .NET Interactive. Leur première tranche ne demande ni service ni Python.
- **Services et paquets de la seconde tranche des jumeaux** : le service Docker Fast Downward (port 8200) pour les jumeaux 1 et 2 — leur appel HTTP n'a pas de garde-fou, sans le service la cellule échoue ; pour le jumeau 3, le paquet NuGet `QuikGraph` 2.5.0 et le paquet Python `up_fast_downward`, absent de `requirements.txt`.

## Pour aller plus loin — niveau Recherche

**Formalisations Lean.** La série porte un lake, `planning_lean`, qui formalise l'admissibilité de la relaxation sans-delete : le coût du plan relaxé optimal ne dépasse jamais celui du plan réel optimal (théorèmes `relaxed_plan_admissible` et `relaxed_plan_witness`, sur les sémantiques réelle et relaxée). Les notebooks de cette partie **ne le consomment pas** : la formalisation éclaire ce que les notebooks 2 et 3 manipulent, elle ne s'exécute pas avec eux. Modules, pins et mesure de `sorry` vivent dans l'inventaire de la série, [`LEAN_INVENTORY.md`](../LEAN_INVENTORY.md), qui n'est pas recopié ici.

**Le fil de recherche.** Le dernier notebook conclut que la recherche dans l'espace d'états est nécessaire mais coûteuse ; la partie 2 montre comment un planificateur industriel et de bonnes heuristiques la rendent praticable. Les statuts de maturité et les notes techniques de la série sont tenus dans le README parent, avec les sous-séries.

## Ressources

- [Planification — README de la série](../README.md) : l'arc complet, les parties suivantes, l'inventaire Lean.
- [Setup de l'environnement](../00-Environment/Planners-0-Setup.ipynb) : installation et vérification.
- [Partie 2 — Planification classique](../02-Classical/README.md) : Fast Downward, heuristiques A*, h-FF, LM-cut, domaines IPC.
- [Choisir sa vitesse de lecture](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) : le principe des parcours à plusieurs vitesses, à la racine du dépôt.
