# Partie 2 — Planification Classique

[← Partie 1 — Fondations](../01-Foundation/README.md) | [↑ Planification](../README.md) | [Partie 3 — Avancée →](../03-Advanced/README.md)

## Ouverture — ce que cette partie enseigne (Découverte)

Cette partie est le **cœur technique** de la série : on y résout les problèmes modélisés en PDDL. Le cycle « décrire un problème (partie 1) → trouver un plan » se ferme ici avec un planificateur industriel, **Fast Downward**, et la théorie des heuristiques qui le rend efficace. On y voit qu'un plan n'est pas une prédiction mais une *séquence d'actions justifiée par une structure de coût*, et qu'une bonne heuristique fait la différence entre un solveur qui termine et un solveur qui explose.

Le fil conducteur : le notebook 3 (partie 1) a montré que la recherche aveugle explose ; cette partie introduit les deux réponses classiques — un planificateur de référence (Fast Downward) et des heuristiques admissibles (A*, LM-cut) qui guident la recherche vers le but.

**À qui elle s'adresse.** Un lecteur qui a suivi la partie 1 — modélisation PDDL, espace d'états — et qui veut comprendre *comment* un planificateur industriel résout ces problèmes de façon (sous-)optimale. Les prérequis exacts sont en [Installation](#installation).

## Comment lire ce README (Découverte)

Un README de série se lit à plusieurs vitesses : le parcours principal par les numéros nus, l'approfondissement par les lettres, la recherche en cours par la section « Pour aller plus loin ». Le principe est exposé à la racine du dépôt, dans [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture).

- **Vous suivez le cœur de la partie** : la table du parcours principal, de haut en bas (les numéros 4, 5, 6).
- **Vous creusez un palier** : la section [Approfondissements](#approfondissements-découverte) porte les lettres 5b et 5c, qui accrochent au numéro 5 un cas formel en Lean et un protocole de mesure.
- **Vous cherchez la recherche en cours** : allez directement à [« Pour aller plus loin »](#pour-aller-plus-loin--niveau-recherche) et aux formalisations Lean.

## Parcours principal (Découverte)

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 4 | [Planners-4-Fast-Downward](Planners-4-Fast-Downward.ipynb) — jumeau [C#](Planners-4-Fast-Downward-Csharp.ipynb) | Architecture 3 étapes (translator PDDL→SAS+, preprocessor, search) ; A*, GBFS, EHC via Docker sur Blocks World et Logistics. Le jumeau C# refait un planificateur SAS+ *from-scratch* (prevail/pre/eff, h^max/h^FF par RPG, domaines Ferry + Logistics) puis branche Fast Downward via l'API Docker, port 8200 (See #4956) | Découverte | — |
| 5 | [Planners-5-Heuristics](Planners-5-Heuristics.ipynb) — jumeau [C#](Planners-5-Heuristics-Csharp.ipynb) | Classification admissible/non-admissible ($h^{add}$, $h^{max}$, $h^{FF}$, LM-cut) ; comparaison expérimentale du nombre de nœuds expansés. Le jumeau C# dérive h-max/h-add/h-FF/landmarks *from-scratch* (démo de non-admissibilité de h^add) puis valide h* = 4 sur Blocks World par Fast Downward, port 8200, avec la comparaison LM-cut (See #4956) | Découverte | [Paliers 5b / 5c](#approfondissements-découverte) |
| 6 | [Planners-6-Domains](Planners-6-Domains.ipynb) — jumeau [C#](Planners-6-Domains-Csharp.ipynb) | Domaines IPC standards (Blocks World, Logistics, Gripper, Ferry, Hanoï) de complexité croissante. Le jumeau C# modélise Atom/Action/State et un BFS forward + anti-cycle *from-scratch* sur Block World, Hanoï et Gripper, puis branche Fast Downward 24.06.1 via l'API Docker, port 8200 (See #4956) | Découverte | [Partie 3 — Avancée](../03-Advanced/README.md) |

Les jumeaux partagent la ligne de leur numéro : même arc, deux langages. Le C# se lit seul — sa première tranche (from-scratch, .NET 9) ne demande ni service ni Python — et sa seconde tranche suppose l'environnement décrit en [Installation](#installation).

**Ce que vous saurez faire à l'issue de cette partie :**

1. **Configurer** un planificateur optimal (Fast Downward via Docker + unified-planning) ;
2. **Choisir** l'heuristique adéquate (LM-cut pour l'optimalité, h-FF pour la vitesse) ;
3. **Modéliser** n'importe quel domaine IPC classique en PDDL ;
4. **Distinguer** heuristiques admissibles (garantie d'optimalité) et non-admissibles (rapidité) ;
5. **Mesurer** ce qu'une nouvelle primitive rend possible — différentiel d'atteignabilité vs approfondissement de recherche (palier [5c](#approfondissements-découverte)).

## Approfondissements (Découverte)

### Autour de 05

Cette partie porte **deux paliers lettrés**, tous deux accrochés au numéro 5. Chaque lettre ajoute une dimension au notebook 5 et suppose un prérequis en plus du parcours principal :

| Lettre | Notebook | Ce qu'elle ajoute | Prérequis en plus |
|---|---|---|---|
| 5b | [Planners-5b-Lean-Relaxation](Planners-5b-Lean-Relaxation.ipynb) | Companion **natif** kernel Lean 4 : preuve formelle 0-sorry de $h^{+} \leq h^{*}$ dans le lake `planning_lean` | kernel Lean 4 (via WSL) |
| 5c | [Planners-5c-Differentiel-Atteignabilite](Planners-5c-Differentiel-Atteignabilite.ipynb) | Différentiel d'atteignabilité (strate 7) : protocole 4 pas — inatteignabilité prouvée, contrôle d'effort, primitive nommée et payante, delta mesuré ; consomme les théorèmes du lake `planning_lean` | Python stdlib pur (sans Docker) |

Les jumeaux C# ne sont pas des approfondissements : ce sont les mêmes numéros dans un autre langage, ils figurent donc sur la ligne de leur numéro dans la table du parcours principal. Le détail de leurs deux tranches (from-scratch, puis moteur SOTA) est décrit dans la colonne « Ce qu'on y apprend ».

## Sous-séries (Découverte)

Cette partie n'en contient pas. Elle est elle-même une **sous-série** de [Planification](../README.md), dont le README porte la vue d'ensemble de l'arc et l'escalier entre les parties.

## Installation

- **Partie 1** maîtrisée : modélisation PDDL, espace d'états (notebooks 1-3).
- **Docker** : les notebooks 4-6 appellent le serveur HTTP Fast Downward (`jsboige/coursia-fast-downward`, port 8200) — les notebooks 5b et 5c n'en dépendent pas (5b : kernel Lean via WSL ; 5c : stdlib pur). Pour les jumeaux C# (4-6), la tranche 1 est from-scratch (.NET 9) et n'en dépend pas ; leur tranche 2 appelle le même serveur sur le port 8200, sans garde-fou : Docker est donc requis pour exécuter le jumeau en entier.
- **Algorithmique** : A*, recherche heuristique dans les graphes.
- **.NET 9 (jumeaux C# uniquement)** : les notebooks `-Csharp` s'exécutent sous .NET Interactive ; leur première tranche ne demande ni service ni Python.

Si Docker n'est pas disponible, les notebooks théoriques (explication de l'architecture, classification des heuristiques) restent accessibles ; seules les exécutions de planification en ligne seront sautées. Pour les jumeaux C#, rien n'est sauté : la cellule de tranche 2 échoue sans le service, et la tranche 1 reste exécutable.

## Pour aller plus loin — niveau Recherche

**Formalisations Lean.** La série porte un lake, `planning_lean`, qui formalise l'admissibilité de la relaxation sans-delete. Les paliers 5b et 5c **le consomment** : 5b y dépose la preuve 0-sorry de $h^{+} \leq h^{*}$, et 5c y consomme les théorèmes pour mesurer un différentiel d'atteignabilité. Modules, pins et mesure de `sorry` vivent dans l'inventaire de la série, [`LEAN_INVENTORY.md`](../LEAN_INVENTORY.md), qui n'est pas recopié ici.

**Le fil de recherche.** La limite que cette partie révèle — l'explosion combinatoire sur les grands domaines — est précisément ce que la partie 3 contourne en changeant de paradigme (contraintes, temporel, hiérarchie). Les statuts de maturité et les notes techniques de la série sont tenus dans le README parent.

## Ressources

- [Partie 1 — Fondations](../01-Foundation/README.md) : le vocabulaire formel, PDDL, espace d'états.
- [Planification — README de la série](../README.md) : l'arc complet, l'inventaire Lean.
- [Partie 3 — Approches avancées](../03-Advanced/README.md) : CP-SAT (OR-Tools), planification temporelle, HTN.
- [Choisir sa vitesse de lecture](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) : le principe des parcours à plusieurs vitesses, à la racine du dépôt.
