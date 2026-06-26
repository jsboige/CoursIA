# Partie 3 — Approches Avancées

[← Partie 2 — Classique](../02-Classical/README.md) | [↑ Planification](../README.md) | [Partie 4 — Neuro-Symbolique →](../04-NeuroSymbolic/README.md)

La planification classique « épuise ses limites » dès que les problèmes deviennent trop grands pour l'exploration d'états. Cette partie présente **trois paradigmes complémentaires** qui contournent l'explosion combinatoire en changeant de point de vue : raisonner en *contraintes* (CP-SAT), raisonner en *temps continu* (PDDL 2.1 temporel), ou raisonner en *tâches hiérarchiques* (HTN). Aucun ne remplace Fast Downward ; chacun ouvre une classe de problèmes que la planification classique sait à peine aborder — ordonnancement sous contraintes de capacité, actions duratives et parallèles, décomposition d'un but complexe en sous-buts réutilisables.

## Position dans la série

| Étape | Question |
|-------|----------|
| ← `02-Classical` | Comment résoudre optimalement en explorant les états ? |
| **Partie 3 — Avancée** | **Que faire quand l'exploration d'états explose ? Trois alternatives.** |
| `04-NeuroSymbolic` → | Comment *apprendre* des heuristiques plutôt que les concevoir ? |

Le fil conducteur : chaque notebook introduit un changement de représentation — les états deviennent des variables soumises à des contraintes (CP-SAT), des intervalles temporels (Temporal), ou des tâches à décomposer (HTN). C'est le geste par excellence de la planification moderne : changer de point de vue pour rendre un problème tractable.

## Notebooks

| # | Notebook | Durée | Contenu |
|---|----------|-------|---------|
| 7 | [Planners-7-OR-Tools](Planners-7-OR-Tools.ipynb) | 45 min | Programmation par contraintes avec CP-SAT (Google OR-Tools) : all-different, cumulative, table ; scheduling ; optimisation multi-objectif |
| 8 | [Planners-8-Temporal](Planners-8-Temporal.ipynb) | 40 min | PDDL 2.1 : durées d'actions, parallélisme, contraintes temporelles simples et denses, ordonnancement de tâches |
| 9 | [Planners-9-HTN](Planners-9-HTN.ipynb) | 45 min | Planification hiérarchique (Hierarchical Task Networks) : tâches primitives/abstraites, méthodes de décomposition, HDDL, solveur inspiré de SHOP2 |

## Prérequis

- **Parties 1 et 2** : modélisation PDDL et planification classique (notebooks 1-6)
- **Notebook 7 (OR-Tools)** : goût pour la programmation par contraintes (variables, domaines, contraintes)
- **Notebooks 8-9** : connaissance de PDDL (domaines, problèmes), étendue à HDDL pour le HTN

## À l'issue de cette partie

Vous saurez :

1. **Modéliser** un problème de scheduling en contraintes CP-SAT et le résoudre avec OR-Tools
2. **Étendre** un domaine PDDL au temporel (PDDL 2.1) — actions duratives, parallélisme
3. **Décomposer** un but en réseaux de tâches hiérarchiques (HTN/HDDL, SHOP2)
4. **Choisir** le paradigme adapté à la structure du problème (états vs contraintes vs hiérarchie)

## Pour continuer

- **Croiser symbolique et apprentissage** → [Partie 4 — Neuro-Symbolique](../04-NeuroSymbolic/README.md) : LLM planning, unified-planning, Learning to Plan (LOOP)
- **Vue d'ensemble** → [Planification (README parent)](../README.md)

La partie 4 ne change plus de paradigme de résolution : elle change *qui cherche* — d'un algorithme conçu à la main vers une heuristique ou une politique *apprise*.
