# Partie 2 — Planification Classique

[← Partie 1 — Fondations](../01-Foundation/README.md) | [↑ Planification](../README.md) | [Partie 3 — Avancée →](../03-Advanced/README.md)

Cette partie est le **cœur technique** de la série : on y résout les problèmes modélisés en PDDL. Le cycle « décrire un problème (partie 1) → trouver un plan » se ferme ici avec un planificateur industriel, **Fast Downward**, et la théorie des heuristiques qui le rend efficace. On y voit qu'un plan n'est pas une prédiction mais une *séquence d'actions justifiée par une structure de coût*, et qu'une bonne heuristique fait la différence entre un solveur qui termine et un solveur qui explose.

## Position dans la série

| Étape | Question |
|-------|----------|
| ← `01-Foundation` | Comment *modéliser* un problème en PDDL ? |
| **Partie 2 — Classique** | **Comment *résoudre* ce problème de façon (sous-)optimale ?** |
| `03-Advanced` → | Que faire quand l'espace d'états est trop grand pour Fast Downward ? |

Le fil conducteur : le notebook 3 (partie 1) a montré que la recherche aveugle explose ; cette partie introduit les deux réponses classiques — un planificateur de référence (Fast Downward) et des heuristiques admissibles (A*, LM-cut) qui guident la recherche vers le but.

## Notebooks

| # | Notebook | Durée | Contenu |
|---|----------|-------|---------|
| 4 | [Planners-4-Fast-Downward](Planners-4-Fast-Downward.ipynb) | 45 min | Architecture 3 étapes (translator PDDL→SAS+, preprocessor, search) ; A*, GBFS, EHC via Docker sur Blocks World et Logistics |
| 5 | [Planners-5-Heuristics](Planners-5-Heuristics.ipynb) | 40 min | Classification admissible/non-admissible ($h^{add}$, $h^{max}$, $h^{FF}$, LM-cut) ; comparaison expérimentale du nombre de nœuds expansés |
| 6 | [Planners-6-Domains](Planners-6-Domains.ipynb) | 50 min | Domaines IPC standards (Blocks World, Logistics, Gripper, Ferry, Hanoï) de complexité croissante |

## Prérequis

- **Partie 1** maîtrisée : modélisation PDDL, espace d'états (notebooks 1-3)
- **Docker** : les notebooks 4-6 appellent le serveur HTTP Fast Downward (`jsboige/coursia-fast-downward`, port 8200)
- **Algorithmique** : A*, recherche heuristique dans les graphes

Si Docker n'est pas disponible, les notebooks théoriques (explication de l'architecture, classification des heuristiques) restent accessibles ; seules les exécutions de planification en ligne seront sautées.

## À l'issue de cette partie

Vous saurez :

1. **Configurer** un planificateur optimal (Fast Downward via Docker + unified-planning)
2. **Choisir** l'heuristique adéquate (LM-cut pour l'optimalité, h-FF pour la vitesse)
3. **Modéliser** n'importe quel domaine IPC classique en PDDL
4. **Distinguer** heuristiques admissibles (garantie d'optimalité) et non-admissibles (rapidité)

## Pour continuer

- **Aller au-delà de l'explosion d'états** → [Partie 3 — Approches Avancées](../03-Advanced/README.md) : CP-SAT (OR-Tools), planification temporelle, HTN
- **Vue d'ensemble** → [Planification (README parent)](../README.md)

La limite que cette partie révèle — l'explosion combinatoire sur les grands domaines — est précisément ce que la partie 3 contourne en changeant de paradigme (contraintes, temporel, hiérarchie).
