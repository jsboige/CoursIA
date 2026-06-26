# Partie 4 — Neuro-Symbolique

[← Partie 3 — Avancée](../03-Advanced/README.md) | [↑ Planification](../README.md)

La dernière partie explore la **frontière entre IA symbolique et apprentissage profond**. Les parties précédentes ont construit des solveurs que l'on *conçoit* ; celle-ci regarde ce qui change quand on *apprend* à planifier. Trois angles : les LLM comme générateurs de plans (notebook 10), une interface unifiée qui rend le modèle PDDL portable entre tous les moteurs (notebook 11), et surtout *Learning to Plan* (notebook 12) — le point où l'apprentissage rencontre la planification, clôture naturelle de la série vers les foundation models.

## Position dans la série

| Étape | Question |
|-------|----------|
| ← `03-Advanced` | Comment résoudre par contraintes, temps ou hiérarchie ? |
| **Partie 4 — Neuro-Symbolique** | **Comment *apprendre* à planifier plutôt que le coder à la main ?** |
| Fin de la série → | Ponts vers RL, vérification formelle, théorie des jeux |

Le fil conducteur : le geste de planifier — un état, un but, une séquence d'actions — reste identique ; ce qui change, c'est l'agent qui cherche. Du LLM prompté (notebook 10) au réseau qui apprend une heuristique (notebook 12), la structure symbolique persiste sous l'apprentissage. C'est elle, rappelle le fil rouge de la série, que l'on emporte au-delà.

## Notebooks

| # | Notebook | Durée | Contenu |
|---|----------|-------|---------|
| 10 | [Planners-10-LLM-Planning](Planners-10-LLM-Planning.ipynb) | 50 min | Large Language Models pour la planification : prompting, génération de plans, plan repair ; limites et avantages |
| 11 | [Planners-11-Unified-Planning](Planners-11-Unified-Planning.ipynb) | 40 min | Interface `unified-planning` : un modèle PDDL, plusieurs solveurs, comparaison croisée des performances |
| 12 | [Planners-12-LOOP](Planners-12-LOOP.ipynb) | 45 min | Learning to Plan (framework LOOP) : state encoder, policy/value networks, encodage PDDL en tenseurs, 85,8 % de coverage IPC |

## Prérequis

- **Parties 1 à 3** : toute la mécanique de la planification symbolique (notebooks 1-9)
- **Machine learning** (notebooks 10, 12) : réseaux de neurones, fonction de perte, rétropropagation
- **API LLM** (notebook 10) : clé OpenAI/Anthropic, prompting
- **PyTorch** (notebook 12) : tenseurs, modules, boucle d'entraînement

## À l'issue de cette partie

Vous saurez :

1. **Utiliser** un LLM pour générer et réparer des plans, et en mesurer les limites
2. **Abstraire** un problème de planification via unified-planning pour le porter d'un solveur à l'autre
3. **Entraîner** un modèle à planifier (LOOP) : encoder un état PDDL, apprendre une politique ou une heuristique
4. **Situer** la planification neuro-symbolique dans la trajectoire des foundation models

## Pour aller plus loin (fin de série)

La série s'achève ; les ponts sortent de Planners :

- **Vers l'apprentissage par renforcement** — un plan est une politique déterministe ; le RL en calcule une stochastique sous incertitude. Pont naturel vers les politiques apprises.
- **Vers la certification formelle** — un plan correct n'est pas un plan sûr : la vérification Lean s'applique aux séquences d'actions critiques.
- **Vers la théorie des jeux** — la planification mono-agent rencontre la recherche adversariale (minimax) en multi-agent.
- **Cartographie complète** → [Planification (README parent) — Ponts avec les autres séries](../README.md)
