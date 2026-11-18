# Fort-Boyard - Duel d'agents Père Fouras vs personnage célèbre

[← CaseStudies](../README.md) | [↑ GenAI](../../README.md)

Simulation multi-agents Semantic Kernel du jeu télévisé Fort Boyard : le Père Fouras pose des énigmes à un personnage célèbre (Laurent Jalabert par défaut), qui doit résoudre l'énigme en mobilisant un mot à deviner (par défaut `anticonstitutionnellement`).

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 1 |
| Difficulté | Intermédiaire |
| Durée | ~1-2h |
| Thème | Orchestration multi-agents + AgentGroupChat |

## Comment lire ce README

Ce cas d'usage se lit à plusieurs vitesses, et le choix vous appartient.

- **Vous voulez voir le duel tourner** : exécutez le carnet en lecture suivie — les blocs numérotés construisent chacun une brique (kernel, prompts, agents, groupe, partie) et chaque brique se relit dans sa « Lecture du résultat ».
- **Vous voulez adapter le duel aux vôtres** : l'exemple guidé sur la personnalisation des personnages se lit seul, en entrée directe par les prompts système.
- **Vous cherchez un point précis** (terminaison, sélection du locuteur, score, historique) : chaque section est autonome et s'ouvre sur le résultat qu'elle produit.

Le principe général — les vitesses de lecture et comment les reconnaître dans un README de série — est exposé dans [Choisir sa vitesse de lecture](../../../../README.md#choisir-sa-vitesse-de-lecture).

## Parcours principal

| # | Notebook | Ce qu'on y apprend |
|---|----------|--------------------|
| 1 | [fort-boyard-python](fort-boyard-python.ipynb) | Monter un duel d'agents complet avec Semantic Kernel — kernel, prompts système, `ChatCompletionAgent`, stratégies de sélection et de terminaison personnalisées dans un `AgentGroupChat`, jusqu'au système de score et à l'historique de partie |

## Approfondissements

Aucun carnet de cette série ne porte de palier lettré : le parcours principal ci-dessus couvre tout ce qui s'exécute dans le dossier. Les approfondissements vivent dans le carnet lui-même, à ouvrir au moment où ils servent :

- les **exemples guidés** — personnaliser les personnages du duel, une terminaison avec détection de renoncement, un système de score — donnent des variantes directement réutilisables ;
- les **exercices non résolus** — duel au protocole binaire, terminaison sur question répétée, mesure de la concision des indices — reprennent chacun une stratégie du duel ;
- le carnet jumeau [fort-boyard-python_en](fort-boyard-python_en.ipynb) en donne la version anglaise.

La série qui possède l'organe de l'orchestration d'agents est [SemanticKernel](../../SemanticKernel/README.md) : ce cas d'usage en est une application, pas le cours.

## Technologies

- **Semantic Kernel** : orchestration multi-agents (`AgentGroupChat`, `ChatCompletionAgent`)
- **OpenAI** : moteur de raisonnement des agents (énigmes + résolution)
- **Python** : orchestration du notebook

## Prérequis

```bash
pip install semantic-kernel python-dotenv jupyter
```

---

*Adapté d'une production étudiante EPF, refactor [#890](https://github.com/jsboige/CoursIA/pull/890).*
