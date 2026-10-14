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

## Notebook

| # | Notebook | Description |
|---|----------|-------------|
| 1 | [fort-boyard-python](fort-boyard-python.ipynb) | Duel d'agents Père Fouras vs Laurent Jalabert (Semantic Kernel, AgentGroupChat) |

## Technologies

- **Semantic Kernel** : orchestration multi-agents (`AgentGroupChat`, `ChatCompletionAgent`)
- **OpenAI** : moteur de raisonnement des agents (énigmes + résolution)
- **Python** : orchestration du notebook

## Prérequis

```bash
pip install semantic-kernel openai jupyter
```

---

*Adapté d'une production étudiante EPF, refactor [#890](https://github.com/jsboige/CoursIA/pull/890).*
