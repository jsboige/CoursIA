# Barbie-Schreck - Duel verbal multi-agents

[← CaseStudies](../README.md) | [↑ GenAI](../../README.md)

Duel verbal multi-agents Semantic Kernel entre Barbie et l'Âne de Shrek, avec illustrations DALL-E des répliques de l'Âne. Un style linguistique (rime, Shakespeare, chanson) est tiré au sort et imposé via les instructions système des deux agents.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 1 |
| Difficulté | Intermédiaire |
| Durée | ~1-2h |
| Thème | Orchestration multi-agents + génération d'images |

## Notebook

| # | Notebook | Description |
|---|----------|-------------|
| 1 | [barbie-schreck](barbie-schreck.ipynb) | Duel verbal Barbie vs Âne de Shrek (Semantic Kernel, DALL-E) |

## Technologies

- **Semantic Kernel** : orchestration multi-agents (deux `ChatCompletionAgent` sur kernels séparés)
- **OpenAI DALL-E** : génération des illustrations de l'Âne à chaque réplique
- **Python** : orchestration du notebook

## Prérequis

```bash
pip install semantic-kernel openai jupyter
```

---

*Adapté d'une production étudiante EPF (Carole & Cléo), refactor [#890](https://github.com/jsboige/CoursIA/pull/890).*
