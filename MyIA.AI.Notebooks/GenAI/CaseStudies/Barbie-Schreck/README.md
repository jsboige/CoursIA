# Barbie-Schreck - Duel verbal multi-agents

[← CaseStudies](../README.md) | [↑ GenAI](../../README.md)

Duel verbal multi-agents Semantic Kernel entre Barbie et l'Âne de Shrek, avec illustrations générées en local (ComfyUI, Qwen-Image-Edit 2.1) des répliques de l'Âne. Un style linguistique (rime, Shakespeare, chanson) est tiré au sort et imposé via les instructions système des deux agents.

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
| 1 | [barbie-schreck](barbie-schreck.ipynb) | Duel verbal Barbie vs Âne de Shrek (Semantic Kernel, ComfyUI) |

## Technologies

- **Semantic Kernel** : orchestration multi-agents (deux `ChatCompletionAgent` sur kernels séparés)
- **ComfyUI (Qwen-Image-Edit 2.1)** : génération en local des illustrations de l'Âne à chaque réplique, via le client partagé `shared/helpers/comfyui_client.py`
- **Python** : orchestration du notebook

## Prérequis

```bash
pip install semantic-kernel python-dotenv ipython jupyter
```

---

*Adapté d'une production étudiante EPF (Carole & Cléo), refactor [#890](https://github.com/jsboige/CoursIA/pull/890).*
