# Recipe-Maker - Générateur de recettes

[← CaseStudies](../README.md) | [↑ GenAI](../../README.md)

Générateur automatisé de recettes culinaires utilisant des agents IA.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 1 |
| Difficulté | Intermédiaire |
| Durée | ~1-2h |
| Thème | Intelligence culinaire |

## Notebook

| # | Notebook | Description |
|---|----------|-------------|
| 1 | [receipe_maker](receipe_maker.ipynb) | Générateur automatisé de recettes culinaires |

## Technologies

- **Python** : orchestration du notebook, génération du PDF (`reportlab`), relecture du PDF (`pypdf`)
- **Semantic Kernel** : Orchestration d'agents
- **OpenAI** : Modèles de langage

## Prérequis

```bash
pip install openai semantic-kernel python-dotenv pydantic reportlab pypdf
```

---

*Projet étudiant - Janvier 2026*
