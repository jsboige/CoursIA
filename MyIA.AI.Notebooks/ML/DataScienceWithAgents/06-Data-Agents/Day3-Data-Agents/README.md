# Journée 3 — Data wrangling & premiers agents autonomes

[← 06-Data-Agents (track)](../README.md) | [Journée 2 →](../Day2-Document-Agents/README.md) | [Track Google ADK (Jours 4-7) →](../../07-Agent-Orchestration/README.md)

La **Journée 3** clôt le track LangChain : les agents deviennent capables de **manipuler des données** par eux-mêmes — nettoyage de données sales, interrogation en langage naturel, puis assemblage des composants d'un agent en un analyseur de données autonome. C'est la transition vers le track Google ADK (Jours 4-7).

## Labs

| Lab | Sujet | Concept-phare |
|-----|-------|---------------|
| [Lab 4 — Data Wrangling](Labs/Lab4-DataWrangling/Lab4-DataWrangling.ipynb) | nettoyer un jeu de données « sale » réaliste | Pandas au service de la robustesse |
| [Lab 5 — Viz & ML](Labs/Lab5-Viz-ML/Lab5-Viz-ML.ipynb) | exploration visuelle puis classification scikit-learn | la visualisation guidant le modèle |
| [Lab 6 — First Agent](Labs/Lab6-First-Agent/Lab6-First-Agent.ipynb) | construire son premier agent LangChain | les 4 composants : LLM, Outils, Prompt, Exécuteur |
| [Lab 7 — Data Analysis Agent](Labs/Lab7-Data-Analysis-Agent/Lab7-Data-Analysis-Agent.ipynb) | agent répondant en langage naturel sur un DataFrame | l'agent comme interface d'analyse |

## Enchaînement

Les quatre labs de la journée se suivent, et chacun part de ce que le précédent a construit :

| Depuis | Vers | Ce qui est repris |
|---|---|---|
| Lab 4 — Data Wrangling | [Lab 5 — Viz & ML](Labs/Lab5-Viz-ML/Lab5-Viz-ML.ipynb) | le DataFrame nettoyé, que l'on explore visuellement puis sur lequel on entraîne un modèle |
| Lab 5 — Viz & ML | [Lab 6 — First Agent](Labs/Lab6-First-Agent/Lab6-First-Agent.ipynb) | l'analyse écrite à la main, que l'agent va orchestrer (les outils qui l'encapsulent) |
| Lab 6 — First Agent | [Lab 7 — Data Analysis Agent](Labs/Lab7-Data-Analysis-Agent/Lab7-Data-Analysis-Agent.ipynb) | les quatre composants de l'agent, appliqués à un DataFrame |

## Prérequis

- Avoir suivi la [Journée 2](../Day2-Document-Agents/README.md) (analyse documentaire agentique).
- **LangChain** + clé API OpenAI (les labs 6 et 7 appellent un LLM).

## Suite

Le workshop se poursuit avec le track **Google ADK** dans [`07-Agent-Orchestration`](../../07-Agent-Orchestration/README.md) : fondations ADK (Lab 8), agents DS-STAR / MLE-STAR, puis mise en production.
