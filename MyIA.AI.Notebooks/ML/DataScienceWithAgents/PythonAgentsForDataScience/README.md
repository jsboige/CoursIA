# PythonAgentsForDataScience — Track LangChain (Labs 1-7)

[← DataScienceWithAgents (parent)](../README.md) | [AgenticDataScience (Google ADK) →](../AgenticDataScience/README.md)

Le track **LangChain** du workshop : 7 labs répartis sur 3 jours qui mènent de la prise en main des outils data science (Journée 1) jusqu'à la construction d'un agent d'analyse de données autonome (Journée 3). C'est le compagnon opérationnel des fondations [`01-PythonForDataScience`](../01-PythonForDataScience/README.md) et [`02-ML-Cours`](../02-ML-Cours/README.md) : on y apprend à orchestrer un LLM pour qu'il accomplisse des tâches data science concrètes — analyser un appel d'offres, pré-qualifier des CVs, nettoyer des données sales, interroger un DataFrame en langage naturel.

## Pourquoi cette série

Le fil conducteur du workshop est un **changement de paradigme** : passer de *l'écriture* du code data science à *l'orchestration* d'agents LLM qui le produisent. Ce track introduit ce saut de façon progressive et encadrée. Chaque lab pose une question pragmatique — un agent accélère-t-il réellement cette tâche ? comment le garder sous contrôle ? — et y répond avec LangChain en gardant l'humain dans la boucle pour la validation. L'enjeu n'est pas de déléguer aveuglément, mais de comprendre *quand* un agent est légitime et *comment* le contraindre (outils, prompt, exécuteur).

## Structure (3 jours, 7 labs)

### Journée 1 — Fondations data science

| Lab | Sujet | Concept-phare |
|-----|-------|---------------|
| [Lab 1 — Bases Data Science](Day1/Labs/Lab1-PythonForDataScience.ipynb) | Pandas + Matplotlib + régression linéaire sur ventes synthétiques | le socle manipulé par tous les labs suivants |

### Journée 2 — Agents pour l'analyse documentaire

| Lab | Sujet | Concept-phare |
|-----|-------|---------------|
| [Lab 2 — RFP Analysis](Day2/Labs/Lab2-RFP-Analysis/Lab2-RFP-Analysis.ipynb) | d'un appel d'offres à un PoC en 1 heure | extraction structurée d'un texte libre par LLM |
| [Lab 3 — CV Screening](Day2/Labs/Lab3-CV-Screening/Lab3-CV-Screening.ipynb) | pré-qualifier des candidats avec l'IA | analyse, notation et résumé de CVs vs offre |

### Journée 3 — Data wrangling & agents

| Lab | Sujet | Concept-phare |
|-----|-------|---------------|
| [Lab 4 — Data Wrangling](Day3/Labs/Lab4-DataWrangling/Lab4-DataWrangling.ipynb) | nettoyer un jeu de données « sale » réaliste | Pandas au service de la robustesse |
| [Lab 5 — Viz & ML](Day3/Labs/Lab5-Viz-ML/Lab5-Viz-ML.ipynb) | exploration visuelle puis classification scikit-learn | visualisation guidant le modèle |
| [Lab 6 — First Agent](Day3/Labs/Lab6-First-Agent/Lab6-First-Agent.ipynb) | construire son premier agent LangChain | les 4 composants : LLM, Outils, Prompt, Exécuteur |
| [Lab 7 — Data Analysis Agent](Day3/Labs/Lab7-Data-Analysis-Agent/Lab7-Data-Analysis-Agent.ipynb) | agent répondant en langage naturel sur un DataFrame | l'agent comme interface d'analyse |

Chaque lab est accompagné de son propre [`README.md`](Day1/Labs/README.md) (objectifs, données fournies, exercices).

## Objectifs d'apprentissage

À l'issue du track, l'apprenant sait :

1. Charger, nettoyer, visualiser et modéliser des données avec Pandas / Matplotlib / scikit-learn (Labs 1, 4, 5).
2. Orchestrer un LLM avec LangChain pour extraire une information structurée d'un texte libre (Labs 2, 3).
3. Assembler les **4 composants** d'un agent (LLM, Outils, Prompt, Exécuteur) et l'armer d'outils data science (Labs 6, 7).
4. Distinguer les tâches où un agent apporte un gain réel de celles qu'il vaut mieux coder à la main.

## Prérequis

- Fondations [`01-PythonForDataScience`](../01-PythonForDataScience/README.md) (NumPy/Pandas) et idéalement [`02-ML-Cours`](../02-ML-Cours/README.md) (workflow sklearn).
- **LangChain** + clé API OpenAI (les labs 2, 3, 6, 7 appellent un LLM).

## Suite logique

Une fois le track mono-agent LangChain maîtrisé, la formation monte en puissance vers les **systèmes multi-agents** : [`AgenticDataScience`](../AgenticDataScience/README.md) (Google ADK, boucles planner-coder, DS-STAR / MLE-STAR, compétitions Kaggle).
