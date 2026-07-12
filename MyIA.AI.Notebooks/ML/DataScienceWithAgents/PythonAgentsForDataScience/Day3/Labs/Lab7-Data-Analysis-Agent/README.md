# Lab 7 : L'Agent d'Analyse de Données

**Objectif :** Construire un agent d'IA capable de comprendre et de répondre à des questions en langage naturel sur un DataFrame Pandas.

Ce laboratoire **fusionne les deux mondes** explorés précédemment : la **Data Science** (Pandas, Labs 1 / 4 / 5) et l'**IA Agentique** (LangChain, Labs 2 / 3 / 6). On obtient un agent spécialisé capable d'exécuter du code Pandas à la volée pour répondre à une question métier formulée en français.

## Objectifs d'apprentissage

À la fin de ce lab, vous saurez :

1. Créer un agent spécialisé avec `create_pandas_dataframe_agent` de LangChain
2. Exposer un DataFrame en entrée d'un agent et contrôler son périmètre
3. Comprendre les risques d'exécution de code généré (verbose / sandbox)
4. Comparer la productivité "agent analyste" vs analyse manuelle

## Prérequis

- [Lab 4 (Data Wrangling)](../Lab4-DataWrangling/README.md) : Pandas manipulation
- [Lab 6 (First Agent)](../Lab6-First-Agent/README.md) : pattern LLM + Tools + Executor
- Clé API LLM configurée (`.env` racine)

## Notebook

- [Lab7-Data-Analysis-Agent.ipynb](Lab7-Data-Analysis-Agent.ipynb) - notebook étudiant
- `Lab7-Data-Analysis-Agent_output.ipynb` - version exécutée de référence

## Suite et transition

Le Lab 7 termine la sous-série **Python Agents for Data Science**. La suite logique est la sous-série [AgenticDataScience](../../../../AgenticDataScience/README.md) (Day 4-7) qui passe à **Google ADK** (Agent Development Kit) pour des agents multi-tools, multi-step plus réalistes.

## Navigation

[<- Index Python Agents](../../../../README.md) | [Lab 6 <<](../Lab6-First-Agent/README.md) | [>> AgenticDataScience](../../../../AgenticDataScience/README.md)
