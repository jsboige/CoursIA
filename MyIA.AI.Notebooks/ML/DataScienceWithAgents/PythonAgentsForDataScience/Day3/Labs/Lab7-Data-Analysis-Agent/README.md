# Lab 7 : L'Agent d'Analyse de Donnees

**Objectif :** Construire un agent d'IA capable de comprendre et de repondre a des questions en langage naturel sur un DataFrame Pandas.

Ce laboratoire **fusionne les deux mondes** explores precedemment : la **Data Science** (Pandas, Labs 1 / 4 / 5) et l'**IA Agentique** (LangChain, Labs 2 / 3 / 6). On obtient un agent specialise capable d'executer du code Pandas a la volee pour repondre a une question metier formulee en francais.

## Objectifs d'apprentissage

A la fin de ce lab, vous saurez :

1. Creer un agent specialise avec `create_pandas_dataframe_agent` de LangChain
2. Exposer un DataFrame en entree d'un agent et controler son perimetre
3. Comprendre les risques d'execution de code genere (verbose / sandbox)
4. Comparer la productivite "agent analyste" vs analyse manuelle

## Prerequis

- [Lab 4 (Data Wrangling)](../Lab4-DataWrangling/README.md) : Pandas manipulation
- [Lab 6 (First Agent)](../Lab6-First-Agent/README.md) : pattern LLM + Tools + Executor
- Cle API LLM configuree (`.env` racine)

## Notebook

- [Lab7-Data-Analysis-Agent.ipynb](Lab7-Data-Analysis-Agent.ipynb) - notebook etudiant
- `Lab7-Data-Analysis-Agent_output.ipynb` - version executee de reference

## Suite et transition

Le Lab 7 termine la sous-serie **Python Agents for Data Science**. La suite logique est la sous-serie [AgenticDataScience](../../../../AgenticDataScience/README.md) (Day 4-7) qui passe a **Google ADK** (Agent Development Kit) pour des agents multi-tools, multi-step plus realistes.

## Navigation

[<- Index Python Agents](../../../../README.md) | [Lab 6 <<](../Lab6-First-Agent/README.md) | [>> AgenticDataScience](../../../../AgenticDataScience/README.md)
