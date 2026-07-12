# Lab 6 : Construire son premier Agent

**Objectif :** Comprendre et construire les 4 composants fondamentaux d'un agent d'IA avec LangChain : le **LLM**, les **Outils**, le **Prompt**, et l'**Exécuteur**.

Après avoir utilisé des chaînes LangChain "fil tendu" dans les Labs 2 et 3, ce laboratoire passe à l'**agent** au sens strict : un programme qui utilise un LLM pour **raisonner**, **choisir** des actions parmi un ensemble d'outils, et **itérer** jusqu'à atteindre un objectif. C'est le pivot conceptuel de la Journée 3.

## Objectifs d'apprentissage

À la fin de ce lab, vous saurez :

1. Assembler les 4 piliers d'un agent LangChain / LangGraph (LLM, Tools, Prompt, Executor)
2. Créer un outil personnalisé avec le décorateur `@tool`
3. Comprendre le cycle ReAct (Reason -> Act -> Observe -> Reason)
4. Tracer les étapes intermédiaires d'un agent pour le débogage

## Prérequis

- [Lab 5 (Viz + ML)](../Lab5-Viz-ML/README.md) : bases scikit-learn (utilisé comme outil par l'agent)
- [Lab 2 / 3](../../../Day2/Labs/) : LangChain de base
- Clé API LLM configurée (`.env` racine)

## Notebook

- [Lab6-First-Agent.ipynb](Lab6-First-Agent.ipynb) - notebook étudiant
- `Lab6-First-Agent_output.ipynb` - version exécutée de référence

## Suite

[Lab 7](../Lab7-Data-Analysis-Agent/README.md) réutilise ce pattern et l'applique à un agent **spécialisé data science** capable de manipuler un DataFrame Pandas en langage naturel.

## Navigation

[<- Index Python Agents](../../../../README.md) | [Lab 5 <<](../Lab5-Viz-ML/README.md) | [>> Lab 7](../Lab7-Data-Analysis-Agent/README.md)
