# Lab 6 : Construire son premier Agent

**Objectif :** Comprendre et construire les 4 composants fondamentaux d'un agent d'IA avec LangChain : le **LLM**, les **Outils**, le **Prompt**, et l'**Executeur**.

Apres avoir utilise des chaines LangChain "fil tendu" dans les Labs 2 et 3, ce laboratoire passe a l'**agent** au sens strict : un programme qui utilise un LLM pour **raisonner**, **choisir** des actions parmi un ensemble d'outils, et **iterer** jusqu'a atteindre un objectif. C'est le pivot conceptuel de la Journee 3.

## Objectifs d'apprentissage

A la fin de ce lab, vous saurez :

1. Assembler les 4 piliers d'un agent LangChain / LangGraph (LLM, Tools, Prompt, Executor)
2. Creer un outil personnalise avec le decorateur `@tool`
3. Comprendre le cycle ReAct (Reason -> Act -> Observe -> Reason)
4. Tracer les etapes intermediaires d'un agent pour le debogage

## Prerequis

- [Lab 5 (Viz + ML)](../Lab5-Viz-ML/README.md) : bases scikit-learn (utilise comme outil par l'agent)
- [Lab 2 / 3](../../../Day2/Labs/) : LangChain de base
- Cle API LLM configuree (`.env` racine)

## Notebook

- [Lab6-First-Agent.ipynb](Lab6-First-Agent.ipynb) - notebook etudiant
- `Lab6-First-Agent_output.ipynb` - version executee de reference

## Suite

[Lab 7](../Lab7-Data-Analysis-Agent/README.md) reutilise ce pattern et l'applique a un agent **specialise data science** capable de manipuler un DataFrame Pandas en langage naturel.

## Navigation

[<- Index Python Agents](../../README.md) | [Lab 5 <<](../Lab5-Viz-ML/README.md) | [>> Lab 7](../Lab7-Data-Analysis-Agent/README.md)
