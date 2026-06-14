# Lab 3 : Pré-qualifier des Candidats avec l'IA

**Objectif :** Utiliser un agent d'IA pour analyser, noter et résumer des CVs par rapport à une offre d'emploi.

Ce laboratoire prolonge la logique du [Lab 2](../Lab2-RFP-Analysis/README.md) (analyse de RFP) en l'appliquant à un autre cas concret de l'avant-vente / RH : le **screening de candidatures**. L'objectif est de transformer une pile de CVs non structurés en une grille de scoring exploitable, en gardant l'humain dans la boucle pour la décision finale.

## Objectifs d'apprentissage

À la fin de ce lab, vous saurez :

1. Utiliser un LLM pour analyser des documents non structurés (CVs en texte libre)
2. Comparer plusieurs documents à une référence commune (offre d'emploi)
3. Noter l'adéquation candidat / offre selon des critères explicites
4. Générer un résumé actionnable pour le recruteur

## Données fournies

- `offre_datascience.txt` : offre d'emploi de référence (Data Scientist)
- `cv_candidat_A.txt`, `cv_candidat_B.txt` : deux CVs à comparer

## Prérequis

- [Lab 2 (RFP)](../Lab2-RFP-Analysis/README.md) : même pattern LangChain + extraction structurée
- Clé API LLM configurée (`.env` racine)

## Notebook

- [Lab3-CV-Screening.ipynb](Lab3-CV-Screening.ipynb) - notebook étudiant
- `Lab3-CV-Screening_output.ipynb` - version exécutée de référence

## Navigation

[<- Index Python Agents](../../../../README.md) | [Lab 2 <<](../Lab2-RFP-Analysis/README.md) | [>> Lab 4](../../../Day3/Labs/Lab4-DataWrangling/README.md)
