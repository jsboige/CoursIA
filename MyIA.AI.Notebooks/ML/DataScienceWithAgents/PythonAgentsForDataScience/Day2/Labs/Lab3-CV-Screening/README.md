# Lab 3 : Pre-qualifier des Candidats avec l'IA

**Objectif :** Utiliser un agent d'IA pour analyser, noter et resumer des CVs par rapport a une offre d'emploi.

Ce laboratoire prolonge la logique du [Lab 2](../Lab2-RFP-Analysis/README.md) (analyse de RFP) en l'appliquant a un autre cas concret de l'avant-vente / RH : le **screening de candidatures**. L'objectif est de transformer une pile de CVs non structures en une grille de scoring exploitable, en gardant l'humain dans la boucle pour la decision finale.

## Objectifs d'apprentissage

A la fin de ce lab, vous saurez :

1. Utiliser un LLM pour analyser des documents non structures (CVs en texte libre)
2. Comparer plusieurs documents a une reference commune (offre d'emploi)
3. Noter l'adequation candidat / offre selon des criteres explicites
4. Generer un resume actionnable pour le recruteur

## Donnees fournies

- `offre_datascience.txt` : offre d'emploi de reference (Data Scientist)
- `cv_candidat_A.txt`, `cv_candidat_B.txt` : deux CVs a comparer

## Prerequis

- [Lab 2 (RFP)](../Lab2-RFP-Analysis/README.md) : meme pattern LangChain + extraction structuree
- Cle API LLM configuree (`.env` racine)

## Notebook

- [Lab3-CV-Screening.ipynb](Lab3-CV-Screening.ipynb) - notebook etudiant
- `Lab3-CV-Screening_output.ipynb` - version executee de reference

## Navigation

[<- Index Python Agents](../../README.md) | [Lab 2 <<](../Lab2-RFP-Analysis/README.md) | [>> Lab 4](../../Day3/Labs/Lab4-DataWrangling/README.md)
