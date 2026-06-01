# Lab 2 : De l'Appel d'Offre au PoC en 1 heure

**Objectif :** Utiliser un agent d'IA simple pour lire un appel d'offre (RFP), en extraire les points cles et generer une ebauche de proposition technique.

Ce laboratoire ouvre la **Journee 2** sur l'IA agentique appliquee a la pre-vente. Il demontre comment **LangChain** orchestre un LLM pour automatiser les taches chronophages d'analyse de documents non structures, tout en gardant l'humain dans la boucle pour la validation finale.

## Objectifs d'apprentissage

A la fin de ce lab, vous saurez :

1. Utiliser LangChain pour orchestrer des taches d'analyse de documents
2. Extraire automatiquement des informations structurees d'un texte libre
3. Generer une proposition technique basee sur les besoins identifies
4. Chainer plusieurs appels LLM dans un pipeline reproductible

## Donnees fournies

- `appel_offre.txt` : exemple d'appel d'offre pour un projet data/IA, format libre representatif des RFP reels.

## Prerequis

- [Lab 1 (Day 1)](../../Day1/Labs/README.md) : bases Pandas + premiere classification ML
- Cle API LLM configuree (`.env` racine)

## Notebook

- [Lab2-RFP-Analysis.ipynb](Lab2-RFP-Analysis.ipynb) - notebook etudiant
- `Lab2-RFP-Analysis_output.ipynb` - version executee de reference

## Navigation

[<- Index Python Agents](../../README.md) | [Lab 1 (Day 1) <<](../../Day1/Labs/README.md) | [>> Lab 3](../Lab3-CV-Screening/README.md)
