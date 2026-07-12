# Lab 2 : De l'Appel d'Offre au PoC en 1 heure

**Objectif :** Utiliser un agent d'IA simple pour lire un appel d'offre (RFP), en extraire les points clés et générer une ébauche de proposition technique.

Ce laboratoire ouvre la **Journée 2** sur l'IA agentique appliquée à la pré-vente. Il démontre comment **LangChain** orchestre un LLM pour automatiser les tâches chronophages d'analyse de documents non structurés, tout en gardant l'humain dans la boucle pour la validation finale.

## Objectifs d'apprentissage

À la fin de ce lab, vous saurez :

1. Utiliser LangChain pour orchestrer des tâches d'analyse de documents
2. Extraire automatiquement des informations structurées d'un texte libre
3. Générer une proposition technique basée sur les besoins identifiés
4. Chaîner plusieurs appels LLM dans un pipeline reproductible

## Données fournies

- `appel_offre.txt` : exemple d'appel d'offre pour un projet data/IA, format libre représentatif des RFP réels.

## Prérequis

- [Lab 1 (Day 1)](../../../Day1/Labs/README.md) : bases Pandas + première classification ML
- Clé API LLM configurée (`.env` racine)

## Notebook

- [Lab2-RFP-Analysis.ipynb](Lab2-RFP-Analysis.ipynb) - notebook étudiant
- `Lab2-RFP-Analysis_output.ipynb` - version exécutée de référence

## Navigation

[<- Index Python Agents](../../../../README.md) | [Lab 1 (Day 1) <<](../../../Day1/Labs/README.md) | [>> Lab 3](../Lab3-CV-Screening/README.md)
