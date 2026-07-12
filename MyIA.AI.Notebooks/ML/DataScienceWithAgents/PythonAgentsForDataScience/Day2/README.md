# Journée 2 — Agents pour l'analyse documentaire

[← PythonAgentsForDataScience (track)](../README.md) | [Journée 1 →](../Day1/Labs/README.md) | [Journée 3 →](../Day3/README.md)

La **Journée 2** opère le basculement central du workshop : de l'écriture du code data science à l'**orchestration d'agents LLM**. On y traite deux tâches documentaires — l'analyse d'un appel d'offres et le pré-screening de CVs — où l'agent extrait une information structurée à partir d'un texte libre, tout en gardant l'humain dans la boucle pour la validation.

## Labs

| Lab | Sujet | Concept-phare |
|-----|-------|---------------|
| [Lab 2 — RFP Analysis](Labs/Lab2-RFP-Analysis/Lab2-RFP-Analysis.ipynb) | d'un appel d'offres à un PoC en 1 heure | extraction structurée d'un texte libre par LLM |
| [Lab 3 — CV Screening](Labs/Lab3-CV-Screening/Lab3-CV-Screening.ipynb) | pré-qualifier des candidats avec l'IA | analyse, notation et résumé de CVs vs offre |

## Prérequis

- Avoir suivi la [Journée 1](../Day1/Labs/README.md) (Pandas, Matplotlib, régression linéaire).
- **LangChain** + clé API OpenAI (les labs 2 et 3 appellent un LLM).

## Suite

La [Journée 3](../Day3/README.md) monte en abstraction : data wrangling agentique, visualisation/ML, puis le premier agent d'analyse de données autonome (Lab 7).
