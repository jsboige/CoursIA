# Défense par construction des agents outillés

[↑ GenAI Security](../README.md)

## Ouverture — ce que cette série enseigne (Découverte)

L'injection indirecte est l'attaque la plus documentée des agents outillés : une instruction cachée dans les données lues par l'agent prend la place de la demande de l'user. Cette série enseigne l'inversion du problème — plutôt que de *détecter* l'injection, la rendre *structurellement impossible*. Le plan est produit par le modèle sur la **seule** demande de l'user ; les données sont lues par une étape isolée, sans droit d'appel d'outil ; chaque valeur porte une étiquette de provenance `USER`/`DATA` propagée par fusion, et une politique refuse tout appel d'outil dont un argument sensible est teinté `DATA`.

**À qui elle s'adresse.** Un lecteur qui a vu un agent outillé (tools, RAG, fonctions) et qui se demande comment il peut être subverti par ses propres entrées. Les concepts sont introduits depuis le début du carnet ; les prérequis exacts sont en [Installation](#installation).

## Comment lire ce README (Découverte)

Un README de série se lit à plusieurs vitesses : le parcours principal par les numéros nus, l'approfondissement par les lettres, la recherche en cours par les sous-séries et la section « Pour aller plus loin ». Le principe est exposé à la racine du dépôt, dans [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture).

- **Vous découvrez la défense par construction** : lisez le carnet unique de la série, de haut en bas.
- **Vous creusez un palier** : cette série n'en porte aucun (voir [Approfondissements](#approfondissements-découverte)).
- **Vous cherchez la recherche en cours** : allez directement à [« Pour aller plus loin »](#pour-aller-plus-loin--niveau-recherche).

## Parcours principal (Découverte)

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| — | [Capability-Plan-Data-Separation](Capability-Plan-Data-Separation.ipynb) | La séparation plan/données et les étiquettes de provenance `USER`/`DATA` rendent l'injection structurellement impossible : banc de 40 scénarios (20 tâches légitimes + 20 injections indirectes déguisées) opposant trois agents — ReAct sans filtre, ReAct + filtre d'allowlist, agent par capacités — sur un modèle local 7B, avec la chaîne de provenance qui rend un refus auditable et la contrepartie mesurée au taux de tâche (18 % contre 72 %). Trois exercices C.1. | Découverte | [GenAI Security](../README.md) |

## Approfondissements (Découverte)

Cette série ne porte aucun approfondissement lettré : un seul carnet, la gradation n'y ouvre pas de palier. Rien n'est perdu ici — il n'y a rien à replier.

## Sous-séries (Découverte)

Cette série n'en contient pas. Elle est elle-même une sous-série de [GenAI Security](../README.md), l'axe « défense par construction » (issue #27512).

## Installation

- **Python 3.10+** : le carnet n'importe que la bibliothèque standard (`json`, `os`, `re`, `time`, `urllib.request`, `dataclasses`).
- **Ollama local** : un modèle `qwen2.5:7b` joignable sur `OLLAMA_BASE` (défaut `http://localhost:11434/v1`), modèle réglable par `OLLAMA_MODEL`. Sans cible locale joignable, le carnet s'arrête en nommant la cause à réparer (règle F) — pas de contournement silencieux.

## Pour aller plus loin — niveau Recherche

- **La contrepartie mesurée.** Sur le banc du carnet, la séparation plan/données se paie au taux de tâche (18 % contre 72 % pour le ReAct) : ce qui planifie ne lit pas ce qui est lu, et l'agent refuse les étapes légitimes teintées `DATA`. Le carnet impute les échecs un par un et déclare la limite qui reste ouverte — la couche de texte libre (un résumé trompeur sans appel d'outil) n'est pas couverte par la politique.
- **Les axes frères de la section** : le red team qui mesure les attaques ([RedTeam](../RedTeam/README.md)), la surface d'attaque de la couche outils ([Tooling](../Tooling/README.md)).

## Ressources

- [GenAI Security — README de la section](../README.md) : les cinq axes, sources canoniques, acceptance commune.
- [Choisir sa vitesse de lecture](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) : le principe des parcours à plusieurs vitesses, à la racine du dépôt.
