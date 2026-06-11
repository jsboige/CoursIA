# CaseStudies - Projets etudiants en IA Generative

<!-- CATALOG-STATUS
series: GenAI-CaseStudies
pedagogical_count: 4
breakdown: CaseStudies=4
maturity: PRODUCTION=3, BETA=1
-->

[← GenAI](../README.md)

Quatre projets complets, bout en bout, illustrent la diversite des applications de l'IA generative : un duel verbal multi-agent avec generation d'images, un generateur de recettes orchestre par agents, un chatbot medical multi-agent avec plugins, et un jeu interactif inspire de Fort Boyard. Chaque projet combine appel a un LLM (OpenAI) avec une architecture agentique (Semantic Kernel ou API directe), et inclut des exercices pour etendre le systeme.

Ces notebooks sont le point d'entree ideal pour decouvrir les capacites de l'IA generative avant d'approfondir dans les series thematiques ([Texte](../Texte/README.md), [SemanticKernel](../SemanticKernel/README.md), [Image](../Image/README.md)).

## Pourquoi ces projets

Les séries thématiques de GenAI démontent chaque composant ; ces quatre projets montrent les composants remontés. Adaptés de réalisations étudiantes, ils ont la taille exacte d'un bon projet de fin de module : assez complets pour exiger une vraie architecture — des rôles, une orchestration, des conditions d'arrêt —, assez courts pour être lus en entier. Lire un système complet apprend ce qu'aucun tutoriel ne montre : où placer la logique métier, comment empêcher deux agents de tourner en rond, quand arrêter une conversation. C'est aussi ce qui en fait de bons sujets d'extension, chaque projet se concluant par trois exercices qui ajoutent une contrainte, un agent ou une stratégie.

## Les quatre projets

**[Fort-Boyard](Fort-Boyard/README.md)** est le meilleur point de départ : un Père Fouras qui fait deviner, un candidat qui propose, et l'API OpenAI sans couche d'orchestration. C'est l'occasion de comprendre les stratégies de terminaison à nu — comment décider qu'un dialogue entre deux LLM est terminé — avant de les retrouver enrobées dans Semantic Kernel.

**[Barbie-Schreck](Barbie-Schreck/README.md)** est le plus visuel : deux personnages que tout oppose sont forcés de débattre sous contraintes, pendant que DALL-E illustre la joute. Sous le jeu, la mécanique est sérieuse : c'est un vrai dialogue multi-agent Semantic Kernel, avec ses prompts système rivaux et l'intégration image-dans-conversation.

**[Recipe-Maker](Recipe-Maker/README.md)** fait collaborer plusieurs agents pour produire une recette personnalisée et l'exporter en PDF. Son intérêt est la chaîne complète : de la conversation entre agents jusqu'au livrable final, en passant par la division du travail entre rôles.

**[Medical-Chatbot](Medical-Chatbot/README.md)** est le plus proche d'un système de production : ses plugins de vérification, de journalisation et de terminaison intelligente montrent comment on encadre un LLM dans un domaine sensible. La leçon dépasse le cas médical — la valeur n'est pas dans la réponse du modèle, mais dans les garde-fous qui l'entourent.

## Objectifs d'apprentissage

A l'issue de ces projets, vous serez capable de :

1. **Orchestrer** des agents conversationnels multi-role avec Semantic Kernel ou l'API OpenAI
2. **Integrer** la generation d'images (DALL-E) dans un dialogue automatise
3. **Concevoir** des strategies de terminaison et des plugins specialises pour des agents
4. **Etendre** un projet existant en ajoutant des contraintes, des agents ou des fonctionnalites (exercices inclus)

## Projets

| # | Projet | Notebook | Technologies | Contenu |
|---|--------|----------|-------------|---------|
| 1 | [Barbie-Schreck](Barbie-Schreck/README.md) | [barbie-schreck.ipynb](Barbie-Schreck/barbie-schreck.ipynb) | Semantic Kernel, OpenAI DALL-E | Duel verbal contraint entre Barbie et l'Ane de Shrek avec generation d'images |
| 2 | [Recipe-Maker](Recipe-Maker/README.md) | [receipe_maker.ipynb](Recipe-Maker/receipe_maker.ipynb) | Semantic Kernel, OpenAI, PDF | Collaboration multi-agents pour generer une recette personnalisee avec export PDF |
| 3 | [Medical-Chatbot](Medical-Chatbot/README.md) | [medical_chatbot.ipynb](Medical-Chatbot/medical_chatbot.ipynb) | Semantic Kernel, OpenAI, plugins | Chatbot medical avec plugins de verification, logging et terminaison intelligente |
| 4 | [Fort-Boyard](Fort-Boyard/README.md) | [fort-boyard-python.ipynb](Fort-Boyard/fort-boyard-python.ipynb) | OpenAI GPT | Jeu de devinettes entre le Pere Fouras et un candidat, avec strategies de terminaison |

Chaque projet contient 3 exercices permettant d'etendre le systeme (ajout de contraintes, nouveaux agents, strategies de terminaison personnalisees).

## Prerequis & environnement

| Besoin | Detail |
|--------|--------|
| Python | 3.10+ |
| `openai` | Requis pour les 4 projets |
| `semantic-kernel` | Requis pour Barbie-Schreck, Recipe-Maker et Medical-Chatbot |
| Cle API | `OPENAI_API_KEY` dans `GenAI/.env` (voir [00-GenAI-Environment](../00-GenAI-Environment/README.md)) |
| `fpdf` | Recipe-Maker uniquement (generation PDF) |

## FAQ

### Quelle cle API est requise ?

Les 4 projets necessitent `OPENAI_API_KEY`. Recipe-Maker et Medical-Chatbot utilisent en plus Semantic Kernel pour l'orchestration agentique. Configurer les cles dans `GenAI/.env` (voir [00-GenAI-Environment](../00-GenAI-Environment/README.md)).

### Peut-on executer Medical-Chatbot sans Semantic Kernel ?

Medical-Chatbot utilise Semantic Kernel pour l'orchestration des plugins (requete vers API, parsing, formatage de reponse). Pour le faire sans SK, remplacer les appels `kernel.invoke()` par des appels directs `openai.chat.completions.create()` -- la logique metier reste la meme, seule la couche d'orchestration change.

### Quelle difference avec les autres series GenAI ?

CaseStudies rassemble des projets complets et autonomes, adaptes de realisations etudiantes. Les series thematiques approfondissent chaque composant : [Texte](../Texte/README.md) pour les techniques NLP avancees, [SemanticKernel](../SemanticKernel/README.md) pour le SDK d'orchestration, [Image](../Image/README.md) pour la generation et l'edition d'images.
