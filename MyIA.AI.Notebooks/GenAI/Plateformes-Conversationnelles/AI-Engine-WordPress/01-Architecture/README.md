# Architecture et surface fonctionnelle

[← README AI-Engine-WordPress](../README.md)

Ce dossier regroupe ce qui relève de la structure d'AI-Engine : la
surface fonctionnelle vue de haut niveau (sections 1 à 3 ci-dessous,
déplacées du README parent lors de la réorganisation #12127) et le
découpage en modules du tableau de bord. Les sections RAG, MCP server
et intégration WordPress restent présentées dans le
[README parent](../README.md) tant que leurs dossiers ne sont pas
créés.

## Sommaire

1. [Vue d'ensemble](#vue-densemble)
2. [Fonctionnalités GenAI cœur](#fonctionnalités-genai-cœur)
3. [Multi-provider et self-hosting](#multi-provider-et-self-hosting)
4. [L'architecture en modules](architecture-en-modules.md)

## Vue d'ensemble

AI-Engine en deux pages : ce que c'est, qui l'utilise, pourquoi on en
parle à côté d'Open WebUI. Statistiques publiques (100K+ installations
actives, 4.9/5 étoiles, version 3.7.0 août 2026, license GPL).

→ le développement chiffré vit dans le
[comparatif](../02-Comparatif/comparatif-owui-vs-ai-engine.md), au
niveau catégorie.

## Fonctionnalités GenAI cœur

Chatbots, Workspace (plein écran dans wp-admin), Copilot pour l'éditeur
WordPress, AI Forms (text/image/audio/file avec logique conditionnelle),
génération d'image et de vision. Comparaison avec les surfaces
équivalentes d'Open WebUI (chat, canaux, prompts).

→ détail et mesures dans la
[section dédiée du comparatif](../02-Comparatif/comparatif-owui-vs-ai-engine.md#fonctionnalités-cœur).

## Multi-provider et self-hosting

AI-Engine supporte **neuf providers distants** (OpenAI, Anthropic,
Google, Mistral, xAI/Grok, Perplexity, OpenRouter, Replicate, Azure)
plus un connecteur **Custom OpenAI-compatible** pour les moteurs
auto-hébergés (Ollama, LM Studio, vLLM, llama.cpp, LocalAI). Côté
Open WebUI, c'est la même philosophie avec OpenAI-compatible + Ollama
natif ; la différence est qu'AI-Engine ne fournit pas son propre
moteur local — il s'appuie sur l'écosystème WordPress existant.

→ [section correspondante du comparatif](../02-Comparatif/comparatif-owui-vs-ai-engine.md#multi-provider-et-self-hosting).

## L'architecture en modules

Le plugin ne s'installe pas d'un bloc : son tableau de bord expose
trois familles de modules activables indépendamment (Client, Server,
Admin), et le protocole MCP s'y configure dans les deux sens à des
endroits distincts. Voir
[`architecture-en-modules.md`](architecture-en-modules.md), extrait du
[cas d'usage éditorial](../04-Cas-Usage-livresagites/livresagites-parcours.md).
