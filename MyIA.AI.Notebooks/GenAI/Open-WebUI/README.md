# Open-WebUI — La plateforme et son assurance qualité

[← Documentation GenAI](../README.md) | [→ Vibe-Coding](../Vibe-Coding/README.md)

> **Sous-domaine ombrelle.** Open WebUI est une interface de chat LLM réelle,
> auto-hébergée et multi-tenant. Ce dossier présente **la plateforme et ses
> fonctionnalités**, puis les met en pratique à travers deux parcours
> complémentaires : un **tour guidé** de la plateforme et une **série QA**
> qui la teste de bout en bout avec Playwright.

---

## Qu'est-ce qu'Open WebUI ?

Open WebUI est une application web open-source qui offre une interface de
conversation unifiée par-dessus des modèles de langage (LLM) — qu'ils soient
hébergés localement (Ollama, vLLM) ou distants (OpenAI, Mistral, Anthropic,
OpenRouter…). C'est un produit *réel*, déployé en production, et non une
démonstration jouet : authentification et rôles (RBAC), streaming des réponses,
RAG sur bases de connaissances, outils et serveurs MCP, génération d'images,
synthèse et reconnaissance vocale, canaux collaboratifs, et administration
multi-tenant.

Cette richesse fonctionnelle en fait un excellent **terrain pédagogique** : on y
apprend à la fois *comment une plateforme GenAI s'utilise* et *comment on en
garantit la qualité*.

---

## Les deux parcours

| Parcours | Angle | Format | État |
|----------|-------|--------|------|
| **Tour de la plateforme** | « À quoi sert Open WebUI et comment l'utilise-t-on ? » | Markdown pédagogique + captures d'écran annotées | 🚧 En construction (Epic #4433) |
| **[Série QA Playwright-OWUI](Playwright-OWUI/README.md)** | « Comment teste-t-on une plateforme GenAI de bout en bout ? » | Notebooks + specs Playwright (5 modules) | ✅ Disponible |

### Tour de la plateforme *(à venir)*

Un parcours narratif qui présente chaque grande fonctionnalité d'Open WebUI
(chat, RAG, outils, administration, multi-tenant…) accompagné de captures
d'écran commentées montrant *comment* on s'en sert. Les captures sont produites
de façon reproductible et **sans fuite de secret** (comptes de démonstration,
données fictives, masquage des champs sensibles).

### Série QA Playwright-OWUI

Une série de 5 modules qui apprend à écrire des tests end-to-end sur Open WebUI
avec Playwright : découverte et sélecteurs, navigation & authentification, chat
& streaming, RAG / outils MCP / canaux, puis isolation multi-tenant et CI/CD.

➡️ **[Ouvrir la série Playwright-OWUI](Playwright-OWUI/README.md)**

---

## Sécurité — pas de secret dans les supports

Tous les supports de ce dossier (markdown, captures, specs) sont conçus pour ne
**jamais** exposer de secret : pas d'URL de tenant réel sensible, pas d'e-mail
nominatif, pas de clé d'API ni de jeton, pas de mot de passe. Les captures
s'appuient sur un tenant de démonstration dédié, des comptes non-administrateur,
des données fictives, et le masquage Playwright (`mask`) des zones sensibles.
Les fichiers `.env` réels ne sont jamais commités (`*.env` est ignoré) — seuls
les `*.env.example` documentent les variables attendues.
