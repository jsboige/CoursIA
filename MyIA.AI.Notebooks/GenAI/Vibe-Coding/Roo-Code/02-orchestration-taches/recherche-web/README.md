# 🔍 Recherche Web avec Roo

## Introduction

Ce guide vous présente les différentes méthodes de recherche web disponibles dans Roo grâce aux Model Context Protocol (MCP). Ces outils permettent à Roo d'accéder à des informations en ligne actualisées et de les intégrer dans ses réponses.

> **Note d'intégration**: Les MCPs mentionnés dans ce document sont désormais organisés dans le dépôt principal selon la structure suivante:
> - **MCPs internes** (développés en interne): `mcps/internal/` (ex: jinavigator-server)
> - **MCPs externes** (intégrations avec des services tiers): `mcps/external/` (ex: searxng)

## Outils de recherche disponibles

Roo dispose de trois méthodes principales pour effectuer des recherches web :

1. **Navigateur intégré** : Permet à Roo de naviguer sur le web comme un utilisateur humain, en visualisant les pages et en interagissant avec elles.

2. **Jinavigator** (MCP interne): Convertit les pages web en format Markdown pour une meilleure analyse du contenu textuel, particulièrement utile pour les articles longs ou les documentations techniques.

3. **SearXNG** (MCP externe): Moteur de recherche méta qui agrège les résultats de plusieurs moteurs de recherche, offrant une vue d'ensemble des informations disponibles sur un sujet.

## Quand utiliser chaque outil ?

| Outil | Cas d'usage idéal | Avantages | Limitations |
|-------|-------------------|-----------|------------|
| **Navigateur intégré** | Sites interactifs, applications web, vérification visuelle | Voit exactement ce que vous voyez, peut interagir avec les éléments | Plus lent, consomme plus de ressources |
| **Jinavigator** | Articles longs, documentation, contenu principalement textuel | Extraction efficace du contenu, format structuré | Ne peut pas interagir avec les éléments dynamiques |
| **SearXNG** | Recherches générales, collecte d'informations variées | Rapide, résultats diversifiés | Moins précis pour l'analyse de pages spécifiques |

## Comment orchestrer ces outils ?

Le mode Orchestrator de Roo peut combiner ces différents outils de recherche pour obtenir les meilleurs résultats :

1. Utiliser **SearXNG** pour identifier les sources pertinentes
2. Employer **Jinavigator** pour extraire et analyser le contenu détaillé
3. Recourir au **Navigateur intégré** pour vérifier visuellement les informations ou interagir avec des éléments spécifiques

## Exemples d'utilisation

Consultez les guides spécifiques pour des exemples détaillés :

- [Utilisation du navigateur intégré](./navigateur-integre.md)
- [Extraction de contenu avec Jinavigator](./jinavigator.md)
- [Recherches avec SearXNG](./searxng.md)

## Bonnes pratiques

- Commencez par des requêtes précises pour obtenir des résultats pertinents
- Combinez plusieurs outils pour vérifier et enrichir les informations
- Utilisez le navigateur intégré avec parcimonie (consommation de ressources)
- Préférez Jinavigator pour l'analyse approfondie de contenus spécifiques
- Utilisez SearXNG pour les recherches générales et l'exploration initiale

## Intégration avec d'autres fonctionnalités

La recherche web peut être combinée avec d'autres capacités de Roo :
- Analyse de code après recherche de documentation
- Création de contenu basé sur des recherches
- Débogage avec référence à des solutions en ligne

## Installation et configuration

Pour utiliser ces outils de recherche web, vous devez installer et configurer les MCPs correspondants :

### Jinavigator (MCP interne)
```bash
# Depuis la racine du dépôt principal
cd mcps/internal/jinavigator-server
npm install
node ./dist/index.js
```

### SearXNG (MCP externe)
```bash
# Depuis la racine du dépôt principal
cd mcps/external/searxng
npm install
node ./dist/index.js
```

Pour plus de détails sur l'installation et la configuration des MCPs, consultez la documentation dans le dépôt principal.