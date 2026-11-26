# Surface d'attaque des outils MCP

[↑ GenAI Security](../README.md)

## Ouverture — ce que cette série enseigne (Découverte)

Un agent outillé par MCP approuve un catalogue d'outils — et se fie à leurs descriptions. Cette série enseigne les trois attaques de cette couche de confiance (injection par description d'outil, rug pull après approbation, collision de noms entre serveurs) et les défenses qui les neutralisent, démontrées de bout en bout sur des **serveurs MCP locaux réels** écrits dans le carnet.

**À qui elle s'adresse.** Un lecteur qui branche des outils sur un agent et qui veut savoir sur quoi sa couche d'approbation veille vraiment. Les prérequis exacts sont en [Installation](#installation).

## Comment lire ce README (Découverte)

Un README de série se lit à plusieurs vitesses : le parcours principal par les numéros nus, l'approfondissement par les lettres, la recherche en cours par les sous-séries et la section « Pour aller plus loin ». Le principe est exposé à la racine du dépôt, dans [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture).

- **Vous découvrez la sécurité de la couche outils** : lisez le carnet unique de la série, de haut en bas.
- **Vous creusez un palier** : cette série n'en porte aucun (voir [Approfondissements](#approfondissements-découverte)).
- **Vous cherchez la recherche en cours** : allez directement à [« Pour aller plus loin »](#pour-aller-plus-loin--niveau-recherche).

## Parcours principal (Découverte)

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| — | [Tooling-MCP-Attack-Surface](Tooling-MCP-Attack-Surface.ipynb) | Trois attaques de bout en bout sur des serveurs MCP stdio locaux — injection par description d'outil, rug pull (le catalogue mute après approbation, rendu visible par le diff d'empreintes), collision de noms entre deux serveurs — et quatre défenses mesurables : empreinte SHA-256 par outil, diff d'inventaire AJOUT/RETRAIT/MUTATION, allowlist qualifiée `(serveur, nom)`, séparation lecture/écriture. Mesure sur un modèle victime réel via OpenRouter : rug pull et collision 3/3 → 0/3, injection 0/10 avant et après, lue honnêtement avec son intervalle de Wilson. Trois exercices C.1. | Découverte | [GenAI Security](../README.md) |

## Approfondissements (Découverte)

Cette série ne porte aucun approfondissement lettré : un seul carnet, la gradation n'y ouvre pas de palier. Rien n'est perdu ici — il n'y a rien à replier.

## Sous-séries (Découverte)

Cette série n'en contient pas. Elle est elle-même une sous-série de [GenAI Security](../README.md), l'axe « surface d'attaque des outils » (issue #18213).

## Installation

- **Python 3.10+** avec le SDK MCP de référence : `pip install mcp` (le carnet l'installe lui-même si absent).
- **Clé API** (`OPENROUTER_API_KEY` ou `OPENAI_API_KEY`) **uniquement** pour la mesure sur modèle victime de la section 7 — sans elle, la cellule affiche le motif et saute la mesure. Tout le reste se rejoue en local (boucle 127.0.0.1 / stdio, aucune machine distante).

## Pour aller plus loin — niveau Recherche

- **Le verdict du carnet** : SOTA-OK — le SDK MCP de référence (`mcp`, API bas niveau `Server` + `ClientSession` sur stdio) est utilisé d'un bout à l'autre, la victime de la mesure est un LLM réel nommé, et aucune attaque n'est simulée par de fausses sorties.
- **Les carnets jumeaux de la série SemanticKernel** qui posent le client MCP de production : [08-SemanticKernel-MCP](../../SemanticKernel/08-SemanticKernel-MCP.ipynb), [11-SemanticKernel-A2A](../../SemanticKernel/11-SemanticKernel-A2A.ipynb) ; le red team de prompts : [09b_Prompt_Security_RedTeam](../../Texte/09b_Prompt_Security_RedTeam.ipynb).
- **L'axe frère** : la défense par construction des agents outillés se mesure dans [Capability](../Capability/README.md).

## Ressources

- [GenAI Security — README de la section](../README.md) : les cinq axes, sources canoniques, acceptance commune.
- [Choisir sa vitesse de lecture](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) : le principe des parcours à plusieurs vitesses, à la racine du dépôt.
