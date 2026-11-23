# Architecture et surface fonctionnelle

[← AI Engine (WordPress)](../README.md) | [↑ Plateformes conversationnelles](../../README.md) | [Instance jetable →](../instance-jetable/README.md)

Avant de piloter AI Engine par son API ou de visiter ses écrans, il faut savoir comment le plugin est découpé. Ce dossier donne cette carte : AI Engine n'est pas un bloc, mais un ensemble de modules qu'on active séparément, et cette structure explique à la fois l'empreinte réelle d'une installation et l'endroit où chaque fonction se configure.

Il s'adresse à qui découvre le plugin et veut situer ce qu'il va lire ensuite, et à qui doit décider quoi activer sur un site. Aucun prérequis technique : le dossier ne contient pas de carnet, il oriente vers ceux qui rendent chaque partie exécutable.

## Comment lire ce README

Les séries du dépôt se lisent à plusieurs vitesses, selon le principe décrit dans [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture).

- Vous **découvrez** : lisez « La carte en bref », puis la note sur l'architecture en modules.
- Vous **creusez un palier** : la section « Où chaque partie devient exécutable » relie chaque famille de modules aux carnets qui la mesurent.
- Vous cherchez **ce qui reste ouvert** : « Pour aller plus loin » renvoie au comparatif et au cas d'usage, qui discutent ce que cette carte ne tranche pas.

## La carte en bref

*Niveau Découverte.*

AI Engine est une extension de WordPress, distribuée en version gratuite sous licence libre et complétée par une offre payante. Les supports du dépôt portent sur la version 3.7.0 gratuite, celle qu'installe l'[instance jetable](../instance-jetable/README.md).

**Ce que le plugin apporte à un site.** Des chatbots intégrables aux pages, un espace de conversation dans l'administration, un assistant dans l'éditeur de contenus, des formulaires pilotés par un modèle, la génération de textes et d'images, la recherche sur le contenu du site par embeddings, et un serveur MCP qui expose le site à des agents distants. Toutes ces fonctions ne sont pas ouvertes par la version gratuite : les carnets de la série mesurent cette frontière au lieu de la supposer.

**Le moteur se choisit.** Le plugin se branche sur plusieurs fournisseurs distants, et sur tout serveur compatible OpenAI par un environnement de type `custom` : c'est par ce connecteur qu'un moteur auto-hébergé le sert. AI Engine n'embarque pas de moteur local.

**Trois familles de modules.** Le tableau de bord range les modules en trois familles activables indépendamment : celle qui décide ce que voit le visiteur du site, celle qui décide ce que le serveur sait faire, et celle qui décide ce que voit l'administrateur. La note [L'architecture en modules](architecture-en-modules.md) en donne le tableau et tire deux conséquences pratiques : un déploiement minimal n'active qu'une petite partie du plugin, et le protocole MCP se configure dans les deux sens à deux endroits distincts — consommer des serveurs externes d'un côté, exposer le site de l'autre.

## Où chaque partie devient exécutable

*Niveau Approfondissement.* La carte se vérifie sur l'instance jetable, par les carnets de la série [« AI Engine par son API »](../03-Functional/README.md).

| Ce que la carte annonce | Où on le mesure |
|---|---|
| Un chatbot est un document de configuration que l'API lit et réécrit | [Chatbots](../03-Functional/03-1-Chatbots/README.md) |
| Un formulaire est un contenu WordPress, avec son brouillon et sa publication | [Formulaires](../03-Functional/03-2-Forms/README.md) |
| Les embeddings se rangent par environnement, et ce rangement est un contrôle d'accès | [RAG et embeddings](../03-Functional/03-3-RAG-et-Embeddings/README.md) |
| Le site est un catalogue d'outils pour agents, avec sa propre autorisation | [Serveur MCP](../03-Functional/03-4-MCP-Server/README.md) |
| Le moteur se déclare dans la configuration du plugin, usage par usage | [Multi-provider](../03-Functional/03-5-Multi-Provider/README.md) |
| Les écrans d'administration qui portent ces réglages | [Tour de la plateforme](../00-Tour-Plateforme/README.md) |

## Pour aller plus loin

*Niveau Recherche.*

- **Ce plugin plutôt qu'une plateforme autonome ?** Le [comparatif avec Open WebUI](../02-Comparatif/comparatif-owui-vs-ai-engine.md) aligne les deux produits critère par critère — [fonctionnalités](../02-Comparatif/comparatif-owui-vs-ai-engine.md#fonctionnalités-cœur), [RAG](../02-Comparatif/comparatif-owui-vs-ai-engine.md#rag-et-embeddings), [MCP](../02-Comparatif/comparatif-owui-vs-ai-engine.md#mcp-model-context-protocol), [coût](../02-Comparatif/comparatif-owui-vs-ai-engine.md#coût) — sans chercher à les classer : ils visent des usages différents et cohabitent souvent.
- **Ce qu'une installation réelle fait de cette carte** : le [cas d'usage éditorial](../04-Cas-Usage-livresagites/livresagites-parcours.md) suit plusieurs fonctions du plugin sur une installation observée, à un niveau architectural.
- **Les deux sens du MCP devant un même agent** : le carnet [Consommer et exposer le MCP](../03-Functional/03-4-MCP-Server/consommer-vs-exposer-le-mcp.ipynb) mesure ce qui arrive quand un agent reçoit deux catalogues à la fois.

## Ressources

- [L'architecture en modules](architecture-en-modules.md) — la note de ce dossier.
- [Les fonctionnalités par l'API](../03-Functional/README.md) — l'ordre de lecture des carnets.
- [Fiche du plugin sur wordpress.org](https://wordpress.org/plugins/ai-engine/) — la source publique des versions et de la licence.
