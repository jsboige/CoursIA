# AI Engine (WordPress) — la couche conversationnelle dans un site de contenu

[← Plateformes conversationnelles](../README.md) | [↑ Documentation GenAI](../../README.md) | [Open WebUI →](../Open-WebUI/README.md)

Beaucoup de sites de contenu — blogs, boutiques, sites éditoriaux — tournent déjà sous WordPress. Plutôt que de poser une plateforme de chat à côté du site, on peut ajouter la couche conversationnelle dans le site lui-même, par l'extension AI Engine. Cette série enseigne ce que cela donne : à quoi ressemble le plugin, comment il est découpé, ce que son API répond réellement, ce qu'un navigateur constate et que l'API ne voit pas, et ce qu'une installation en service en fait. Elle garde [Open WebUI](../Open-WebUI/README.md) comme point de comparaison : la question n'est pas de classer les deux produits, mais de savoir quand l'un convient mieux que l'autre.

Elle s'adresse à qui administre ou intègre un site WordPress, à qui évalue une plateforme conversationnelle pour un projet, et à qui veut voir le protocole MCP intégré à un système de gestion de contenu. Le tour de l'interface et la carte du plugin se lisent sans prérequis ; les carnets demandent de savoir lire du JSON et envoyer une requête HTTP en Python.

## Comment lire ce README

Les séries du dépôt se lisent à plusieurs vitesses, selon le principe décrit dans [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture).

- Vous **découvrez** : suivez le parcours principal dans l'ordre ; ses deux premières étapes se lisent sans rien installer.
- Vous **creusez un palier** : la section « Approfondissements » ajoute le comparatif avec Open WebUI et l'étude d'une installation en service.
- Vous cherchez **ce qui reste ouvert** : « Pour aller plus loin » rassemble les frontières que la série mesure sans les franchir.

## Parcours principal

*Niveau Découverte pour les étapes 1 et 2, Approfondissement ensuite.* Chaque étape est un dossier, avec son propre README.

| # | Étape | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 1 | [Tour de la plateforme](00-Tour-Plateforme/README.md) | À quoi ressemble AI Engine et comment on s'en sert depuis son interface : tableau de bord, catalogue des modules, éditeur de chatbots, réglages des moteurs, bac à sable, générateurs, puis le site public et une conversation réelle. | Toute personne qui découvre le plugin | [Comparatif avec Open WebUI](02-Comparatif/comparatif-owui-vs-ai-engine.md) |
| 2 | [Architecture et surface fonctionnelle](01-Architecture/README.md) | Le plugin n'est pas un bloc : des familles de modules activables séparément, et un protocole MCP qui se configure dans les deux sens à deux endroits distincts. | Qui doit décider quoi activer sur un site | [L'architecture en modules](01-Architecture/architecture-en-modules.md) |
| 3 | [Les fonctionnalités par l'API](03-Functional/README.md) | Piloter le plugin par requêtes, sur une instance jetable : une chaîne de carnets qui parcourt ses faces — administrateur, agent, visiteur, éditeur — et des carnets autonomes qui prolongent chaque palier. | Administrateur, intégrateur, développeur d'agents | [Cas d'usage éditorial](04-Cas-Usage-livresagites/livresagites-parcours.md) |
| 4 | [Parcours QA — ce que l'API ne voit pas](05-Playwright-AI-Engine/README.md) | L'application d'administration écrit : une valeur posée par l'API peut être défaite par la seule ouverture d'une page de réglages. Ce qu'un vrai navigateur constate, et pourquoi il faut publier un taux plutôt qu'un verdict. | Testeur, intégrateur | [Sécurité et méthode](06-Securite-et-Methode/README.md) |
| 5 | [Sécurité et méthode](06-Securite-et-Methode/README.md) | La règle de publication des supports, et un carnet qui mesure ce qu'un test de structure ne voit pas quand un assistant a modifié le rendu d'une page. | Relecteur de pages générées, contributeur | [Quand la vérification est verte et le système est cassé](../../../../docs/reference/verification-verte-systeme-casse.md) |

Les étapes 3 à 5 partagent un même terrain : l'[instance jetable « Maison Valmont »](instance-jetable/README.md), un WordPress local au contenu entièrement synthétique. Aucun carnet ne s'adresse à un site en service.

## Approfondissements

*Niveau Approfondissement.*

### Autour de 1 — comparer avec une plateforme autonome

Le [comparatif avec Open WebUI](02-Comparatif/comparatif-owui-vs-ai-engine.md) aligne les deux produits critère par critère : positionnement, fonctionnalités, RAG, MCP, extensibilité, sécurité, coût. Il se termine par trois cas — choisir l'un, choisir l'autre, les faire cohabiter — et par ses limites connues. Il se lit sans rien installer.

### Autour de 3 — ce qu'une installation en service en fait

Le [cas d'usage éditorial](04-Cas-Usage-livresagites/livresagites-parcours.md) observe le plugin sur le site d'une maison d'édition, où il outille une chaîne de production plutôt qu'un auteur isolé. Il suit l'assistant de l'éditeur, le RAG sur corpus et le piège des environnements multiples, le site comme serveur MCP exposant des verbes du métier, et le formulaire comme machine à états. L'installation est décrite à un niveau architectural, sans contenu, sans nom et sans capture ; chacun de ses parcours a un carnet compagnon dans la série par l'API, qui rejoue la question sur l'instance jetable ou sur des données synthétiques.

Prérequis en plus : aucun pour ces deux lectures.

## Sous-séries

*Chaque dossier porte son propre niveau, rappelé dans son README.*

**[Tour de la plateforme](00-Tour-Plateforme/README.md).** Le pendant « interface » de la série par l'API : on y apprend à se servir de l'outil à la souris, là où les carnets apprennent à l'automatiser. Chaque section dit ce qu'est la fonctionnalité, ce que montre la capture, puis donne la capture. Les images sont produites par un script rejouable contre l'instance jetable : elles suivent l'interface, pas l'inverse, et ne montrent ni clé ni donnée réelle.

**[Architecture et surface fonctionnelle](01-Architecture/README.md).** La carte du plugin : ce qu'il apporte à un site, comment le moteur se choisit, et les familles de modules de son tableau de bord. Le dossier ne contient pas de carnet ; il relie chaque partie de la carte au dossier qui la rend exécutable.

**[Comparatif](02-Comparatif/comparatif-owui-vs-ai-engine.md).** Un tableau structuré des deux plateformes de la famille, construit pour répondre à « quand l'une plutôt que l'autre », pas pour désigner un vainqueur.

**[Les fonctionnalités par l'API](03-Functional/README.md).** Le cœur exécutable de la série. Une chaîne numérotée de carnets fait le tour du plugin par ses routes et ses quatre faces — administrateur, agent, visiteur, rédacteur ; des carnets autonomes approfondissent l'audit d'un formulaire, d'un catalogue d'outils, d'un modèle, d'une chaîne de transformations ou d'un corpus. Le dossier se divise en sous-séries par thème : chatbots, formulaires, RAG et embeddings, serveur MCP, multi-provider.

**[Cas d'usage éditorial](04-Cas-Usage-livresagites/livresagites-parcours.md).** L'observation d'une installation réelle, restituée par ses structures et ses comptages. C'est lui qui fournit aux carnets autonomes leurs questions : la dérive d'un assistant d'édition, la fuite entre environnements de vecteurs, le catalogue d'outils générique, le coût caché d'un formulaire conditionnel.

**[Parcours QA](05-Playwright-AI-Engine/README.md).** Un carnet qui pilote un vrai navigateur sur l'instance jetable et montre l'angle mort commun à toutes les sondes d'API : l'application d'administration réécrit des réglages à l'ouverture d'une page. La leçon de méthode est de répéter, compter et publier une proportion.

**[Sécurité et méthode](06-Securite-et-Methode/README.md).** La règle « pas de secret dans les supports », qui vaut pour toute la série, et un carnet d'audit visuel : un test de structure reste vert sur des pages au rendu cassé, et il faut un détecteur par classe de défaut, mesuré sur le style que le navigateur calcule.

**[Instance jetable](instance-jetable/README.md).** Le terrain commun des carnets : une pile Docker qui installe WordPress, la version gratuite du plugin et un contenu synthétique, branchée sur un moteur de langage local. Son README donne le montage pas à pas, la vérification rapide, une note de maintenance et le nettoyage.

## Installation et prérequis

*Niveau Découverte.*

Le tour, la carte du plugin, le comparatif et le cas d'usage se lisent sans rien installer. Les carnets demandent :

| Ce qu'il faut | Pour quoi |
|---|---|
| Docker, et l'[instance jetable](instance-jetable/README.md) démarrée, servie par défaut sur le port local 8093 | Tous les carnets qui interrogent le plugin |
| Le fichier `instance-jetable/.env`, copié de son gabarit et complété du mot de passe d'application créé au montage | Tous les carnets qui interrogent le plugin |
| Un moteur de langage local compatible OpenAI, déclaré dans ce même fichier | Les carnets qui obtiennent une réponse générée |
| Un modèle d'embeddings servi par ce moteur | La mesure de dérive d'un assistant et la comparaison des découpages sur vecteurs réels |
| Python 3.10 ou plus récent, avec `requests` et `python-dotenv` | Tous les carnets ; chaque sous-série précise ses paquets en plus |
| `playwright` et son navigateur Chromium | Le parcours QA, l'audit visuel, et la régénération des captures du tour |
| Le fichier [`.env.example`](.env.example) de ce dossier, copié en `.env` | Diriger le banc d'évaluation de modèle vers un autre moteur, ou l'audit de catalogue vers un autre serveur MCP |

Aucune adresse ni clé n'est écrite dans un carnet, et aucun fichier `.env` n'est versionné. Aucun GPU n'est requis par les carnets eux-mêmes : le besoin en calcul est celui du moteur que vous servez. Plusieurs carnets écrivent sur l'instance et rétablissent son état en fin d'exécution : exécutez-les sur l'instance jetable, jamais sur un site en service.

## Pour aller plus loin

*Niveau Recherche.*

- **La frontière de la version gratuite.** La série travaille sur la version gratuite du plugin et mesure ce qu'elle n'ouvre pas — indexation et recherche par embeddings, champs de formulaire dynamiques, actions de l'assistant d'édition — sans décrire ce qu'elle n'a pas pu observer. Rejouer ces mesures sur une installation qui dispose de l'offre payante reste à faire.
- **Un persona n'est pas une frontière de sécurité.** La note [Cadrer ce qu'un agent a le droit de faire](../cadrer-les-agents.md) sépare l'intention, la portée et l'autorité d'un assistant, et le carnet [Différencier plusieurs assistants](../differencier-les-assistants.ipynb) mesure ce qu'un prompt promet réellement.
- **Un catalogue d'outils générique** donne à un agent beaucoup de pouvoir et peu de compréhension : concevoir les verbes métier qui manquent est un exercice ouvert de la sous-série [Serveur MCP](03-Functional/03-4-MCP-Server/README.md).
- **Les vérifications vertes qui ne prouvent rien** forment le fil commun du parcours QA et de l'audit visuel ; l'[étude de cas](../../../../docs/reference/verification-verte-systeme-casse.md) du dépôt en catalogue les classes.

## Ressources

- [Plateformes conversationnelles](../README.md) — la famille, et la plateforme voisine.
- [Tests de bout en bout pour Open WebUI](../Open-WebUI/Playwright-OWUI/README.md) — le pendant du parcours QA sur l'autre plateforme.
- [Fiche du plugin sur wordpress.org](https://wordpress.org/plugins/ai-engine/) — versions, licence et documentation publique.
- [Spécification du protocole MCP](https://modelcontextprotocol.io) — la référence du protocole.
