# Serveur MCP — WordPress comme catalogue d'outils pour agents

[← Les fonctionnalités par l'API](../README.md) | [↑ AI Engine (WordPress)](../../README.md) | [Instance jetable →](../../instance-jetable/README.md)

Avec AI Engine, un site WordPress ne se contente pas d'héberger un chatbot : il devient un serveur MCP, c'est-à-dire un catalogue d'outils qu'un agent distant peut découvrir et appeler. Cette sous-série prend ce serveur par quatre côtés : le protocole qui le fait parler, l'autorisation qui décide qui peut l'appeler, la qualité de ce qu'il expose, et ce qui arrive quand un agent reçoit son catalogue en même temps que celui d'un autre serveur.

Elle s'adresse à qui veut brancher un agent sur un site, à qui administre ce branchement, et à qui doit juger un serveur MCP qu'il n'a pas écrit. Le premier carnet de la chaîne, [Présenter AI Engine par son API](../03-5-Multi-Provider/presenter-ai-engine-par-son-api.ipynb), est le prérequis du parcours principal ; avoir déjà vu un échange JSON-RPC aide, sans être nécessaire.

## Comment lire ce README

Les séries du dépôt se lisent à plusieurs vitesses, selon le principe décrit dans [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture).

- Vous **découvrez** : lisez le parcours principal ; le premier carnet suffit pour faire agir un agent sur le site.
- Vous **creusez un palier** : la section « Approfondissements » passe de l'usage du serveur à son audit.
- Vous cherchez **ce qui reste ouvert** : « Pour aller plus loin » rassemble les questions de conception que les mesures laissent ouvertes.

## Parcours principal

*Niveau Découverte pour la première ligne, Approfondissement pour la seconde.* Les numéros sont les rangs des carnets dans la chaîne « AI Engine par son API », dont l'ordre complet figure dans le [README parent](../README.md) ; les rangs intermédiaires se lisent dans les sous-séries voisines.

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 4 | [Piloter WordPress par MCP](piloter-wordpress-par-mcp.ipynb) | Parler au serveur par son protocole : ouverture de session, découverte du catalogue d'outils et de leurs schémas, appels en lecture, puis cycle de vie complet d'un article (créer un brouillon, le relire, le supprimer, vérifier le compte). Mesurer la frontière de sécurité : sans authentification, chaque appel est refusé ; chaque outil porte un niveau d'accès, lisible sur la route miroir de l'administration. | Développeur d'agents, intégrateur | [Auditer un serveur MCP](auditer-un-serveur-mcp.ipynb) |
| 8 | [Le serveur MCP et son autorisation](autour-du-consent-oauth-du-serveur-mcp.ipynb) | Le plugin est son propre serveur d'autorisation OAuth. Suivre la délégation de bout en bout : documents de découverte, enregistrement dynamique d'un client, escalier des refus (preuve PKCE exigée, consentement réservé aux administrateurs), consentement, échange du code contre un jeton, appel d'outil avec ce jeton, révocation immédiate. Comparer les trois clés de la plateforme : mot de passe d'application, jeton OAuth, nonce. | Administrateur, auditeur de sécurité | [Consommer et exposer le MCP](consommer-vs-exposer-le-mcp.ipynb) |

Aucun des deux carnets n'appelle de modèle de langage : ils mesurent le protocole et ses refus, pas une réponse générée. Le rang 4 s'authentifie par mot de passe d'application ; le rang 8 crée sur l'instance les comptes de test dont il a besoin, que d'autres carnets de la chaîne réutilisent.

## Approfondissements

*Niveau Approfondissement.*

### Autour de 4 — juger un catalogue qu'on n'a pas écrit

[Auditer un serveur MCP](auditer-un-serveur-mcp.ipynb) défend une thèse : un serveur utile expose les verbes du métier, pas les tables de la base. Pour la rendre vérifiable, il mesure pour chaque outil une distance au schéma de persistance, calculée à partir du seul schéma d'entrée, et signale les « imposteurs » : des outils dont le nom annonce un objet du métier que leur schéma ne sait pas nommer. Deux catalogues sont audités : celui que l'instance expose réellement, presque entièrement composé d'opérations génériques sur les tables du site, et un catalogue d'atelier synthétique qui mêle opérations génériques et verbes métier vérifiés. L'écart entre les deux est la leçon ; l'heuristique reste un premier filtre, pas un verdict.

Prérequis en plus : aucun paquet hors de la bibliothèque standard. Le carnet s'exécute hors ligne sur le catalogue d'atelier ; la lecture du catalogue réel demande l'instance jetable, ou tout autre serveur désigné par les variables `MCP_TOOL_CATALOG_URL` et `MCP_TOOL_TOKEN` (gabarit : [`.env.example`](../../.env.example)).

### Autour de 8 — deux catalogues devant un même agent

[Consommer et exposer le MCP](consommer-vs-exposer-le-mcp.ipynb) étudie les deux sens du protocole sur l'instance : le site expose son catalogue, et le carnet le consomme en client, en même temps que celui d'un second serveur réel et indépendant, le serveur `filesystem` de référence du projet MCP, qui tient un rayon de fiches de lecture. Le risque étudié est la double écriture : devant deux catalogues fusionnés, quel outil l'agent choisit-il pour une tâche située à la frontière ?

Le carnet procède en deux mesures. La première, structurelle, compare les signatures des outils et se révèle incapable de classer le risque. La seconde, comportementale, soumet une batterie de tâches à un modèle réel, répète chaque tâche et rend chaque taux avec son intervalle de confiance, sur deux moteurs de la même famille pour séparer ce qui vient du modèle de ce qui vient du protocole. Une phrase de politique de routage ajoutée au prompt ne déplace pas le taux de confusion : la conclusion plaide pour une contrainte mécanique — filtrer les outils côté client, imposer des préfixes — plutôt que pour une consigne. Trois exemples guidés précèdent les exercices.

Prérequis en plus : l'instance jetable ; le paquet Python `mcp` et le client `openai` ; Node.js, pour lancer le serveur `filesystem` par `npx` ; deux moteurs de langage locaux compatibles OpenAI capables d'appels d'outils. L'exécution complète est longue, la batterie étant répétée.

## Installation et prérequis

*Niveau Découverte.*

- **L'instance jetable « Maison Valmont »** démarrée et son fichier `instance-jetable/.env` renseigné : le [README de l'instance](../../instance-jetable/README.md) donne le montage, le port et la création du mot de passe d'application que les carnets lisent dans ce fichier.
- **Python 3.10 ou plus récent** avec `requests` et `python-dotenv` pour le parcours principal.
- **Aucun moteur de langage** pour les rangs 4 et 8 ni pour l'audit de catalogue ; deux moteurs locaux pour le dernier approfondissement, comme indiqué plus haut.
- **Aucun GPU n'est requis par les carnets eux-mêmes** : le besoin en calcul est celui des moteurs que vous servez.

Les carnets écrivent sur l'instance (articles de test, comptes, clients OAuth) et nettoient derrière eux. Exécutez-les sur l'instance jetable, jamais sur un site en service.

## Pour aller plus loin

*Niveau Recherche.*

- **Un catalogue générique donne à l'agent un pouvoir maximal et une compréhension minimale.** L'audit le mesure ; concevoir les verbes métier qui manquent est le troisième exercice du carnet d'audit, et le parcours 3 du [cas d'usage éditorial](../../04-Cas-Usage-livresagites/livresagites-parcours.md) décrit une installation dont le serveur en expose.
- **La dérive d'un catalogue entre deux versions** — des outils ajoutés, retirés ou renommés, et l'agent qui comptait sur l'ancien nom — fait l'objet du quatrième exercice du même carnet.
- **Ce qu'un agent a le droit de faire ne se règle pas dans son prompt.** La note [Cadrer les agents](../../../cadrer-les-agents.md) sépare l'intention, la portée et l'autorité, et prend la réversibilité de l'action comme critère de décision.

## Ressources

- [Les fonctionnalités par l'API](../README.md) — l'ordre complet de la chaîne et les autres sous-séries.
- [Comparatif Open WebUI et AI Engine](../../02-Comparatif/comparatif-owui-vs-ai-engine.md#mcp-model-context-protocol) — le MCP vu des deux plateformes.
- [Architecture en modules](../../01-Architecture/architecture-en-modules.md) — la place du serveur MCP dans le plugin.
- [Spécification du protocole MCP](https://modelcontextprotocol.io) — la référence du protocole.
