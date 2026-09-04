# 03 — Functional : le plugin exploré par l'API

[← README AI-Engine-WordPress](../README.md)

Les notebooks de ce niveau **appellent réellement l'API** d'une instance
WordPress jetable dédiée au plugin AI Engine — montage en 5 étapes,
corpus synthétique 100 % (Maison Valmont), credentials via `.env` jamais
commité. Deux lectures y cohabitent : une **chaîne continue** « par son
API », où chaque notebook reprend la question laissée ouverte par le
précédent, et des **compagnons autonomes**, exploitables seuls.

## Les cinq sous-séries

| Sous-série | Contenu |
|---|---|
| [03-1-Chatbots](03-1-Chatbots/README.md) | Chatbots et assistants : documents JSON, faces visiteur et éditeur, pièces jointes, sorties structurées, dérive |
| [03-2-Forms](03-2-Forms/README.md) | AI Forms : le formulaire comme contenu WordPress, et le formulaire conditionnel comme machine à états |
| [03-3-RAG-et-Embeddings](03-3-RAG-et-Embeddings/README.md) | Découpage de corpus long, environnements de vecteurs partitionnés |
| [03-4-MCP-Server](03-4-MCP-Server/README.md) | WordPress serveur MCP : outils, consentement OAuth, audit du catalogue |
| [03-5-Multi-Provider](03-5-Multi-Provider/README.md) | Socle de la série, régie des environnements, évaluation des modèles |

## La chaîne « par son API » — ordre de lecture

Onze notebooks, dans l'ordre où la série les a construits : chaque étape
reprend la question laissée ouverte par la précédente.

1. [`presenter-ai-engine-par-son-api.ipynb`](03-5-Multi-Provider/presenter-ai-engine-par-son-api.ipynb)
   pose le socle : instance, catalogue des routes `mwai/v1`, première
   completion réelle avec compte de tokens.
2. [`configurer-chatbots-par-l-api.ipynb`](03-1-Chatbots/configurer-chatbots-par-l-api.ipynb)
   traite les chatbots comme des **documents JSON** — lecture,
   duplication, écriture read-modify-write — puis mesure honnêtement ce
   que les instructions d'un persona changent, et ce qu'elles ne changent
   pas.
3. [`administrer-les-formulaires-par-l-api.ipynb`](03-2-Forms/administrer-les-formulaires-par-l-api.ipynb)
   montre l'autre style d'API du plugin : le formulaire est un
   **contenu** WordPress (custom post type `mwai_form`, CRUD unitaire,
   corps Gutenberg, rendu public par shortcode) — et mesure la frontière
   gratuite/Pro (du contenu rendu, pas encore des champs).
4. [`piloter-wordpress-par-mcp.ipynb`](03-4-MCP-Server/piloter-wordpress-par-mcp.ipynb)
   ouvre la seconde face du plugin : **WordPress comme serveur MCP** —
   endpoint JSON-RPC `mcp/v1/http`, handshake avec négociation de
   version, catalogue de 43 outils à JSON Schema, et de vrais
   `tools/call` en lecture puis en écriture — la frontière
   d'authentification mesurée à 401 sur chaque méthode.
5. [`brancher-plusieurs-providers-par-l-api.ipynb`](03-5-Multi-Provider/brancher-plusieurs-providers-par-l-api.ipynb)
   ouvre la régie des **environnements** : la matrice
   `ai_<usage>_default_env` lue et écrite par l'API, l'interrogation
   d'un provider, le cycle déclarer/basculer/rétablir — et le piège
   mesuré par accident : `settings/update` **ne met pas à jour, il
   remplace**. La matrice croisée laisse des cases vides, dont la case
   json.
6. [`parler-au-chatbot-en-visiteur-par-l-api.ipynb`](03-1-Chatbots/parler-au-chatbot-en-visiteur-par-l-api.ipynb)
   ouvre la troisième face, celle du **navigateur d'un visiteur
   anonyme** (namespace `mwai-ui/v1`) : la page publique n'embarque
   aucun jeton, l'amorçage passe par `start_session`, la conversation
   par `chats/submit` au `X-WP-Nonce` — et la nuance : un nonce est un
   anti-CSRF, pas une authentification.
7. [`obtenir-des-donnees-structurees-par-l-api.ipynb`](03-1-Chatbots/obtenir-des-donnees-structurees-par-l-api.ipynb)
   ferme la dernière veine « non prouvée » : la route `/ai/json`, qui
   ignore `envId`/`model` et lit **la case json de la matrice d'usages**
   laissée vide à l'étape 5. Le notebook reproduit l'erreur à froid,
   remplit la case par read-modify-write, obtient du JSON réellement
   exploitable, puis mesure honnêtement la promesse : le **null
   silencieux** du parser PHP et la nature de la contrainte de format.
8. [`autour-du-consent-oauth-du-serveur-mcp.ipynb`](03-4-MCP-Server/autour-du-consent-oauth-du-serveur-mcp.ipynb)
   reprend la question laissée ouverte par l'étape 4 : comment un client
   tiers se connecte-t-il **sans les clés de l'admin** ? Serveur
   d'autorisation OAuth 2.0 embarqué, enregistrement dynamique, PKCE,
   consentement réservé aux administrateurs, code → token → appel MCP
   réel au bearer délégué — puis révocation mesurée.
9. [`interroger-lassistant-de-lediteur-par-l-api.ipynb`](03-1-Chatbots/interroger-lassistant-de-lediteur-par-l-api.ipynb)
   complète le tour des **quatre faces** du plugin — admin, agent,
   visiteur, éditeur — par celle de celui qui écrit : la route
   `mwai-ui/v1/editor/submit`, dont le contrat se découvre par les
   refus, et où la frontière gratuite/Pro est inscrite dans la réponse
   elle-même. La route est stateless : le tour isolé oublie, le tour qui
   re-apporte `messages` souvient.
10. [`donner-une-memoire-ephemere-au-chatbot-par-l-api.ipynb`](03-1-Chatbots/donner-une-memoire-ephemere-au-chatbot-par-l-api.ipynb)
    ouvre la cinquième surface : la famille `mwai-ui/v1/files/*`, celle
    des **pièces jointes** — éphémères par architecture (TTL d'une heure
    prouvé par soustraction), partitionnées par utilisateur, avec le
    miroir admin `mwai/v1/openai/files/*`. Le stockage est fait ; la
    question devient son usage.
11. [`joindre-un-fichier-au-chatbot-par-l-api.ipynb`](03-1-Chatbots/joindre-un-fichier-au-chatbot-par-l-api.ipynb)
    ferme le dossier pièces jointes par la question qui suit le
    stockage : **comment un fichier téléversé entre-t-il dans une
    completion ?** La réponse mesurée est un drame en trois actes — le
    contrat mal nommé (200 silencieux), le texte annoté puis jeté, le
    fichier réellement vu.

## Les compagnons autonomes

Sept notebooks de ce niveau se lisent seuls, sans suivre la chaîne :

- [`eval-choisir-son-modele.ipynb`](03-5-Multi-Provider/eval-choisir-son-modele.ipynb)
  — cinq propriétés discriminantes contre n'importe quel endpoint
  compatible OpenAI, en stdlib pur sans clé ni réseau : « je l'ai
  essayé, il répond bien » devient un tableau reproductible.
- [`ingestion-corpus-long-rag.ipynb`](03-3-RAG-et-Embeddings/ingestion-corpus-long-rag.ipynb)
  — découper un catalogue avant de l'indexer : la dégradation du
  retrieval vient du chunking, pas de l'embedder.
- [`separer-les-environnements-de-vecteurs.ipynb`](03-3-RAG-et-Embeddings/separer-les-environnements-de-vecteurs.ipynb)
  — fuite cross-environnement et accident de réindexation, mesurés sur
  un vector store partitionné.
- [`auditer-un-serveur-mcp.ipynb`](03-4-MCP-Server/auditer-un-serveur-mcp.ipynb)
  — un serveur MCP utile expose les verbes du métier, pas les tables.
- [`consommer-vs-exposer-le-mcp.ipynb`](03-4-MCP-Server/consommer-vs-exposer-le-mcp.ipynb)
  — les deux sens du fil : chevauchement cross-catalogue, redondance
  d'écriture dangereuse.
- [`auditer-un-formulaire-conditionnel.ipynb`](03-2-Forms/auditer-un-formulaire-conditionnel.ipynb)
  — un formulaire à branchement est une machine à états implicite :
  sept champs engendrent treize états.
- [`mesurer-la-derive-dun-copilot.ipynb`](03-1-Chatbots/mesurer-la-derive-dun-copilot.ipynb)
  — le gate humain à chaque étape ne protège pas la chaîne : des
  destructrices complémentaires perdent la moitié du document.

## Note de méthode

L'ordre de lecture ci-dessus n'est pas inventé : il est restauré depuis
le README racine antérieur à la réorganisation en sous-séries
(refonte `#13434`), où la série « par son API » était présentée dans
l'ordre où chaque notebook reprend la question laissée ouverte par le
précédent. Les README de sous-séries, eux, indexent les mêmes notebooks
par thème — les deux lectures sont complémentaires.

Voir le [README AI-Engine-WordPress](../README.md) pour le parcours
complet (architecture, comparatif Open WebUI, cas d'usage).
