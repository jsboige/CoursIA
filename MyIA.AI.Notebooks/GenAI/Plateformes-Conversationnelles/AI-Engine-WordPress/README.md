# AI-Engine (WordPress) — extension GenAI côté contenu

[← Documentation GenAI](../../README.md) | [↑ Plateformes conversationnelles](../README.md) | [Open-WebUI](../Open-WebUI/README.md) | [Tour OWUI](../Open-WebUI/00-Tour-Plateforme/README.md) | [QA Playwright-OWUI](../Open-WebUI/Playwright-OWUI/README.md)

> **Parcours découverte.** Ce dossier présente **AI-Engine**, l'extension
> WordPress de Jordy Meow, comme **presqu'équivalent d'Open WebUI** côté
> *site de contenu*. La question n'est pas « quel produit choisir en
> absolu » — les deux ciblent des usages différents — mais « quand l'un
> est plus adapté que l'autre » pour un projet donné. Cible : qui a déjà
> un WordPress, qui évalue Open WebUI, qui veut voir MCP intégré à un CMS.

---

## Pourquoi une plateforme voisine d'Open WebUI ?

La série voisine **[Open-WebUI](../Open-WebUI/README.md)** documente la plateforme éponyme :
auto-hébergée, multi-tenant, centrée *chat LLM*. Mais ce n'est pas la
seule interface GenAI réaliste : beaucoup de sites de contenu (blogs,
forums, boutiques WooCommerce, sites éditoriaux) ont déjà un WordPress
installé. Plutôt que de poser Open WebUI *à côté* de WordPress, on peut
**ajouter la couche GenAI directement dans WordPress** via l'extension
**AI-Engine**. C'est ce que ce parcours explore — en gardant Open WebUI
comme point de comparaison pour les fonctionnalités communes (chat,
RAG, outils MCP, personas).

Le projet **livresagités** — une installation WordPress de maison
d'édition, avec workflow de manuscrits, comité de lecture et catalogue
WooCommerce — sert de **terrain d'observation** concret. Aucune donnée
de ce site n'est reproduite ici : ce dossier ne transmet que des
structures et des comptages, sans contenu, sans nom, et sans capture
d'écran (voir la note de méthode du
[parcours détaillé](04-Cas-Usage-livresagites/livresagites-parcours.md#note-de-méthode--pourquoi-il-ny-a-aucune-capture)).

---

## Vue d'ensemble (5 min)

| Parcours | Format | Où |
|---|---|---|
| 1. Tour de l'UI (admin + front) | markdown + captures instance jetable | [00-Tour-Plateforme/](00-Tour-Plateforme/README.md) |
| 2. Architecture et surface fonctionnelle | markdown | [01-Architecture/](01-Architecture/README.md) |
| 3. Comparatif OWUI vs AI-Engine | tableau structuré | [02-Comparatif/](02-Comparatif/comparatif-owui-vs-ai-engine.md) |
| 4. Cas d'usage livresagités | markdown observé | [04-Cas-Usage-livresagites/](04-Cas-Usage-livresagites/livresagites-parcours.md) |
| 5. Sécurité et méthode | markdown + notebook | [06-Securite-et-Methode/](06-Securite-et-Methode/README.md) |
| 6. Récit de bout en bout, par l'API | notebooks exécutés | série « par son API » dans [03-Functional/](03-Functional/) |

## Comment lire — 3 portes d'entrée

- **Vous découvrez AI-Engine** → [00-Tour-Plateforme/](00-Tour-Plateforme/README.md)
  (l'interface en écrans commentés) puis [01-Architecture/](01-Architecture/README.md).
- **Vous voulez comparer à Open WebUI** → [02-Comparatif/](02-Comparatif/comparatif-owui-vs-ai-engine.md).
- **Vous allez l'installer sur un WordPress** → [03-Functional/](03-Functional/)
  (fonctionnalités par thème), [04-Cas-Usage-livresagites/](04-Cas-Usage-livresagites/livresagites-parcours.md)
  (le terrain réel) et [06-Securite-et-Methode/](06-Securite-et-Methode/README.md)
  (la méthode sans-fuite).

Les sections du parcours suivent le même rythme : **ce que c'est**
(la fonctionnalité en deux phrases), **comment ça marche** (architecture
et séquence d'appels), **comparaison OWUI** (l'équivalent ou son
absence), **référence livresagités** (un cas d'usage réel, sans PII).

Les notebooks de la série « par son API » appellent réellement l'API
d'une instance jetable dédiée (montage en 5 étapes dans
[`instance-jetable/`](instance-jetable/), corpus synthétique 100 %
« Maison Valmont ») ; configuration par copie de
[`.env.example`](.env.example) vers `.env` — jamais commité.

---

## Index par thème

### Tour et QA

- [Tour de la plateforme](00-Tour-Plateforme/README.md) — l'interface d'AI-Engine en douze écrans commentés, captures sur instance jetable
- [QA Playwright-AI-Engine](05-Playwright-AI-Engine/README.md) — ce que l'API ne voit pas : l'interface d'administration défait des écritures REST, et pas toujours

### Architecture et comparatif

- [Vue d'ensemble, fonctionnalités cœur, multi-provider](01-Architecture/README.md) — regroupé depuis la racine
- [Architecture en modules](01-Architecture/architecture-en-modules.md) — le découpage en modules du plugin
- [Comparatif OWUI vs AI-Engine](02-Comparatif/comparatif-owui-vs-ai-engine.md) — tableau structuré des fonctionnalités

### Cas d'usage

- [Parcours livresagités](04-Cas-Usage-livresagites/livresagites-parcours.md) — 88 outils MCP dont 24 métier, six environnements d'embeddings, le terrain d'observation réel

### Fonctionnel — chatbots et assistants

- [configurer-chatbots-par-l-api](03-Functional/03-1-Chatbots/configurer-chatbots-par-l-api.ipynb) — les chatbots sont des documents JSON : lire, dupliquer, écrire (read-modify-write) — et mesurer ce que les instructions d'un persona changent réellement
- [parler-au-chatbot-en-visiteur](03-Functional/03-1-Chatbots/parler-au-chatbot-en-visiteur-par-l-api.ipynb) — la face navigateur : page sans jeton, `start_session` seul endpoint public, et nonce = anti-CSRF, pas authentification
- [interroger-lassistant-de-lediteur](03-Functional/03-1-Chatbots/interroger-lassistant-de-lediteur-par-l-api.ipynb) — la face éditeur : nonce `wp_rest`, contrat découvert par les refus, frontière gratuite/Pro inscrite dans la réponse
- [donner-une-memoire-ephemere](03-Functional/03-1-Chatbots/donner-une-memoire-ephemere-au-chatbot-par-l-api.ipynb) — la famille `files/*` : upload par refus, TTL d'une heure prouvé par soustraction, partition par utilisateur
- [joindre-un-fichier-au-chatbot](03-Functional/03-1-Chatbots/joindre-un-fichier-au-chatbot-par-l-api.ipynb) — un fichier joint a trois destins : ignoré (200 silencieux), annoté-puis-jeté (tokens à l'appui), réellement vu (l'image bicolore)
- [mesurer-la-derive-dun-copilot](03-Functional/03-1-Chatbots/mesurer-la-derive-dun-copilot.ipynb) — le gate humain à chaque étape ne protège pas la chaîne : des destructrices complémentaires perdent la moitié du document
- [obtenir-des-donnees-structurees](03-Functional/03-1-Chatbots/obtenir-des-donnees-structurees-par-l-api.ipynb) — la route `/ai/json` : la case json de la matrice d'usages, son remplissage, le null silencieux du parser

### Fonctionnel — formulaires

- [administrer-les-formulaires-par-l-api](03-Functional/03-2-Forms/administrer-les-formulaires-par-l-api.ipynb) — le formulaire est un contenu WordPress (CPT `mwai_form`) : CRUD unitaire, rendu par shortcode, frontière gratuite/Pro mesurée
- [auditer-un-formulaire-conditionnel](03-Functional/03-2-Forms/auditer-un-formulaire-conditionnel.ipynb) — un formulaire à branchement est une machine à états implicite : sept champs engendrent treize états, coût LLM et champs morts émergents

### Fonctionnel — RAG et embeddings

- [ingestion-corpus-long-rag](03-Functional/03-3-RAG-et-Embeddings/ingestion-corpus-long-rag.ipynb) — découper un catalogue avant de l'indexer : la dégradation du retrieval vient du chunking, pas de l'embedder
- [separer-les-environnements-de-vecteurs](03-Functional/03-3-RAG-et-Embeddings/separer-les-environnements-de-vecteurs.ipynb) — fuite cross-environnement et accident de réindexation, mesurés sur un vector store partitionné

### Fonctionnel — serveur MCP

- [piloter-wordpress-par-mcp](03-Functional/03-4-MCP-Server/piloter-wordpress-par-mcp.ipynb) — WordPress serveur MCP : handshake JSON-RPC, catalogue à JSON Schema, vrais `tools/call` en écriture
- [consommer-vs-exposer-le-mcp](03-Functional/03-4-MCP-Server/consommer-vs-exposer-le-mcp.ipynb) — les deux sens du fil : chevauchement cross-catalogue (Jaccard sur verbe, cible), la redondance d'écriture est dangereuse
- [auditer-un-serveur-mcp](03-Functional/03-4-MCP-Server/auditer-un-serveur-mcp.ipynb) — un serveur MCP utile expose les verbes du métier, pas les tables : classification CRUD/métier + distance au schéma
- [autour-du-consent-oauth](03-Functional/03-4-MCP-Server/autour-du-consent-oauth-du-serveur-mcp.ipynb) — l'escalier des refus de l'OAuth embarqué : PKCE, consent admin mécanisé, token délégué — puis révocation mesurée

### Fonctionnel — multi-provider

- [presenter-ai-engine-par-son-api](03-Functional/03-5-Multi-Provider/presenter-ai-engine-par-son-api.ipynb) — le socle de la série : instance jetable, catalogue des routes `mwai/v1`, première completion réelle
- [brancher-plusieurs-providers](03-Functional/03-5-Multi-Provider/brancher-plusieurs-providers-par-l-api.ipynb) — la matrice `ai_<usage>_default_env` lue et écrite — et le piège : `settings/update` ne met pas à jour, il remplace
- [eval-choisir-son-modele](03-Functional/03-5-Multi-Provider/eval-choisir-son-modele.ipynb) — cinq propriétés discriminantes contre n'importe quel endpoint : « je l'ai essayé, il répond bien » devient un tableau reproductible

### Sécurité et méthode

- [Sécurité et méthode](06-Securite-et-Methode/README.md) — pas de secret dans les supports, posture PII, et le notebook qui mesure ce que le smoke test ne voit pas

---

## Sécurité — pas de secret dans les supports

La politique complète — aucun secret exposé, aucune capture d'écran,
aucun contenu privé livresagités, constantes de substitution dans les
exemples, `.env` jamais commités — vit dans
[06-Securite-et-Methode/](06-Securite-et-Methode/README.md).

---

## Voir aussi

- [Plateformes conversationnelles](../README.md) — point d'entrée de la catégorie
- [README d'Open-WebUI](../Open-WebUI/README.md) — dossier voisin
- [Tour OWUI](../Open-WebUI/00-Tour-Plateforme/README.md) — pendant « chat LLM » centré
- [QA Playwright-OWUI](../Open-WebUI/Playwright-OWUI/README.md) — pendant « assurance qualité » de bout en bout
- [`instance-jetable/`](instance-jetable/) — montage en 5 étapes de l'instance de démo, corpus 100 % synthétique
- Epic [#4433](https://github.com/jsboige/CoursIA/issues/4433) —
  refonte pédagogique GenAI (ce parcours en est une extension)
- Issue [#9734](https://github.com/jsboige/CoursIA/issues/9734) —
  mandat user à l'origine de ce dossier
