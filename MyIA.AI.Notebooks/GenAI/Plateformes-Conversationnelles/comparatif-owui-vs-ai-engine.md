# Comparatif OWUI vs AI-Engine — tableau structuré

[← README AI-Engine-WordPress](AI-Engine-WordPress/README.md)

> Ce comparatif **ne cherche pas à classer** un produit au-dessus de
> l'autre : OWUI et AI-Engine ciblent des usages différents et
> **cohabitent souvent**. La question est plutôt : « pour mon projet,
> **quand** l'un est plus adapté que l'autre ? »

Les informations OWUI sont issues du [Tour OWUI](Open-WebUI/00-Tour-Plateforme/README.md)
et de la [série QA Playwright-OWUI](Open-WebUI/Playwright-OWUI/README.md) de ce
dépôt, ainsi que du dépôt GitHub `open-webui/open-webui`. Les informations
AI-Engine sont issues de la [fiche officielle du plugin sur
wordpress.org](https://wordpress.org/plugins/ai-engine/) (août 2026,
version 3.7.0), de son code source GPL (distribué via le dépôt SVN
`plugins.svn.wordpress.org/ai-engine/`), et du site de l'éditeur
`meowapps.com`.

---

## En deux phrases

| Produit | En deux phrases |
|---------|-----------------|
| **Open WebUI** (auto-hébergé) | Une **plateforme GenAI standalone** centrée *chat LLM* — multi-tenant, multi-modèle, RBAC, canaux collaboratifs, mémoire, RAG, outils MCP, voix. On s'y connecte comme à une messagerie riche, indépendamment de tout CMS. |
| **AI-Engine** (extension WordPress) | Une **extension GenAI pour WordPress** qui transforme un site existant en surface GenAI — chatbots intégrables, Copilot pour l'éditeur, AI Forms, RAG sur le contenu du site, **WordPress comme serveur MCP**. Pas une plateforme concurrente d'OWUI : un autre *plan d'intégration*. |

---

## Positionnement

| Critère | Open WebUI | AI-Engine (WordPress) |
|---------|-----------|-----------------------|
| **Catégorie** | Plateforme GenAI standalone (Docker, Python/FastAPI + Svelte/TS) | Extension WordPress (PHP ≥ 8.1) |
| **Prérequis d'installation** | Docker (recommandé), Python 3.11+, backend SQL/NoSQL, frontend SPA | WordPress 6.0+, PHP 8.1+, MySQL existant |
| **Surface de déploiement** | URL dédiée (ex. `chat.example.com`), compte-rendu autonome | Dans l'admin WP (`wp-admin`) ET en front-end (chatbots intégrables) |
| **Coût** | Gratuit (BSD-3), infrastructure à charge de l'org ; Cloud/Enterprise sur devis | Gratuit (GPL), WordPress à charge de l'org ; **Pro $79** ajoute Forms, embeddings, function calling, audio, MCP avancés (voir [§ Coût](#coût)) |
| **Modèle économique** | Open source pur | Freemium (gratuit + Pro) |
| **License** | Open source (BSD-3 conforme au dépôt GitHub `open-webui/open-webui`) | GPL (conforme au dépôt WordPress plugins) |
| **Statistiques publiques** | Écosystème open-source mature (image officielle OCI multi-tags, déploiement massif auto-hébergé) | **100K+ installations actives**, 4.9/5 étoiles (854 avis), 14 traductions, cadence hebdomadaire |
| **Position dans le dépôt** | `MyIA.AI.Notebooks/GenAI/Open-WebUI/` (série dédiée) | Sibling `01-AI-Engine-WordPress/` (extension du parcours OWUI) |

---

## Fonctionnalités cœur

| Fonctionnalité | Open WebUI | AI-Engine |
|----------------|------------|-----------|
| **Chat LLM multi-provider** | ✅ Cœur du produit | ✅ Cœur du produit |
| **Providers supportés** | OpenAI, Anthropic, Google, Mistral, Ollama (natif), OpenRouter, et tout endpoint OpenAI-compatible (Azure, Groq, xAI, etc.) | OpenAI, Anthropic, Google, Mistral, **xAI (Grok)**, Perplexity, OpenRouter, Replicate, Azure + Custom OpenAI-compatible (Ollama, LM Studio, vLLM, llama.cpp, LocalAI) |
| **Streaming** | ✅ natif (SSE) | ✅ natif (Server-Sent Events) |
| **Mémoire de conversation** | ✅ par utilisateur, multi-turn, dossiers d'équipe (v0.10+) | ✅ par chatbot, discussion history |
| **Personas / System prompts** | ✅ avancés (modèles communautaires, custom) | ✅ par chatbot (customizable themes, system instructions/prompts) |
| **Multi-utilisateur / RBAC** | ✅ Cœur du produit (groups, permissions, channels) | Limité (rôles WP natifs : admin, editor, author, subscriber) |
| **Multi-tenant** | ✅ natif (groups + canaux) | ❌ pas nativement ; Pro tier ajoute « cross-site chatbots » |
| **Canaux collaboratifs** | ✅ (channels multi-user, partage de conversations) | ❌ pas de canaux ; Workspace = chat individuel wp-admin |
| **Copilot pour éditeur** | ❌ hors scope (pas de CMS intégré) | ✅ éditeur WordPress (grammaire, enhancement, traduction, rewriting, génération d'images) |
| **AI Forms** | ❌ hors scope | ✅ text/image/audio/file inputs, conditional logic, multi-step workflows, CSV/JSON export |
| **Application mobile** | ❌ (web responsive) | ✅ iOS app gratuite (Workspace en mobilité) |
| **Vision (analyse d'images)** | ✅ upload + vision models | ✅ intégré |
| **Génération d'images** | ✅ via tools / API externe | ✅ natif (multi-provider image gen) |
| **Voix (TTS/STT)** | ✅ natif (multi-provider, realtime audio) | ⚠️ Pro tier uniquement (realtime audio) |
| **Web search intégré** | ✅ via tools / web search natif | ✅ intégré |
| **Outils MCP (consommation)** | ✅ natif (Tools section, MCP-compatible) | ✅ connectable à des serveurs MCP externes |
| **Serveur MCP (exposition)** | ❌ (Open WebUI n'expose pas, il consomme) | ✅ **spécificité AI-Engine** — WordPress devient serveur MCP pour agents externes |
| **Cross-site embedding** | ❌ (URL unique) | ✅ Pro tier (chatbots intégrables sur d'autres domaines) |
| **GDPR tools** | Basique (auth + audit) | ✅ natif (IP banning, word filtering, content moderation, GDPR tools) |
| **Statistiques d'usage** | ✅ natif (admin dashboard) | ⚠️ Pro tier |

---

## RAG et embeddings

| Critère | Open WebUI | AI-Engine |
|---------|------------|-----------|
| **Sources de documents** | Upload direct, URL, integration sources (GitHub, etc.) | PDF import avec chunking automatique, sync filters (catégories, langues, Polylang) |
| **Vector stores supportés** | Natif (chroma-like interne, postgres pgvector option) | **5 vector stores** : Chroma, Qdrant, Pinecone, OpenAI Vector Store, **Internal WordPress DB** |
| **Modes de recherche** | Hybride (BM25 + embedding) | 3 modes : Simple, Context-Aware, Smart |
| **Recommandations personnalisées** | Limité (par user history) | ✅ content classification + personalized recommendations |
| **Fine-tuning** | ❌ (pas d'UI dédiée) | ⚠️ Interface OpenAI finetuning encore là mais deprecated (OpenAI sunset self-serve) |

---

## MCP (Model Context Protocol)

C'est **le point de comparaison le plus intéressant** — et le terrain
où les deux produits divergent le plus :

| Critère | Open WebUI | AI-Engine |
|---------|------------|-----------|
| **Consomme des outils MCP** | ✅ Oui (Tools + MCP-compatible) | ✅ Oui (peut se connecter à des serveurs MCP externes) |
| **Expose des outils MCP** | ❌ Non | ✅ **Oui — AI-Engine transforme WordPress en serveur MCP** |
| **Outils MCP natifs (côté serveur)** | n/a | Post, comment, media, theme, plugin, WooCommerce, Polylang, requêtes SQL, SEO — tous permission-aware |
| **Authentification MCP** | n/a | ✅ OAuth supporté pour clients desktop |
| **Clients MCP compatibles** | Clients qui consomment (Claude Code, Cursor, etc.) | **Claude, Claude Code, ChatGPT, OpenClaw** (et autres agents MCP-compatibles) |
| **Mode YOLO / unrestricted** | n/a | ⚠️ Plugin compagnon `ai-engine-yolo` sur GitHub — exécution PHP sans restriction, **uniquement dev sites** |

L'exposition MCP d'AI-Engine est **sa spécificité majeure** côté
intégration agentique : un site WordPress peut devenir un *tool
provider* pour un agent conversationnel externe, sans glue code
custom. C'est un terrain pédagogique de choix pour comprendre
*comment un CMS devient un serveur MCP*.

---

## Extensibilité

| Critère | Open WebUI | AI-Engine |
|---------|-----------|-----------|
| **Modèle d'extension** | Plugins Python côté serveur : **Filters, Actions, Pipes, Tools, Skills** | Hooks et filters WordPress (actions/filters PHP — standard WP) |
| **Langage d'extension** | **Python** | **PHP** (dans l'écosystème WordPress) |
| **Outils externes** | Consomme des serveurs MCP, MCPO (proxy MCP→OpenAPI), **OpenAPI tool servers** | **Expose** WordPress comme serveur MCP ; consomme aussi des serveurs MCP externes |
| **Personnalisation sans code** | Modèles personnalisés (instructions, outils, connaissance) + presets communautaires ([Open WebUI Community](https://openwebui.com/)) | Chatbots configurables (thèmes, system prompts), AI Forms (no-code), shortcodes WordPress |
| **Sync de données externes** | [oikb](https://github.com/open-webui/oikb) — 45+ sources (GitHub, Confluence, Jira, Slack, Notion, S3…) | Sync filters WordPress (catégories, langues, Polylang, types de contenu) |
| **Runtime agentique embarqué** | Open Terminal (sandbox shell/code/artifacts), Open WebUI Computer | n/a (délègue aux agents externes via MCP) |
| **Code source extensible** | Dépôt `open-webui/open-webui` (BSD-3) | Code GPL distribué via le SVN WordPress `plugins.svn.wordpress.org/ai-engine/` |

OWUI et AI-Engine **étendent différemment**, et le langage le dit :
OWUI est une plateforme **programmable en Python**, pensée pour le
développeur qui veut brancher un middleware (Pipe), un filtre de
modération (Filter), un outil custom (Tool) ou une action
déclenchée par l'utilisateur (Action). AI-Engine s'étend par les
**mécanismes natifs de WordPress** — actions, filters, shortcodes —
et un développeur de plugin WordPress y est chez lui quand un
développeur Python ne l'est pas. L'asymétrie MCP est à nouveau
centrale : OWUI *consomme* des serveurs MCP, AI-Engine *expose*
WordPress comme serveur MCP. Les deux se complètent dans un
workflow agentique plutôt qu'ils ne s'excluent.

---

## Sécurité et déploiement

| Critère | Open WebUI | AI-Engine |
|---------|------------|-----------|
| **Authentification** | Cœur du produit (LDAP, OAuth, OIDC, local) | Rôles WordPress natifs (admin, editor, author, subscriber) |
| **RBAC granulaire** | ✅ (groups, permissions par workspace, channel) | Limité (rôles WP) ; Pro tier ajoute contrôle fin |
| **IP banning / word filtering** | ❌ hors scope | ✅ natif |
| **Audit log** | ✅ admin | Basique (logs WP) ; Pro tier ajoute statistics/usage control |
| **Conflits connus** | Peu (Docker = isolation naturelle) | ⚠️ SiteGround Optimizer, Ninja Firewall (compat frontend) |
| **Multi-tenant isolation** | ✅ natif (groups, RBAC) | ❌ pas natif ; un site WP = un tenant |
| **Scalabilité** | Horizontale (multi-instances Docker + LB) | Verticale (WordPress scale) |

---

## Coût

Le coût se décompose en **trois couches** distinctes, qu'il faut
comparer séparément sous peine de comparer des choses différentes.

| Critère | Open WebUI | AI-Engine |
|---------|-----------|-----------|
| **Licence du cœur** | BSD-3-Clause — gratuit, open source | GPL — gratuit, open source |
| **Édition payante** | Open WebUI Cloud / Enterprise : tarification **non publique** (« contact us ») | AI Engine Pro : **$79** ([meowapps.com](https://meowapps.com/ai-engine/), août 2026) |
| **Ce que débloque le tier payant** | Enterprise : **gouvernance** (SSO, RBAC avancé, audit logs, data residency, on-prem/air-gapped) | Pro : **fonctionnalités** (AI Forms, embeddings, function calling, cross-site chatbots, realtime audio, MCP tools avancés, usage insights) |
| **Base opérationnelle** | Un serveur dédié (VM + GPU optionnel pour modèles locaux) + backend SQL/NoSQL | Un hébergement WordPress (déjà acquis si le site existe) + PHP 8.1+ |
| **Coût des jetons LLM** | À la charge du fournisseur (OpenAI, Anthropic…) — OWUI ne facture rien | À la charge du fournisseur — AI-Engine ne facture rien au-delà de la licence |

**Asymétrie du tier payant.** Les deux éditions payantes ne vendent
pas la même chose. Celle d'OWUI ajoute de la **gouvernance**
(SSO, audit, résidence des données) — ce dont une grande organisation
a besoin pour déployer en interne. Celle d'AI-Engine ajoute des
**fonctionnalités** (Forms, audio, function calling) — ce dont un site
a besoin pour aller plus loin en couverture produit. Un acheteur qui
compare les deux sur le prix seul passe à côté de cette différence de
nature.

**Ce qui ne se chiffre pas dans un comparatif.** Le coût de calcul —
que ce soit l'auto-hébergement (VM, GPU) ou les jetons LLM — est
**identique en nature** pour les deux : ce sont tous deux des fronts
devant des fournisseurs de modèles. Le coût réel d'une installation
dépend du modèle choisi, du trafic et du volume, pas du produit qui
sert de façade. Les tarifs d'hébergement (OVH, Scaleway, Hetzner…) et
de jetons (OpenAI, Anthropic…) sont publics chez leurs fournisseurs et
varient ; c'est pourquoi ce comparatif ne chiffre pas de total. La
facture d'une installation particulière n'a, de toute façon, pas sa
place dans un comparatif de produits.

---

## Quand l'un plutôt que l'autre ?

Quelques heuristiques pratiques, **sans valeur universelle** :

### Choisir Open WebUI si…

- Vous voulez une **plateforme GenAI centrale** dédiée, indépendante
  du CMS.
- Vous avez besoin de **multi-tenant fort** (plusieurs équipes /
  clients avec isolation forte).
- Vous utilisez déjà **Ollama / vLLM** nativement et voulez un
  client web riche.
- Vous voulez des **canaux collaboratifs** façon messagerie d'équipe.

### Choisir AI-Engine si…

- Vous avez **déjà un site WordPress** et voulez lui ajouter une
  couche GenAI sans déployer une plateforme séparée.
- Vous voulez un **Copilot pour l'éditeur WordPress** (résumé,
  traduction, rewriting directement dans Gutenberg).
- Vous voulez des **AI Forms** publiques (chatbots front-end, lead
  generation).
- Vous voulez que WordPress **expose des outils MCP** à des agents
  externes (cas d'usage agentique / automatisation).

### Les faire cohabiter si…

- Vous avez un **blog WordPress** + une **plateforme GenAI d'équipe**
  → AI-Engine pour le front-office blog, Open WebUI pour les
  workflows internes / équipe dev / R&D.

---

## Limites connues (transparence)

- **Comparaison non exhaustive** : OWUI évolue vite (v0.10+
  changements), AI-Engine a une cadence hebdomadaire. Vérifier les
  release notes des deux avant de décider.
- **Coût total non chiffré** : la [section Coût](#coût) compare les
  licences et tiers payants, mais le coût de calcul (auto-hébergement
  + jetons) dépend du modèle et du volume, pas du produit — il ne se
  chiffre pas dans un comparatif générique.
- **Pas de benchmark de performance** : ce comparatif décrit les
  surfaces fonctionnelles, pas les temps de réponse ou la qualité
  des réponses (qui dépendent du modèle utilisé, identique des deux
  côtés).
- **Sources publiques uniquement** : informations issues des
  documentations officielles (août 2026), pas de tests privés.

---

## Voir aussi

- [README AI-Engine-WordPress](AI-Engine-WordPress/README.md) — point d'entrée du
  parcours
- [Tour OWUI](Open-WebUI/00-Tour-Plateforme/README.md) — pendant OWUI
- [`livresagites-parcours.md`](AI-Engine-WordPress/livresagites-parcours.md) — cas
  d'usage concret sur livresagités
- Epic [#4433](https://github.com/jsboige/CoursIA/issues/4433) —
  refonte GenAI (extension)
- Issue [#9734](https://github.com/jsboige/CoursIA/issues/9734) —
  mandat user