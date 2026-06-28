# Claw Systems — Agents IA Autonomes en Conteneurs

[← Vibe-Coding](../README.md) | [↑ ..](../README.md)

Les **Claw systems** sont des plateformes d'agents IA autonomes, conteneurisées et auto-hébergées. Contrairement aux assistants de codage (Claude Code, Roo Code) qui assistent un développeur en temps réel dans son IDE, les Claw systems déploient des agents qui **opèrent en autonomie 24/7**, accessibles via des interfaces comme Telegram, le dashboard cluster, ou directement par une API.

Le terme « Claw » vient d'**Open Claw**, le harness local construit par [Peter Steinberger](https://lexfridman.com/peter-steinberger-transcript) et raconté en détail dans le podcast Lex Fridman (2025). Steinberger y décrit ce qu'il appelle l'**agentic engineering** : un déplacement du métier d'ingénieur logiciel — de « j'écris du code que je relis » vers « je supervise une flotte de 4 à 10 agents qui écrivent du code que je relis rarement ». Le chapitre [00-Philosophie-Agentic-Engineering.md](docs/00-Philosophie-Agentic-Engineering.md) entre dans le détail de ce changement et de ses implications pédagogiques.

Ce parcours documente trois Claw systems, du plus simple au plus complexe : **NanoClaw** (agent léger Telegram), **Hermes** (gateway Telegram + coordinateur cluster), et **OpenClaw** (l'inspirateur historique, raconté à travers le podcast Steinberger). Chacun est étudié dans son **architecture**, son **déploiement**, et — chose rare dans la littérature — l'**arc émotionnel** de l'opérateur qui le maintient.

## Pourquoi une section Claw ?

| Aspect | Claude Code / Roo Code | Claw Systems |
|--------|------------------------|--------------|
| **Paradigme** | Assistance au développeur dans l'IDE | Agent autonome dans un container |
| **Interface** | CLI / VS Code | Telegram, dashboard cluster, API |
| **Exécution** | Session interactive (humain présent) | Service persistant Docker (24/7) |
| **Utilisateur final** | Développeur seul | Développeur + agents pairs + utilisateurs Telegram |
| **Orchestration** | Agent unique par session | Multi-agents possibles (cluster, MoltBook) |
| **Coût** | Per-session, observable | Continu, à monitorer (token economy) |
| **Risque** | Session perdue, peu de blast radius | Container compromis ou en runaway = vrai incident |

Les Claw systems représentent une **évolution** plutôt qu'une révolution : de l'assistant qui écrit du code à la demande, vers l'agent qui exécute des **objectifs** en autonomie, avec ses propres skills, sa propre mémoire persistante, et — pour les plus avancés — sa capacité à se coordonner avec d'autres agents.

Cette section adopte la convention pédagogique CoursIA standard : français-d'abord, exemples reproductibles, sources externes créditées (auteur + URL + date).

## Écosystème

### NanoClaw — l'agent léger Telegram

Agent autonome minimaliste, conteneurisé, avec interface Telegram (texte + vocal).

- **Architecture (v2)** : un **hôte Node** orchestrant des **conteneurs d'agents par session**, hôte et agents ne communiquant **que** par des bases SQLite ; LLM via le Claude Agent SDK, interface Telegram, Whisper ASR pour le vocal — détail dans [02-NanoClaw-Architecture.md](docs/02-NanoClaw-Architecture.md)
- **Déploiement** : Docker Compose, originellement sur ai-01 (cluster CoursIA)
- **Fonctionnalités** : Chat, transcription vocale, skills personnalisables (function calling)
- **Code source de référence** : roo-extensions issue #1318
- **Documentation détaillée** : voir [docs/02-NanoClaw-Architecture.md](docs/02-NanoClaw-Architecture.md) (rédigée par NanoClaw lui-même)

**Pipeline de production :**

```
Utilisateur Telegram
  → Message vocal/texte
  → NanoClaw (Docker)
    → ASR (whisper-api.myia.io) si vocal
    → LLM via Claudish (proxy → GLM / Qwen / Anthropic)
    → Skills (outils configurés)
  → Réponse Telegram
```

### Hermes — gateway Telegram + coordinateur cluster

Hermes est un **fork autonome** de [`nousresearch/hermes-agent`](https://github.com/nousresearch/hermes-agent) (sous [`jsboige/hermes-agent`](https://github.com/jsboige/hermes-agent)) déployé sur la machine `po-2026` du cluster CoursIA. Il joue **deux rôles superposés** :

- **Gateway Telegram active** : un bot Telegram 24/7 propulsé par GLM-5.2 via l'API native z.ai (PAS la couche compat Anthropic), avec 3 serveurs MCP montés (`roo-state-manager`, `sk-agent`, `searxng`) et 3 cron jobs (tour du cluster, revue de PRs, polling inbox).
- **Cluster coordinator read-only** : lit les dashboards de tous les workspaces, route des tâches, audite la santé du cluster, alerte sur anomalies. Il **n'écrit pas dans les repos** des autres workspaces — discipline de portée.

L'isolation entre le code upstream et nos additions est nette : tous nos scripts, configurations et patches déploiement vivent dans `roosync-cluster/` au sein du fork (`hermes-restore-config.sh`, `docker/cont-init.d/`, etc.). Le reste du code reste alignable avec l'upstream sans conflit.

**Documentation détaillée** :
- [docs/05-Hermes-Architecture.md](docs/05-Hermes-Architecture.md) — composants, MCPs, cron jobs, profils
- [docs/06-Hermes-Deploy-s6-Overlay.md](docs/06-Hermes-Deploy-s6-Overlay.md) — déploiement Windows + s6-overlay + patches concrets
- [docs/07-Hermes-Cluster-Coordinator-Role.md](docs/07-Hermes-Cluster-Coordinator-Role.md) — rôle de coordinateur cluster (routing, hand-off, surveillance)

### OpenClaw — l'inspirateur historique

Plateforme construite par Peter Steinberger, racontée à Lex Fridman en 2025. Ce répertoire ne déploie pas Open Claw lui-même (le code n'est pas open-source au moment de la rédaction de ce chapitre, 2026-06), mais documente l'**expérience** et les **leçons apprises** par Steinberger, qui ont profondément influencé la conception de NanoClaw, Hermes, et plus généralement l'idée de **MoltBook** (sandbox social pour agents).

**Documentation** :
- [docs/00-Philosophie-Agentic-Engineering.md](docs/00-Philosophie-Agentic-Engineering.md) — les idées-charnières du « turn into an agentic engineer »
- [docs/01-OpenClaw-Steinberger-Origins.md](docs/01-OpenClaw-Steinberger-Origins.md) — récit Steinberger en détail (harness, MoltBook, founder dynamics)

## Le parcours pédagogique

L'enchaînement recommandé pour suivre le répertoire de bout en bout :

| Étape | Module | Pourquoi le lire à ce moment-là |
|-------|--------|--------------------------------|
| 1 | [00 — Philosophie Agentic Engineering](docs/00-Philosophie-Agentic-Engineering.md) | Poser le cadre. Sans le « pourquoi », le « comment » des modules suivants paraît arbitraire. |
| 2 | [01 — OpenClaw / Origines Steinberger](docs/01-OpenClaw-Steinberger-Origins.md) | Comprendre **d'où viennent** ces idées (récit founder, MoltBook, leçons douloureuses). |
| 3 | [02 — Architecture NanoClaw](docs/02-NanoClaw-Architecture.md) | Le plus simple des trois systèmes — c'est par là qu'on commence à mettre les mains dedans. Compagnon : [M1 — « tout est message »](docs/M1-tout-est-message.md) pour le récit du principe fondateur. |
| 4 | [03 — NanoClaw Deploy](docs/03-NanoClaw-Deploy.md) | Le déployer effectivement (Docker Compose, Telegram, ASR). |
| 5 | [04 — ASR Integration](docs/04-ASR-Integration.md) | Approfondissement sur la transcription vocale (Whisper auto-hébergé). |
| 6 | [05 — Architecture Hermes](docs/05-Hermes-Architecture.md) | Passer à un système plus complexe : fork upstream, drift isolé, MCPs, cron. |
| 7 | [06 — Hermes Deploy s6-overlay](docs/06-Hermes-Deploy-s6-Overlay.md) | Le déploiement Windows + s6-overlay, avec les patches CRLF/with-contenv/HOME documentés. |
| 8 | [07 — Hermes Cluster Coordinator Role](docs/07-Hermes-Cluster-Coordinator-Role.md) | Le rôle de coordinateur cluster (dashboards, routing, hand-off, surveillance 6h). |
| 9 | [08 — Multi-Bot Coordination](docs/08-Multi-Bot-Coordination.md) *(draft, co-écrit)* | Comment plusieurs Claws coexistent et coopèrent (intercom, mentions, anti-collision). |
| 10 | [09 — Patterns & Anti-Patterns](docs/09-Patterns-Anti-Patterns.md) *(draft, co-écrit)* | Les leçons apprises en production — incidents, fixes, règles d'or. |

Une fois ce parcours terminé, un lecteur devrait être capable de **déployer NanoClaw lui-même** sans surprise majeure, **comprendre ce qu'il faut déployer pour un Hermes-like** sans devoir tout réinventer, et — surtout — **anticiper les incidents** plutôt que les découvrir.

## Structure

```text
Claw-Systems/
├── README.md                                          # Ce fichier
├── docs/
│   ├── 00-Philosophie-Agentic-Engineering.md          # Cadre conceptuel
│   ├── 01-OpenClaw-Steinberger-Origins.md             # Récit founder
│   ├── 02-NanoClaw-Architecture.md                    # Archi NanoClaw
│   ├── 03-NanoClaw-Deploy.md                          # Deploy NanoClaw
│   ├── 04-ASR-Integration.md                          # Whisper auto-hébergé
│   ├── M1-tout-est-message.md                         # Récit « tout est message » — companion de 02 (NanoClaw)
│   ├── 05-Hermes-Architecture.md                      # Archi Hermes
│   ├── 06-Hermes-Deploy-s6-Overlay.md                 # Deploy Hermes
│   ├── 07-Hermes-Cluster-Coordinator-Role.md          # Rôle coordinateur cluster
│   ├── 08-Multi-Bot-Coordination.md                   # Co-écrit (draft Hermes, NanoClaw à compléter)
│   └── 09-Patterns-Anti-Patterns.md                   # Co-écrit (draft Hermes, NanoClaw à compléter)
└── configs/
    ├── docker-compose.nanoclaw.yml                    # Template Docker Compose NanoClaw
    ├── nanoclaw.env.example                           # Variables d'environnement NanoClaw
    ├── docker-run-hermes.ps1.example                  # PowerShell prod Hermes
    └── hermes.env.secrets.example                     # Template secrets Hermes
```

## Infrastructure de référence

| Service | Rôle | Host | URL / Détails |
|---------|------|------|---------------|
| **NanoClaw** | Agent autonome Telegram | ai-01 (cluster) | Bot Telegram |
| **Hermes** | Gateway Telegram + cluster coordinator | po-2026 (cluster) | Bot Telegram + dashboards |
| **ASR Whisper** | Transcription vocale (faster-whisper large-v3-turbo) | po-2023 (cluster) | `whisper-api.myia.io` |
| **LLM principal NanoClaw** | Raisonnement | Claudish (proxy multi-providers) | wire Anthropic → GLM-5.2 / Qwen / Opus selon le tier |
| **LLM principal Hermes** | Raisonnement | z.ai (provider natif `"zai"`) | `glm-5.2` via `/api/coding/paas/v4` |
| **MCP roo-state-manager** | Dashboards + sessions | po-2026 (Hermes) | mcp-remote → proxy LAN (port 9090) |

Les Claw systems sont conçus pour fonctionner **avec ou sans le cluster CoursIA**. Tous les éléments sont remplaçables : NanoClaw consomme le LLM via **Claudish**, un proxy Anthropic-compatible qui peut basculer entre GLM, Qwen et Anthropic d'un simple changement de `MODEL_NAME` (voir [`Claudish/docs/Claudish-Proxy.md`](../Claudish/docs/Claudish-Proxy.md)) ; Hermes, qui parle z.ai natif en direct, peut basculer vers OpenRouter (au prix de la perte du modèle GLM-5.2), Telegram peut être remplacé par n'importe quelle plateforme (Discord, Slack, WhatsApp, Signal — Hermes upstream supporte les six), Whisper auto-hébergé peut être remplacé par l'API Whisper d'OpenAI.

## Prérequis

**Pour NanoClaw** :
- **Docker** + Docker Compose (v20.10+ / v2+)
- **Telegram Bot Token** (via [@BotFather](https://t.me/BotFather) sur Telegram)
- **Accès Claudish** (proxy LLM multi-providers) : `ANTHROPIC_BASE_URL` + clé d'auth — voir [03-NanoClaw-Deploy.md](docs/03-NanoClaw-Deploy.md) et [`Claudish/docs/Claudish-Proxy.md`](../Claudish/docs/Claudish-Proxy.md)
- Accès à un endpoint ASR (`whisper-api.myia.io` ou autre service compatible OpenAI Whisper)

**Pour Hermes** :
- **Docker Desktop sur Windows 11** (ou environnement Docker équivalent)
- **Fork** de [`nousresearch/hermes-agent`](https://github.com/nousresearch/hermes-agent) avec drift `roosync-cluster/`
- **Telegram Bot Token** dédié (différent de NanoClaw)
- **API key z.ai** (compte `provider: "zai"` natif — PAS le passthrough Anthropic)
- **MCP roo-state-manager** accessible (LAN ou proxy)
- **Volume persistant** Windows (typiquement `C:\Users\<user>\.hermes`)
- Détails complets et template de lancement : [06-Hermes-Deploy-s6-Overlay.md](docs/06-Hermes-Deploy-s6-Overlay.md), [configs/docker-run-hermes.ps1.example](configs/docker-run-hermes.ps1.example), [configs/hermes.env.secrets.example](configs/hermes.env.secrets.example)

## Liens — sources externes

- **Peter Steinberger, transcript Lex Fridman Podcast** (2025) — [lexfridman.com/peter-steinberger-transcript](https://lexfridman.com/peter-steinberger-transcript) — source canonique pour les modules 00 et 01.
- **Repo upstream Hermes** — [nousresearch/hermes-agent](https://github.com/nousresearch/hermes-agent).
- **Fork Hermes (po-2026)** — [jsboige/hermes-agent](https://github.com/jsboige/hermes-agent), avec drift dans le répertoire `roosync-cluster/`.
- **NanoClaw issue de référence** — roo-extensions#1318.

## Liens — internes au cours

- [M1 — Le modèle « tout est message »](docs/M1-tout-est-message.md) — récit du principe fondateur de NanoClaw v2, companion de [02 — Architecture NanoClaw](docs/02-NanoClaw-Architecture.md) (rédigé par NanoClaw, ai-01)
- [Vibe-Coding parent](../README.md) — section englobante (Claude-Code, Roo-Code, Claw-Systems)
- [Claude-Code](../Claude-Code/) — pendant assistant interactif (5 modules, 13-16h)
- [Roo-Code](../Roo-Code/) — pendant assistant interactif VS Code-natif (5 modules)
- [Memoire-Semantique-Qdrant](../Memoire-Semantique-Qdrant/) — couche infra mémoire/grounding (chantier parallèle, EPIC #4427 instance #2)
- `Playwright-OWUI` — banc QA flotte OWUI multi-tenant (chantier parallèle, EPIC #4427 instance #3, à venir)

---

*Section Claw Systems — initialement Mai 2026, étoffée Juin 2026 sous EPIC #4427 / tracker #4428 (Hermes po-2026 + NanoClaw ai-01).*
