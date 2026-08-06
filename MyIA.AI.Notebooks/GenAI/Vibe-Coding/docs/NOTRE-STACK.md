# Notre Stack — le harnais réel derrière les ateliers Vibe-Coding

[← Vibe-Coding](../README.md) | [↑ ..](../README.md)

Les ateliers de cette série ([Claude Code](../Claude-Code/), [Roo Code](../Roo-Code/), [Claw Systems](../Claw-Systems/), [Claudish](../Claudish/)) présentent les assistants de codage agentiques du marché. Ils montrent comment *vibber* — décrire en langage naturel ce que l'on veut construire et laisser l'IA écrire le code — **dans une session unique**, sur un poste.

Ce module présente fidèlement **le harnais que nous utilisons réellement**, au-delà d'une session : un **cluster de machines** qui coordonnent des dizaines d'agents en parallèle, avec une mémoire partagée, une messagerie inter-agents, et des outils maison spécialisés. C'est le « vibe-coding à l'échelle d'une flotte » — le prolongement naturel des ateliers quand on veut automatiser non plus une tâche, mais tout un pipeline de développement continu.

L'objectif pédagogique : comprendre que les briques présentées dans les autres modules (sessions, `CLAUDE.md`, agents, MCP) se composent en une **architecture de coordination** qui est elle-même le sujet le plus original de notre démarche.

## Ce qui est « tû » dans les autres modules

Les ateliers Claude Code / Roo Code introduisent les MCP (Model Context Protocol) avec des serveurs **génériques** du marché : [searxng](https://github.com/searxng/searxng) (recherche web), [github](https://github.com/github/github-mcp-server), [playwright](https://github.com/microsoft/playwright-mcp) (automation navigateur). C'est nécessaire pour démarrer, mais ça laisse dans l'ombre la partie la plus originale — **nos propres serveurs MCP**, écrits pour les besoins spécifiques du cluster :

| MCP maison | Rôle réel | Documentation pérenne |
|------------|-----------|----------------------|
| **roo-state-manager** | Le cœur de la coordination : ~34 outils pour les dashboards multi-machines, la messagerie inter-agents, le navigateur de conversations, l'indexation sémantique (Qdrant) et la recherche dans le code. Détailé ci-dessous. | [docs/reference/architecture_mcp_roo.md](../../../../docs/reference/architecture_mcp_roo.md) |
| **qc-mcp-lite** | Backtests QuantConnect (compile, exécution, lecture de métriques) via l'API cloud, sans scripts REST ad-hoc. | [docs/qc/quantconnect.md](../../../../docs/qc/quantconnect.md) |
| **jupyter-papermill** | Exécution et validation de notebooks Jupyter (Python, .NET, Lean) — le socle de la règle « notebooks committés AVEC leurs sorties ». | [docs/reference/kernels-runtime.md](../../../../docs/reference/kernels-runtime.md) |
| **sk-agent** | Vision et agents multi-modèles (Semantic Kernel) — analyse qualitative de figures, comparaison de rendus. | [docs/reference/common-commands.md](../../../../docs/reference/common-commands.md) |
| **searxng**, **playwright**, **markitdown** | Recherche web canonique, automation navigateur (dont exécution des notebooks QuantConnect en fallback), conversion PDF/DOCX → Markdown. | [docs/reference/common-commands.md](../../../../docs/reference/common-commands.md) |

Ces serveurs sont déclarés dans `.mcp.json` (configuration de projet) et `~/.claude.json` (configuration globale). **Aucun secret n'est committé** : les jetons vivent dans `.secrets/master.env` (gitignoré), propagés vers les `.env` consommateurs par un script dédié (cf. [docs/genai/secrets-management.md](../../../../docs/genai/secrets-management.md)).

## roo-state-manager et RooSync — la coordination cluster

`roo-state-manager` est notre serveur MCP le plus original. Il expose environ **34 outils** organisés autour de trois capacités :

1. **Dashboards multi-machines (RooSync).** Trois types de tableaux partagés — `global`, `machine`, `workspace` — où chaque agent poste son état de cycle (`[INFO]`, `[CLAIMED]`, `[DONE]`, `[ASK USER]`…). Un agent qui démarre une session lit le dashboard de son workspace pour retrouver les directives du coordinateur ; il poste son bilan en fin de session. L'auto-condensation préemptive (à ~92 %) garde les tableaux à taille bornée sans intervention manuelle.

2. **Messagerie inter-agents.** Des messages directs (DM) prioritaires (`LOW` / `MEDIUM` / `HIGH` / `URGENT`) entre machines, qui survivent à la condensation des dashboards. Le DM est le canal de décision du coordinateur : un dispatch HIGH oriente un worker vers une tâche précise.

3. **Mémoire conversationnelle et sémantique.** Un navigateur de conversations (`conversation_browser`) pour relire l'historique des sessions, et une indexation vectorielle (Qdrant) + recherche dans le code (`codebase_search`) qui permettent à un agent de retrouver du contexte pertinent sans tout relire.

L'architecture interne complète (gestion des processus MCP, fusion des configurations, cycle de vie des serveurs) est détaillée dans [docs/reference/architecture_mcp_roo.md](../../../../docs/reference/architecture_mcp_roo.md).

## Le pattern coordinateur / workers

Au-delà des outils, le harnais repose sur un **pattern d'orchestration** :

- **Un coordinateur** (`ai-01`) qui fusionne les PR, arbitre les conflits, dispatche le travail, et veille à ce qu'aucune demande utilisateur ne stagne. Il ne code pas lui-même le contenu métier — il merge et route.
- **Des workers** (`po-2023`, `po-2024`, `po-2025`, `po-2026`…) spécialisés par famille (Lean, QuantConnect, GenAI, .NET, Symbolic AI…). Chaque worker **pioche dans le pool d'issues ouvertes** (GitHub), pose un `[CLAIMED]` avant de commencer, livre une PR atomique (un sujet), et rapporte sur son dashboard. Un worker **ne merge jamais** lui-même — c'est la règle d'isolement des responsabilités.
- **Des cycles cron.** Chaque worker est réveillé à intervalle régulier (cron session-only), exécute un cycle de travail autonome, et se rendort. Le coordinateur tourne sur sa propre cadence. Le « ping-pong » entre les deux est entretenu par un ré-arme explicite en fin de session.
- **Des règles auto-chargées.** Les conventions du cluster vivent dans [`.claude/rules/`](../../../../.claude/rules/) (anti-régression, hygiène PR, honnêteté des notebooks, secrets…) — chargées automatiquement à chaque session, elles codifient les leçons des incidents passés plutôt que de répéter les erreurs.

Le détail des machines (GPUs, spécialisations, topologie) est dans [docs/reference/cluster-agents.md](../../../../docs/reference/cluster-agents.md), et la configuration des agents/skills/rules dans [docs/reference/claude-code-config.md](../../../../docs/reference/claude-code-config.md).

## Pourquoi c'est le prolongement naturel des ateliers

Un atelier « découverte Claude Code » (module 01) apprend à démarrer une session, écrire un `CLAUDE.md`, utiliser les `@`-mentions. Le module 05 (Automatisation avancée) introduit skills, subagents et MCP **génériques**. Ce module-ci montre la **même composition poussée à l'échelle d'un cluster** : les `CLAUDE.md` deviennent un harnais de règles auto-chargées, les MCP génériques sont complétés par des MCP maison spécialisés, et la session unique devient un cycle coordonné parmi dizaines.

La lecture recommandée après cet atelier :
1. Les autres modules de cette série (pour la mécanique session-unique).
2. [docs/reference/cluster-agents.md](../../../../docs/reference/cluster-agents.md) (la topologie réelle).
3. [docs/reference/architecture_mcp_roo.md](../../../../docs/reference/architecture_mcp_roo.md) (les internals du coordinateur).

Ce module est **anonymisé** : il décrit les rôles et les familles, pas les hôtes sensibles ni les secrets. Les exemples d'outils sont réels et pointent vers la documentation pérenne existante — il n'y a pas de duplication de contenu, seulement des liens.
