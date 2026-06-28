# Hermes — Architecture

[← Claw-Systems](../README.md) | [↑ ..](../README.md)

Hermes est un agent conversationnel autonome derivé du projet open-source
**[hermes-agent](https://github.com/nousresearch/hermes-agent)** (Nous Research).
La version deployée dans ce cluster est un [fork](https://github.com/jsboige/hermes-agent)
qui ajoute une couche d'orchestration cluster (RooSync) sans modifier le coeur upstream.

Contrairement a NanoClaw (Telegram + LLM, architecture minimale), Hermes est un
**agent complet** : boucle de raisonnement, appel d'outils, gestion de session
persistante, compression de contexte, skills, et plusieurs surfaces d'interaction
(CLI, TUI, gateway multi-plateformes).

## Origine du projet

| Element | Valeur |
|---------|--------|
| Upstream | [`nousresearch/hermes-agent`](https://github.com/nousresearch/hermes-agent) |
| Fork cluster | [`jsboige/hermes-agent`](https://github.com/jsboige/hermes-agent) |
| Notre drift | `roosync-cluster/` (ADR, scripts, docs) — isole du code upstream |
| Langage | Python 3.11+ (uv), TypeScript (TUI Ink) |
| Licence | voir upstream |

Le principe : **le code upstream reste synchronisable**. Tout ce qui est specifique
au cluster (scripts de deploiement, restore-config, docker, ADR) vit dans
`roosync-cluster/` et n'altere jamais les sources Hermes. Un `git merge upstream/main`
reste donc un merge propre.

## Boucle d'agent (coeur)

```
Message utilisateur → AIAgent._run_agent_loop()   (run_agent.py)
  ├── Assemblage du system prompt   (agent/prompt_builder.py)
  ├── Appel LLM (API OpenAI-compatible, provider au choix)
  ├── Si tool_calls → dispatch via tools/registry.py → execute → boucle
  ├── Si reponse texte → persister la session → retourner
  └── Compression de contexte si approche de la limite de tokens
```

C'est une boucle **ReAct-classique** : l'agent peut enchainer plusieurs appels
d'outils avant de produire une reponse finale. Chaque tour est journalise dans
une session SQLite (`~/.hermes/state.db`, recherche full-text via FTS5).

## Surfaces d'interaction

| Surface | Fichier | Usage |
|---------|---------|-------|
| **CLI** | `cli.py` | Terminal interactif (prompt_toolkit) |
| **TUI** | `ui-tui/` | Interface riche Ink/React via stdio JSON-RPC |
| **Gateway** | `gateway/run.py` | Bot multi-plateformes (Telegram, Discord, Slack, WhatsApp, Signal...) |

En production, Hermes tourne en **gateway** : c'est la surface qui expose le bot
Telegram 24/7. La CLI et la TUI servent au developpement et au debug.

## Chaine de dependances des outils

```
tools/registry.py        (aucune dep, importe par tous les outils)
       ↑
tools/*.py               (chacun s'enregistre via registry.register() a l'import)
       ↑
model_tools.py           (declenche la decouverte des outils)
       ↑
run_agent.py, cli.py, batch_runner.py
```

Cette organisation fait que **l'ajout d'un outil = un nouveau fichier dans `tools/`**
qui s'auto-enregistre. Pas de registre central a maintenir manuellement.

## Provider LLM

Hermes parle l'API **OpenAI-compatible**. N'importe quel provider exposant ce
contrat fonctionne : OpenRouter, OpenAI direct, un serveur vLLM local, ou
**z.ai** (GLM).

Dans ce cluster, Hermes utilise **GLM-5.2 via z.ai natif** :

```yaml
model: glm-5.2
provider: zai            # endpoint natif /api/coding/paas/v4
```

> **Attention :** ne JAMAIS utiliser la couche de compatibilite Anthropic
> (`ANTHROPIC_BASE_URL=https://api.z.ai/api/anthropic`). Cette traduction perd
> le registre d'outils MCP apres une compression de contexte. Voir
> [06-Hermes-Deploy-s6-Overlay.md](06-Hermes-Deploy-s6-Overlay.md).

## Serveurs MCP (Model Context Protocol)

Hermes se connecte a trois serveurs MCP qui lui donnent acces au cluster :

| Serveur | Role |
|---------|------|
| `roo-state-manager` | Coordination : dashboards, conversations, indexation semantique, messagerie inter-machines |
| `sk-agent` | Vision / multi-agent |
| `searxng` | Recherche web canonique |

Les serveurs sont atteints via un proxy MCP LAN (port 9090). Quand le proxy est
indisponible, un fallback local (volume-monte) prend le relais — detail dans le
guide de deploiement.

## Crons integrés

Hermes porte sa propre planification (cron jobs persistés dans `cron/jobs.json`)
en plus du planificateur OS. Trois jobs tournent en production :

| Job | Cadence | Role |
|-----|---------|------|
| `cluster-tour` | 6h | Tour de santé du cluster, lecture dashboards, rapport |
| `pr-review` | planifié | Review de PRs assignées |
| `inbox-poll` | planifié | Scrutation de la messagerie inter-machines |

## Systeme de profils

Plusieurs instances Hermes isolees coexistent via la variable `HERMES_HOME`.
Tout le code doit appeler `get_hermes_home()` (depuis `hermes_constants`) —
**jamais** hardcoder `Path.home() / ".hermes"`, sinon les profils cassent.

| Chemin | Usage |
|--------|-------|
| `~/.hermes/config.yaml` | Tous les reglages (modele, terminal, toolsets, compression) |
| `~/.hermes/.env` | Cles API et secrets **uniquement** |
| `~/.hermes/auth.json` | Identifiants OAuth |
| `~/.hermes/skills/` | Skills actifs |
| `~/.hermes/state.db` | Base de sessions SQLite |

## Points d'entree cles

| Fichier | Role |
|---------|------|
| `run_agent.py` | Classe `AIAgent` — boucle de conversation, dispatch d'outils |
| `cli.py` | `HermesCLI` — CLI interactif |
| `model_tools.py` | Orchestration des outils, `handle_function_call()` |
| `toolsets.py` | Groupements d'outils et presets par plateforme |
| `hermes_state.py` | Stockage de session SQLite + FTS5 |
| `hermes_cli/main.py` | Point d'entree CLI, parsing, profils |
| `hermes_cli/config.py` | Gestion de config, `DEFAULT_CONFIG`, variables d'env |
| `hermes_cli/commands.py` | Registre central des slash commands |
| `gateway/run.py` | `GatewayRunner` — cycle de vie plateformes, routage messages |
| `agent/prompt_builder.py` | Assemblage du system prompt (identite, skills, contexte, memoire) |

## Hermes vs NanoClaw

| Aspect | NanoClaw | Hermes |
|--------|----------|--------|
| **Origine** | Projet maison leger | Fork d'agent open-source complet |
| **Surfaces** | Telegram seulement | CLI + TUI + gateway multi-plateformes |
| **Outils** | Skills simples | Registre d'outils + MCP + skills |
| **Session** | Stateless / leger | SQLite persistant + FTS5 |
| **Rôle cluster** | Bot terminal | Coordinateur (routing, audit) + bot |

Les deux sont complementaires : NanoClaw est le **bot utilisateur final** leger,
Hermes est le **coordinateur** qui voit tout le cluster et route les tâches.

## Liens

- [Guide de deploiement Hermes (s6-overlay)](06-Hermes-Deploy-s6-Overlay.md)
- [Hermes Coordinateur de Cluster](07-Hermes-Cluster-Coordinator-Role.md)
- [Coordination Multi-Bot](08-Multi-Bot-Coordination.md)
- Upstream : [nousresearch/hermes-agent](https://github.com/nousresearch/hermes-agent)
