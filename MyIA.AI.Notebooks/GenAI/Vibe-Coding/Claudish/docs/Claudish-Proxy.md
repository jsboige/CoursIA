# Claudish — Proxy Anthropic-Compatible Multi-Providers

> Sources : [github.com/MadAppGang/claudish](https://github.com/MadAppGang/claudish) (upstream) · [github.com/jsboige/claudish](https://github.com/jsboige/claudish) (déploiement MyIA) · [claudish.com](https://claudish.com)

Ce document décrit **Claudish** tel qu'il est déployé sur le cluster MyIA : un proxy compatible avec l'API Anthropic qui fait tourner Claude Code, les agents autonomes et les bots sur **n'importe quel fournisseur de modèles**. Il explique le principe, le router à 3 providers, la façon de connecter un bot, et les avancées du fork.

---

## 1. Le principe — un seul format wire, plusieurs providers

**Claude Code** (et le SDK, et tous les bots qui parlent le protocole Anthropic) adressent toujours `https://api.anthropic.com`. Claudish s'intercale entre le client et le fournisseur :

```
        parle Anthropic wire                traduit vers le provider cible
client ──────────────────────► claudish ─────────────────────────────► GLM / Qwen / Anthropic
(Claude Code, bot, SDK)        (proxy)        (OpenAI / Gemini / Anthropic / Ollama…)
```

- **En entrée**, claudish expose l'API Anthropic à l'identique (`/v1/messages`). Côté client, rien ne change.
- **En sortie**, il traduit vers le wire du provider cible (OpenAI, Gemini, Anthropic natif, Ollama…).
- **Résultat** : un agent conçu pour Claude peut parler à GLM, Qwen, Gemini, etc., sans toucher à son code.

### Upstream vs déploiement MyIA

| | Upstream (MadAppGang) | Déploiement MyIA (jsboige) |
|---|---|---|
| **Rôle** | Outil open-source : « Claude Code. Any Model. » | Fork opérationnel du cluster |
| **Forme** | CLI local (`claudish --model …`) | Service Docker persistant, exposé via passerelle IIS |
| **Routing** | Fallback automatique multi-providers | **No-fallback** : 1 provider budgeté par tier (voir §3) |
| **Ops** | — | Capture, surveillance trafic, watchdog, concurrence plafonnée (voir §6) |

---

## 2. Topologie de déploiement

```
┌──────────────┐   ┌─────────────────┐   ┌──────────────────┐   ┌─────────────────┐
│ Claude Code  │   │  models.myia.io │   │  claudish        │   │  Provider cible │
│  / agent     ├──►│  (IIS reverse-  ├──►│  po-2023:3000    ├──►│  GLM / Qwen /   │
│  / bot       │   │   proxy, HTTPS) │   │  (Docker, Hono)  │   │  Anthropic      │
└──────────────┘   └─────────────────┘   └──────────────────┘   └─────────────────┘
                          TLS, cache IIS        traduction wire + concurrence
```

- **claudish** tourne dans un conteneur Docker sur `po-2023`, port `3000`.
- La passerelle **IIS** (`models.myia.io`) termine le TLS et reverse-proxie vers le conteneur.
- Tous les clients (agents Claude Code, bots Hermes/NanoClaw) pointent sur `https://models.myia.io`.

---

## 3. Le router à 3 providers (no-fallback)

C'est le cœur du déploiement MyIA. Au lieu de laisser le proxy basculer silencieusement entre providers (ce qui change la qualité et le coût en plein milieu d'une conversation), **chaque tier de modèle a un unique provider budgeté** :

| Tier | Modèle visible | Provider réel | Route | Budget |
|------|----------------|---------------|-------|--------|
| **Opus** (réflexion lourde) | `claude-opus-4-8` | Anthropic natif | `ai-01` | Max Claude |
| **Sonnet** (usage courant) | `glm-5.2` | Z.AI GLM Coding Plan | `gc@glm-5.2` | Coding Plan |
| **Haiku** (rapide, léger) | `qwen3.6-35b-a3b` | vLLM self-hosté | `vllm-myia@…` | GPU maison (po-2023) |

**Principe no-fallback :**
- Sur un burst (rate-limit), claudish **backoff** puis réessaie le **même** provider.
- Sur une panne franche, il **fail-hard** (erreur explicite) — il ne bascule **jamais** vers un autre provider en silence.
- Raison : un switch de provider à l'insu de l'agent dégrade silencieusement la qualité et rend les coûts imprévisibles. Mieux vaut une erreur visible qu'une dérive cachée.

### Contrôle de concurrence

Certains providers ne supportent pas les requêtes parallèles illimitées. Claudish plafonne la concurrence **par provider** :

- **Haiku / Qwen (vLLM)** — cap `1` (séquentiel). Un GPU ne fait pas 4 prefills de 120K tokens en parallèle sans se gripper (`max-num-batched-tokens` saturé → famine GPU).
- **Sonnet / GLM Coding** — cap `8`. Une rafale de longs streams GLM qui s'empilent congestionne l'event-loop du proxy et remonte en 503 côté IIS.

Au-delà du cap, les requêtes attendent en file FIFO et passent dès qu'un slot se libère — elles ne sont **jamais rejetées** (priorité absolue : ne jamais bloquer l'agent, voir §6).

---

## 4. Connecter un agent Claude Code

Côté Claude Code (ou le SDK), on pointe simplement le base URL vers claudish :

```powershell
$env:ANTHROPIC_BASE_URL = "https://models.myia.io"
$env:ANTHROPIC_AUTH_TOKEN = "<clé claudish>"
$env:ANTHROPIC_MODEL = "glm-5.2"          # tier Sonnet → Z.AI GLM
# ou laisse claudish choisir le tier via le profil actif
```

C'est tout. Claude Code croit parler à Anthropic ; claudish route en réalité vers GLM/Qwen/Anthropic selon le modèle demandé.

---

## 5. Connecter un bot — le trick du nom Claude (leçon Hermes)

Les bots autonomes (Hermes, NanoClaw) parlent parfois un wire non-Anthropic (OpenAI `/chat/completions`). Or **claudish ne sert que le wire Anthropic** : un `/chat/completions` renvoie `404`.

Deux approches, du plus simple au plus invasif :

| Option | Quoi faire | Quand |
|--------|------------|-------|
| ⭐ **Remap de nom (recommandée)** | Le bot envoie un **nom de modèle Claude** (ex. `claude-sonnet-4-6`). Claudish le remappe vers le modèle budgeté du tier (`glm-5.2` via `gc@`) selon le profil actif. **1 ligne de config côté bot, aucun patch de wire.** | Le bot sait juste poster un `model` dans sa requête Anthropic. |
| Patch du wire | Faire parler le bot Anthropic natif (messages/tools au format Anthropic) | Le bot a déjà une intégration Anthropic, ou on contrôle son code. |

> **Leçon Hermes (juin 2026)** : le bot Hermes bloquait le routing. Le fix n'a **pas** été de patcher le wire du bot, mais simplement de lui faire envoyer un nom Claude — claudish s'occupe du reste via le `modelMap` du profil. C'est le pattern réutilisable pour tout bot qui s'intègre au cluster.

**Détail qui mord** : les slugs de modèle doivent correspondre exactement. `glm-5-2` (tiret) → 404 ; `glm-5.2` (point) → OK. À vérifier en cas d'erreur de routing inexpliquée.

---

## 6. Avancées du fork MyIA

Au-delà du routing de base, le fork `jsboige/claudish` ajoute ce qui fait tourner un proxy en production 24/7 :

| Avancée | Rôle |
|---------|------|
| **Never-hang (priorité #1)** | Un flux se termine **toujours**, même si le provider coupe mid-stream ou renvoie du vide. Un agent bloqué est jugé pire qu'une erreur propre. |
| **Overload 529** | Un 429 « quota » (que le client peut interrompre en stoppant le tour) est converti en `529 overloaded_error` + `Retry-After`, pour que le client **réessaie** au lieu d'abandonner. |
| **Contrôle de concurrence** | `LocalModelQueue` (cap GPU) + `ConcurrencyLimiter` (cap provider remote), indépendants par provider (voir §3). |
| **Interception web search** | Les appels `web_search` des providers sont interceptés et servis via SearXNG (MCP) — ne bloque jamais l'agent (dégradation gracieuse en texte). |
| **Support `/compact` non-streaming** | Les requêtes `stream:false` (condensation de contexte) sont rebufferisées en un message JSON, pas en SSE. |
| **Channel mode (MCP)** | Sessions de modèle async avec notifications push (`notifications/claude/channel`). |
| **Capture & surveillance** | Capture des corps de requête (`CLAUDISH_CAPTURE_DIR`), scripts `traffic-live/summary/history.ps1`, watchdog auto-restart. |

---

## 7. Variables d'environnement clés

| Variable | Effet |
|----------|-------|
| `ANTHROPIC_BASE_URL` | URL claudish (les clients pointent ici au lieu de `api.anthropic.com`) |
| `ANTHROPIC_AUTH_TOKEN` | Clé d'auth claudish |
| `ANTHROPIC_MODEL` | Modèle/tier par défaut (`glm-5.2`, `claude-opus-4-8`, `qwen3.6-35b-a3b`) |
| `providerConcurrency` (config) | Cap de concurrence par provider (`{ "glm-coding": 8 }`) |
| `customEndpoints` (config) | Endpoints nommés (`vllm-myia@…`) avec leur propre `maxConcurrency` |
| `SEARXNG_URL` / `SEARXNG_MCP_URL` | Backends de recherche web interceptés |
| `CLAUDISH_CAPTURE_DIR` | Active la capture des corps pour reprod offline |

---

## 8. Troubleshooting

| Symptôme | Cause | Fix |
|----------|-------|-----|
| `404` sur `/chat/completions` | Le bot parle wire OpenAI ; claudish ne sert que l'wire Anthropic | Option ⭐ : envoyer un nom de modèle Claude (remap), ou faire parler le bot Anthropic |
| `404` ou erreur de routing sur `glm-5-2` | Slug erroné (tiret au lieu du point) | Utiliser `glm-5.2` |
| `503` intermittents côté IIS | Congestion du proxy (longs streams empilés sur un provider plafonné) | Vérifier les caps `providerConcurrency` ; le backoff/limiter doit lisser la rafale |
| Agent qui « freeze » (socket closed) | Flux non terminé proprement | Ne devrait plus arriver (never-hang) — si oui, c'est un bug à reporter |

---

## 9. Liens & lectures

- **Upstream** : [MadAppGang/claudish](https://github.com/MadAppGang/claudish) — code source, README, docs.
- **Déploiement MyIA** : `jsboige/claudish` (fork), serveur `po-2023`, passerelle `models.myia.io`.
- **Bots consommateurs** : voir [Claw-Systems/](../Claw-Systems/) (Hermes, NanoClaw).
- **Agents Claude Code consommateurs** : voir [Claude-Code/](../Claude-Code/).

---

*Section Claudish — Juin 2026. Proxy Anthropic-compatible multi-providers du cluster MyIA : un format wire en entrée, trois providers budgetés en sortie, jamais de bascule silencieuse.*
