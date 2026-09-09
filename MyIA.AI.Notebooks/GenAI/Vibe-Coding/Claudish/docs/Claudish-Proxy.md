# Claudish — Proxy Anthropic-Compatible Multi-Providers

> Sources : [github.com/MadAppGang/claudish](https://github.com/MadAppGang/claudish) (upstream) · [github.com/jsboige/claudish](https://github.com/jsboige/claudish) (déploiement MyIA) · [claudish.com](https://claudish.com)

Ce document décrit **Claudish** tel qu'il est déployé sur le cluster MyIA : un proxy compatible avec l'API Anthropic qui fait tourner Claude Code, les agents autonomes et les bots sur **n'importe quel fournisseur de modèles**. Il explique le principe, le router à 3 providers, la façon de connecter un agent (Claude Code) et un bot, les avancées du fork, et les war-stories qui ont forgé son design.

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

### Et Roo Code ?

**Non, Roo Code ne passe pas par claudish.** Les deux outils ne se sont jamais croisés : Roo *déclinait* pile au moment où claudish *émergeait*. Roo s'est donc toujours configuré en **OpenRouter direct** (via l'UI Fournisseurs), et n'a jamais eu besoin du proxy. En pratique, le trafic du proxy est à **100 % du `claude-cli/*`** (Claude Code, le SDK, les bots) — aucune signature Roo, Cline ou OpenRouter.

La raison technique : claudish ne sert que le **wire Anthropic** (`POST /v1/messages`). Un appel OpenAI-style `/chat/completions` renvoie `404`. Roo étant orienté wire OpenAI-compat, il ne peut pas consommer claudish tel quel.

> **Piège de télémétrie** : si vous voyez `cc_entrypoint=claude-vscode` dans les captures de trafic, c'est **Claude Code lancé depuis VS Code**, pas Roo Code. Les deux sont des extensions VS Code différentes ; ne pas les confondre.

**Perspective (successeur Zoo)** : le remplaçant de Roo, **Zoo Code**, est amené à router par claudish — via son provider Anthropic pointé sur `models.myia.io` + un nom de modèle Claude remappé (le même pattern cross-bot que la leçon Hermes ci-dessous). Ce sera une **configuration par poste**, pas une feature du proxy. À suivre côté turf `roo-extensions`.

---

## 5. Connecter un bot — le trick du nom Claude (leçon Hermes)

Les bots autonomes (Hermes, NanoClaw) parlent parfois un wire non-Anthropic (OpenAI `/chat/completions`). Or **claudish ne sert que le wire Anthropic** : un `/chat/completions` renvoie `404`.

Deux approches, du plus simple au plus invasif :

| Option | Quoi faire | Quand |
|--------|------------|-------|
| **Remap de nom (recommandée)** | Le bot envoie un **nom de modèle Claude** (ex. `claude-sonnet-4-6`). Claudish le remappe vers le modèle budgeté du tier (`glm-5.2` via `gc@`) selon le profil actif. **1 ligne de config côté bot, aucun patch de wire.** | Le bot sait juste poster un `model` dans sa requête Anthropic. |
| Patch du wire | Faire parler le bot Anthropic natif (messages/tools au format Anthropic) | Le bot a déjà une intégration Anthropic, ou on contrôle son code. |

> **Leçon Hermes (juin 2026)** : le bot Hermes bloquait le routing. Le fix n'a **pas** été de patcher le wire du bot, mais simplement de lui faire envoyer un nom Claude — claudish s'occupe du reste via le `modelMap` du profil. C'est le pattern réutilisable pour tout bot qui s'intègre au cluster.

**Détail qui mord** : les slugs de modèle doivent correspondre exactement. `glm-5-2` (tiret) → 404 ; `glm-5.2` (point) → OK. À vérifier en cas d'erreur de routing inexpliquée.

---

## 6. Avancées du fork MyIA

Au-delà du routing de base, le fork `jsboige/claudish` ajoute ce qui fait tourner un proxy en production 24/7 :

| Avancée | Rôle |
|---------|------|
| **Never-hang (priorité #1)** | Un flux se termine **toujours**, même si le provider coupe mid-stream ou renvoie du vide. Un agent bloqué est jugé pire qu'une erreur propre. |
| **Overload 529** | Un 429 de **surcharge transitoire** (ou 503) est converti en `529 overloaded_error` + `Retry-After`, pour que le client **réessaie** au lieu d'abandonner ; le 429 « quota » reste distinct (passe tel quel). |
| **Contrôle de concurrence** | `LocalModelQueue` (cap GPU) + `ConcurrencyLimiter` (cap provider remote), indépendants par provider (voir §3). |
| **Interception web search** | Les appels `web_search` des providers sont interceptés et servis via SearXNG (MCP) — ne bloque jamais l'agent (dégradation gracieuse en texte). |
| **Support `/compact` non-streaming** | Les requêtes `stream:false` (condensation de contexte) sont rebufferisées en un message JSON, pas en SSE. |
| **Channel mode (MCP)** | Sessions de modèle async avec notifications push (`notifications/claude/channel`). |
| **Capture & surveillance** | Capture des corps de requête (`CLAUDISH_CAPTURE_DIR`), scripts `traffic-live/summary/history.ps1`, watchdog auto-restart. |

---

## 7. War-stories — trois leçons du fork en production

Ces trois épisodes, extraits de l'historique du fork `jsboige/claudish`, illustrent pourquoi le proxy est conçu *comme il l'est*. Chacun porte une leçon transférable au-delà de claudish.

### 7.1 Architecture par soustraction — le no-fallback (24/06/2026)

Au démarrage, claudish enchaînait les providers en fallback : si GLM rate-limitait, il basculait sur Qwen. **Le problème** : cette bascule se faisait à l'insu de l'agent, en plein milieu d'une conversation — changeant la qualité du modèle et le coût d'un tour sur l'autre, de façon invisible et imprévisible. Pire, le chemin fallback vers Qwen (GPU maison) a grippé le backend à plusieurs reprises (concurrence non bornée sur des contextes longs = famine GPU).

**La décision** n'a pas été d'ajouter du code pour mieux orchestrer les bascules, mais de **le retirer** : suppression de `defaultProvider`, une seule entrée par chaîne. Depuis, sur un burst claudish **backoff** puis réessaie le *même* provider ; sur une panne franche il **fail-hard** (erreur explicite). *Leçon : un fallback silencieux est une dégradation cachée. Mieux vaut une erreur visible qu'une dérive de qualité invisible — et un chemin de code en moins est un bug en moins.*

### 7.2 Never-hang — le proxy qui crash déguisé en bug de stream (commit `8afe19d`, 14/06/2026)

Le symptôme : un gel récurrent sur un workflow CoursIA réel (portage d'un fichier `.cs`, sur `po-2025`). Côté client, cela ressemblait à un bug de lifecycle de stream — messages d'erreur « Content block not found », sockets fermées.

**La cause racine** était tout autre : un block `server_tool_use` de Z.AI déclenchait un handler qui lisait une variable d'index déclarée avec `let` dans un bloc `try` interne, alors que la closure vivait dans le scope externe → `ReferenceError` → **crash du process** → restart du conteneur. Le client ne voyait qu'une socket morte, pas le plantage.

**La leçon transférable** : *un proxy qui crash produit des symptômes de socket-close qui imitent un bug de lifecycle de stream. Quand un client « freeze », il faut **grep les exceptions dans les logs du proxy** avant de partir chasser des race conditions côté stream.* C'est la motivation de la priorité #1 du fork — **never-hang** : un flux se termine *toujours*, même si le provider coupe mid-stream. Un agent bloqué est jugé pire qu'une erreur propre.

### 7.3 Résilience — overload GLM convertie en HTTP 529 (commit `67a5dd0`)

Quand Z.AI est en surcharge, il renvoie du `429` (ou `503`). Un `429` brut, c'est un code « quota » que le client interprète souvent comme *arrêt* — il abandonne le tour au lieu de réessayer. Or une surcharge transitoire de Z.AI se résout typiquement en quelques minutes.

**Le fix** : claudish distingue la surcharge transitoire du quota épuisé, convertit la première en `529 overloaded_error` avec un `Retry-After`, et applique un **backoff patient** (~5 min, 6 retries, schedule 5/10/20/40/80/150 s) côté proxy avant de rendre la main. Le client reçoit un `529` (signal « réessaie ») plutôt qu'un `429` (signal « arrête »). Validé en production : **36 épisodes de surcharge convertis en 529 sur une fenêtre, zéro `429` atteint un client.**

*Leçon : les codes HTTP sont sémantiques (`429` ≠ `529`), et un client bien élevé réessaie sur `529`. Le dogfooding — tester ses propres fixes en prod sur le cluster — a révélé un chemin non couvert (le 429 HTTP-direct) que les tests unitaires n'avaient pas attrapé.*

---

## 8. Variables d'environnement clés

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

## 9. Troubleshooting

| Symptôme | Cause | Fix |
|----------|-------|-----|
| `404` sur `/chat/completions` | Le bot parle wire OpenAI ; claudish ne sert que l'wire Anthropic | Option recommandée : envoyer un nom de modèle Claude (remap), ou faire parler le bot Anthropic |
| `404` ou erreur de routing sur `glm-5-2` | Slug erroné (tiret au lieu du point) | Utiliser `glm-5.2` |
| `503` intermittents côté IIS | Congestion du proxy (longs streams empilés sur un provider plafonné) | Vérifier les caps `providerConcurrency` ; le backoff/limiter doit lisser la rafale |
| Agent qui « freeze » (socket closed) | Flux non terminé proprement | Ne devrait plus arriver (never-hang) — si oui, c'est un bug à reporter |

---

## 10. Liens & lectures

- **Upstream** : [MadAppGang/claudish](https://github.com/MadAppGang/claudish) — code source, README, docs.
- **Déploiement MyIA** : `jsboige/claudish` (fork), serveur `po-2023`, passerelle `models.myia.io`.
- **Bots consommateurs** : voir [Claw-Systems/](../Claw-Systems/) (Hermes, NanoClaw).
- **Agents Claude Code consommateurs** : voir [Claude-Code/](../Claude-Code/).

---

*Section Claudish — Juillet 2026. Proxy Anthropic-compatible multi-providers du cluster MyIA : un format wire en entrée, trois providers budgetés en sortie, jamais de bascule silencieuse.*
