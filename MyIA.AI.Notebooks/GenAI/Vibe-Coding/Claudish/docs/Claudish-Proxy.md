# Claudish — Proxy Multi-Providers, Wires Anthropic et OpenAI

> Sources : [github.com/MadAppGang/claudish](https://github.com/MadAppGang/claudish) (upstream) · [github.com/jsboige/claudish](https://github.com/jsboige/claudish) (déploiement MyIA) · [claudish.com](https://claudish.com)

Ce document décrit **Claudish** tel qu'il est déployé sur le cluster MyIA : un proxy qui fait tourner Claude Code, les agents autonomes et les bots sur **n'importe quel fournisseur de modèles**. Il explique le principe des deux wires d'entrée, la topologie, le router à 3 tiers avec cascade de bascule notifiée, la façon de connecter un agent (Claude Code) et un bot, les avancées du fork, et les war-stories qui ont forgé son design.

> **État documenté au 2026-09-09** (#15418) : ce guide a été réconcilié avec le fork live (commits à l'appui) et des mesures directes du déploiement (`models.myia.io`). Les sections historiques sont datées comme telles.

---

## 1. Le principe — deux formats wire en entrée, plusieurs providers en sortie

**Claude Code** (et le SDK, et les bots qui parlent le protocole Anthropic) adressent toujours `https://api.anthropic.com` ; les clients **wire OpenAI** (GPT-5, Codex, routeurs tiers, notebooks) postent du `/chat/completions`. Claudish accepte **les deux** et s'intercale entre le client et le fournisseur :

```
   wire Anthropic (/v1/messages) OU OpenAI (/v1/chat/completions)
client ────────────────────────────────► claudish ─────────────────────────────► provider cible
(Claude Code, bot, SDK, client OpenAI)    (proxy)     (Anthropic / GLM / MiniMax / Qwen / DeepSeek)
```

- **En entrée**, claudish expose `/v1/messages` (wire Anthropic) **et** `/v1/chat/completions` (wire OpenAI). Mesuré live le 2026-09-09 : un POST sur `https://models.myia.io/v1/chat/completions` répond `200` avec un corps JSON conforme OpenAI.
- **En sortie**, il traduit vers le wire du provider cible (Anthropic natif, Anthropic-compatible comme MiniMax-M3, OpenAI-compatible comme z.ai GLM).
- **Résultat** : un agent conçu pour Claude *ou* pour l'API OpenAI peut parler à GLM, MiniMax, Qwen, Anthropic, etc., sans toucher à son code.

> **Historique (juillet 2026)** : le guide décrivait alors « un seul format wire en entrée » (`/v1/messages` seulement, `/chat/completions` → 404). C'était l'état du déploiement à cette date ; le wire OpenAI en entrée a été exposé et maintenu depuis (le fork livre encore des correctifs dédiés au handler OpenAI en septembre 2026).

### Upstream vs déploiement MyIA

| | Upstream (MadAppGang) | Déploiement MyIA (jsboige) |
|---|---|---|
| **Rôle** | Outil open-source : « Claude Code. Any Model. » | Fork opérationnel du cluster |
| **Forme** | CLI local (`claudish --model …`) | Service Docker persistant, exposé via passerelle IIS + sidecar LAN |
| **Routing** | Fallback automatique multi-providers | **Cascade ordonnée par tier, TTL par step, bascule notifiée** (voir §3) |
| **Wires d'entrée** | Anthropic | Anthropic **et** OpenAI |
| **Ops** | — | Capture, surveillance trafic, watchdog, concurrence plafonnée (voir §6) |

---

## 2. Topologie de déploiement

```
┌──────────────┐   ┌─────────────────┐   ┌──────────────────┐   ┌─────────────────┐
│ Claude Code  │   │  models.myia.io │   │  claudish        │   │  Provider cible │
│  / agent     ├──►│  (IIS reverse-  ├──►│  po-2023:3000    ├──►│  Anthropic /    │
│  / bot       │   │   proxy, HTTPS) │   │  (Docker, Hono)  │   │  GLM / MiniMax /│
└──────────────┘   └─────────────────┘   └──────────────────┘   │  Qwen / DeepSeek│
                          TLS, cache IIS        traduction wire  └─────────────────┘
                                                 + cascade + concurrence
        agents distants (LAN) ──► sidecar ai-01 (192.168.0.46:3000) ──► même claudish
```

- **claudish** tourne dans un conteneur Docker sur `po-2023`, port `3000` (hub).
- La passerelle **IIS** (`models.myia.io`) termine le TLS et reverse-proxie vers le conteneur.
- Le **sidecar ai-01** (`192.168.0.46:3000`) relaie en LAN pour les agents distants.
- Les clients (agents Claude Code, clients OpenAI, bots Hermes/NanoClaw) pointent sur `https://models.myia.io` ou le sidecar selon leur position.

### Authentification client → claudish

Clé proxy **obligatoire** (fork 2026-08), acceptée dans **trois** en-têtes équivalents — vérifié dans le middleware `packages/cli/src/fork/middleware/proxy-auth.ts` du fork et mesuré live le 2026-09-09 :

| En-tête | Forme |
|---|---|
| `x-proxy-key` | `x-proxy-key: <clé>` |
| `x-api-key` | `x-api-key: <clé>` |
| `Authorization` | `Authorization: Bearer <clé>` |

Exceptions : les requêtes `GET` (healthcheck, découverte de modèles) passent sans clé ; le **pass-through Anthropic natif** est exempt (OAuth du client ou swap de clé géré par le handler natif). Toute autre requête sans clé valide reçoit `401 invalid proxy authentication`.

---

## 3. Le router à 3 tiers — cascade ordonnée, bascule notifiée

C'est le cœur du déploiement MyIA. **Chaque tier a un provider nominal budgété** et une **cascade de bascule ordonnée** entre providers de même direction (`degraded>degraded>degraded` ou `improved>improved>improved`) — implémentée dans `packages/cli/src/fork/failover.ts` :

| Tier | Provider nominal | Cascade (état au 2026-08-18) | Direction |
|------|------------------|--------------------------------|-----------|
| **Opus** (réflexion lourde) | Anthropic natif | `qwen-token-plan@qwen3.8-max > gc@glm-5.3 > ds@deepseek-v4-flash` | degraded |
| **Sonnet** (usage courant) | z.ai GLM Coding Plan (GLM-5.3) | `ds@deepseek-v4-flash` (PAYG direct, latéral) | lateral |
| **Haiku** (rapide, léger) | MiniMax-M3 (Anthropic-compatible) | `qwen-token-plan@qwen3.8-max > ds@deepseek-v4-flash` | improved |

**Fonctionnement de la cascade :**
- Chaque step de la cascade a un **TTL indépendant** (échelle `10m/30m/1h/4h/24h`) qui survit à l'armement du rôle — un quota wall hebdomadaire (Qwen) n'est pas re-probé toutes les 10 min pendant que la fenêtre GLM 5h se ré-initialise.
- Sur un burst (rate-limit), claudish **backoff** sur le step courant et passe au suivant quand le TTL expire.
- Sur une panne franche, le step suivant prend la main **avec notice de dégradation explicite** : le marqueur `[claudish] Failover model active` apparaît dans la réponse (observé live le 2026-09-09 lors d'un épuisement du nominal GLM). Les notices existent en deux moments — **onset** (bascule) et **recovery** (retour au nominal), diffusées sur 3 canaux : log proxy, dashboard `workspace-claudish`, client (en-tête/corps SSE).
- Le step final (PAYG direct) est **toujours servi** quand tout le reste est épuisé — l'agent ne meurt jamais, il dégrade avec notification.

> **Historique — l'ère no-fallback (24/06/2026 → 12/08/2026)** : le déploiement a d'abord supprimé tout fallback (voir §7.1). La cascade notifiée l'a remplacée le 2026-08-12 (commit `823e614`) : la bascule existe de nouveau, mais **jamais silencieuse** — c'est la différence avec le fallback d'origine.

### Contrôle de concurrence

Certains providers ne supportent pas les requêtes parallèles illimitées. Claudish plafonne la concurrence **par provider** :

- **GPU self-hosté (vLLM/Qwen)** — cap séquentiel. Un GPU ne fait pas 4 prefills de 120K tokens en parallèle sans se gripper (`max-num-batched-tokens` saturé → famine GPU).
- **GLM Coding** — cap ~8. Une rafale de longs streams GLM qui s'empilent congestionne l'event-loop du proxy et remonte en 503 côté IIS.

Au-delà du cap, les requêtes attendent en file FIFO et passent dès qu'un slot se libère — elles ne sont **jamais rejetées** (priorité absolue : ne jamais bloquer l'agent, voir §6).

---

## 4. Connecter un agent Claude Code

Côté Claude Code (ou le SDK), on pointe simplement le base URL vers claudish :

```powershell
$env:ANTHROPIC_BASE_URL = "https://models.myia.io"
$env:ANTHROPIC_AUTH_TOKEN = "<clé claudish>"
$env:ANTHROPIC_MODEL = "glm-5.3"          # tier Sonnet → Z.AI GLM
# ou laisse claudish choisir le tier via le profil actif
```

C'est tout. Claude Code croit parler à Anthropic ; claudish route en réalité vers GLM/MiniMax/Qwen/Anthropic selon le modèle demandé.

### Et les clients wire OpenAI ?

Un client OpenAI (notebook, GPT-5, Codex, routeur tiers) pointe sa base URL sur le même proxy et utilise le wire `/v1/chat/completions` :

```python
client = OpenAI(base_url="https://models.myia.io/v1", api_key="<clé claudish>")
```

Mesuré live le 2026-09-09 : POST `/v1/chat/completions` → `200` + JSON conforme OpenAI (le champ `model` de la réponse porte l'identité du modèle effectivement servi — utile pour vérifier qu'on n'est pas sur un step de cascade).

### Et Roo Code ?

**Roo Code n'a jamais consommé claudish à ce jour** — mais pour des raisons d'historique, plus de wire. Les deux outils ne se sont jamais croisés : Roo *déclinait* pile au moment où claudish *émergeait* (juin-juillet 2026). Roo s'est donc toujours configuré en **OpenRouter direct** (via l'UI Fournisseurs). À l'époque des mesures, le trafic du proxy était à **100 % du `claude-cli/*`** (Claude Code, le SDK, les bots) — aucune signature Roo, Cline ou OpenRouter. Depuis, le wire OpenAI est exposé : un client Roo serait aujourd'hui techniquement consommable via le mode OpenAI-compatible, mais ce n'est pas la configuration de la flotte.

> **Piège de télémétrie** : si vous voyez `cc_entrypoint=claude-vscode` dans les captures de trafic, c'est **Claude Code lancé depuis VS Code**, pas Roo Code. Les deux sont des extensions VS Code différentes ; ne pas les confondre.

**Perspective (successeur Zoo)** : le remplaçant de Roo, **Zoo Code**, est amené à router par claudish — via son provider Anthropic pointé sur `models.myia.io` + un nom de modèle Claude remappé (le même pattern cross-bot que la leçon Hermes ci-dessous). Ce sera une **configuration par poste**, pas une feature du proxy. À suivre côté turf `roo-extensions`.

---

## 5. Connecter un bot — le trick du nom Claude (leçon Hermes)

Les bots autonomes (Hermes, NanoClaw) parlent parfois un wire non-Anthropic. Depuis l'exposition du wire OpenAI en entrée, un bot OpenAI-native peut poster directement sur `/v1/chat/completions` — mais le pattern le plus robuste reste le **remap de nom** :

| Option | Quoi faire | Quand |
|--------|------------|-------|
| **Remap de nom (recommandée)** | Le bot envoie un **nom de modèle Claude** (ex. `claude-sonnet-4-6`). Claudish le remappe vers le modèle budgeté du tier (`glm-5.3` via `gc@`) selon le profil actif. **1 ligne de config côté bot, aucun patch de wire.** | Le bot sait juste poster un `model` dans sa requête. |
| Wire OpenAI direct | Poster sur `/v1/chat/completions` avec la clé proxy (`Authorization: Bearer` accepté, mesuré 2026-09-09). | Le bot est OpenAI-native et vous voulez la route la plus courte. |
| Patch du wire | Faire parler le bot Anthropic natif (messages/tools au format Anthropic). | Le bot a déjà une intégration Anthropic, ou on contrôle son code. |

> **Leçon Hermes (juin 2026)** : le bot Hermes bloquait le routing. Le fix n'a **pas** été de patcher le wire du bot, mais simplement de lui faire envoyer un nom Claude — claudish s'occupe du reste via le `modelMap` du profil. C'est le pattern réutilisable pour tout bot qui s'intègre au cluster.

**Détail qui mord** : les slugs de modèle doivent correspondre exactement. `glm-5-2` (tiret) → 404 ; `glm-5.2` (point) → OK. À vérifier en cas d'erreur de routing inexpliquée. Les slugs des steps de cascade se lisent `provider@modèle` (ex. `gc@glm-5.3`, `ds@deepseek-v4-flash`).

---

## 6. Avancées du fork MyIA

Au-delà du routing de base, le fork `jsboige/claudish` ajoute ce qui fait tourner un proxy en production 24/7 :

| Avancée | Rôle |
|---------|------|
| **Cascade de failover notifiée** | Rôle → cascade ordonnée de substituts, TTL par step (échelle 10m→24h), notices onset/recovery sur 3 canaux ; le step final PAYG est toujours servi (`fork/failover.ts`, mandat 2026-08-12). |
| **Never-hang (priorité #1)** | Un flux se termine **toujours**, même si le provider coupe mid-stream ou renvoie du vide. Un agent bloqué est jugé pire qu'une erreur propre. |
| **Overload 529** | Un 429 de **surcharge transitoire** (ou 503) est converti en `529 overloaded_error` + `Retry-After`, pour que le client **réessaie** au lieu d'abandonner ; le 429 « quota » reste distinct (passe tel quel). |
| **Contrôle de concurrence** | `LocalModelQueue` (cap GPU) + `ConcurrencyLimiter` (cap provider remote), indépendants par provider (voir §3). |
| **Interception web search** | Les appels `web_search` des providers sont interceptés et servis via SearXNG (MCP) — ne bloque jamais l'agent (dégradation gracieuse en texte). |
| **Support `/compact` non-streaming** | Les requêtes `stream:false` (condensation de contexte) sont rebufferisées en un message JSON, pas en SSE. |
| **Channel mode (MCP)** | Sessions de modèle async avec notifications push (`notifications/claude/channel`). |
| **Capture & surveillance** | Capture des corps de requête (`CLAUDISH_CAPTURE_DIR`), scripts `traffic-live/summary/history.ps1`, watchdog auto-restart. |

---

## 7. War-stories — trois leçons du fork en production

Ces trois épisodes, extraits de l'historique du fork `jsboige/claudish`, illustrent pourquoi le proxy est conçu *comme il l'est*. Chacun porte une leçon transférable au-delà de claudish. **Ce sont des récits historiques datés** — l'état courant du déploiement est décrit aux §1-§3.

### 7.1 Architecture par soustraction — le no-fallback (24/06/2026) [HISTORIQUE — supersédé le 12/08/2026]

Au démarrage, claudish enchaînait les providers en fallback : si GLM rate-limitait, il basculait sur Qwen. **Le problème** : cette bascule se faisait à l'insu de l'agent, en plein milieu d'une conversation — changeant la qualité du modèle et le coût d'un tour sur l'autre, de façon invisible et imprévisible. Pire, le chemin fallback vers Qwen (GPU maison) a grippé le backend à plusieurs reprises (concurrence non bornée sur des contextes longs = famine GPU).

**La décision d'alors** n'a pas été d'ajouter du code pour mieux orchestrer les bascules, mais de **le retirer** : suppression de `defaultProvider`, une seule entrée par chaîne. Sur un burst claudish backoff puis réessaie le *même* provider ; sur une panne franche il fail-hard. *Leçon : un fallback **silencieux** est une dégradation cachée.*

**Ce que cette leçon est devenue** : le no-fallback strict a tenu de fin juin au 12/08/2026 (commit `823e614`). La cascade qui le remplace conserve le principe anti-silence — bascule **notifiée** (onset + recovery, 3 canaux), TTL par step, dernier step toujours servi — tout en réintroduisant la résilience multi-providers. La leçon transférable survit inchangée : *mieux vaut une bascule visible qu'une dérive de qualité invisible.*

### 7.2 Never-hang — le proxy qui crash déguisé en bug de stream (commit `8afe19d`, 14/06/2026)

Le symptôme : un gel récurrent sur un workflow CoursIA réel (portage d'un fichier `.cs`, sur `po-2025`). Côté client, cela ressemblait à un bug de lifecycle de stream — messages d'erreur « Content block not found », sockets fermées.

**La cause racine** était tout autre : un block `server_tool_use` de Z.AI déclenchait un handler qui lisait une variable d'index déclarée avec `let` dans un bloc `try` interne, alors que la closure vivait dans le scope externe → `ReferenceError` → **crash du process** → restart du conteneur. Le client ne voyait qu'une socket morte, pas le plantage.

**La leçon transférable** : *un proxy qui crash produit des symptômes de socket-close qui imitent un bug de lifecycle de stream. Quand un client « freeze », il faut **grep les exceptions dans les logs du proxy** avant de partir chasser des race conditions côté stream.* C'est la motivation de la priorité #1 du fork — **never-hang** : un flux se termine *toujours*, même si le provider coupe mid-stream. Un agent bloqué est jugé pire qu'une erreur propre.

### 7.3 Résilience — overload GLM convertie en HTTP 529 (commit `67a5dd0`)

Quand Z.AI est en surcharge, il renvoie du `429` (ou `503`). Un `429` brut, c'est un code « quota » que le client interprète souvent comme *arrêt* — il abandonne le tour au lieu de réessayer. Or une surcharge transitoire de Z.AI se résout typiquement en quelques minutes.

**Le fix** : claudish distingue la surcharge transitoire du quota épuisé, convertit la première en `529 overloaded_error` avec un `Retry-After`, et applique un **backoff patient** (~5 min, 6 retries, schedule 5/10/20/40/80/150 s) côté proxy avant de rendre la main. Le client reçoit un `529` (signal « réessaie ») plutôt qu'un `429` (signal « arrête »). Validé en production : **36 épisodes de surcharge convertis en 529 sur une fenêtre, zéro `429` atteint un client.**

*Leçon : les codes HTTP sont sémantiques (`429` ≠ `529`), et un client bien élevé réessaie sur `529`. Le dogfooding — tester ses propres fixes en prod sur le cluster — a révélé un chemin non couvert (le 429 HTTP-direct) que les tests unitaires n'avaient pas attrapés.*

---

## 8. Variables d'environnement clés

### Quel consommateur lit quelle variable (#15286)

Quatre consommateurs cohabitent dans l'écosystème et **chacun lit ses propres variables** : configurer « son » accès pour l'un ne configure aucun des trois autres. C'est la table à lire **avant** de copier un `.env` d'un voisin.

| Consommateur | Variables lues | Où le vérifier |
|---|---|---|
| **Claude Code (CLI)** | `ANTHROPIC_BASE_URL` + `ANTHROPIC_AUTH_TOKEN` (ou `ANTHROPIC_API_KEY` selon l'installateur) + `ANTHROPIC_MODEL` | [§4](#4-connecter-un-agent-claude-code) ci-dessus · [Claude-Code/docs/INSTALLATION-CLAUDE-CODE.md](../../Claude-Code/docs/INSTALLATION-CLAUDE-CODE.md) |
| **Notebook Claudish** (helper Python) | `ANTHROPIC_AUTH_TOKEN` + `CLAUDISH_BASE_URL` (défaut `http://localhost:3000`) | [`notebooks/helpers/claudish_client.py`](../notebooks/helpers/claudish_client.py) — la base URL est lue **à l'appel** (depuis #15312) : la poser dans une cellule **après** l'import est honorée |
| **TP wire OpenAI (T01)** | client `OpenAI()` + `OPENAI_MODEL` | matériaux de cours hors dépôt (mesuré par l'audit EPF, #15286) |
| **Gabarit projet étudiant** | `MODEL_API_KEY` + `MODEL_BASE_URL` — **rien d'autre** | gabarit remis aux groupes, hors dépôt (audit #15286) |

Deux pièges mesurés :

- le gabarit étudiant (`MODEL_*`) ne partage **aucune** variable avec les trois autres conventions — un étudiant qui configure « son » accès en configure un quart (#15286, défaut 2) ;
- les gabarits `.env.example` hérités enseignaient une **cible morte (401)** — l'ancien vLLM direct — au lieu de Claudish ; repointés vers `models.myia.io/v1` par #15050 (2026-09-07).

### Référence des variables (déploiement Claudish)

| Variable | Effet |
|----------|-------|
| `ANTHROPIC_BASE_URL` | URL claudish (les clients pointent ici au lieu de `api.anthropic.com`) |
| `ANTHROPIC_AUTH_TOKEN` | Clé d'auth claudish |
| `ANTHROPIC_MODEL` | Modèle/tier par défaut (`glm-5.3`, `claude-opus-5`, `qwen3.6-35b-a3b`, `MiniMax-M3`) |
| `OPENAI_BASE_URL` / `api_key` | Équivalent côté client wire OpenAI (base `https://models.myia.io/v1`) |
| `CLAUDISH_BASE_URL` | Base URL du helper notebook (défaut `http://localhost:3000`, lue à l'appel — #15286/#15312) |
| `providerConcurrency` (config) | Cap de concurrence par provider (`{ "glm-coding": 8 }`) |
| `customEndpoints` (config) | Endpoints nommés (`vllm-myia@…`) avec leur propre `maxConcurrency` |
| `SEARXNG_URL` / `SEARXNG_MCP_URL` | Backends de recherche web interceptés |
| `CLAUDISH_CAPTURE_DIR` | Active la capture des corps pour reprod offline |

---

## 9. Troubleshooting

| Symptôme | Cause | Fix |
|----------|-------|-----|
| `401 invalid proxy authentication` | Clé proxy absente/erronée | Fournir la clé dans `x-proxy-key`, `x-api-key` ou `Authorization: Bearer` (§2) |
| Réponses portant `[claudish] Failover model active` | **Pas une panne client** : le nominal du tier est épuisé, un step de cascade sert avec notice | Consulter le dashboard `workspace-claudish` / logs proxy ; le nominal revient à l'expiration du TTL (notice de recovery) |
| `404` ou erreur de routing sur `glm-5-2` | Slug erroné (tiret au lieu du point) | Utiliser `glm-5.2` — ou le slug cascade `gc@glm-5.3` |
| `503` intermittents côté IIS | Congestion du proxy (longs streams empilés sur un provider plafonné) | Vérifier les caps `providerConcurrency` ; le backoff/limiter doit lisser la rafale |
| Agent qui « freeze » (socket closed) | Flux non terminé proprement | Ne devrait plus arriver (never-hang) — si oui, c'est un bug à reporter |
| Client OpenAI qui échoue alors que Claude Code marche | Vérifier la base URL du client | Le wire OpenAI se consomme sur `<base>/v1/chat/completions` (mesuré 200 live le 2026-09-09) |

---

## 10. Liens & lectures

- **Upstream** : [MadAppGang/claudish](https://github.com/MadAppGang/claudish) — code source, README, docs.
- **Déploiement MyIA** : `jsboige/claudish` (fork), serveur `po-2023` (hub) + sidecar `ai-01`, passerelle `models.myia.io`.
- **Bots consommateurs** : voir [Claw-Systems/](../Claw-Systems/) (Hermes, NanoClaw).
- **Agents Claude Code consommateurs** : voir [Claude-Code/](../Claude-Code/).

---

*Section Claudish — réconciliée le 2026-09-09 (#15418) avec le fork live et le README canonique (refonte #11555). Proxy multi-providers du cluster MyIA : **deux formats wire en entrée** (Anthropic `/v1/messages` + OpenAI `/v1/chat/completions`), trois tiers routés en **cascade ordonnée notifiée** (Anthropic natif / GLM-5.3 / MiniMax-M3 / Qwen / DeepSeek) — bascule **jamais silencieuse** depuis le commit `823e614` (2026-08-12).*
