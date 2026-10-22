# Claudish — Proxy Multi-Providers, Wires Anthropic et OpenAI

> Sources : [github.com/MadAppGang/claudish](https://github.com/MadAppGang/claudish) (upstream) · [github.com/jsboige/claudish](https://github.com/jsboige/claudish) (déploiement MyIA) · [claudish.com](https://claudish.com)

Ce document décrit **Claudish** tel qu'il est déployé sur le cluster MyIA : un proxy qui fait tourner Claude Code, les agents autonomes et les bots sur **n'importe quel fournisseur de modèles**. Il explique le principe des deux wires d'entrée, la topologie hub/relais, la cascade de substitution par rôle, la façon de connecter un agent (Claude Code) et un bot, les avancées du fork, les récits de production qui ont forgé son design, et ce que la mesure de la flotte a appris.

> **État documenté au 2026-10-21** : mise à jour de la réconciliation du 2026-09-09 (#15418) avec six semaines d'évolution du fork. Les références `claudish#NNN` renvoient aux issues et PRs du fork [jsboige/claudish](https://github.com/jsboige/claudish). Les sections historiques sont datées comme telles.

---

## 1. Le principe — deux formats wire en entrée, plusieurs providers en sortie

**Claude Code** (et le SDK, et les bots qui parlent le protocole Anthropic) adressent toujours `https://api.anthropic.com` ; les clients **wire OpenAI** (notebooks, SDK OpenAI, routeurs tiers) postent du `/chat/completions`. Claudish accepte **les deux** et s'intercale entre le client et le fournisseur :

```text
   wire Anthropic (/v1/messages) OU OpenAI (/v1/chat/completions)
client ────────────────────────────────► claudish ─────────────────────────────► provider cible
(Claude Code, bot, SDK, client OpenAI)    (proxy)     (Anthropic / GLM / MiniMax / Qwen / DeepSeek / vLLM)
```

- **En entrée**, claudish expose `/v1/messages` (wire Anthropic) **et** `/v1/chat/completions` (wire OpenAI). La requête OpenAI est convertie au format Anthropic, passe par **le même** pipeline (routage, cascade, comptabilité), puis la réponse est retraduite : un client OpenAI hérite de tout cela en changeant seulement sa `base_url`.
- **En sortie**, il traduit vers le wire du provider cible (Anthropic natif, Anthropic-compatible comme MiniMax, OpenAI-compatible comme z.ai GLM ou vLLM, Responses API pour OpenAI Codex).
- **Résultat** : un agent conçu pour Claude *ou* pour l'API OpenAI peut parler à GLM, MiniMax, Qwen, Anthropic, etc., sans toucher à son code.

> **Historique (juillet 2026)** : le guide décrivait alors « un seul format wire en entrée » (`/v1/messages` seulement, `/chat/completions` → 404). Le wire OpenAI en entrée a été exposé depuis.

### Upstream vs déploiement MyIA

| | Upstream (MadAppGang) | Déploiement MyIA (jsboige) |
|---|---|---|
| **Rôle** | Outil open-source : « Claude Code. Any Model. » | Fork opérationnel du cluster |
| **Forme** | CLI local (`claudish --model …`) | Service Docker persistant : un hub, des relais par poste, une passerelle HTTPS |
| **Routing** | Fallback automatique multi-providers | **Cascade ordonnée par rôle, mur par fournisseur, bascule annoncée** (voir §3) |
| **Wires d'entrée** | Anthropic | Anthropic **et** OpenAI |
| **Ops** | — | Capture, instruments de trafic, watchdog, drain avant redémarrage, concurrence plafonnée (voir §6 et §10) |

**La dérive fork/upstream, mesurée le 2026-10-21** : la base commune date du 2026-05-09 (v7.1.2). Depuis, le fork a ajouté 626 commits et l'upstream 1 475 (v13.3.0) ; une fusion directe produirait plus d'une centaine de fichiers en conflit, concentrés dans les handlers, les providers et les adaptateurs. Le mainteneur upstream demande des contributions **étroites, une modification par PR**. *Leçon : un fork opérationnel qui accumule du code de production s'éloigne vite de son amont ; isoler le code propre au déploiement (ici sous `fork/`) et remonter tôt les correctifs génériques est ce qui garde la resynchronisation possible.*

---

## 2. Topologie de déploiement

```text
┌──────────────┐   ┌──────────────────────┐          ┌──────────────────┐   ┌─────────────────┐
│ Claude Code  │   │ relais Claudish local│   LAN    │ hub Claudish     │   │ Fournisseur     │
│  / agent     ├──►│ (sidecar Docker)     ├─────────►│ po-2025:3000     ├──►│ Anthropic / GLM │
│  / bot       │   │ NOMINAL : relaie     │          │ (Docker, Hono)   │   │ MiniMax / Qwen  │
└──────────────┘   │ AUTONOMOUS : sert    │          └──────────────────┘   │ DeepSeek / vLLM │
                   └──────────────────────┘                   ▲             └─────────────────┘
   clients distants ──► models.myia.io (IIS, HTTPS) ──────────┘
```

- Le **hub** tourne dans un conteneur Docker sur `po-2025` depuis la bascule du **2026-09-05** (il était auparavant sur `po-2023`).
- La passerelle **IIS** (`models.myia.io`) termine le TLS et reverse-proxie **directement vers le hub**.
- Plusieurs postes font tourner leur propre **relais** (*sidecar*), le même binaire en mode relais ; les autres passent par la passerelle.

### Un binaire, trois modes

| Configuration | Mode | Comportement |
|---|---|---|
| pas d'amont configuré | **HUB** | sert tout localement |
| amont configuré, hub **vivant** | **NOMINAL** | relaie la requête brute au hub ; pas de capture locale (le hub capture centralement) |
| amont configuré, hub **mort** | **AUTONOMOUS** | sert localement avec la même cascade, et capture localement |

**L'hystérésis est volontairement asymétrique** : deux échecs consécutifs du contrôle de santé suffisent pour passer en autonome, mais le retour exige trois contrôles réussis, 60 s de refroidissement **et** une sonde profonde (un vrai tour d'appel d'outil qui doit aller jusqu'à `message_stop`). Basculer vite, revenir prudemment : c'est ce qui évite le battement.

**Les boucles sont détectées par identité, pas par configuration** : chaque processus publie un identifiant aléatoire sur `/health`, et chaque relais ajoute le sien à un en-tête `x-claudish-hops`. Un nœud qui retrouve son propre identifiant sert localement au lieu de se relayer à lui-même. Chaque requête porte aussi l'en-tête `X-Claudish-Machine`, que le relais préserve : c'est ce qui permet d'attribuer le trafic par poste au hub.

### Authentification client → claudish

Clé proxy **obligatoire**, acceptée dans **trois** en-têtes équivalents :

| En-tête | Forme |
|---|---|
| `x-proxy-key` | `x-proxy-key: <clé>` |
| `x-api-key` | `x-api-key: <clé>` |
| `Authorization` | `Authorization: Bearer <clé>` |

Les requêtes `GET` (contrôle de santé, découverte de modèles) passent sans clé. Une requête sans clé ne peut être servie **que** par le pass-through Anthropic natif, avec l'authentification Anthropic du client lui-même : toute autre voie (remap, endpoint personnalisé, marche de cascade) dépenserait une clé que l'appelant ne détient pas, et refuse avant tout appel amont (claudish#416). Toute autre requête sans clé valide reçoit `401 invalid proxy authentication`.

**Clés scopées pour les consommateurs externes** (claudish#400) : un partenaire, une voie GPU partagée ou un pilote de cours reçoit une clé qui s'authentifie comme la clé proxy mais n'atteint **que** les modèles de sa liste blanche. Un modèle hors liste reçoit un `403` étiqueté ; un plafond de requêtes simultanées par clé répond `429` étiqueté ; chaque requête est attribuée à la clé dans les captures. Révoquer un externe revient à supprimer une entrée de configuration — jamais à faire tourner la clé de toute la flotte. Quand la clé proxy elle-même tourne, l'ancienne reste acceptée pendant une fenêtre de recouvrement, et le hub **compte** qui l'utilise encore (claudish#439) : on sait qui n'a pas migré avant de couper.

---

## 3. La cascade par rôle — substitution ordonnée, bascule annoncée

C'est le cœur du déploiement MyIA. Claude Code raisonne en **rôles** (`opus`, `sonnet`, `haiku`, `fable`) ; chaque rôle a un modèle **nominal** et une **liste ordonnée de substituts** (la cascade), implémentée dans `packages/cli/src/fork/failover.ts`. Principe de composition : les **forfaits** d'abord, le **paiement à l'usage** en dernière marche — celle qui sert toujours.

Composition relevée sur le hub le **2026-10-21** (profil de routage + environnement du conteneur lus par valeur, recoupés avec les marqueurs de réponse des captures) :

| Rôle | Nominal | Cascade (`>` = ordre) | Direction déclarée |
|------|---------|-----------------------|--------------------|
| **Opus** (réflexion lourde) | Anthropic natif, version **épinglée** par le `modelMap` (§7.7) — authentifié par le poste client | `cx@gpt-6.1-sol > role:sonnet` | lateral > degraded |
| **Sonnet** (usage courant) | `gc@glm-5.3` (forfait de code z.ai) | `mistral@zai-glm-5-3 > kc@k3 > qwen-token-plan@deepseek-v4.1-flash-1017 > ds@deepseek-flash` | degraded > lateral ×3 |
| **Haiku** (rapide, léger) | `mmc@MiniMax-M3.1-Flash` | `vllm-myia@swift-1.5-27b > role:sonnet` | degraded > improved |
| **Fable** | `cx@gpt-6-astra` (voie OpenAI Codex) | `cx@gpt-6.1-sol > role:sonnet` | lateral > degraded |

- **Haiku est différencié par poste, sans seconde configuration** : deux postes sont **armés en permanence** sur leur cascade par un armement limité à la machine (`CLAUDISH_FAILOVER_ACTIVE=haiku@<poste>`, claudish#552) — ils sont servis par le modèle vLLM local ; les autres restent sur MiniMax jusqu'à son mur hebdomadaire, où l'armement automatique prend le relais.
- **L'armement automatique est actif sur tous les rôles** (`CLAUDISH_FAILOVER_AUTO=1`) : la cascade s'arme au **deuxième** refus qualifiant, pas au premier.
- **Le rôle est reconnu par sous-chaîne** : un `haiku` nu comme un `claude-haiku-4-5` complet atterrissent sur le même nominal. Les sous-agents de Claude Code sont servis par `glm-5.3`.

> **Exemple daté (2026-08-18)** — la cascade Opus était alors `qwen-token-plan@qwen3.8-max > gc@glm-5.3 > ds@deepseek-v4-flash` (direction *degraded*), celle de Haiku `qwen-token-plan@qwen3.8-max > ds@deepseek-v4-flash` (direction *improved*). Deux mois plus tard, aucune marche n'a survécu : la composition suit les forfaits souscrits et change plus souvent que ce guide ; ce qui reste stable, ce sont les mécanismes ci-dessous.

### Les mécanismes de la cascade

- **Une marche épuisée sort de la rotation pour un délai croissant** — `10 min → 30 min → 1 h → 4 h → 24 h`, un barreau par *épisode* d'échec, puis elle est re-sondée. Une date de remise à zéro connue (forfait hebdomadaire) remplace l'échelle.
- **Le mur est posé sur le fournisseur, pas sur le rôle** (claudish#275) : si GLM refuse pour quota, toutes les requêtes dont le nominal est sur GLM descendent leur propre cascade ; un rôle servi ailleurs n'est pas dérouté. Un rôle peut aussi être forcé sur sa cascade pour **une seule machine** (claudish#552).
- **Une session garde sa marche au moins 10 minutes** (fenêtre glissante) : pas de va-et-vient de modèle au milieu d'une conversation. Elle la quitte si la marche échoue, ou si le nominal est revenu **de façon vérifiée**.
- **Une marche peut déléguer à un autre rôle** (`role:sonnet`, claudish#274) : elle prend alors ce que ce rôle sert à cet instant. Le graphe de délégation est prouvé **sans cycle** au chargement.
- **Une marche qui ne peut pas prendre cette requête est sautée** (claudish#431) — contexte trop long pour sa fenêtre, ou limiteur saturé — sans être marquée en échec : elle n'est pas en panne, la requête n'est simplement pas pour elle.
- **Une surcharge passagère du nominal** (503, 529) parcourt la cascade **une fois**, sans rien écrire dans l'état : pas d'armement, pas de mur, pas d'épinglage de session (claudish#299).
- **Ce qui arme la cascade est volontairement étroit** : `402`, ou un `429` dont le corps nomme un mur de quota. Une limite de débit à la minute n'arme rien. **`401` et `404` n'arment jamais** : basculer cacherait une erreur de câblage derrière une réponse plausible.
- **Chaque substitution est annoncée** : au début (onset) et au retour du nominal (recovery), en texte sur `/v1/messages`, dans l'en-tête `x-claudish-failover-notice` sur `/v1/chat/completions` (claudish#229). Les notices décrivent des **faits**, jamais des instructions à l'agent.
- **Le budget d'une session peut être borné** (claudish#317) : les tokens de sortie sont comptés par (machine, session) sur 24 h glissantes. Un seuil d'**alerte** marque les sessions qui dérapent ; un **plafond**, s'il est fixé, refuse localement avec un `429` étiqueté **avant** de payer l'amont. La flotte tourne en alerte seule tant que le mainteneur n'a pas fixé les valeurs.

> **Historique — l'ère no-fallback (24/06/2026 → 12/08/2026)** : le déploiement a d'abord supprimé tout fallback (voir §7.1). La cascade annoncée l'a remplacée le 2026-08-12 (commit `823e614`) : la bascule existe de nouveau, mais **jamais silencieuse**.

### Contrôle de concurrence

Certains providers ne supportent pas les requêtes parallèles illimitées. Claudish plafonne la concurrence **par provider** :

- **GPU self-hosté (vLLM)** — cap séquentiel. Un GPU ne fait pas 4 prefills de 120K tokens en parallèle sans se gripper (`max-num-batched-tokens` saturé → famine GPU).
- **GLM Coding** — cap ~8. Une rafale de longs streams GLM qui s'empilent congestionne l'event-loop du proxy et remonte en 503 côté IIS.

Au-delà du cap, les requêtes attendent en file FIFO et passent dès qu'un slot se libère. Dans une cascade, une marche dont le limiteur est saturé est désormais **sautée** plutôt qu'attendue (voir ci-dessus).

---

## 4. Connecter un agent Claude Code

Côté Claude Code (ou le SDK), on pointe simplement le base URL vers claudish — le relais local du poste s'il existe, sinon la passerelle :

```powershell
$env:ANTHROPIC_BASE_URL = "https://models.myia.io"
$env:ANTHROPIC_AUTH_TOKEN = "<clé claudish>"
$env:ANTHROPIC_MODEL = "glm-5.3"          # rôle Sonnet → Z.AI GLM
# ou laisse claudish choisir via le modelMap du profil actif
```

C'est tout. Claude Code croit parler à Anthropic ; claudish route en réalité vers GLM/MiniMax/Qwen/Anthropic selon le modèle demandé.

### Et les clients wire OpenAI ?

Un client OpenAI (notebook, SDK, routeur tiers) pointe sa base URL sur le même proxy et utilise le wire `/v1/chat/completions` :

```python
client = OpenAI(base_url="https://models.myia.io/v1", api_key="<clé claudish>")
```

- Le champ `model` de la réponse porte l'identité du modèle effectivement servi — utile pour vérifier qu'on n'est pas sur une marche de cascade.
- Une substitution est annoncée dans l'en-tête `x-claudish-failover-notice` (UTF-8 encodé en base64), jamais dans le contenu : un client OpenAI qui parse la réponse n'y trouve pas de texte inattendu.
- Les contrôles de réflexion des clients OpenAI (`enable_thinking`, `reasoning_effort`) sont traduits vers l'objet `thinking` d'Anthropic, avec un budget toujours légal (claudish#437).
- Un flux mal formé se termine par un chunk terminal et `data: [DONE]` : la règle « ne jamais bloquer » vaut aussi sur ce wire.

### Et Roo Code ?

**Roo Code n'a jamais consommé claudish à ce jour** — pour des raisons d'historique, plus de wire. Roo *déclinait* pile au moment où claudish *émergeait* (juin-juillet 2026) et s'est toujours configuré en **OpenRouter direct**. Le wire OpenAI exposé depuis le rendrait techniquement consommable, mais ce n'est pas la configuration de la flotte.

> **Piège de télémétrie** : `cc_entrypoint=claude-vscode` dans les captures de trafic, c'est **Claude Code lancé depuis VS Code**, pas Roo Code.

**Perspective (successeur Zoo)** : le remplaçant de Roo, **Zoo Code**, est amené à router par claudish — via son provider Anthropic pointé sur claudish + un nom de modèle Claude remappé (le pattern de la leçon Hermes ci-dessous). Ce sera une **configuration par poste**, pas une feature du proxy.

---

## 5. Connecter un bot — le trick du nom Claude (leçon Hermes)

Les bots autonomes (Hermes, NanoClaw) parlent parfois un wire non-Anthropic. Un bot OpenAI-native peut poster directement sur `/v1/chat/completions` — mais le pattern le plus robuste reste le **remap de nom** :

| Option | Quoi faire | Quand |
|--------|------------|-------|
| **Remap de nom (recommandée)** | Le bot envoie un **nom de modèle Claude** (ex. `claude-sonnet-4-6`). Claudish le remappe vers le modèle budgété du rôle selon le profil actif. **De la config côté bot, aucun patch de wire.** | Le bot sait juste poster un `model` dans sa requête. |
| Wire OpenAI direct | Poster sur `/v1/chat/completions` avec la clé proxy (`Authorization: Bearer` accepté). | Le bot est OpenAI-native et vous voulez la route la plus courte. |
| Patch du wire | Faire parler le bot Anthropic natif (messages/tools au format Anthropic). | Le bot a déjà une intégration Anthropic, ou on contrôle son code. |

> **Leçon Hermes (juin 2026)** : le bot Hermes bloquait le routing. Le fix n'a **pas** été de patcher le wire du bot, mais de lui faire envoyer un nom Claude — claudish s'occupe du reste via le `modelMap` du profil. C'est le pattern réutilisable pour tout bot qui s'intègre au cluster.

**Détail qui mord** : les slugs de modèle doivent correspondre exactement. `glm-5-2` (tiret) → 404 ; `glm-5.2` (point) → OK. Les slugs des marches de cascade se lisent `provider@modèle` (ex. `gc@glm-5.3`, `ds@deepseek-v4-flash`). Avec une clé scopée, c'est **l'orthographe envoyée par le client** qui est comparée à la liste blanche : deux alias d'un même modèle sont deux entrées distinctes.

---

## 6. Avancées du fork MyIA

Au-delà du routing de base, le fork `jsboige/claudish` ajoute ce qui fait tourner un proxy en production 24/7 :

| Avancée | Rôle |
|---------|------|
| **Cascade de substitution annoncée** | Rôle → cascade ordonnée, mur par fournisseur, délai par marche, maintien de session, notices onset/recovery (§3). |
| **Never-hang (priorité #1)** | Un flux se termine **toujours** par `message_stop`, même si le provider coupe mid-stream ou renvoie du vide. Aucun `controller.error()` dans le code de production. Un agent bloqué est jugé pire qu'une erreur propre. |
| **Watchdog du premier événement** | Un flux admis en `200` qui ne produit aucun événement utile est coupé après 300 s ; un flux **relancé** reçoit son **propre** watchdog (§7.6). |
| **Récupération avant tout événement visible** | Si l'amont meurt avant que le client ait reçu quoi que ce soit, la requête est ré-émise (au plus 2 fois) au lieu d'être conclue par un message d'erreur (claudish#170). |
| **Refus de politique étiqueté** | Un refus `invalid_prompt` est réessayé à l'identique (2 fois), puis rendu sous une étiquette explicite — jamais une « réponse vide » inexpliquée (claudish#65). |
| **Overload 529** | Une surcharge transitoire est convertie en `529 overloaded_error` + `Retry-After`, pour que le client **réessaie** au lieu d'abandonner ; le 429 « quota » reste distinct (§7.3). |
| **Garde de credential sur la voie native** | La voie Anthropic native refuse localement (`403` étiqueté, zéro appel amont) de transmettre une clé qui n'est pas une clé Anthropic (§7.9). |
| **Épinglage de version native** | Le `modelMap` d'un rôle fixe la version Anthropic réellement envoyée (§7.7). |
| **Comptabilité de contexte fidèle** | Les trois compteurs d'entrée (`input`, `cache_read`, `cache_creation`) sont livrés ensemble et amorcés **par session** (§7.8). |
| **Politiques de réflexion par fournisseur** | `CLAUDISH_QWEN_THINKING` (désactivée par défaut : le forfait Qwen facture la sortie), `CLAUDISH_GLM_THINKING`, niveau d'effort MiniMax — relus à chaque requête. |
| **Contrôle de concurrence** | `LocalModelQueue` (cap GPU) + `ConcurrencyLimiter` (cap provider remote), indépendants par provider (§3). |
| **Interception web search** | Les appels de recherche web des providers sont interceptés et servis via SearXNG — un outil déclaré par le client sous le même nom lui est rendu tel quel ; une recherche ratée devient du texte, jamais un blocage. |
| **Support `/compact` non-streaming** | Les requêtes `stream:false` (condensation de contexte) reçoivent un message JSON, jamais du SSE. |
| **Drain avant redémarrage** | Un redémarrage attend un vrai zéro de flux actifs avant de couper (§7.5) ; un watchdog redémarre le service la nuit, dans une fenêtre creuse. |
| **Channel mode (MCP)** | Sessions de modèle asynchrones avec notifications push. |
| **Capture & instruments** | Capture des corps de requête/réponse, attribution par machine et par session, outil MCP de lecture du trafic (§10). |

---

## 7. War-stories — leçons du fork en production

Ces épisodes, extraits de l'historique du fork `jsboige/claudish`, illustrent pourquoi le proxy est conçu *comme il l'est*. Chacun porte une leçon transférable au-delà de claudish. **Ce sont des récits historiques datés** — l'état courant du déploiement est décrit aux §1-§3.

### 7.1 Architecture par soustraction — le no-fallback (24/06/2026) [HISTORIQUE — supersédé le 12/08/2026]

Au démarrage, claudish enchaînait les providers en fallback : si GLM rate-limitait, il basculait sur Qwen. **Le problème** : cette bascule se faisait à l'insu de l'agent, en plein milieu d'une conversation — changeant la qualité du modèle et le coût d'un tour sur l'autre, de façon invisible et imprévisible. Pire, le chemin fallback vers Qwen (GPU maison) a grippé le backend à plusieurs reprises (concurrence non bornée sur des contextes longs = famine GPU).

**La décision d'alors** n'a pas été d'ajouter du code pour mieux orchestrer les bascules, mais de **le retirer** : suppression de `defaultProvider`, une seule entrée par chaîne. Sur un burst claudish backoff puis réessaie le *même* provider ; sur une panne franche il fail-hard. *Leçon : un fallback **silencieux** est une dégradation cachée.*

**Ce que cette leçon est devenue** : le no-fallback strict a tenu de fin juin au 12/08/2026 (commit `823e614`). La cascade qui le remplace conserve le principe anti-silence — bascule **annoncée**, délai par marche, dernière marche toujours servie. La leçon transférable survit inchangée : *mieux vaut une bascule visible qu'une dérive de qualité invisible.*

### 7.2 Never-hang — le proxy qui crash déguisé en bug de stream (commit `8afe19d`, 14/06/2026)

Le symptôme : un gel récurrent sur un workflow CoursIA réel (portage d'un fichier `.cs`, sur `po-2025`). Côté client, cela ressemblait à un bug de lifecycle de stream — messages d'erreur « Content block not found », sockets fermées.

**La cause racine** était tout autre : un block `server_tool_use` de Z.AI déclenchait un handler qui lisait une variable d'index déclarée avec `let` dans un bloc `try` interne, alors que la closure vivait dans le scope externe → `ReferenceError` → **crash du process** → restart du conteneur. Le client ne voyait qu'une socket morte, pas le plantage.

**La leçon transférable** : *un proxy qui crash produit des symptômes de socket-close qui imitent un bug de lifecycle de stream. Quand un client « freeze », il faut **grep les exceptions dans les logs du proxy** avant de partir chasser des race conditions côté stream.* C'est la motivation de la priorité #1 du fork — **never-hang** : un flux se termine *toujours*, même si le provider coupe mid-stream.

### 7.3 Résilience — overload GLM convertie en HTTP 529 (commit `67a5dd0`)

Quand Z.AI est en surcharge, il renvoie du `429` (ou `503`). Un `429` brut, c'est un code « quota » que le client interprète souvent comme *arrêt* — il abandonne le tour au lieu de réessayer. Or une surcharge transitoire de Z.AI se résout typiquement en quelques minutes.

**Le fix** : claudish distingue la surcharge transitoire du quota épuisé, convertit la première en `529 overloaded_error` avec un `Retry-After`, et applique un **backoff patient** (~5 min, 6 retries, schedule 5/10/20/40/80/150 s) côté proxy avant de rendre la main. Validé en production : **36 épisodes de surcharge convertis en 529 sur une fenêtre, zéro `429` atteint un client.**

*Leçon : les codes HTTP sont sémantiques (`429` ≠ `529`), et un client bien élevé réessaie sur `529`. Le dogfooding a révélé un chemin non couvert (le 429 HTTP-direct) que les tests unitaires n'avaient pas attrapé.*

### 7.4 Le retour en arrière silencieux — vérifier le chemin, pas l'intention (07/09 → 11/09/2026)

Le 2026-09-05, le hub déménage de `po-2023` vers `po-2025`. La bascule est vérifiée et passe. Le 07/09 à 15:37, la règle de la passerelle IIS qui pointait vers le nouveau hub est **restaurée à l'identique de son état d'avant**, sans annonce. Aucun cycle de surveillance ne le voit : on surveillait la santé du nouveau hub, qui était parfait — simplement, une partie du trafic n'y arrivait plus. C'est la panne du hub, le 11/09, qui le révèle : pendant ces quatre jours, **2 779 requêtes et 263,6 millions de tokens** avaient été servis par la cascade locale de l'ancien hub, dont 106 millions en paiement à l'usage, invisibles du nouveau.

*Leçons* : (1) un changement de flotte n'est fini que lorsqu'on a **mesuré, pour chaque consommateur, où il atterrit réellement** — lu dans la configuration vivante, pas déduit de l'intention du changement ; (2) la surveillance couvre le **chemin** (les points d'entrée qui alimentent le service), pas seulement le trafic qu'on reçoit ; (3) un retour en arrière d'infrastructure partagée passe par le même canal que le changement — non annoncé, c'est un incident, pas un correctif. Depuis, tout changement du point d'entrée de la flotte est annoncé avant d'être appliqué.

### 7.5 Le remède qui coûte plus que la panne — un redémarrage tue les flux (20/09/2026)

Un matin, un composant de transfert réseau du chemin vers le hub se bloque — un défaut qu'un redémarrage du hub ne peut pas corriger. Le geste réflexe est appliqué quand même : **13 redémarrages du conteneur hub en une matinée**. Chaque redémarrage coupe *tous* les flux SSE en cours, sur *toutes* les machines qui relaient — 9 à 13 flux actifs chacune, autant de tours d'agent perdus. **La perte de tours à l'échelle de la flotte venait du remède, pas de la panne.**

La réponse a été double. D'abord, rendre la panne amont récupérable : si l'amont meurt **avant** que le client ait reçu quoi que ce soit, la requête est ré-émise au lieu d'être conclue (§6). Ensuite, ne redémarrer qu'au bon moment : le script de drain attend que le compteur de flux actifs atteigne **un vrai zéro**. Une première mesure de 30 minutes avait conclu que ce zéro n'arrivait jamais (minimum 1) ; une sonde de deux jours (92 364 échantillons) a corrigé : le plancher **est** zéro (4,62 % des échantillons), et il survient dans les 300 s dans 57,5 % des cas — les accalmies sont simplement brèves (5,9 s en moyenne). Le drain attend donc ce zéro 300 s, puis choisit le meilleur moment disponible. Et le redémarrage quotidien programmé a été **supprimé** de la flotte.

*Leçons : mesurer le coût du remède, pas seulement celui de la panne ; et une fenêtre de mesure trop courte peut produire une conclusion fausse avec une parfaite assurance.*

### 7.6 Une garde désarmée par son propre déclencheur (14/09/2026)

Pendant un incident d'ordonnancement chez un fournisseur, des flux répondent `200`, envoient des commentaires `keep-alive`… et ne produisent jamais de contenu. Ils tiennent les slots du hub environ **900 s chacun** (46 flux, 19 en attente au pic). Réponse : un **watchdog du premier événement utile** — sans première ligne `data:` après 300 s, l'amont est coupé et le tour se termine proprement. Un commentaire `keep-alive` ne compte pas comme un événement utile, alors qu'une longue réflexion du modèle, elle, produit des événements : elle ne peut pas déclencher la coupure.

Puis le piège : ce watchdog se **désarme** à la première ligne `data:`. Or un chunk d'erreur (`data: {"error":…}`) est une telle ligne — et c'est lui qui déclenche la **relance** transparente de la requête. La relance partait donc sans protection : mesuré en revue, avec une fenêtre de 1 s et sans protection dédiée, le flux client était encore ouvert après 6 s. Chaque relance reçoit désormais son propre watchdog.

*Leçon : une garde qui se désarme sur un signal ne peut pas protéger ce que ce même signal déclenche.*

### 7.7 Le modèle demandé n'est pas le modèle servi (22/09/2026)

Le `modelMap` du hub indiquait `claude-opus-4-8` pour le rôle Opus depuis des semaines. Mesure sur 48 h : **6 487 réponses natives consécutives** servies en `claude-opus-5` — l'identifiant que les clients demandaient. Modifier la carte et recharger : 34 sur 34, toujours `claude-opus-5`. La voie native transmettait le champ `model` du client tel quel ; la carte choisissait la **voie**, jamais la **version**. Le correctif épingle la version à l'endroit où la requête part réellement vers Anthropic, et seulement pour les identifiants `claude-*` — un identifiant nu comme `glm-5.3` ne doit jamais se retrouver sur le wire d'Anthropic.

*Leçon : une valeur de configuration n'est un réglage que si elle atteint le wire. Vérifier ce qui est servi (le champ `model` de la réponse), pas ce qui est configuré.*

### 7.8 Un état mono-utilisateur dans un service partagé (septembre-octobre 2026)

Claude Code calcule l'occupation de son contexte en **additionnant brutement** trois compteurs : `input_tokens + cache_creation_input_tokens + cache_read_input_tokens` (vérifié dans le code distribué du client). Un proxy qui envoie un `input_tokens` réduit **sans** ses deux compagnons sous-estime le contexte de toute la part en cache — et désarme silencieusement la condensation automatique. Depuis claudish#179, les trois compteurs partent toujours ensemble, avec des valeurs initiales explicites à 0.

Le 18/10, un second défaut apparaît sur la même zone : un événement de début de message annonce **166 322 tokens** pour une session qui en fait **233**. L'amorce venait d'un compteur partagé par tous les clients du même modèle — un héritage du CLI upstream, conçu pour **un seul** utilisateur local. Sur un hub partagé, la session suivante recevait la taille de la conversation d'un autre : condensation déclenchée à tort, ou désarmée, et fuite d'information entre utilisateurs. L'amorce est désormais rangée **par session** (claudish#518).

*Leçons : lire le code du consommateur pour savoir ce que vos nombres veulent dire ; et un état « par processus », anodin dans un outil mono-utilisateur, devient une fuite entre clients dès que l'outil devient un service partagé.*

### 7.9 La clé de quelqu'un d'autre (30/09 → 01/10/2026)

Un poste distant envoyait à la voie Anthropic native une clé qui n'était pas une clé Anthropic : 40 refus amont `Invalid Bearer` en deux jours, chacun après un aller-retour réseau inutile — et une clé tierce transmise à un fournisseur qui n'avait pas à la voir. La voie native refuse désormais **localement**, avant tout appel, avec un `403` étiqueté (claudish#296) ; quand une clé Anthropic et une clé étrangère arrivent ensemble, l'étrangère est retirée et la bonne authentifie (claudish#305).

Détail qui compte : le **texte** du refus est porteur. La cascade s'arme sur un `403` dont le corps mentionne un mur de quota ; si le message de refus contenait un mot de cette famille, le proxy basculerait sur sa propre erreur. Le libellé est donc épinglé par un test contre le vrai prédicat de bascule.

*Leçon : un message d'erreur est une interface — d'autres morceaux de code le lisent, et ses mots ont des conséquences.*

### 7.10 Le port tenu par un mort — l'écoute la plus spécifique gagne (octobre 2026)

Sur un poste, un processus de relais WSL figé tenait encore `127.0.0.1:3000`, pendant que le conteneur publiait le même port sur toutes les interfaces. Pour une connexion vers `localhost:3000`, c'est l'écoute **la plus spécifique** qui l'emporte : les agents du poste ont parlé pendant **9 heures** à un processus mort, alors que le conteneur, sain, répondait normalement sur l'adresse du réseau local — et donc à toutes les sondes qui passaient par là.

*Leçon : un port occupé n'est pas un port servi. Sonder l'entrée par la même adresse que le client, pas par celle qui arrange l'instrument.*

### 7.11 Des suites vertes qui ne regardaient pas (octobre 2026)

Trois cas en trois semaines, sur la même idée :

- **Une suite rouge qui sortait 0** (claudish#519) — sous Windows PowerShell 5.1, un module enregistré en UTF-8 **sans BOM** et contenant un tiret cadratin est lu dans la page de code locale : erreur d'analyse, **416 tests sur 471** en échec, et l'enveloppe rendait quand même un code de sortie nul.
- **Des tests sautés, pas exécutés** (claudish#533 → #571) — près de trente tests de canaux dépendaient d'un vrai exécutable absent des postes Windows ; ils s'y affichaient « skip », jamais en échec. Un faux exécutable compilé les fait désormais tourner.
- **Une garde qui acceptait son contournement** (claudish#582) — une règle structurelle vérifiait qu'un bloc `finally` réaffecte `$ErrorActionPreference` ; `= 'Continue'` la satisfaisait, sans rien restaurer. La règle exige maintenant que la cible soit la variable capturée avant le bloc, et chaque règle est accompagnée d'un mutant qui doit la faire rougir.

*Leçon : un vert ne vaut qu'avec son contrôle positif — une suite doit savoir échouer sur le défaut qu'elle prétend garder. En revue, on mute la garde et on regarde le test rougir.*

### 7.12 La durée d'un épisode, c'est d'abord celle du détecteur (octobre 2026)

Un histogramme des passages d'un relais en mode autonome : **31 épisodes**, de 61 à 203 s, médiane **78 s** — pratiquement le plancher imposé par l'hystérésis (deux échecs pour entrer, trois battements sains, un délai de refroidissement et une sonde profonde pour sortir). La durée mesurée était surtout celle de la machine à états, pas celle des pannes.

Le poste soupçonné a été disculpé par le double chemin : le hub mettait jusqu'à **43 s** à renvoyer ses en-têtes sur des corps de plusieurs mégaoctets, la lenteur était de son côté. Et l'enquête a buté sur un angle mort : dans les captures du hub, une requête relayée et une requête directe se ressemblent. La chaîne des sauts, déjà maintenue pour détecter les boucles, sera inscrite dans l'enveloppe de capture (claudish#566 — fusionné le 2026-10-21, en attente du prochain déploiement du hub).

*Leçons : avant d'interpréter une distribution, en soustraire le plancher de l'instrument ; et tout instrument a une fenêtre — ce qu'il ne voit pas ne compte pas comme zéro.*

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

Côté client :

| Variable | Effet |
|----------|-------|
| `ANTHROPIC_BASE_URL` | URL claudish (les clients pointent ici au lieu de `api.anthropic.com`) |
| `ANTHROPIC_AUTH_TOKEN` | Clé d'auth claudish |
| `ANTHROPIC_MODEL` | Modèle/rôle par défaut (`glm-5.3`, `claude-opus-5`, `MiniMax-M3`, …) |
| `OPENAI_BASE_URL` / `api_key` | Équivalent côté client wire OpenAI (base `https://models.myia.io/v1`) |
| `CLAUDISH_BASE_URL` | Base URL du helper notebook (défaut `http://localhost:3000`, lue à l'appel — #15286/#15312) |

Côté proxy (opérateur) :

| Variable | Effet |
|----------|-------|
| `CLAUDISH_RELAY_UPSTREAM` | Absente : mode hub. Présente : mode relais vers ce hub (§2) |
| `CLAUDISH_FAILOVER_<RÔLE>` | Cascade du rôle, marches séparées par `>` ; sans valeur, tout le mécanisme est inerte (§3) |
| `CLAUDISH_FIRST_EVENT_TIMEOUT_MS` | Délai du watchdog du premier événement utile (défaut 300 s, `0` = désactivé) |
| `CLAUDISH_SESSION_BUDGET_WARN` / `_CEILING` | Seuil d'alerte / plafond de tokens de sortie par session (§3) |
| `CLAUDISH_QWEN_THINKING` / `CLAUDISH_GLM_THINKING` | Politique de réflexion par fournisseur |
| `CLAUDISH_CAPABILITY_VOCAB` | Négociation de capacités à la condensation (désactivée par défaut — voir le [ledger §0](MCP-Capability-Negotiation.md)) |
| `providerConcurrency` (config) | Cap de concurrence par provider (`{ "glm-coding": 8 }`) |
| `customEndpoints` (config) | Endpoints nommés avec leur propre `maxConcurrency` |
| `inboundKeys` (config) | Clés scopées : liste blanche de modèles, plafond simultané (§2) |
| `SEARXNG_URL` / `SEARXNG_MCP_URL` | Backends de recherche web interceptés |
| `CLAUDISH_CAPTURE_DIR` | Active la capture des corps pour reproduction hors ligne (vide = rien n'est écrit) |

⚠ Dans un conteneur, l'environnement est figé **à la création** : une nouvelle valeur n'entre qu'à la prochaine recréation du conteneur, et seulement si la variable figure dans le fichier compose. « Relue à chaque requête » veut dire relue dans l'environnement du processus, pas dans le fichier `.env` sur disque.

---

## 9. Troubleshooting

| Symptôme | Cause | Fix |
|----------|-------|-----|
| `401 invalid proxy authentication` | Clé proxy absente/erronée | Fournir la clé dans `x-proxy-key`, `x-api-key` ou `Authorization: Bearer` (§2) |
| `403` « key '…' is not permitted to use model '…' » | Clé scopée, modèle hors de sa liste blanche | Demander l'ajout du modèle **sous l'orthographe exacte** que le client envoie (§5) |
| `403 permission_error` « no Anthropic credential to send » | Voie native sans clé Anthropic (ou avec une clé étrangère) | Fournir une authentification Anthropic, ou demander un modèle non natif (§7.9) |
| `429` étiqueté de plafond de session ou de plafond par clé | Budget de session ou plafond simultané d'une clé scopée atteint | Ce n'est pas un quota fournisseur : attendre le délai indiqué (`retry-after`) |
| Réponses portant `[claudish] Failover model active` (ou en-tête `x-claudish-failover-notice`) | **Pas une panne client** : le nominal du rôle est épuisé, une marche de cascade sert avec notice | Rien à faire ; le nominal revient à l'expiration du délai (notice de recovery) |
| `[Upstream policy refusal — invalid_prompt: …]` | Le fournisseur refuse le contenu, même après deux nouvelles tentatives | Reformuler ; ce n'est ni une panne ni un quota |
| `404` ou erreur de routing sur `glm-5-2` | Slug erroné (tiret au lieu du point) | Utiliser `glm-5.2` — ou le slug cascade `gc@glm-5.3` |
| `503` intermittents côté IIS | Congestion du proxy (longs streams empilés sur un provider plafonné) | Vérifier les caps `providerConcurrency` |
| `502` en rafale sur la passerelle | Redémarrage (drainé) du hub : la passerelle n'a pas de relais de secours | Réessayer ; un poste avec relais local bascule en autonome pendant ce temps |
| Agent qui « freeze » (socket closed) | Flux non terminé proprement | Ne devrait plus arriver (never-hang) — si oui, c'est un bug à reporter, après avoir cherché un redémarrage du proxy dans la même minute (§7.2, §7.5) |
| Client OpenAI qui échoue alors que Claude Code marche | Vérifier la base URL du client | Le wire OpenAI se consomme sur `<base>/v1/chat/completions` |

---

## 10. Mesurer une flotte d'agents — ce que les instruments ont appris

Le fork s'est doté d'instruments parce que plusieurs « évidences » se sont révélées fausses à la mesure (§7.4, §7.5, §7.7, §7.12). Les principaux : la **capture** des corps de requête et de réponse, l'attribution par machine (`X-Claudish-Machine`), par session et par clé, un **outil MCP de lecture du trafic** (histogrammes datés, sessions planifiées vs interactives, et un `UNKNOWN` déclaré plutôt qu'un chiffre périmé quand le corpus a tourné), et des scripts d'analyse (autopsie de tours, consommation par voie, tendance des condensations).

Trois résultats d'octobre 2026 sur le coût d'une flotte d'agents :

- **La sortie est dans les tours d'outils** (claudish#445) — sur 24 h de captures d'un relais, les tours qui se terminent par un appel d'outil portent **92,3 %** des tokens de sortie (504 tokens par tour), les réponses finales **7,7 %** (1 180 tokens par tour, 28 fois plus rares). Raccourcir les réponses finales ne touche que 7,7 % du volume. *Couverture* : un relais en mode nominal ne capture pas ; l'échantillon est la part servie localement.
- **Les outils chargés sont presque tous utilisés** (claudish#23) — dans une session de travail CoursIA, 40 des 46 outils MCP chargés ont été appelés au moins une fois (87 %). Le levier d'allègement est nommé, pas générique : un serveur dont la moitié des outils n'est jamais appelée.
- **La consommation croît par le contexte re-payé, pas par la production** (claudish#328) — entre le pic de juillet et octobre, le volume quotidien de prompt a été multiplié par **3,9**, dont la lecture de cache par **5,0**, quand la sortie n'a fait que doubler et que la sortie par réponse a *baissé* de 12 %.

*Leçon : avant d'optimiser une flotte d'agents, mesurer où partent réellement les tokens. L'intuition (« les réponses sont trop longues ») visait la mauvaise cible.*

---

## 11. Liens & lectures

- **Upstream** : [MadAppGang/claudish](https://github.com/MadAppGang/claudish) — code source, README, docs.
- **Déploiement MyIA** : [jsboige/claudish](https://github.com/jsboige/claudish) (fork) — hub `po-2025`, relais par poste, passerelle `models.myia.io`. Les références `claudish#NNN` de ce guide y renvoient.
- **Négociation de capacités** : [MCP-Capability-Negotiation.md](MCP-Capability-Negotiation.md) — la proposition d'août et ce qui en a été construit.
- **Bots consommateurs** : voir [Claw-Systems/](../../Claw-Systems/) (Hermes, NanoClaw).
- **Agents Claude Code consommateurs** : voir [Claude-Code/](../../Claude-Code/).

---

*Section Claudish — mise à jour du 2026-10-21, après la réconciliation du 2026-09-09 (#15418) et la refonte du 2026-08-18 (#11555). Proxy multi-providers du cluster MyIA : **deux wires en entrée** (Anthropic `/v1/messages` + OpenAI `/v1/chat/completions`), un hub et des relais par poste, quatre rôles routés en **cascade annoncée** — bascule **jamais silencieuse** depuis le commit `823e614` (2026-08-12).*
