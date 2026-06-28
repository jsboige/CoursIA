# Coordination Multi-Bot

[← Claw-Systems](../README.md) | [↑ ..](../README.md)

> **Module co-écrit.** Ce document est une collaboration Hermes (po-2026) + NanoClaw
> (ai-01). La structure et les sections « côté Hermes » sont remplies ; les sections
> marquées `<!-- NANOCLAW -->` attendent la contribution NanoClaw pour le rééquilibrer
> en un récit symétrique. Voir [tracker #4428](https://github.com/jsboige/CoursIA/issues/4428).

Un seul agent autonome, c'est déjà intéressant. **Plusieurs agents autonomes qui se
parlent**, c'est un autre problème entièrement — et c'est le sujet de ce module.

Ce répertoire documente deux Claw systems qui coexistent dans le cluster CoursIA :
**NanoClaw** (machine `ai-01`, modèle GLM-5.2) et **Hermes** (machine `po-2026`,
GLM-5.2 via z.ai). Ils partagent le même LLM sous-jacent, des serveurs MCP communs,
et — surtout — un canal de coordination partagé. Ce module décrit **comment ils se
parlent**, **comment ils évitent de se marcher dessus**, et **comment un opérateur
humain garde la main**.

## Le problème de la coordination

Quand plusieurs agents tournent en parallèle, trois classes d'incidents apparaissent :

1. **Collision** — deux agents traitent la même tâche, produisent du travail dupliqué
2. **Silence** — un agent tombe muet sans crash visible ; personne ne sait s'il travaille
3. **Bagarre** — deux agents se répondent en boucle, s'alimentent mutuellement

Ces incidents ne se produisent presque jamais avec un agent unique. Ils sont la
**spécificité** du multi-bot, et toute l'architecture de coordination est conçue
pour les prévenir.

## Le canal partagé : dashboards RooSync

Ni NanoClaw ni Hermes ne se parlent en direct (pas de socket, pas d'API synchrone).
Ils communiquent via un **tableau noir partagé** : les dashboards RooSync.

| Type de dashboard | Portée | Usage |
|-------------------|--------|-------|
| `workspace-<nom>` | Un workspace (ex. `CoursIA`) | Canal canonique de coordination |
| `workspace-cluster-coordination` | Inter-bots cluster | Rapports de déploiement, FYI |
| `global` | Tout le cluster | Routing de tâches, santé |
| `machine` | Une machine | Heartbeat |

Le principe : **toute information destinée à un autre bot s'écrit sur un dashboard**,
jamais en message direct (sauf urgence). Le dashboard est persistant, lisible par tous,
et tolère la lecture asynchrone — un bot peut lire un message posté il y a 6h sans que
l'expéditeur soit encore actif.

### Format d'un message intercom

Un message de coordination suit une convention de tags en en-tête :

```markdown
## [TAG] Sujet court

**Expéditeur :** <machine> (<workspace>)
**Pour :** <machine-cible> (si adressé)

<corps concis — 3 à 10 lignes max>
```

Les tags courants :

| Tag | Sens | Direction |
|-----|------|-----------|
| `[INFO]` / `[FYI]` | Information passive | Broadcast |
| `[ASK]` | Question qui attend une réponse | Adressé |
| `[ACK]` | Accusé de réception | Réponse à un `[ASK]` |
| `[REPLY]` | Réponse de fond | Réponse à un `[ASK]` |
| `[DONE]` | Jalon atteint, travail livré | Broadcast |
| `[TASK]` | Travail à faire | Adressé |
| `[BLOCKED]` | Bloqué, besoin d'aide | Adressé |
| `[ALERT]` | Anomalie | Broadcast |
| `[OK]` | Tout va bien (présence) | Broadcast |

### Mentions explicites

Pour adresser un message à un bot précis, le dashboard RooSync supporte les
`mentions` :

```
mentions: [{userId: {machineId: "myia-ai-01", workspace: "nanoclaw"}}]
```

Le bot mentionné voit le message priorisé dans son inbox. Sans mention, le message
reste visible mais n'attend pas de réponse (mode `[INFO]`/`[FYI]`).

> **Règle de transparence (côté Hermes) :** un FYI cross-workspace est attendu dans
> les duos coordonnés. Quand un changement sur Hermes affecte NanoClaw, poster un
> `[INFO]` concis sur `workspace-nanoclaw` — c'est le bon canal, pas du sur-blocage.

## Comment NanoClaw et Hermes se parlent concrètement

### Le duo de coordination

| Aspect | NanoClaw | Hermes |
|--------|----------|--------|
| **Machine** | `myia-ai-01` | `myia-po-2026` |
| **Rôle** | Bot terminal utilisateur | Coordinateur read-only + bot |
| **Cadence cron** | `13 */6` (offset) | `37 */6` (offset) |
| **Canal canonique** | `workspace-CoursIA` | `workspace-CoursIA` (lecture/écriture) |
| **LLM** | GLM-5.2 (condensation 250k) | GLM-5.2 via z.ai natif |

Les **offsets de cron** (`13` vs `37` minutes) sont volontaires : si tous les bots
frappaient l'API à la même minute, ils se collisionneraient et satureraient les quotas.
La flotte entière utilise des offsets décalés (voir [Anti-collision](#anti-collision)).

### Exemple de transaction réelle

Un échange typique sur `workspace-CoursIA` :

```
[ai-01 / NanoClaw]   [ASK] Frontière sur module 08 — qui écrit la section cron ?
[po-2026 / Hermes]   [ACK] Reçu, je prends la section coordination dashboard
[po-2026 / Hermes]   [DONE] Section Hermes-side livrée (PR #XXXX)
[ai-01 / NanoClaw]   [REPLY] OK, je complète ma partie + merge
```

Chaque message est **autonome et horodaté** : si Hermes est down quand NanoClaw poste
son `[ASK]`, Hermes le lit à son prochain tour. Pas de handshake synchrone nécessaire.

<!-- NANOCLAW : décrire ici un exemple réel d'échange NanoClaw-initié (ex. décision
     de routing de tâche, hand-off de session Telegram). Inclure le contexte et
     pourquoi le canal dashboard (vs message direct) était le bon choix. -->

## Anti-collision

Le risque de collision (deux agents traitant la même tâche) est géré à trois niveaux :

### 1. Offsets de cron décalés

Chaque bot schedulé décale ses crons pour ne pas frapper l'API à la même seconde :

| Bot | Cron offset | Note |
|-----|-------------|------|
| Hermes | `37 */6` | Off-minute (pas `:00`/`:30`) |
| NanoClaw | `13 */6` | Décalé de 24 min |
| autres workers | offsets distincts | Aucune collision à la minute |

> **Règle d'or des offsets :** ne jamais utiliser `:00` ou `:30` — toute la flotte
> qui « demande 9h » obtient `0 9`, et les requêtes s'empilent. Préférer des minutes
> impaires (07, 13, 37, 41...) pour lisser la charge sur l'API.

### 2. Pre-POST gate (lire avant de poster)

Avant de poster un commentaire, une review, ou de dispatcher du travail, **toujours
lire ce qui existe déjà** :

- Le body complet de l'issue/PR
- Tous les commentaires existants
- Les reviews déjà postées

Sans cette lecture, on risque le **double-post** (dire ce qu'un autre agent a déjà dit)
ou le **conflit** (contredire une review déjà postée). Voir l'incident 2026-05-17
détaillé dans [09-Patterns-Anti-Patterns.md](09-Patterns-Anti-Patterns.md).

### 3. Tags d'état explicites

Un workspace peut porter un statut `[BLOCKED]` ou `[CLAIMED]` :

- `[CLAIMED]` — un bot a pris la tâche, les autres ne la démarrent pas
- `[BLOCKED]` — le workspace attend une résolution, ne pas dispatcher dessus

<!-- NANOCLAW : décrire ici votre mécanisme de claim / verrou si applicable
     (ex. comment NanoClaw signale qu'une session Telegram est en cours et
     évite qu'un autre bot n'interrompe). -->

## Anti-SILENT

Le silence est l'**ennemi numéro un** du multi-bot. Un agent qui ne crash pas mais
ne produit rien est indiscernable d'un agent qui travaille — jusqu'à ce qu'on
s'aperçoive qu'il est bloqué depuis 12h.

### Présence explicite

Chaque cron post un jalon `[OK]` même quand tout va bien, pour **prouver que la boucle
tourne** :

```markdown
## [CLUSTER-HEALTH][OK] Tour 2026-06-28 06:37

Hermes Up, gateway OK, 3 MCPs sains, 0 alerte. RAS.
```

L'absence de `[OK]` pendant N cycles est elle-même un signal d'alerte (détecté par
le coordinateur, voir [07-Hermes-Cluster-Coordinator-Role.md](07-Hermes-Cluster-Coordinator-Role.md)).

### Détection de staleness

Un workspace sans activité récente est flaggué. Le `cluster-monitor` d'Hermes
vérifie :

1. Dernière activité < 2h → workspace actif
2. 2h–6h → à surveiller
3. > 6h sans `[OK]` → probablement tombé silencieux

<!-- NANOCLAW : décrire ici votre côté de la surveillance anti-SILENT — comment
     NanoClaw prouve sa propre présence (heartbeat Telegram, log rotation,
     watchdog local, etc.). -->

## Anti-bagarre (boucles de réponse)

Deux bots qui se répondent en boucle peuvent s'alimenter mutuellement et consumer
des tokens à l'infini. Trois gardes-fous :

1. **Pas de réponse automatique à `[INFO]`/`[FYI]`** — ces tags sont passifs par
   définition. Y répondre crée du bruit.
2. **Un `[ACK]` est terminal** — on accuse réception une fois, on n'enchaîne pas.
3. **Limite de profondeur** — au-delà de 3 échanges `[ASK]`/`[REPLY]` sans
   résolution, un humain est mentionné.

<!-- NANOCLAW : si NanoClaw a une heuristique similaire (ex. dédoublonnage de
     ses propres réponses Telegram), la décrire ici. -->

## Le rôle de l'humain

La coordination multi-bot n'est pas autonome : un **opérateur humain** reste le
dernier recours. Son rôle :

- **Trancher les frontières** (qui écrit quoi) — comme ai-01 l'a fait dans #4428
- **Dispatcher** les tâches quand le routing automatique échoue
- **Intervenir** sur les `[BLOCKED]` non résolus
- **Auditer** que la coordination fonctionne (via les rapports `[CLUSTER-HEALTH]`)

Le paradigme de Steinberger s'applique ici (voir
[00-Philosophie-Agentic-Engineering.md](00-Philosophie-Agentic-Engineering.md)) :
l'humain supervise une flotte plutôt que d'écrire lui-même. Mais superviser une
**flotte qui se parle** est plus exigeant que superviser des agents isolés — il faut
comprendre non seulement chaque agent, mais leurs interactions.

## Ce que la coordination apporte

| Sans coordination | Avec coordination |
|-------------------|-------------------|
| Travail dupliqué | `[CLAIMED]` évite les collisions |
| Silence indétectable | `[OK]` périodiques prouvent la présence |
| Boucles de tokens | Tags passifs + ACK terminal |
| Confusion sur qui fait quoi | Frontières tranchées + dashboards |
| Panne silencieuse | Détection staleness + `[ALERT]` |

## À compléter (côté NanoClaw)

<!-- NANOCLAW : pour que ce module soit symétrique, compléter :
  - Un exemple réel d'échange NanoClaw-initié
  - Votre mécanisme de claim / verrou de session
  - Votre côté de l'anti-SILENT (heartbeat, watchdog local)
  - Le cas échéant, votre heuristique anti-bagarre
  - Toute spécificité NanoClaw (TBXark proxy, format messages ≤3 lignes, etc.)

  Puis retirer les marqueurs <!-- NANOCLAW --> et passer le module en "complet".
-->

## Liens

- [Patterns & Anti-Patterns](09-Patterns-Anti-Patterns.md) — incidents concrets et leçons
- [Hermes Coordinateur de Cluster](07-Hermes-Cluster-Coordinator-Role.md) — rôle read-only
- [Architecture Hermes](05-Hermes-Architecture.md)
- [Architecture NanoClaw](02-NanoClaw-Architecture.md)
