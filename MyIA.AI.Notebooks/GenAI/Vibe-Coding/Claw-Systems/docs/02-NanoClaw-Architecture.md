# NanoClaw v2 — Architecture technique

[← Claw-Systems](../README.md) | [↑ ..](../README.md)

> Ce chapitre décrit le **NanoClaw v2 réel**, tel qu'il tourne en production sur le
> cluster CoursIA (le bot **ClusterManager** sur la machine `ai-01`, accessible par
> Telegram). Le *principe fondateur* — « tout est message » — est raconté en récit
> dans [M1 — Le modèle « tout est message »](M1-tout-est-message.md) ; ce document-ci
> en donne l'**architecture technique** : les processus, les bases de données, et le
> cycle de vie d'une requête. Lire M1 d'abord si vous voulez le « pourquoi » ; ce
> chapitre est le « comment ».

## De la v1 à la v2 : pourquoi une réécriture

Les premières versions de NanoClaw suivaient le modèle classique des bots LLM : **une
seule boucle agentique**, dans **un seul conteneur**, qui écoute Telegram, appelle un
LLM (via OpenRouter ou un modèle local), exécute des outils, et répond. Simple, mais
fragile dès qu'on veut **plusieurs conversations isolées**, **plusieurs agents** aux
personnalités distinctes, ou une **frontière de sécurité** nette entre ce que voit un
utilisateur et ce que voit un autre.

NanoClaw **v2** est une réécriture *from scratch* qui inverse la structure : au lieu
d'un agent monolithique, on a **un hôte Node unique** qui orchestre des **conteneurs
d'agents éphémères, un par session**. L'hôte ne raisonne pas — il route. Les agents ne
routent pas — ils raisonnent. Et entre les deux, **rien ne circule qui ne soit un
message** écrit dans une base SQLite.

| | v1 (modèle conceptuel antérieur) | v2 (production réelle) |
|---|---|---|
| **Topologie** | 1 conteneur = 1 agent | 1 hôte Node + N conteneurs (1 par session) |
| **Communication hôte↔agent** | en-process (même boucle) | **uniquement** via 2 bases SQLite par session |
| **Isolation** | aucune (un seul espace) | par session + par groupe d'agents |
| **Plateformes** | Telegram | adaptateurs de canal (Telegram, Discord, Slack, …) installés par skill |
| **Secrets** | variables d'environnement | injectés par requête via le vault OneCLI |

## Le principe fondateur : « tout est message »

La décision structurante de la v2 tient en une phrase : **il n'y a ni IPC, ni file
watcher, ni pipe stdin entre l'hôte et le conteneur.** Les **deux bases SQLite** d'une
session sont la **seule** surface d'entrée/sortie entre les deux mondes.

Un message Telegram entrant devient une ligne dans une base. La réponse de l'agent
devient une ligne dans une autre base. Le « réveil » d'un conteneur est un message. Un
redémarrage planifié est un message. Une question en attente d'approbation est un
message. Cette uniformité est ce qui rend le système **observable** (tout est dans
SQLite, inspectable à froid), **rejouable**, et **robuste aux crashs** (un conteneur
qui meurt ne perd rien — l'état durable est dans les bases, pas dans sa mémoire).

> Le récit de *pourquoi* ce choix — et ce qu'il coûte — est dans
> [M1 — Le modèle « tout est message »](M1-tout-est-message.md).

## Le modèle d'entités

Avant de router un message, il faut savoir **qui** parle, **où**, et **à quel agent**.
La v2 modélise cela par une chaîne d'entités, du concret (un humain sur une plateforme)
vers l'abstrait (une session de conteneur) :

```
users                 «<canal>:<handle>» — une identité de plateforme (kind, display_name)
  ↓  appartiennent à
messaging_groups      un chat / canal sur une plateforme (instance = adaptateur)
  ↕  reliés N-à-N via messaging_group_agents (session_mode, trigger_rules, priorité)
agent_groups          un agent : workspace, mémoire, CLAUDE.md, personnalité, config conteneur
  ↓  produisent
sessions              (agent_group + messaging_group + thread_id) → un conteneur dédié
```

Le **privilège** est porté par l'utilisateur (`owner` / `admin`, global ou *scopé* à un
groupe d'agents), pas par le groupe d'agents. Trois niveaux d'isolation sont possibles
entre canaux : `agent-shared`, `shared`, ou agents séparés. Une **session** est
l'intersection d'un agent, d'un canal, et d'un fil de discussion : c'est **l'unité de
conteneur** et, de fait, l'unité d'isolation à l'exécution.

## Vue d'ensemble du flux

Le trajet complet d'un message, de la plateforme à la réponse :

```
  Utilisateur Telegram
        │  (message texte / vocal)
        ▼
  Adaptateur de canal  ──────────────►  HÔTE (un seul process Node)
        │                                     │
        │                              router.ts : messaging_group → agent_group → session
        │                                     │
        │                                     ▼   écrit
        │                              ┌──────────────┐
        │                              │  inbound.db  │  messages_in (+ réveille le conteneur)
        │                              └──────┬───────┘
        │                                     │  lit (poll)
        │                                     ▼
        │                       CONTENEUR (par session, runtime Bun)
        │                         agent-runner : poll → Claude Agent SDK → outils → réponse
        │                                     │  écrit
        │                              ┌───────▼──────┐
        │                              │ outbound.db  │  messages_out, session_state
        │                              └──────┬───────┘
        │                                     │  lit (poll)
        ◄─────────────────────────────  delivery.ts : livre via l'adaptateur
  Réponse Telegram
```

Points-clés : **l'hôte ne parle jamais directement au conteneur** (il écrit dans
`inbound.db` et lit `outbound.db`) ; **le conteneur ne parle jamais directement à
l'hôte** (il lit `inbound.db` et écrit `outbound.db`). Le réveil lui-même n'est pas un
signal système : c'est une nouvelle ligne dans `messages_in`.

## Le split two-DB par session

Chaque session possède **deux** fichiers SQLite sous
`data/v2-sessions/<session_id>/` :

| Fichier | Écrit par | Lu par | Contenu principal |
|---------|-----------|--------|-------------------|
| `inbound.db` | **hôte** | conteneur | `messages_in`, routing, destinations, `pending_questions`, `processing_ack` |
| `outbound.db` | **conteneur** | hôte | `messages_out`, `session_state` |

La règle invariante : **exactement un écrivain par fichier**. C'est ce qui évite toute
contention de verrou entre deux montages (l'hôte et le conteneur voient les mêmes
fichiers via des montages séparés). Deux garde-fous concrets en découlent :

- **Parité des `seq`** : l'hôte numérote ses messages avec des `seq` **pairs**, le
  conteneur avec des `seq` **impairs**. Impossible de collisionner sur un numéro de
  séquence, même en écriture concurrente sur des fichiers distincts.
- **Le heartbeat est un *touch* de fichier**, pas une écriture en base. Le conteneur
  prouve qu'il est vivant en touchant `/workspace/.heartbeat` ; l'hôte lit la *mtime*.
  Aucune transaction SQLite n'est nécessaire pour le battement de cœur — donc aucune
  contention parasite.

Cette séparation est *load-bearing* : elle est aussi ce qui rend le système
inspectable. Pour une requête ad hoc depuis un skill ou un script, on passe par le
wrapper en arbre plutôt que par le binaire `sqlite3` :

```bash
pnpm exec tsx scripts/q.ts data/v2-sessions/<session_id>/inbound.db \
  "SELECT seq, role, substr(content,1,60) FROM messages_in ORDER BY seq DESC LIMIT 5"
```

## La base centrale

Tout ce qui n'est **pas** par-session vit dans une base centrale unique,
`data/v2.db` : `users`, `user_roles`, `agent_groups`, `messaging_groups`, le câblage
(`messaging_group_agents`), `pending_approvals`, `user_dms`, les tables du pont Chat
SDK, et `schema_version`. Les migrations sont versionnées sous `src/db/migrations/`.

On a donc un **modèle à trois bases** : une base centrale (l'état partagé) et, par
session, une paire entrée/sortie (le flux de messages). Aucune de ces bases n'est
partagée en écriture entre deux processus.

## Le runtime : deux mondes, un seul canal

L'hôte et le conteneur n'exécutent **pas le même runtime**, et ne partagent **aucun
module** :

| | Hôte | Conteneur (agent-runner) |
|---|---|---|
| **Runtime** | Node | Bun |
| **Gestionnaire de paquets** | pnpm | bun |
| **Rôle** | routage, livraison, *sweep*, cycle de vie des conteneurs | poll, appel LLM, exécution d'outils |
| **LLM** | — | via le **Claude Agent SDK** (abstraction de provider) |

Le conteneur est piloté par le **Claude Agent SDK**, derrière une abstraction de
provider (le provider `claude` est intégré ; d'autres, comme OpenCode, s'installent
depuis la branche `providers`). Le **modèle** est configurable par groupe d'agents (via
la config conteneur en base, ou `.env`) : en production sur `ai-01`, ClusterManager
tourne sous **GLM-5.2**, avec une fenêtre de condensation plafonnée à 250k tokens. La
config runtime par groupe (provider, modèle, paquets, serveurs MCP, montages) vit dans
la table `container_configs` et est **matérialisée** en `groups/<folder>/container.json`
au moment du *spawn*, pour que le *runner* de conteneur puisse la lire.

> Hôte et conteneur ne communiquent **que** par les bases de session. Il n'y a aucun
> appel de fonction, aucun socket, aucun module commun entre les deux arbres de code —
> c'est la traduction concrète de « tout est message ».

## Les secrets : le vault OneCLI

Aucune clé d'API, token OAuth, ou credential ne transite par une variable
d'environnement ni par le contexte de chat. Les secrets sont gérés par le **gateway
OneCLI** et **injectés dans le conteneur au moment de la requête**. Le conteneur
apprend à utiliser ce proxy via un *skill* dédié (`onecli-gateway`), qui lui enseigne
notamment à **ne jamais demander de credentials bruts**. Conséquence pratique : un
`401` sur une API dont la clé *est* pourtant dans le vault signale en général un agent
en mode `selective` plutôt qu'un secret manquant (voir
[03-NanoClaw-Deploy.md](03-NanoClaw-Deploy.md)).

## Les canaux : des adaptateurs installés par skill

Le tronc commun NanoClaw ne livre **aucun** adaptateur de canal spécifique : le dépôt
est l'**infrastructure** (registre, pont Chat SDK), et les adaptateurs réels
(Telegram, Discord, Slack, WhatsApp, …) vivent sur une branche `channels` et sont
copiés en place par des skills `/add-<canal>` idempotents. Même logique pour les
providers non-Claude (branche `providers`). On garde ainsi un tronc minimal et on
n'embarque que ce dont une installation a besoin.

## Points de vigilance

- **Un seul écrivain par base.** Ne jamais faire écrire l'hôte dans `outbound.db` ni le
  conteneur dans `inbound.db` — c'est l'invariant qui tient tout le modèle.
- **Les logs du conteneur sont éphémères** (`--rm`). Si un agent échoue silencieusement
  *dans* le conteneur, il n'y a pas de log persistant : c'est `messages_in` /
  `messages_out` qu'on inspecte pour savoir où la chaîne s'est interrompue.
- **`journal_mode=DELETE`** sur les bases de session est *load-bearing* pour la
  visibilité cross-montage — ne pas le passer en WAL.
- **Sécurité.** Le token de bot ne doit jamais être commité ; les credentials passent
  par le vault, pas par `.env` versionné.

## Pour aller plus loin

- [03-NanoClaw-Deploy.md](03-NanoClaw-Deploy.md) — déployer NanoClaw (service, build du
  conteneur, vault de secrets, montages).
- [04-ASR-Integration.md](04-ASR-Integration.md) — la transcription vocale (Whisper
  auto-hébergé).
- [08-Multi-Bot-Coordination.md](08-Multi-Bot-Coordination.md) — comment plusieurs
  Claws coexistent (intercom, mentions, anti-collision).
- [09-Patterns-Anti-Patterns.md](09-Patterns-Anti-Patterns.md) — les leçons de
  production (incidents réels → correctifs).

## Liens

- [M1 — Le modèle « tout est message »](M1-tout-est-message.md) — le récit du principe fondateur
- [Architecture Hermes](05-Hermes-Architecture.md) — le second Claw system du cluster
- [Claw-Systems (README)](../README.md)
