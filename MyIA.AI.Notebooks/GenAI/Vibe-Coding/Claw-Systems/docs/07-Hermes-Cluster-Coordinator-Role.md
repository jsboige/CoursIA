# Hermes — Coordinateur de Cluster

[← Claw-Systems](../README.md) | [↑ ..](../README.md)

Au-dela d'être un bot Telegram, Hermes joue un **rôle d'orchestrateur read-only**
pour le cluster Myia AI. Il route les tâches, audite la santé, et suit les
hand-offs entre workspaces — sans jamais modifier de code.

Ce rôle répond a un besoin concret : quand plusieurs agents tournent sur
plusieurs machines (NanoClaw sur ai-01, Hermes sur po-2026, des workers
schedulés ailleurs), **quelqu'un doit garder la vue d'ensemble**. Hermes est ce
quelqu'un.

## Principe : read-only

Hermes **lit** l'état du cluster et **écrit des décisions** (sur des dashboards),
mais ne modifie jamais les dépôts, le code, ni l'infrastructure.

| Hermes FAIT | Hermes NE FAIT PAS |
|-------------|--------------------|
| Lire les dashboards de tous les workspaces | Écrire/modifier du code |
| Écrire sur le dashboard global (routing, santé) | Gérer les serveurs MCP |
| Suivre les hand-offs entre workspaces | Pousser vers git |
| Alerter sur les anomalies (machines stale, seuils) | Exécuter des builds/tests |

Cette frontière est volontaire : un coordinateur qui écrit du code devient un
développeur de plus, et perd sa neutralité d'arbitre.

## Canaux de communication

| Canal | Outil | Usage |
|-------|-------|-------|
| **Coordination** | dashboard `workspace-cluster-coordination` | Rapports de déploiement, coordination inter-bots |
| **Global** | dashboard `global` | Décisions de routing, rapports de santé |
| **Lecture** | dashboard `workspace-<nom>` | Lire n'importe quel workspace |
| **Alertes** | messagerie inter-machines (`roosync_send`) | Notifications urgentes cross-machine |
| **Statut** | dashboard `machine` | Heartbeat au niveau machine |

> **Règle de transparence :** un FYI cross-workspace est attendu dans les duos
> coordonnés. Quand un changement sur Hermes affecte un bot collaborateur
> (NanoClaw par ex.), poster un `[INFO]`/`[FYI]` concis sur le dashboard de ce
> workspace — c'est le bon canal, pas du sur-blocage.

## Deux agents internes

### 1. cluster-monitor

Audit de santé périodique a travers tous les workspaces. Lit chaque dashboard,
résume l'état du cluster, poste un rapport `[CLUSTER-HEALTH]` sur le dashboard
global. Détecte : machines stale (sans activité récente), seuils de condensation
approchés, tags `[BLOCKED]`/`[ALERT]` non traités.

### 2. task-router

Surveille le dashboard global pour les requêtes `[TASK-ROUTE]`. Évalue les
règles de routing et poste `[DELEGATED]` sur le dashboard du workspace cible.

Le routing Phase 1 est **par mots-clés** : `fix`/`feat`/`refactor` → roo-extensions
(code), `docker`/`nanoclaw` → nanoclaw (infra), `train`/`model` → CoursIA (ML),
etc. Une Phase 2future utiliserait la recherche sémantique.

## Protocol de session

### Début de session
1. Lire le dashboard global (`roosync_dashboard(type: "global")`)
2. Lister tous les dashboards (`roosync_dashboard(action: "list")`)
3. Lire les dashboards des workspaces actifs
4. Poster `[ONLINE]` sur le dashboard global

### Pendant la session
- Surveiller les `[TASK-ROUTE]` sur le dashboard global
- Générer les rapports `[CLUSTER-HEALTH]` (à la demande ou schedulés)
- Suivre les changements de statut `[HAND-OFF]`

### Fin de session
1. Poster `[OFFLINE]` sur le dashboard global
2. Bilan : workspaces audités, tâches routées, alertes envoyées

## Protocol de hand-off (cross-workspace)

Tout hand-off suit un cycle de vie explicite, tracé sur le dashboard global :

```
Initiated → In Transit → Acknowledged → Processing → Complete → Closed
```

| État | Sens | Qui le pose |
|------|------|-------------|
| `Initiated` | Le workspace source poste la tâche sur le global | Source |
| `In Transit` | Hermes route vers le workspace cible | Hermes |
| `Acknowledged` | La cible confirme la réception | Cible |
| `Processing` | La cible commence a travailler | Cible |
| `Complete` | La cible poste le résultat | Cible |
| `Closed` | Hermes enregistre la complétion | Hermes |

### SLA par priorité

| Priorité | ACK | Processing | Completion |
|----------|-----|------------|------------|
| URGENT | 15 min | 1h | 4h |
| HIGH | 30 min | 4h | 24h |
| MEDIUM | 2h | 24h | 48h |
| LOW | 24h | 48h | 1 semaine |

En cas de breach SLA : Hermes poste un `[SLA-ALERT]`, notifie la machine cible,
et après 2× breach, route la tâche vers le workspace suivant disponible.

## Tags utilisés

| Tag | Usage |
|-----|-------|
| `[CLUSTER-HEALTH]` | Rapports de santé périodiques |
| `[TASK-ROUTE]` | Requêtes de routing de tâche (entrée) |
| `[DELEGATED]` | Confirmation de délégation (sortie) |
| `[HAND-OFF]` | Suivi de hand-off cross-workspace |
| `[ALERT]` | Notifications d'anomalie cluster |
| `[ONLINE]` / `[OFFLINE]` | Disponibilité Hermes |

## Règles de routing (Phase 1)

| Type de tâche | Mots-clés | Workspace cible |
|---------------|-----------|-----------------|
| Code | `fix`, `feat`, `refactor`, `build`, `test` | `roo-extensions` |
| Conteneur/Docker | `docker`, `container`, `nanoclaw` | `nanoclaw` |
| Documentation | `docs`, `README`, `CLAUDE.md` | au choix |
| ML/Training | `train`, `model`, `GPU`, `epoch` | `CoursIA` |
| Infrastructure | `MCP`, `server`, `config`, `deploy` | `roo-extensions` |
| Inconnu | — | `roo-extensions` (défaut sûr) |

### Check de capacité avant routing

Avant de router vers un workspace, vérifier :
1. Utilisation dashboard < 80 % (sous le seuil de condensation)
2. Dernière activité < 2h (workspace actif)
3. Pas de statut `[BLOCKED]` sur le workspace

Si le check échoue → router vers le workspace suivant, ou garder sur le global.

## Surveillance et anti-SILENT

Un risque réel en cluster multi-agents : un agent qui **tombe silencieux**
(sans crash visible, mais sans produire de travail non plus). Hermes combat ça
par :

- **Présence chat** : les crons postent un jalon `[OK]` même quand tout va bien,
  pour prouver que la boucle tourne
- **Détection de staleness** : un workspace sans activité récente est flaggué
- **Cadence** : cluster-tour 12h + self-check 2×/jour (compromis économie tokens
  / réactivité), doublés côté hôte par des watchdogs 15–30 min (voir ci-dessous)

### Vérifier ce que les bots PEUVENT FAIRE et DISENT

L'incident le plus instructif du domaine (août 2026, ~3,5 jours) : le backend
MCP derrière le proxy est mort **en gardant un handshake vert** — processes,
ports et freshness tous OK, pendant que chaque appel d'outil échouait en silence.
Les deux bots du cluster ont **dit** (« bus down, 40+ cycles ») et personne ne
lisait leurs messages. Depuis, la surveillance est **capability-first** :

1. **Capability** : sonder le chemin d'écriture réel (appel d'outil, pas le
   handshake) — c'est le rôle de `mcp-chain-watchdog` côté ai-01
2. **Parole** : lire ce que les bots rapportent (regex `bus down|undelivered|
   fallback|write failed` sur leurs messages) — c'est le check 8 de la routine
   opérateur
3. **Jamais attribuer un post manquant au prompt-skip** avant d'avoir écarté un
   bus mort (l'attribution erronée d'août a coûté 3 jours de diagnostic)

### La surcouche opérateur (session Claude Code hôte)

En plus du bot, une **session Claude Code sur la machine hôte** porte un cron de
surveillance 12h (`17 */12`, self-re-arming) qui exécute une routine à 8
vérifications : container/gateway, fraîcheur des crons, activité reviews,
watchdogs, NanoClaw, tour global, **lecture des messages des bots**. L'escalade
est volontairement bornée à 5 critères durs (container down, reviews >4h,
NanoClaw >36h, global >36h, bus MCP down) — tout le reste est [INFO], pas
[ALERT]. Cette discipline évite la fatigue d'alerte, le vrai tueur des systèmes
de surveillance.

Voir [08-Multi-Bot-Coordination.md](08-Multi-Bot-Coordination.md) pour le
concret de la coordination Hermes ↔ NanoClaw, et
[09-Patterns-Anti-Patterns.md](09-Patterns-Anti-Patterns.md) pour les patterns
de résilience (dont le mécanisme anti-SILENT).

## Contraintes

1. **Pas d'opérations git** — Hermes lit l'état, ne modifie jamais les dépôts
2. **Pas de modif de code** — ce n'est pas un agent d'implémentation
3. **Pas de gestion MCP** — l'infra est gérée par d'autres workspaces
4. **Pas de secrets** — Hermes n'a pas besoin de clés au-dela de l'accès MCP

> **Exception documentée :** pour une mission explicite validée par le sponsor
> (ex. étoffement de cette section Claw-Systems), Hermes peut sortir de son
> rôle read-only et contribuer a un dépôt via worktree dédié + PR. C'est alors
> un travail **déporté et borné**, pas un changement de rôle permanent.

## Liens

- [Architecture Hermes](05-Hermes-Architecture.md)
- [Déploiement Hermes (s6-overlay)](06-Hermes-Deploy-s6-Overlay.md)
- [Coordination Multi-Bot](08-Multi-Bot-Coordination.md)
