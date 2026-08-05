# Règles globales machine — détail déporté

Détail des règles portées par `~/.claude/CLAUDE.md` (harnais **machine**, auto-chargé dans tous les workspaces). La règle y reste succincte ; le détail — matrices complètes, verbatims, incidents fondateurs — vit ici et se lit à la demande.

**Source de vérité du harnais global** : `.claude/configs/user-global-claude.md` dans le dépôt **roo-extensions**, déployé en `~/.claude/CLAUDE.md` sur chaque machine. Un trim local est écrasé au prochain déploiement s'il n'est pas répercuté à la source.

---

## Read Body Before Any Action

Règle HARD, aucune exception. Avant de **poster un commentaire**, **reviewer**, **merger**, **dispatcher du travail**, ou **commencer un fix** sur une issue/PR, lire :

1. **Le body complet** (description, scope, décisions, caveats déjà documentés)
2. **Tous les commentaires existants** (`gh pr view N --json comments`, `gh issue view N --comments`)
3. **Toutes les reviews déjà postées** (`gh pr view N --json reviews`) — humains ET bots, avec leur `state` (APPROVED / CHANGES_REQUESTED / COMMENTED)
4. **Le diff** (`gh pr diff N` ou `git diff base..head`) avant review ou merge

Le titre seul n'est pas la PR. Le `mergeStateStatus` seul n'est pas une review. Sauter cette lecture = agir à l'aveugle.

### Matrice action → lecture obligatoire

| Action | Lecture obligatoire avant |
|---|---|
| `gh pr comment N` | body PR + tous comments + toutes reviews existantes |
| `gh pr review N` | idem + diff complet |
| `gh pr merge N` | idem + `mergeStateStatus` + `reviews[].state == "CHANGES_REQUESTED"` **et** comments inline non-résolus → **NE PAS merger** si demandes non-adressées |
| `gh issue comment N` | body issue + tous comments existants |
| Dispatch d'une tâche sur une issue | body issue + comments + linked PRs |
| Fix d'un bug basé sur une issue | body issue + comments + PRs liées + diagnostic existant |
| Audit reassessment | body audit + le code source réel (vérification > mémo) |

### Anti-patterns interdits

- « Le titre dit X, je traite X » → lire le body, X peut être autre chose
- « Le bot a APPROVED, je merge » → lire le body PR + comments humains + CHANGES_REQUESTED
- « Je connais le sujet, je sais quoi dire » → lire ce qui a déjà été dit, ne pas dupliquer/contredire
- « L'issue est ouverte depuis 2 jours, je commence à fix » → lire si un autre agent a déjà commencé/diagnostiqué/abandonné
- « Pas de redite » en reviews : vérifier qu'aucun reviewer n'a déjà soulevé le point

### Incident fondateur (2026-05-17, ai-01 sur CoursIA)

6 reviews détaillées postées sur des PRs étudiantes EPITA Contraintes, avec des sections « Questions pour la soutenance » **en duplicate ET en conflit** avec les reviews brèves bienveillantes déjà postées par un autre agent (`jsboigeEpita`) — la veille de la soutenance.

Si les comments existants avaient été lus AVANT, l'incident aurait été détecté : (a) style bref bienveillant déjà adopté, (b) un autre agent était en charge des reviews publiques, (c) fuite jury par-dessus la review de l'autre agent. La règle « lire avant » détecte les incohérences avant le post.

---

## Multi-Machine Ping-Pong — Re-arm

Le cluster ne fonctionne en continu que si chaque agent (coordinateur ET workers) ré-arme son réveil à la fin de chaque turn où il a terminé tout ce qu'il pouvait faire seul. Sans re-arme, l'agent s'endort pendant que le cluster continue à produire du travail (PRs, reviews, dispatches) — ping-pong rompu.

Mandat user 2026-05-19 (incident R67/R68 sur ai-01) : « dans le cadre d'une tâche interactive avec messages utilisateurs, ça doit être systématique pour le ping-pong entre le coordinateur et les workers ».

### Quand re-armer, par rôle

| Rôle | Déclencheur | Prompt typique |
|---|---|---|
| **Coordinateur** | Après dispatch à TOUS les workers + complétion de ses tâches individuelles (merges, reviews, bilan), en attente des prochaines PRs/reports | `/coordinate` |
| **Worker** | Après soumission de TOUTES ses PRs (attente review/merge) + complétion des tâches dispatchées, en attente du prochain dispatch | `/executor` ou prompt worker spécifique |

### Cadence — cron porté, pas ScheduleWakeup

`ScheduleWakeup` est clampé runtime à `[60, 3600]s` (max 1 h) : **il ne PEUT PAS porter un cycle multi-heures**. Conséquences :

- **Coordinateur piloté par cron** : `CronCreate("<minute off-:00> */<N> * * *", "/coordinate")` (job session-only, auto-expire 7 j). **NE PAS re-armer un `ScheduleWakeup` par-dessus** — cela ré-introduirait un cycle plus court que la cadence décidée.
- **Sessions interactives coord/worker NON pilotées par cron** : `ScheduleWakeup(delaySeconds: 3540, …)` à chaque fin de turn pour ne pas rompre le ping-pong. C'est le **plafond technique**, pas un mandat de cadence horaire.
- **Jitter** : minute off-`:00` (ex. 3540 s = 59 min) pour éviter que tous les agents frappent l'API à la même seconde.
- **Auto-régulation** via cap 3-IDLE (#2185, par exécutant) + override urgent `[WAKE-CLAUDE]` routé `machine:workspace` (début de ligne sur un append dashboard). **PAS** via timer adaptatif — ne pas faire varier l'intervalle « selon la charge perçue ».

### Scope STRICT — quand la règle s'applique

EXCLUSIVEMENT : sessions Claude Code **interactives** (REPL avec messages utilisateur) où l'agent joue **activement** un rôle **coordinateur** OU **worker** dans un workflow multi-machine.

### Quand elle NE s'applique PAS

| Type d'interaction | Re-arme ? | Pourquoi |
|---|---|---|
| Workers schedulés (Task Scheduler, cron, `start-claude-worker.ps1`) | **NON** | Cadence gérée externalement — re-armer = double-firing |
| Méta-analystes scheduled (cycle 72 h) | **NON** | Cadence externe (`start-meta-audit.ps1`) |
| Sessions interactives informationnelles (Q/R, pas de rôle coord/worker actif) | **NON** | Pas de ping-pong à entretenir |
| Sessions interactives ad-hoc / debugging / one-shot | **NON** | Pas de ping-pong à entretenir |
| Workspace single-machine (pas de cluster) | **NON** | Pas de cluster à animer |
| Handoff documenté (un autre agent assume la suite) | **NON** | Continuité portée par l'autre agent |

**Heuristique** : « Y a-t-il un cluster d'autres machines en train de produire du travail dont je dois m'occuper au tour suivant ? » — si OUI **et** session interactive **et** rôle coord/worker → re-arme. Sinon → pas de re-arme.

Le champ `reason` du `ScheduleWakeup` doit être informatif (visible en télémétrie et par le user).

---

## Voir aussi

- `~/.claude/CLAUDE.md` — le harnais global (règles succinctes)
- [`.claude/rules/harness-hygiene.md`](../../.claude/rules/harness-hygiene.md) — les 3 tiers d'information
- [`.claude/rules/coordinator-discipline.md`](../../.claude/rules/coordinator-discipline.md) — discipline coordinateur
- [`.claude/rules/proactive-coordination.md`](../../.claude/rules/proactive-coordination.md) — L740 (re-arm des crons expirés)
