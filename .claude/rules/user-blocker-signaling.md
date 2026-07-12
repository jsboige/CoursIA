# User-blocker signaling — anti-dilution

S'applique a **tous les agents** du cluster CoursIA (workers `po-*` + coordinateur `ai-01`). Source : mandat user 2026-05-28T12:48Z (verbatim + workers/coordinator detail + categories + anti-patterns) : [docs/user-blocker-signaling-detail.md](../../docs/reference/user-blocker-signaling-detail.md).

## Regle HARD

Quand un livrable d'agent **depend d'une action user non faite** (relecture, validation subjective, export manuel, signature, confirmation, sign-off), le bloqueur **doit etre signale explicitement a chaque fin de session** — pas dilue dans `[DONE]` long, pas laisse dependre du wakeup.

| Agent | Mecanisme | Cadence |
|-------|-----------|---------|
| Workers `po-*` | Tag `[ASK USER] <action> — bloque depuis <N>` separe du `[DONE]` | A CHAQUE fin de session |
| Workers `po-*` | Ping en **premier** si user-message recu | Sur session interactive detectee |
| Workers `po-*` | Escalation `roosync_messages send` priority HIGH vers ai-01 | Apres 5 sessions sans action (~15h) |
| ai-01 | Section "Actions user en attente" en tete `/coordinate` | Chaque wakeup |
| ai-01 | Post `[ESCALATION USER]` en tete dashboard | Bloqueur > 3 cycles (~9h) |
| ai-01 | Rappel actifs en fin de session, meme si rien n'a change | Chaque fin |

**Anti-patterns** : diluer dans rapport DONE long ; attendre passivement le wakeup ; mentionner une fois puis disparaitre ; lister 5 user-blocks en bloc sans hierarchie ; "le user n'a pas regarde" sans re-pinger.

## Voir aussi

- [docs/user-blocker-signaling-detail.md](../../docs/reference/user-blocker-signaling-detail.md) — verbatim, categories, anti-patterns, interaction regles
- [coordinator-discipline.md](coordinator-discipline.md) — symetrique cote agent ("aucune demande user ne pourrit > 1 cycle")
- [proactive-coordination.md](proactive-coordination.md) — 1 PR/wakeup + main + side-track
