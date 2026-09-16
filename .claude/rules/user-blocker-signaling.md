# User-blocker signaling — registre durable

S'applique à **tous les agents** du cluster CoursIA (workers `po-*` + coordinateur `ai-01`). Sources : mandat user 2026-05-28T12:48Z sur la visibilité des blocages, puis mandat supersédant du 2026-09-15 (#3656) : le user arbitre **par pull, pas par push**. Détail et articulation : [docs/user-blocker-signaling-detail.md](../../docs/reference/user-blocker-signaling-detail.md).

## Règle HARD

Toute question ou action qui attend le user est écrite immédiatement dans le registre persistant du workspace :

`~/.claude/projects/<hash>/memory/user-question-registry.md`

Le registre est indexé dans `MEMORY.md`. Chaque entrée ouverte porte obligatoirement :

1. **ce qui est attendu du user** ;
2. **comment vérifier qu'elle est morte**.

En fin de session, les questions ouvertes sont restituées **en un seul bloc** depuis ce registre. Une question non répondue survit aux reprises de cron et se représente au cycle suivant ; elle n'est jamais re-postée séparément dans le fil ou dupliquée dans une seconde liste. Une réponse vérifiée déplace l'entrée dans la courte section « répondues ».

Les tags `ASK` / `[ASK USER]` et la section « Actions user en attente » sont des **signaux ponctuels** : ils pointent vers le registre, qui seul porte l'état durable. Ils ne créent pas une file parallèle et ne prescrivent aucun re-poke intermédiaire.

Un plan demandant validation vit dans le scratchpad (`$TEMP`) ; la restitution finale donne son **chemin**, pas une copie du plan dans le fil.

**Anti-patterns** : question en cours de session ; même question dans le registre et dans une liste dashboard ; re-poke à chaque wakeup ; entrée sans critère de mort ; retrait sans réponse user vérifiée ; plan recopié dans le fil.

## Voir aussi

- [docs/user-blocker-signaling-detail.md](../../docs/reference/user-blocker-signaling-detail.md) — mandats, migration de l'ancienne cadence, cycle de vie des entrées
- [coordinator-discipline.md](coordinator-discipline.md) — discipline symétrique côté agent
- [proactive-coordination.md](proactive-coordination.md) — coordination proactive sans interruption user
