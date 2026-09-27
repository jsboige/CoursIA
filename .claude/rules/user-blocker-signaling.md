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

## Quand le user engage la conversation — réponses intermédiaires (mandat user 2026-09-26)

Le registre porte les questions **de l'agent au user**. Quand c'est **le user** qui ouvre un échange en cours de session (question, Concern, remarque), la **conclusion vérifiée** reste réservée au **message final**. Les outils de question bloquante sont retirés du harnais par choix. Mais le user lit ce qui passe : il faut lui donner de quoi partir ou réagir.

1. **Tôt, une poignée de messages** qui disent la tendance et le **niveau de croyance initial** : ce qui est mesuré, ce qui est supposé, ce qui reste à vérifier. Le user peut partir avec ce qui lui suffit pour l'instant, ou réagir et engager la conversation.
   **Forme** : un bloc de **texte visible**, dans la langue du user, placé avant la commande suivante dans le même message. Cette forme s'affiche **sans clore le tour**. Une réponse restée dans le raisonnement n'atteint pas le user (mesuré le 2026-09-26 dans le transcript : trois réponses d'étape perdues ainsi, le user a cru à un silence).
2. **Sans en faire des caisses, et sans insister.** Si le user ne revient pas, il est probablement sur un autre écran ; la boucle agentique reprend.
3. **Un résultat intermédiaire significatif** (une mesure qui renverse l'hypothèse, une décision prise) mérite un court message, au cas où le user repasserait.
4. **La conclusion vérifiée va dans le dernier message.** Si le user ne l'a ni vue ni commentée avant la session suivante (cron), elle se **réitère** au cycle suivant, portée par la mémoire de reprise (handover), puis sort dès qu'il a réagi.

**Anti-patterns** : garder tout pour le message final pendant que le user attend ; relancer un user qui ne répond pas ; présenter une croyance initiale comme une conclusion vérifiée.

## Voir aussi

- [docs/user-blocker-signaling-detail.md](../../docs/reference/user-blocker-signaling-detail.md) — mandats, migration de l'ancienne cadence, cycle de vie des entrées
- [coordinator-discipline.md](coordinator-discipline.md) — discipline symétrique côté agent
- [proactive-coordination.md](proactive-coordination.md) — coordination proactive sans interruption user
