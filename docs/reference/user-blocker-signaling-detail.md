# User-blocker signaling — détail

Détail de [.claude/rules/user-blocker-signaling.md](../../.claude/rules/user-blocker-signaling.md). Voir aussi [coordinator-discipline.md](../../.claude/rules/coordinator-discipline.md) et [proactive-coordination.md](../../.claude/rules/proactive-coordination.md).

## Deux mandats, une seule règle actuelle

### Mandat initial — visibilité (2026-05-28T12:48Z)

Après l'épisode audiobook #1273, une validation subjective avait disparu pendant plusieurs cycles. Le user a demandé qu'un blocage dont il porte l'action soit visible en fin de session plutôt que dilué dans un long `[DONE]`.

### Mandat supersédant — arbitrage par pull (2026-09-15, #3656)

Le user a ensuite précisé :

> « Je prefere que tu gardes tes questions pour la fin de session, et si jamais le cron reprend, que tu les gardes tant qu'elles sont pas repondues dans une memoire que tu dois restituer en fin de session. Ca va demander une MAJ du harnais global en coordination avec roo-extensions »

Et pour les plans :

> « Pour le mode plan utilisez un scratchpad et si une validation utilisateur est necessaire, donner le chemin du scratchpad en fin de session »

Le second mandat conserve le but du premier — aucun blocage ne disparaît — mais retire son mécanisme répétitif. La visibilité vient désormais d'une **restitution unique en fin de session**, alimentée par une mémoire durable, et non de messages répétés pendant le cycle.

## Support canonique

Chaque workspace tient un fichier :

`~/.claude/projects/<hash>/memory/user-question-registry.md`

Il est indexé dans `MEMORY.md` pour être rechargé après reprise ou cron. Une entrée ouverte contient au minimum :

| Champ | Rôle |
|---|---|
| Question / action | décision ou geste précis, sans contexte implicite |
| Attendu du user | ce que le user doit fournir ou décider |
| Critère de mort | preuve observable qui permet de retirer l'entrée |
| Ouverte depuis | date/cycle pour conserver l'ancienneté sans re-poke |

Le registre porte deux sections courtes : **ouvertes** et **répondues**. Une entrée ne quitte les ouvertes qu'après réponse user et vérification de son critère de mort. Elle passe alors dans « répondues » ; elle n'est jamais auto-expirée.

## Cycle worker et coordinateur

1. Dès qu'une question non bloquante apparaît, l'agent l'ajoute ou la met à jour dans le registre — sans l'adresser dans le fil.
2. Le travail non bloqué continue (`always-pick-next`).
3. En fin de session, l'agent restitue en **un bloc** toutes les entrées ouvertes pertinentes.
4. Au cycle suivant, `MEMORY.md` rend le registre retrouvable ; les entrées ouvertes sont restituées à nouveau en fin de session si elles n'ont pas été répondues.
5. Une réponse user déclenche la vérification du critère de mort puis le déplacement vers « répondues ».

Le coordinateur agrège de la même manière les questions des lanes : il ne maintient pas une seconde table dashboard. Si un tag `ASK`, `[ASK USER]` ou une section « Actions user en attente » est utile pour signaler le bloc final, ce signal **référence le registre** et ne devient jamais le stockage de l'état.

## Migration de l'ancienne règle

Les prescriptions suivantes sont retirées parce qu'elles créaient précisément les interruptions et listes divergentes interdites par #3656 :

- re-poke à chaque fin de payload ou wakeup ;
- ping en premier dès qu'un message user arrive ;
- compteurs d'escalade automatiques à 3 ou 5 cycles ;
- table « Actions user en attente » entretenue séparément du registre ;
- copie d'une même question dans `[ASK USER]`, dashboard, DM et rapport final.

La suppression ne retire aucune protection : la persistance vient du fichier mémoire, l'ancienneté reste un champ, et la restitution finale conserve la visibilité demandée en mai.

## Plans avec validation

Un plan qui nécessite une validation user est écrit dans le scratchpad (`$TEMP`). Le registre contient la question, l'attendu et le critère de mort ; le rapport final donne le **chemin du scratchpad**. Le plan n'est pas recopié dans le fil.

## Anti-patterns interdits

- Poser une question en milieu de session alors qu'elle peut attendre la restitution finale.
- Arrêter tout le cycle pour une question non bloquante.
- Ouvrir une entrée sans attendu explicite ou sans critère de mort.
- Auto-expirer une question faute de réponse.
- Maintenir une liste dashboard parallèle au registre mémoire.
- Répéter la question à chaque wakeup au lieu de laisser le registre assurer la continuité.
- Copier un plan complet dans le fil au lieu de rendre son chemin scratchpad.

## Interaction avec les autres règles

- **Harnais global #3656** : `.claude/configs/user-global-claude.md` définit le contrat machine-global ; cette règle CoursIA en est le renvoi workspace.
- **[coordinator-discipline.md](../../.claude/rules/coordinator-discipline.md)** : les obligations agent restent dans le ledger turn-local ; seules les questions user traversant les sessions vont dans ce registre.
- **CLAUDE.md reporting dashboard** : un signal `ASK` reste possible, mais le dashboard ne porte pas l'état durable et ne duplique pas les entrées.
- **`always-pick-next`** : une question ouverte exclut uniquement le geste qui en dépend ; elle n'arrête pas les autres grains.
