# User-blocker signaling — detail

Detail de [.claude/rules/user-blocker-signaling.md](../../.claude/rules/user-blocker-signaling.md). Voir aussi [coordinator-discipline.md](../../.claude/rules/coordinator-discipline.md), [proactive-coordination.md](../../.claude/rules/proactive-coordination.md).

## Source mandate (2026-05-28T12:48Z)

Apres l'episode audiobook #1273 ou la validation subjective restait pendante depuis plusieurs cycles sans qu'aucun agent ne re-amorce la demande.

Verbatim user :
> "Globalement quand c'est moi qui bloque, il faut que les agents me le signalent dans un message en fin de session. Comme il y a des wakeup, ca peut se diluer sans que je m'en rende compte, mais il faut en remettre une couche a chaque fin de session en attendant le wakeup, ou bien alors il faut que toi tu me le signales si ca traine (ex pour les notes a rendre)."

## Workers (po-2023 / po-2024 / po-2025 / po-2026)

1. **Fin de session = tag dedie `[ASK USER]`**, en plus du `[DONE]` :
   ```
   [ASK USER] <one-line action attendue> — bloque depuis <N> sessions, attente <X>
   ```
   Pas noye dans la prose du rapport. Tag separe, visible.

2. **Re-poke a CHAQUE fin de session** tant que l'action user n'est pas faite. Re-afficher avec compteur d'anciennete.

3. **Ping direct au prochain passage user** : si le worker detecte une session interactive user (message user recu pendant le tour), presenter le bloqueur **en premier** dans la reponse, pas apres le travail technique.

4. **Plafond escalation** : apres **5 sessions sans action user** (~15h en cron 3h), escalader vers ai-01 via `roosync_messages send` (priority HIGH).

## Coordinateur (ai-01)

1. **Section dediee "Actions user en attente"** en tete du briefing `/coordinate` au debut de **chaque** wakeup. Tableau avec anciennete en cycles + machine + une-ligne d'action. Toujours en haut.

2. **Escalation timer** : si un bloqueur user depasse **3 cycles (~9h)** sans action, post explicite `[ESCALATION USER]` sur dashboard workspace en tete du rapport courant.

3. **Signaler proactivement** quand le user est en session interactive sur ai-01 et que **n'importe quel** bloqueur user (sur n'importe quelle machine) traine.

4. **Fin de session ai-01 = rappeler les blocs user actifs** dans le resume final, meme si rien n'a change ce cycle.

## Anti-patterns interdits

- **Diluer dans un rapport DONE long** : le user ne scrolle pas, signal noye = perdu.
- **Attendre passivement le wakeup suivant** sans re-poke : la dilution mandate vient explicitement de la.
- **Mentionner une fois puis disparaitre** : re-poster chaque fin de session.
- **Lister 5 user-blocks d'un coup en bloc** : hierarchiser par priorite reelle (notes a rendre = urgent calendaire ; validation audiobook = pas calendaire).
- **Inverser la responsabilite** : "le user n'a pas regarde, c'est bloque" sans re-pinger = faute de l'agent.

## Categories actuelles user-blocking (exemples, etat 2026-05-28)

| Categorie | Detail | Anciennete | Urgence calendaire |
|-----------|--------|------------|---------------------|
| ESGF GForm CSV peer-evals | Export manuel CSV depuis GForm pour `GradeBookApp` | Plusieurs cycles | OUI — soutenances 26+29 mai |
| Confirmation grades Gr03 ESGF | Decision user cas borderline | Plusieurs cycles | OUI — meme fenetre |
| Validation subjective audiobook | Ecoute Act 1+2 tags-only FishAudio | Plusieurs cycles | NON |
| Sign-off batch delete branches ZERO-DIFF | ~78 branches | Plusieurs cycles | NON — hygiene |
| Sign-off relance Jared Broad | Decision "QC bien en ordre" | En cours | NON — conditionne gates QC |

## Interaction avec autres regles

- **[coordinator-discipline.md](../../.claude/rules/coordinator-discipline.md)** "Aucune demande user ne pourrit > 1 cycle" : cette regle = l'inverse symetrique (quand c'est le user qui pourrit cote action).
- **CLAUDE.md section A** "Reporting dashboard" : `[ASK USER]` en plus des posts debut/livraison/fin, pas a la place.
- **CLAUDE.md G.7** "Stagnation cross-cycle = escalade" : applicable user-block > 5 cycles.
