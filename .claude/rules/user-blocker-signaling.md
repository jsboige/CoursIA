# User-blocker signaling — anti-dilution

S'applique à **tous les agents** du cluster CoursIA (workers `po-*` + coordinateur `ai-01`).

**Source mandate** : user 2026-05-28T12:48Z, après l'épisode audiobook #1273 où la validation subjective restait pendante depuis plusieurs cycles sans qu'aucun agent ne ré-amorce la demande.

Verbatim user :
> "Globalement quand c'est moi qui bloque, il faut que les agents me le signalent dans un message en fin de session. Comme il y a des wakeup, ça peut se diluer sans que je m'en rende compte, mais il faut en remettre une couche à chaque fin de session en attendant le wakeup, ou bien alors il faut que toi tu me le signales si ça traine (ex pour les notes à rendre)."

## Règle HARD

Quand un livrable d'agent **dépend d'une action user qui n'est pas faite** (relecture, validation subjective, export manuel, signature, confirmation, sign-off), le bloqueur **doit être signalé explicitement à chaque fin de session** — pas dilué dans un rapport `[DONE]` long ni laissé dépendre du wakeup pour rappeler.

### Workers (po-2023 / po-2024 / po-2025 / po-2026)

1. **Fin de session = tag dédié `[ASK USER]`**, en plus du `[DONE]` :
   ```
   [ASK USER] <one-line action attendue> — bloqué depuis <N> sessions, attente <X>
   ```
   Pas noyé dans la prose du rapport. Tag séparé, visible.

2. **Re-poke à CHAQUE fin de session** tant que l'action user n'est pas faite. Pas d'oubli "j'avais déjà mentionné cycle 87". Ré-afficher avec compteur d'ancienneté.

3. **Ping direct au prochain passage user sur la machine du worker** : si le worker détecte une session interactive user sur sa machine (message user reçu pendant le tour), présenter le bloqueur **en premier** dans la réponse, pas après le travail technique.

4. **Plafond escalation** : après **5 sessions sans action user** (≈ 15h en cron 3h), escalader vers ai-01 via inbox `roosync_messages send` (priority HIGH) pour que le coordinateur le remonte dans son briefing.

### Coordinateur (ai-01)

1. **Section dédiée "Actions user en attente"** en tête du briefing `/coordinate` au début de **chaque** wakeup. Format tableau avec ancienneté en cycles + machine concernée + une-ligne d'action. Toujours en haut, pas en milieu de rapport.

2. **Escalation timer** : si un bloqueur user dépasse **3 cycles (≈ 9h)** sans action, post explicite `[ESCALATION USER]` sur dashboard workspace en tête du rapport courant — pas seulement dans la liste section.

3. **Signaler proactivement** quand le user est en session interactive sur ai-01 et que **n'importe quel** bloqueur user (sur n'importe quelle machine) traîne. Le user a explicitement demandé que ai-01 le signale "si ça traîne (ex pour les notes à rendre)".

4. **Fin de session ai-01 = rappeler les blocs user actifs** dans le résumé final, même si rien n'a changé ce cycle. Le silence = dilution.

## Anti-patterns interdits

- **Diluer dans un rapport DONE long** : le user scrolle pas, le signal noyé est perdu.
- **Attendre passivement le wakeup suivant** sans re-poke d'aucun agent : la dilution mandate vient explicitement de là.
- **Mentionner une fois puis disparaître** : "ai-01 l'avait dit cycle 87, c'est bon" — non. Re-poster chaque fin de session.
- **Lister 5 user-blocks d'un coup en bloc** : hiérarchiser par priorité réelle (notes à rendre = urgent calendaire ; validation audiobook = pas calendaire).
- **Inverser la responsabilité** : "le user n'a pas regardé, c'est bloqué" sans re-pinger = faute de l'agent, pas du user. Le signal est notre responsabilité.

## Catégories actuelles user-blocking (exemples)

À titre indicatif (état 2026-05-28, peut évoluer) :

| Catégorie | Détail | Ancienneté typique | Urgence calendaire |
|-----------|--------|---------------------|---------------------|
| ESGF GForm CSV peer-evals | Export manuel CSV depuis GForm pour ingestion `GradeBookApp` | Plusieurs cycles | OUI — soutenances 26 + 29 mai → grading semaine 1er juin |
| Confirmation grades Gr03 ESGF | Décision user sur cas borderline groupe 03 | Plusieurs cycles | OUI — même fenêtre grading |
| Validation subjective audiobook | Écoute Act 1 + Act 2 tags-only samples FishAudio | Plusieurs cycles | NON — pas calendaire |
| Sign-off batch delete branches ZERO-DIFF | Validation user pour supprimer ~78 branches ZERO-DIFF | Plusieurs cycles | NON — hygiène |
| Sign-off relance Jared Broad | Décision quand "QC bien en ordre" | En cours | NON — conditionné gates QC |

## Interaction avec autres règles

- **[.claude/rules/coordinator-discipline.md](coordinator-discipline.md)** "Aucune demande user ne pourrit > 1 cycle" : cette règle-ci est **l'inverse symétrique** (quand c'est le user qui pourrit côté action), et complète la discipline coordinator.
- **CLAUDE.md section A** "Reporting dashboard" : les `[ASK USER]` viennent en plus des posts standards début/livraison/fin, pas à la place.
- **CLAUDE.md G.7** "Stagnation cross-cycle = escalade" : applicable à un user-block qui traîne > 5 cycles, escalade documentée.

## Voir aussi

- [coordinator-discipline.md](coordinator-discipline.md) — ai-01 merge actif + no languishing demandes user (côté agent)
- [proactive-coordination.md](proactive-coordination.md) — 1 PR/wakeup + main + side-track async
- [pr-review-discipline.md](pr-review-discipline.md) — Section honnêteté rapports
- CLAUDE.md "REGLES AGENTS / Code avant documentation" — reports sur dashboard, pas dans repo
