# Git workflow — détail : verbatim force-push, incidents, rationale

Détail durable de [`.claude/rules/git-workflow.md`](../../.claude/rules/git-workflow.md) (harness-hygiene tier 2). La règle porte le périmètre opératoire ; ce fichier porte les verbatims et les incidents qui le fondent.

## 1. Force-push — décision user 2026-08-08 (verbatim)

> « *Je ne suis pas fan des force-pushs, on a déjà perdu pas mal de contenu dans le passé à cause de ça, et il existe généralement une alternative à base de merge. Mais pour une branche de feature qui n'est pas manipulée par plusieurs agents de front, ça n'est pas la même histoire. Donc en gros si on interdit sur main et on permet sur des branches de PRs, ça me va.* »

### Pourquoi un périmètre plutôt qu'un interdit global

L'ancienne rédaction interdisait `--force` **partout**, urgence-user comprise. Elle a été remplacée par un périmètre parce que les deux cas n'ont pas la même conséquence :

| Cible | Ce qu'un force-push y détruit |
|---|---|
| `main` | du contenu **partagé et déjà consommé** par ~95 forks étudiants — incident **2026-03-13**, commits potentiellement perdus |
| branche de feature à lane unique | uniquement le travail **non mergé de cette lane** |

Un interdit global avait donc un coût réel (rebases impossibles, branches abandonnées) pour une protection que `allow_force_pushes: false` assure déjà côté serveur sur la seule cible qui compte.

### `allow_force_pushes` n'est pas lisible sans droit admin (#9991)

Une version antérieure de la règle donnait `gh api repos/jsboige/CoursIA/branches/main/protection -q .allow_force_pushes` comme preuve à portée de main. Cet endpoint renvoie **404 sans droit admin sur le dépôt** (constaté sous `myia-ai-01`) : le compte admin `jsboige` est requis pour **lire** la protection, alors qu'il ne l'est pas pour merger.

Un 404 y est donc **une question, pas une absence mesurée**. Un agent qui l'interprète comme « pas de protection configurée » conclut l'inverse de la vérité. Ce que chaque lane peut vérifier sans droit admin, c'est le **comportement** : un `git push --force` sur `main` est rejeté par le serveur. La règle ne dépend pas de la lisibilité de la config. Cf [[protection-404-is-ambiguous]].

## 2. L677-L4 — pourquoi ★★ et pas ★★★

La leçon « body de PR hors worktree » est opérationnelle, mais son incident fondateur (corps de PR committé dans le worktree → revert + recommit) reste **rare et recoverable** : le coût est de ~5 min de rebase. Les leçons `★★★` (L898 collision cross-lane, L721 stale tracker) coûtent des **heures** et produisent des rétractations publiques — d'où l'écart de cotation.

Réutilisations enregistrées : c.680 (fondatrice), puis c.683 à c.690.

## 3. Auto-close prématuré — incident #2211

GitHub ferme une issue sur `Refs #N`, `Fixes #N`, `Closes #N` dans un **message de commit** comme dans un body de PR. Trois issues (#1943, #2048, #2158) ont été fermées automatiquement par des PRs **partielles** qui utilisaient `Refs #N` en croyant à une simple référence.

D'où la syntaxe sûre : `See #N` / `Part of #N` pour lier sans fermer, `Closes #N` réservé au cas où **tous** les critères d'acceptation sont atteints. Piège associé : le champ `prev:` du tag `Grain:` peut lui aussi contenir un `#N` dans un message de commit — cf [[grain-prev-field-can-autoclose]].

## Voir aussi

- [`.claude/rules/git-workflow.md`](../../.claude/rules/git-workflow.md) — la règle
- [`docs/reference/orphan-branch-scan-l576.md`](orphan-branch-scan-l576.md) — scan de branche orpheline, 4 ancres
- [`.claude/rules/lane-claim-protocol.md`](../../.claude/rules/lane-claim-protocol.md) — « plusieurs agents de front » = un `[CLAIMED]` d'une autre lane
- [`.claude/rules/secrets-hygiene.md`](../../.claude/rules/secrets-hygiene.md) règle 5 — secret commité : cherry-pick + rotation, jamais réécriture d'historique
