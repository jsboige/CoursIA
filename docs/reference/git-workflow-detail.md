# Git workflow — détail : verbatim force-push, incidents, rationale

> REFERENCE — vivante — dernière révision 2026-11-11

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

## 4. DWELL — pourquoi `update-branch` ne re-arme plus le plancher (#16962)

La règle a porté jusqu'au 2026-09-21 l'affirmation « `gh pr update-branch` remet le plancher DWELL à zéro (#15859) ». Le défaut a été **réel** : avant #16149, le plancher se mesurait depuis la date de committer de la **tête**, et `update-branch` en crée une. #16149 a remplacé cette mesure par `last_authoritative_committed_at` (`scripts/ci/merge_dwell.py`), qui remonte la chaîne first-parent au-delà d'une fusion de base **prouvée content-free**.

Le prédicat est **conjonctif**, et c'est ce qui le rend sûr : deux parents, second parent **ancêtre de la base**, et arbre du merge **identique à l'auto-merge** (`git merge-tree --write-tree`). La troisième condition vient d'une CR ai-01 du 2026-09-16 — la forme des parents n'exempte pas une résolution manuelle de conflit. Tout ce qui n'est pas prouvé reste mesuré : **fail-closed**.

### La vérification, et pourquoi elle n'était pas une lecture

L'affirmation de la règle a été **confrontée à l'organe** avant d'être corrigée :

| Ce qui a été lu | Ce qu'il établit |
|---|---|
| `last_authoritative_committed_at` — docstring + boucle `current = first ; continue` | le prédicat et les trois conditions, cités à la source |
| `scripts/tests/test_merge_dwell.py` — **6** tests `#16149` + **9** tests CR-2026-09-16 (37 au total) | la propriété est **épinglée**, dont des cas sur dépôt git réel et sur checkout superficiel |
| `git grep` sur les surfaces normatives | **une seule** portait l'affirmation périmée — la ligne de règle |
| `merge_dwell.py` (message du gate) | la cadence du balayage est mesurée **2 h 33 – 5 h 18**, « pas horaire » — alors que la règle l'appelait « horaire » |

Le défaut était donc **documentaire** : la règle contredisait un organe correct et testé. Le second écart (« balayage horaire ») a été trouvé par la même passe et corrigé dans le même geste — les deux vivaient sur la même ligne.

### Le rouge `DWELL` n'est pas un défaut de la PR — c'est le balayage qui le lève

Le gate **nomme lui-même** la cause dans son message : la tête est trop récente pour le plancher, rien n'est à corriger dans le code. Un `DWELL` rouge se résorbe donc **sans geste de la lane**, quand le balayage repasse et re-mesure la tête. C'est la raison pour laquelle un rouge de cette classe peut rester affiché des heures sans que personne ne soit en faute.

La cadence réelle du balayage est **lente et irrégulière** : la mesure de **#15197** la situe entre **178 et 341 minutes** — le message du gate, sur une autre fenêtre, annonce « 2 h 33 – 5 h 18 ». Les deux lectures s'accordent sur ce qui compte ici : ce n'est **pas** horaire, et une PR peut légitimement attendre plusieurs heures avant que la jambe repasse au vert. Attendre n'est donc pas un échec de lane ; c'est le fonctionnement nominal.

### Pourquoi un rejeu de jambe est gratuit

`gh run rerun <run_id> --job <job_id>` ne crée **aucun commit** : la tête ne bouge pas, donc le plancher non plus. C'est le remède que le message du gate nomme lui-même, et il est préférable à `update-branch` quand le seul rouge est `DWELL` — ce dernier n'est pas nuisible, mais il déclenche une rafale CI complète sur un pool de runners partagé.

### La leçon de méthode

Une règle du harnais est **datée de sa rédaction, pas de sa lecture**. Quand une règle interdit un geste et que l'organe qui l'implémente est lisible, lire l'organe coûte trente secondes — c'est [verify-before-claiming.md](../../.claude/rules/verify-before-claiming.md) appliqué au harnais lui-même : **une règle est une claim comme une autre**.

## 5. Worktree cleanup (#14195) — problème, mesures datées et contrôle positif

**Problème mesuré (2026-09-02)** : chaque review de PR notebook / build Lean crée un worktree ; sans organe de retrait, ces worktrees s'accumulent — **265 sur po-2026 en 36 h**, **103 sur ai-01** (précédent #8924). Le mécanisme est nommé depuis le 2026-08-05, mais l'organe n'avait jamais été construit (`scripts/ci/prune_merged_worktrees.py`).

**Pourquoi une tâche planifiée et pas la règle seule** : la prose d'une règle ne s'exécute pas seule — les règles sont injectées au démarrage de session et perdues en cas de crash, si bien qu'une consigne « purger en fin de cycle » ne s'applique que si la session se termine proprement. La tâche planifiée est donc le mécanisme, et l'appel manuel de fin de cycle le filet.

**Refus ≠ échec — mesure (roo-extensions #3895, 27/09)** : sur 3 machines, **86-100 %** des worktrees vus sont REFUSE (worktrees de cycle nés HEAD-détachés ou sales par construction — po-2023 a saturé ses disques dessus). Un REFUS est une **décision** de l'organe (exit 0), pas une panne : la règle qui en découle reste dans `.claude/rules/git-workflow.md`.

**Mesure 2026-09-03 (po-2027, cycle #14195)** :

| | Avant | Après `--apply` |
|---|---:|---:|
| Worktrees enregistrés | 5 | 4 |
| … REMOVE | 1 (test-prune-merged, PR #14403 MERGED) | — |
| … REFUSE | 4 (main + 3 PR OPEN) | 4 |

Le worktree de test créé sur `fix/14142-qc40-followup-state` (PR #14403 mergée par squash 2026-09-02) a été retiré — c'est le **contrôle positif** manquant à tout prédicat d'ascendance : un squash-merge efface l'ascendance, mais `gh pr list --state all --search` retrouve la PR par le nom de branche.

**L'ancre PR passe au listing REST par branche (2026-11, #23636)** : `gh pr list --state all --search "head:<branche>"` consomme le chemin de recherche GraphQL, refusé sous le login partagé alors même que le compteur horaire du seau `search` reste positif (plafond de points propre au chemin de recherche ; mesure firsthand 2026-10-31 : 3 échecs consécutifs `GraphQL: API rate limit already exceeded` alors que `gh api rate_limit` rendait `core: 4950` — le compteur ne prédit pas ce refus, seul le log de l'appel tranche). L'ancre autoritative est désormais `gh api "repos/<owner>/<repo>/pulls?state=all&head=<owner>:<branche>&per_page=5"` : seau `core`, filtre sur la tête **exacte** — le qualificatif `head:` de `--search` matche par sous-chaîne, donc moins précis pour l'intention « la PR dont `headRefName == branche` ». Le repli `--search` reste réservé aux branches de fork dont le propriétaire du head est inconnu : le filtre `head=` accepte bien `<fork-owner>:<branch>`, mais la voie REST de l'organe ne connaît que le propriétaire du dépôt courant. Ce n'est **pas** l'ancre interdite `commits/<oid>/pulls` (faux négatifs mesurés sur PRs OPEN) : le listing par branche n'a pas ce défaut. Fail-closed conservé dans l'organe : une erreur `gh` reste un `RuntimeError` → verdict `no_gh_unverifiable`, jamais un « 0 worktree » silencieux. Correctif appliqué dans `anchor_search_pr_for_branch` de `scripts/ci/prune_merged_worktrees.py` ; récurrence fondatrice #15369, mesure #23636, déploiement #23642.

## 6. Le scope avale le mot-clé — la mesure sur 500 commits (#23348)

Détail déporté de la puce « Safe reference syntax » de la règle. Le mandat `type(scope): subject` a une place invite pour le numéro d'issue — `type(scope,#N): subject` — et cette forme ne ferme rien : `(` et le scope s'assoient entre le mot-clé de fermeture et le numéro.

Mesuré sur `origin/main` sur 500 commits : **299 numéros d'issues distincts cités de cette façon, 186 encore ouverts** ; parmi les **162** cités par un verbe de correction, **95 encore ouverts** — des issues dont le fix est déjà sur `main`, qui gonflent le tapis de travail déjà fait. GitHub ne ferme que si le mot-clé **précède immédiatement** la référence ; tout ce qui s'intercale est du texte.

L'organe de triage : `python scripts/ci/list_scope_swallowed_issues.py` (`--json`, `--all-forms`) nomme les paires (issue ouverte, commit de correction). Il ne ferme rien, ne commente rien : triage et fermeture reviennent au coordinateur (G.9).

## Voir aussi

- [`.claude/rules/git-workflow.md`](../../.claude/rules/git-workflow.md) — la règle
- [`docs/reference/orphan-branch-scan-l576.md`](orphan-branch-scan-l576.md) — scan de branche orpheline, 4 ancres
- [`.claude/rules/lane-claim-protocol.md`](../../.claude/rules/lane-claim-protocol.md) — « plusieurs agents de front » = un `[CLAIMED]` d'une autre lane
- [`.claude/rules/secrets-hygiene.md`](../../.claude/rules/secrets-hygiene.md) règle 5 — secret commité : cherry-pick + rotation, jamais réécriture d'historique

## § Levier B — rationales déportés de `.claude/rules/git-workflow.md`

La règle `git-workflow.md` est **auto-chargée** à chaque session ; ce fichier
ne l'est pas. Les blocs ci-dessous sont repris **verbatim** : ce qui sort de
la règle entre ici sans réécriture.

| Ligne de la règle (base `7a558e4d7ce8`) | Bloc déplacé |
|---|---|
| L27 | le scope avale le mot-clé — la mesure sur 500 commits |
| L32 | incident fondateur de l'auto-close prématuré |
| L38 | pourquoi un périmètre plutôt qu'un interdit global |
| L53 | `update-branch` tue le dossier de prévalidation |
| L62 | pourquoi la forme opérationnelle n'est pas reformulée ici |
| L63 | `--force-with-lease` plutôt que `--force` |
| L67 | `allow_force_pushes` n'est pas lisible sans droit admin |
| L125 | mesure datée et contrôle positif du prune |

### L27 — le scope avale le mot-clé — la mesure sur 500 commits

The mandated `type(scope): subject` form has an inviting place for the issue number — `type(scope,#N): subject` — and that form closes nothing: `(` and the scope sit between the keyword and the number. Never rely on the subject alone to close (mesure sur `origin/main` : 500 commits, 299 numéros cités ainsi, **186 encore ouverts** ; parmi les 162 cités par un verbe de correction, **95 encore ouverts** — des fixes déjà sur `main`).

### L32 — incident fondateur de l'auto-close prématuré

Incident fondateur : trois issues fermées par `Refs #N` sur des PRs partielles.

### L38 — pourquoi un périmètre plutôt qu'un interdit global

Les deux cas n'ont pas la même conséquence (contenu partagé sur `main`, travail non mergé d'une seule lane sur sa branche) — le détail du verbatim, de la table de décision et de l'incident 2026-03-13 est dans §1.

### L53 — `update-branch` tue le dossier de prévalidation

C'est la moitié qu'on oublie : c'est cette péremption, et non le DWELL, qui referme la boucle — [prevalidation-dossier-order-detail.md](prevalidation-dossier-order-detail.md) §1-§3.

### L62 — pourquoi la forme opérationnelle n'est pas reformulée ici

Deux surfaces qui redécrivent la même règle finissent par diverger (#16962) — le verbatim de l'organe et la réconciliation de l'issue fondatrice sont dans [prevalidation-dossier-order-detail.md](prevalidation-dossier-order-detail.md).

### L63 — `--force-with-lease` plutôt que `--force`

Il échoue si le remote a bougé depuis ta dernière lecture — précisément le cas « une autre lane a poussé sans que je le sache ». C'est le garde-fou qui rend le périmètre ci-dessus sûr.

### L67 — `allow_force_pushes` n'est pas lisible sans droit admin

Un 404 sur `branches/main/protection` est **une question, pas une absence mesurée** (#9991). Ce qu'une lane peut vérifier sans admin, c'est le comportement : un `push --force` sur `main` est rejeté par le serveur. Cf §1.

### L125 — mesure datée et contrôle positif du prune

Mesure datée et contrôle positif (po-2027, cycle #14195 ; tableau avant/après et contrôle positif du squash-merge) : §5.
