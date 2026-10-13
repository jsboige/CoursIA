# Scripts Tests (CPU) — point de triage unique

**Issue d'origine** : [#17299](https://github.com/jsboige/CoursIA/issues/17299)
**Check** : `Scripts Tests (CPU)` (workflow `.github/workflows/scripts-tests.yml`)
**Statut du document** : règle acceptée par la lane `myia-po-2026:CoursIA-2`, voir commentaire de claim [#17299 (comment)](https://github.com/jsboige/CoursIA/issues/17299#issuecomment-5768041331). Étendue aux modes 5-6 par `myia-po-2026:CoursIA` le 2026-10-03.

## Pourquoi ce document

`Scripts Tests (CPU)` est un check **REQUIS** dont le rouge a **six causes distinctes**
(4 confirmées, 2 candidates) mesurées à des dates différentes, par des lanes
différentes, sans point de ralliement.

Le réflexe coûteux observé : traiter un rouge d'**infra** comme un défaut de
**contenu** (fixer un test qui n'est pas en cause, pousser un commit qui ne fait que
ré-armer des timers et les re-stamps d'autres lanes). Ce document est le **point de
triage unique** : avant tout geste sur un rouge de ce check, identifier le mode
par son **tell**, puis appliquer le remède qui lui correspond.

## Les modes (4 confirmés, 2 candidats)

| # | Mode | Tell (dans le log du step / annotations du check-run) | Remède | Statut |
|---|------|---|---|---|
| 1 | **Contrat d'erreur troué** — l'E2E de `prune_merged_worktrees` parsait stdout avant sa précondition | `JSONDecodeError: Expecting value: line 1 column 1` avec stdout vide ; `rc=1` inatteignable par les chemins nommés | **Fix réel** livré : [#17293](https://github.com/jsboige/CoursIA/issues/17293) (`run()` fait sortir les exceptions inattendues en `rc=2` + traceback + marqueur ; le test distingue skip motivé / échec dur) | **corrigé** |
| 2 | **Fetch-promisor / SIGKILL** pendant le checkout | runner tué pendant `git fetch` (promisor), trace SIGKILL | rerun ; suivi capacité | documenté dans [#17253](https://github.com/jsboige/CoursIA/issues/17253) |
| 3 | **403 quota** empoisonnant les organes | le **bloc `env:` du step** contient le JSON d'erreur 403 devenu `PR_BODY` ; `tag_required`/`perimeter` accusent un manquement de **contenu** qui n'existe pas | **ne pas réparer le body** ; attendre le quota, rerun | fix partiel [#17272](https://github.com/jsboige/CoursIA/issues/17272) (advisory), [#17275](https://github.com/jsboige/CoursIA/issues/17275) (retry gate) |
| 4 | **Saturation pid/process du runner** | un **frère du même run** meurt sur `_fork_exec` (`BlockingIOError: [Errno 11] Resource temporarily unavailable`) ; watchdog xdist `workers morts` + silence 480 s ; `main` oscille success/failure en ~3 min **sans commit pertinent** ; le test passe **en <1 s en local** | **rien dans le contenu** ; rerun, et intégrer à l'arbitrage capacité (cf mesure po-2027 : 3 OOM ciblés sur suite pytest complète, VM WSL 24 Go) | **ouvert** — arbitrage capacité |
| 5 | **Job `failure` sans step fautive** (runner démonté avant la sortie) | `.steps[]` : toutes les steps substantielles `success` — **dont `Run tests`** ; steps `Post …` à `null` ; **aucune annotation** (titre/summary vides) ; log du job `BlobNotFound` (rien téléversé) | **rien dans le contenu** ; nommer le rouge comme infra, ne pas relancer en boucle ; la preuve de contenu devient l'exécution locale de la suite sur la tête exacte | **candidat** — famille infra (2/4), tell distinct |
| 6 | **Lock git orphelin** dans le workspace du slot (fetch impossible) | `cannot lock ref 'refs/remotes/origin/…': Unable to create '….lock': File exists` (3 retries puis exit 1), échec en **< 1 min** — la suite n'a pas commencé ; **tout job du slot** échoue au fetch | sur la machine du pool : `find <git-du-slot> -name '*.lock' -mmin -60` puis `pgrep -a git` — **aucun process git vivant** = orphelin : `rm` du `.lock` précis, rejeu des **enfants** (pas du gate, #15905) | **candidat** — famille fetch/checkout (2) ; occurrence sur jambe kernel-drift |

## Règle de triage (acceptance du document)

1. **Avant tout geste**, lire l'**annotation du check-run** et le **log du step** (pas
   le `tail` du log — le diagnostic est souvent en tête de step).
2. Si le test mis en cause **passe en local en <1 s** ET que `main` oscille sans
   commit pertinent ET qu'un frère du même run meurt sur `_fork_exec` → **mode 4** :
   aucun commit, rerun, mesure capacité. Ne pas commenter une PR qui porte un
   dossier (le commentaire l'invalide).
3. Si le corps du rouge contient un JSON d'erreur 403 → **mode 3** : ne pas
   toucher au body de la PR.
4. Si le rouge nomme une **exception Python réelle** dans le code du script →
   **mode 1** : c'est un vrai défaut, le fix de [#17293](https://github.com/jsboige/CoursIA/issues/17293)
   doit déjà le rendre diagnosticable ; sinon, nouveau mode à documenter ici.
5. Sur tout `failure` de ce check, **descendre au niveau des steps** :
   `gh api repos/jsboige/CoursIA/actions/jobs/<job_id> --jq '.steps[] | "\(.conclusion) :: \(.name)"'`.
   `Run tests` **vert** = aucun test n'a échoué, quoi que dise la conclusion du job ;
   steps `Post …` nulles + log `BlobNotFound` → **mode 5**.
6. Un échec de **fetch en < 1 min** sur `cannot lock ref … File exists` → **mode 6** :
   diagnostiquer le slot (`find` des `.lock` récents + `pgrep -a git`) ; si aucun
   process git ne détient le lock, `rm` ciblé + rejeu des enfants.
7. Tout **nouveau mode** identifié s'ajoute à cette table (commentaire), pas en
   knowledge dispersée.

## Ce qui n'est PAS ce document

- La **cause racine du mode 4** (capacité du slot sous composition) relève de
  l'arbitrage capacité CI en cours (mesures po-2027 du 21/09 : 3 crashes ciblés,
  preuve de non-défaut par SUCCESS au même SHA à 16:55:36Z).
- [#17253](https://github.com/jsboige/CoursIA/issues/17253) garde la paternité du mode 2.

## Références de mesure

- Modes 3+4 mesurés le 2026-09-21 sur [#16219](https://github.com/jsboige/CoursIA/pull/16219),
  [#16464](https://github.com/jsboige/CoursIA/pull/16464),
  [#16405](https://github.com/jsboige/CoursIA/pull/16405)
  (triage firsthand : frère `_fork_exec`, 403 dans `env:`, `main` a8aafc3f/b5c64988
  à 3 min d'écart).
- Mode 1 : issue [#17292](https://github.com/jsboige/CoursIA/issues/17292),
  fix [#17293](https://github.com/jsboige/CoursIA/issues/17293).
- Mode 4, occurrences du 23/09 (ai-01) : `main` rouge sur 3 commits de suite
  (première occurrence job `107071049208`, `main` `bcc8796a80`, pool
  `myia-ai-01-wsl-*` sous-dimensionné par rapport au prescrit du dépôt) —
  commentaires [#17299 (23/09)](https://github.com/jsboige/CoursIA/issues/17299#issuecomment-5792849135).
- Mode 5 : occurrence du 25/09 (po-2026) — job `107958799623`, PR #17755,
  runner `myia-po-2026-wsl-6`, 12 steps (10 success dont `Run tests`, 2 `Post` nulles),
  zéro annotation, log `BlobNotFound` ; `main` vert 4 fois dans la fenêtre exacte
  du rouge. Commentaire [#17299 (25/09)](https://github.com/jsboige/CoursIA/issues/17299#issuecomment-5827700612).
- Mode 6 : occurrence du 02/10 (po-2026) — slot-5 (`myia-po-2026-wsl-5`,
  pool `CoursIA-runners-p0`), ref `fix/18457-pagmem-mru` locké, tout job du slot
  au sol ; `rm` du lock + rejeu des enfants → success, PR #18864 débloquée.
  Commentaire [#17299 (03/10)](https://github.com/jsboige/CoursIA/issues/17299#issuecomment-5964040224).
- Amplyleur du mode 4 (OOM ciblés suite pytest) : messages dashboard 20:25Z-20:31Z
  (po-2027).

## Voir aussi

- [Issue #17299](https://github.com/jsboige/CoursIA/issues/17299) — body de l'issue,
  source canonique de cette table.
- [Issue #17253](https://github.com/jsboige/CoursIA/issues/17253) — mode 2.
- [Issue #17292](https://github.com/jsboige/CoursIA/issues/17292) et
  [#17293](https://github.com/jsboige/CoursIA/issues/17293) — mode 1.
- [Issue #17272](https://github.com/jsboige/CoursIA/issues/17272) et
  [#17275](https://github.com/jsboige/CoursIA/issues/17275) — mode 3.
- `MEMORY.md` `c.679-L3` (installation rate limit) — pattern parent du mode 3.