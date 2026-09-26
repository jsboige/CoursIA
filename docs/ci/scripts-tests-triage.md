# Scripts Tests (CPU) — point de triage unique

**Issue d'origine** : [#17299](https://github.com/jsboige/CoursIA/issues/17299)
**Check** : `Scripts Tests (CPU)` (workflow `.github/workflows/scripts-tests.yml`)
**Statut du document** : règle acceptée par la lane `myia-po-2026:CoursIA-2`, voir commentaire de claim [#17299 (comment)](https://github.com/jsboige/CoursIA/issues/17299#issuecomment-5768041331).

## Pourquoi ce document

`Scripts Tests (CPU)` est un check **REQUIS** dont le rouge a **quatre causes distinctes**
mesurées à des dates différentes, par des lanes différentes, sans point de ralliement.

Le réflexe coûteux observé : traiter un rouge d'**infra** comme un défaut de
**contenu** (fixer un test qui n'est pas en cause, pousser un commit qui ne fait que
ré-armer des timers et les re-stamps d'autres lanes). Ce document est le **point de
triage unique** : avant tout geste sur un rouge de ce check, identifier le mode
par son **tell**, puis appliquer le remède qui lui correspond.

## Les 4 modes

| # | Mode | Tell (dans le log du step / annotations du check-run) | Remède | Statut |
|---|------|---|---|---|
| 1 | **Contrat d'erreur troué** — l'E2E de `prune_merged_worktrees` parsait stdout avant sa précondition | `JSONDecodeError: Expecting value: line 1 column 1` avec stdout vide ; `rc=1` inatteignable par les chemins nommés | **Fix réel** livré : [#17293](https://github.com/jsboige/CoursIA/issues/17293) (`run()` fait sortir les exceptions inattendues en `rc=2` + traceback + marqueur ; le test distingue skip motivé / échec dur) | **corrigé** |
| 2 | **Fetch-promisor / SIGKILL** pendant le checkout | runner tué pendant `git fetch` (promisor), trace SIGKILL | rerun ; suivi capacité | documenté dans [#17253](https://github.com/jsboige/CoursIA/issues/17253) |
| 3 | **403 quota** empoisonnant les organes | le **bloc `env:` du step** contient le JSON d'erreur 403 devenu `PR_BODY` ; `tag_required`/`perimeter` accusent un manquement de **contenu** qui n'existe pas | **ne pas réparer le body** ; attendre le quota, rerun | fix partiel [#17272](https://github.com/jsboige/CoursIA/issues/17272) (advisory), [#17275](https://github.com/jsboige/CoursIA/issues/17275) (retry gate) |
| 4 | **Saturation pid/process du runner** | un **frère du même run** meurt sur `_fork_exec` (`BlockingIOError: [Errno 11] Resource temporarily unavailable`) ; watchdog xdist `workers morts` + silence 480 s ; `main` oscille success/failure en ~3 min **sans commit pertinent** ; le test passe **en <1 s en local** | **rien dans le contenu** ; rerun, et intégrer à l'arbitrage capacité (cf mesure po-2027 : 3 OOM ciblés sur suite pytest complète, VM WSL 24 Go) | **ouvert** — arbitrage capacité |

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
5. Tout **nouveau mode** identifié s'ajoute à cette table (commentaire), pas en
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
- Amplyseur du mode 4 (OOM ciblés suite pytest) : messages dashboard 20:25Z-20:31Z
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