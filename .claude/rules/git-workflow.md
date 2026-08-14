# Git Workflow Rules

## Branch Naming

```
type/name-short-descriptif
```
Examples: `feature/notebook-transformers`, `fix/ml-example-bug`, `docs/improve-readme`

## Commit Messages

```
Type: description courte de la modification
```
Examples: `Add: notebook sur les Transformers`, `Fix: correction d'erreurs dans l'exemple ML.NET`

### Safe reference syntax (prevent premature issue auto-close)

GitHub auto-closes issues on `Refs #N`, `Fixes #N`, `Closes #N`. Use safe syntax:

| Intent | Correct | Wrong |
|--------|---------|-------|
| Link without closing | `See #N` or `Part of #N` | ~~`Refs #N`~~ |
| Close when ALL criteria met | `Closes #N` (verify acceptance first) | ~~`Fixes #N`~~ for partial |
| Partial delivery | `See #N` (partial: X/Y criteria) | ~~`Refs #N`~~ |

**Incident**: 3 issues (#1943, #2048, #2158) auto-closed by GitHub on partial PRs using `Refs #N`. See #2211.

## Safety Rules

### Force push — interdit sur `main`, autorisé sur une branche de PR à lane unique

**Décision user 2026-08-08** : périmètre, pas interdit global — les deux cas n'ont pas la même conséquence (sur `main` un force-push écrase du contenu partagé, déjà consommé par ~95 forks étudiants ; sur une branche de feature à lane unique il ne réécrit que le travail non mergé de cette lane). Verbatim + incident 2026-03-13 : [git-workflow-detail.md](../../docs/reference/git-workflow-detail.md).

| Cible | Règle | Ce qui la porte |
|---|---|---|
| **`main`** | **INTERDIT**, sans exception d'urgence | `allow_force_pushes: false` — GitHub **refuse** le push. C'est le serveur qui tranche, pas une consigne |
| **Branche de PR (`feature/*`, `fix/*`, `docs/*`) à lane unique** | **AUTORISÉ**, `--force-with-lease` préféré | aucune protection plateforme : c'est la discipline de lane qui répond |
| **Branche manipulée par plusieurs agents de front** | **INTERDIT** | un `[CLAIMED]` d'une autre lane sur l'issue vaut « plusieurs agents » → [lane-claim-protocol.md](lane-claim-protocol.md) |

- **L'alternative merge d'abord, quand elle existe** : `git merge origin/main`, `gh pr update-branch`, cherry-pick, revert, nouveaux commits. Le force-push est le dernier recours, jamais le réflexe de rebase par défaut.
- **`--force-with-lease` plutôt que `--force`** : il échoue si le remote a bougé depuis ta dernière lecture — précisément le cas « une autre lane a poussé sans que je le sache ». C'est le garde-fou qui rend le périmètre ci-dessus sûr.
- **Jamais de `reset --hard`** sur `main` ni sur une branche partagée.
- **Un secret déjà commité ne se répare PAS par réécriture d'historique** : branche propre + cherry-pick, et **rotation de la clé** (cf [secrets-hygiene.md](secrets-hygiene.md) règle 5).

**`allow_force_pushes` n'est PAS lisible sans droit admin** : `gh api .../branches/main/protection` renvoie **404** sous `myia-ai-01` (#9991). Un 404 y est **une question, pas une absence mesurée** — l'interpréter comme « pas de protection » conclut l'inverse de la vérité. Ce qu'une lane peut vérifier sans admin, c'est le comportement : un `push --force` sur `main` est rejeté par le serveur.

---

### Other Safety Rules

- NEVER commit without explicit user approval
- If secrets are accidentally committed, create a new clean branch with cherry-pick rather than rewriting history
- Always commit incrementally to avoid needing force pushes
- Prefer adding specific files by name over `git add -A` or `git add .`

## Notebook-Specific

- When committing notebook files, always verify outputs are intentionally included
- Commit enrichment changes separately from execution output changes
- Use descriptive commit messages mentioning which notebooks were modified and why

## Orphan-branch scan (L576 ★★)

**S'applique quand** un worker voit une branche distante `jsboige/*` et **envisage de la self-pick**. Les ancres `pulls` **peuvent mentir** : REST `commits/<oid>/pulls` renvoie un faux négatif pour une branche pourtant attachée à une PR OPEN, et une branche squash-mergée n'est jamais ancêtre de `main`. Conclure « orpheline » sur une seule ancre = auto-pick d'un travail en cours, ou re-livraison d'un travail déjà sur `main`.

**Quatre ancres, toutes à passer** — matrice de décision complète, faux positifs mesurés et incident fondateur (c.576, branches attachées à #7086-#7091) : [orphan-branch-scan-l576.md](../../docs/reference/orphan-branch-scan-l576.md).

```bash
git merge-base --is-ancestor <sha> origin/main          # 1. intégrée upstream ? (muette si squash)
gh api repos/jsboige/CoursIA/commits/<sha>/pulls        # 2. REST (faux négatif possible)
gh pr list --state all --search "head:<branch>"         # 3. autoritatif sur les PRs
git log origin/main --oneline --grep "<sujet>"          # 4. identité de CONTENU (squash → sujet préservé)
```

**Anti-pattern** : ne JAMAIS conclure « orpheline » sur `git fetch` + REST seul. Coût de l'investigation : ~10 s. Coût de son omission : un cycle dupliqué, ou l'écrasement d'un travail en cours.
## PR Body Generation

**L677-L4 ★★** — le **body de PR se génère HORS worktree** : scratchpad `<scratchpad-dir>/c<NNN>_pr_body.md` + `gh pr create --body-file <scratchpad-path>`. Jamais un `PR_BODY.md` / `BODY.md` **dans** le worktree, qu'un `git add .` stagerait et qu'un rebase ou amend ramènerait dans un commit de code. Vérifier `git status` avant tout `git add .` : pas de `*.md` orphelin de body dans les fichiers tracés.

Autres leçons ancrées (L721 stale-tracker, L740 cron 7 j, L898 collision cross-lane) : [proactive-coordination.md](proactive-coordination.md) §Leçons ancrées.
