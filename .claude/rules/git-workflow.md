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

### 🚨 CRITICAL - NEVER FORCE PUSH

**INCIDENT 2026-03-13** : Force push sur main a potentiellement écrasé des commits
- **Règle** : `git push --force` et `--force-with-lease` sont INTERDITS
- **Exception** : Uniquement urgence extrême avec validation explicite du user AU PRÉALABLE
- **Alternative** : Créer feature branch, cherry-pick, revert, ou nouveaux commits
- **Si PR nécessaire** : Créer feature branch FROM main, ne JAMAIS reset main

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

## PR Body Generation

**Leçon ancrée** — [L677-L4 ★★](cycle-c680-argumentation-stale-paths.md) (c.680, voir aussi c.683/c.684/c.685/c.686/c.687/c.688/c.689/c.690 réutilisations) : le **body de PR se génère HORS worktree**, jamais dans un fichier du worktree (qui finirait stageé par `git add .` ou committe accidentellement).

| Pattern | Correct | Wrong |
|---------|---------|-------|
| **Body** | scratchpad `<scratchpad-dir>/c<NNN>_pr_body.md` (hors worktree) + `gh pr create --body-file <scratchpad-path>` | ~~Créer/Edit un `PR_BODY.md` ou `BODY.md` dans le worktree~~ |
| **Anti-regression** | vérifier `git status` avant `git add .` — pas de `*.md` orphelin du PR body dans la liste des fichiers trackés | ~~Stageer tous les fichiers sans revue~~ |
| **Pourquoi** | éviter contamination du diff (`+lines` du body en `git diff --stat`), éviter qu'un rebase ou amend ramène le body dans un commit de code, éviter `git add -A` qui capture des scratchpads locaux |

**Pourquoi L677-L4 seulement `★★` et pas `★★★`** : la leçon est opérationnelle mais l'incident fondateur (corps de PR committe dans le worktree → revert + recommit) reste rare et recoverable. Le coût = 5 min de rebase. Les `★★★` (L898 collision cross-lane, L721 stale tracker) coûtent des heures.

**Voir aussi** : [proactive-coordination.md](proactive-coordination.md) section "Leçons ancrées (c.8087 L-coupling)" — L721★/L740★/L898★★★ ancrés par c.8088 (PR #8101, complément du même audit L-coupling c.8087 #8099).
