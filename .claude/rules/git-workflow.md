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

## Orphan-branch scan (L576 ★★)

**S'applique quand** un worker voit une branche distante `jsboige/*` (via `git fetch`, listing `git branch -r`, ou topic-file date) et **envisage de la self-pick**. Risque : **REST `commits/<oid>/pulls` peut renvoyer un empty / faux negatif** pour une branche reellement attachee a une PR OPEN. Conclure « orpheline » sur REST seul = auto-pick dangereux d'un travail deja en cours.

**Compound gate obligatoire** (3 ancres, voir [lecon-L576](https://github.com/jsboige/CoursIA/blob/main/.claude/memory/lecon-L576-rest-commits-pulls-fpos.md)) — TOUTES doivent etre passees avant de reclamer la branche :

```bash
# 1. Integree upstream ?
git merge-base --is-ancestor <branch-sha> origin/main && echo "INTEGREE_UPSTREAM_ARRETER" || echo "BRANCHE_VIVANTE"

# 2. REST endpoint (peut FPOS negatif)
gh api repos/jsboige/CoursIA/commits/<branch-sha>/pulls --jq '.[].number' || echo "REST_FPOS_POSSIBLE"

# 3. **GATE AUTORITATIF** — `gh pr list --search head:<branch>` couvre les cas ou REST echoue
gh pr list --state all --search "head:<branch>" --json number,state -q '.[].number'
```

**Decision matrixe (issue [c.576](https://github.com/jsboige/CoursIA/issues/576), fondateur 2026-07-17)** :

| Gate 1 (merge-base) | Gate 2 (REST pulls) | Gate 3 (gh pr list) | Verdict |
|---------------------|---------------------|---------------------|---------|
| `INTEGREE` | n'importe | n'importe | **ARRETER** (deja sur main, pas de travail a faire) |
| vivante | vide (=0 PRs) | vide (=0 PRs) | **ORPHELINE CONFIRMEE** (ok self-pick, poser `[CLAIMED]` sur dashboard) |
| vivante | vide MAIS | **PR(s) OPEN/MERGED** | **FPOS REST** : la branche est ATTACHEE — NE PAS self-pick, PR en cours |
| vivante | PRs listes | PRs identiques | confirmation canonique — NE PAS self-pick |
| vivante | PRs listes | gate 3 echoue | incoherence — `gh pr view <PR>` pour reconcilier |

**Anti-pattern** : ne JAMAIS conclure « orpheline » sur `git fetch` + REST seul. Gate 3 est autoritatif ; l'investigation prend ~10 secondes et elimine le risque de double-pickup.

**Voir aussi** : [lecon-L576](https://github.com/jsboige/CoursIA/blob/main/.claude/memory/lecon-L576-rest-commits-pulls-fpos.md) (detail fondateur + symtome 5 branches `jsboige/*` decouvertes c.576 / attachees a #7086-#7091). Sub-grain 5/5 de l'epic #7423 « revue globale du harnais » (boucle vertueuse close par cette PR — dernier orphelin L576 ancre dans git-workflow ; reste 5 orphelines pour futurs grains cross-famille : L574 / L751 / L770 / L771 / L772+L789+L790+L791).
## PR Body Generation

**Leçon ancrée** — [L677-L4 ★★](cycle-c680-argumentation-stale-paths.md) (c.680, voir aussi c.683/c.684/c.685/c.686/c.687/c.688/c.689/c.690 réutilisations) : le **body de PR se génère HORS worktree**, jamais dans un fichier du worktree (qui finirait stageé par `git add .` ou committe accidentellement).

| Pattern | Correct | Wrong |
|---------|---------|-------|
| **Body** | scratchpad `<scratchpad-dir>/c<NNN>_pr_body.md` (hors worktree) + `gh pr create --body-file <scratchpad-path>` | ~~Créer/Edit un `PR_BODY.md` ou `BODY.md` dans le worktree~~ |
| **Anti-regression** | vérifier `git status` avant `git add .` — pas de `*.md` orphelin du PR body dans la liste des fichiers trackés | ~~Stageer tous les fichiers sans revue~~ |
| **Pourquoi** | éviter contamination du diff (`+lines` du body en `git diff --stat`), éviter qu'un rebase ou amend ramène le body dans un commit de code, éviter `git add -A` qui capture des scratchpads locaux |

**Pourquoi L677-L4 seulement `★★` et pas `★★★`** : la leçon est opérationnelle mais l'incident fondateur (corps de PR committe dans le worktree → revert + recommit) reste rare et recoverable. Le coût = 5 min de rebase. Les `★★★` (L898 collision cross-lane, L721 stale tracker) coûtent des heures.

**Voir aussi** : [proactive-coordination.md](proactive-coordination.md) section "Leçons ancrées (c.8087 L-coupling)" — L721★/L740★/L898★★★ ancrés par c.8088 (PR #8101, complément du même audit L-coupling c.8087 #8099).
