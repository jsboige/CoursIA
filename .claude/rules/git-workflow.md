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

**Décision user 2026-08-08** (verbatim) : « *Je ne suis pas fan des force-pushs, on a déjà perdu pas mal de contenu dans le passé à cause de ça, et il existe généralement une alternative à base de merge. Mais pour une branche de feature qui n'est pas manipulée par plusieurs agents de front, ça n'est pas la même histoire. Donc en gros si on interdit sur main et on permet sur des branches de PRs, ça me va.* »

L'ancienne rédaction interdisait `--force` **partout**, urgence-user comprise. Elle est remplacée par un **périmètre**, parce que les deux cas n'ont pas la même conséquence : sur `main` un force-push écrase du contenu partagé et déjà consommé par ~95 forks étudiants (incident **2026-03-13**, commits potentiellement perdus) ; sur une branche de feature qu'une seule lane manipule, il ne réécrit que le travail non mergé de cette lane.

| Cible | Règle | Ce qui la porte |
|---|---|---|
| **`main`** | **INTERDIT**, sans exception d'urgence | `allow_force_pushes: false` dans la protection de branche — GitHub **refuse** le push. Ce n'est pas qu'une consigne (vérifiable : `gh api repos/jsboige/CoursIA/branches/main/protection -q .allow_force_pushes`) |
| **Branche de PR (`feature/*`, `fix/*`, `docs/*`) à lane unique** | **AUTORISÉ**, `--force-with-lease` préféré | aucune protection côté plateforme : c'est la discipline de lane qui répond |
| **Branche manipulée par plusieurs agents de front** | **INTERDIT** | un `[CLAIMED]` d'une autre lane sur l'issue vaut « plusieurs agents » → [lane-claim-protocol.md](lane-claim-protocol.md) |

- **L'alternative merge d'abord, quand elle existe** : `git merge origin/main`, `gh pr update-branch`, cherry-pick, revert, nouveaux commits. Le force-push est le dernier recours, jamais le réflexe de rebase par défaut.
- **`--force-with-lease` plutôt que `--force`** : il échoue si le remote a bougé depuis ta dernière lecture — précisément le cas « une autre lane a poussé sans que je le sache ». C'est le garde-fou qui rend le périmètre ci-dessus sûr.
- **Jamais de `reset --hard`** sur `main` ni sur une branche partagée.
- **Un secret déjà commité ne se répare PAS par réécriture d'historique** : branche propre + cherry-pick, et **rotation de la clé** (cf [secrets-hygiene.md](secrets-hygiene.md) règle 5).

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

**Compound gate obligatoire** (3 ancres, detail : [orphan-branch-scan-l576.md](../../docs/reference/orphan-branch-scan-l576.md)) — TOUTES doivent etre passees avant de reclamer la branche :

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

**Voir aussi** : [orphan-branch-scan-l576.md](../../docs/reference/orphan-branch-scan-l576.md) (detail fondateur + symtome 5 branches `jsboige/*` decouvertes c.576 / attachees a #7086-#7091). *Ce detail a longtemps ete cite a l'URL `.claude/memory/lecon-L576-...md` : ce chemin est ignore par `.gitignore` (ligne 651, etat local par machine), donc il ne peut jamais exister sur `main` et le lien etait mort par construction. Ne pas le retablir — la doc perenne vit dans `docs/`, cf [harness-hygiene.md](harness-hygiene.md).* Sub-grain 5/5 de l'epic #7423 « revue globale du harnais » (boucle vertueuse close par cette PR — dernier orphelin L576 ancre dans git-workflow ; reste 5 orphelines pour futurs grains cross-famille : L574 / L751 / L770 / L771 / L772+L789+L790+L791).
## PR Body Generation

**Leçon ancrée** — L677-L4 ★★ (c.680, voir aussi c.683/c.684/c.685/c.686/c.687/c.688/c.689/c.690 réutilisations ; détail en mémoire locale per-machine) : le **body de PR se génère HORS worktree**, jamais dans un fichier du worktree (qui finirait stageé par `git add .` ou committe accidentellement).

| Pattern | Correct | Wrong |
|---------|---------|-------|
| **Body** | scratchpad `<scratchpad-dir>/c<NNN>_pr_body.md` (hors worktree) + `gh pr create --body-file <scratchpad-path>` | ~~Créer/Edit un `PR_BODY.md` ou `BODY.md` dans le worktree~~ |
| **Anti-regression** | vérifier `git status` avant `git add .` — pas de `*.md` orphelin du PR body dans la liste des fichiers trackés | ~~Stageer tous les fichiers sans revue~~ |
| **Pourquoi** | éviter contamination du diff (`+lines` du body en `git diff --stat`), éviter qu'un rebase ou amend ramène le body dans un commit de code, éviter `git add -A` qui capture des scratchpads locaux |

**Pourquoi L677-L4 seulement `★★` et pas `★★★`** : la leçon est opérationnelle mais l'incident fondateur (corps de PR committe dans le worktree → revert + recommit) reste rare et recoverable. Le coût = 5 min de rebase. Les `★★★` (L898 collision cross-lane, L721 stale tracker) coûtent des heures.

**Voir aussi** : [proactive-coordination.md](proactive-coordination.md) section "Leçons ancrées (c.8087 L-coupling)" — L721★/L740★/L898★★★ ancrés par c.8088 (PR #8101, complément du même audit L-coupling c.8087 #8099).
