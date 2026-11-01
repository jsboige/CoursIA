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

GitHub auto-closes an issue only when a closing keyword (`close`/`closes`/`closed`, `fix`/`fixes`/`fixed`, `resolve`/`resolves`/`resolved`) **immediately** precedes the reference. Anything between the two is text, and nothing closes. Use safe syntax:

| Intent | Correct | Wrong |
|--------|---------|-------|
| Link without closing | `See #N` or `Part of #N` | ~~`Refs #N`~~ |
| Close when ALL criteria met | `Closes #N` on its own line (verify acceptance first) | ~~`Fixes #N`~~ for partial |
| Partial delivery | `See #N` (partial: X/Y criteria) | ~~`Refs #N`~~ |

**The scope swallows the keyword (#23348).** The mandated `type(scope): subject` form has an inviting place for the issue number — `type(scope,#N): subject` — and that form closes nothing: `(` and the scope sit between the keyword and the number. Measured on `origin/main` over 500 commits: 299 distinct issue numbers cited this way, **186 still open**; among the 162 cited by a correction verb, **95 still open** — issues whose fix is already on `main`, inflating the belt with work already done. Never rely on the subject alone to close. Two forms that work:

- `Fix(ci,#22937): …` **and** a `Closes #22937` line in the commit body (for a squash merge, the PR body becomes that message);
- `Fix(ci): …` and a `Closes #22937` line in the body.

The lister `python scripts/ci/list_scope_swallowed_issues.py` (`--json`, `--all-forms`) names the pairs (open issue, correction commit) so the residual can be triaged. It closes nothing, comments nothing: triage and closure belong to the coordinator (G.9).

## Safety Rules

### Force push — interdit sur `main`, autorisé sur une branche de PR à lane unique

**Décision user 2026-08-08** : périmètre, pas interdit global — les deux cas n'ont pas la même conséquence (contenu partagé sur `main`, travail non mergé d'une seule lane sur sa branche). Verbatim, rationale et incident 2026-03-13 : [git-workflow-detail.md §1](../../docs/reference/git-workflow-detail.md).

| Cible | Règle | Ce qui la porte |
|---|---|---|
| **`main`** | **INTERDIT**, sans exception d'urgence | `allow_force_pushes: false` — GitHub **refuse** le push. C'est le serveur qui tranche, pas une consigne |
| **Branche de PR (`feature/*`, `fix/*`, `docs/*`) à lane unique** | **AUTORISÉ**, `--force-with-lease` préféré | aucune protection plateforme : c'est la discipline de lane qui répond |
| **Branche manipulée par plusieurs agents de front** | **INTERDIT** | un `[CLAIMED]` d'une autre lane sur l'issue vaut « plusieurs agents » → [lane-claim-protocol.md](lane-claim-protocol.md) |

- **L'alternative merge d'abord, quand elle existe** : `git merge origin/main`, `gh pr update-branch`, cherry-pick, revert, nouveaux commits. Le force-push est le dernier recours, jamais le réflexe de rebase par défaut.
- **`gh pr update-branch` ne remet PAS le plancher DWELL à zéro quand la fusion est sans conflit** (#16149) : `last_authoritative_committed_at` saute les fusions de rafraîchissement **prouvées content-free**, et fail-close sur tout le reste (résolution manuelle de conflit, rebase, preuve indisponible = **ré-armé**). **Rafraîchir une branche propre pour récupérer un fix de `main` est donc gratuit.** Ce rouge n'est pas un défaut de la PR — le gate le nomme et le balayage le lève seul ; sur une PR dont le **seul** rouge est `DWELL`, le geste **gratuit** est de rejouer la jambe (`gh run rerun <run_id> --job <job_id>`) : aucun commit, donc aucun ré-armement. Prédicat conjonctif, cadence réelle du balayage (178-341 min, #15197) et récit de la correction (#16962) : [git-workflow-detail.md §4](../../docs/reference/git-workflow-detail.md#4-dwell--pourquoi-update-branch-ne-re-arme-plus-le-plancher-16962).
- **Ce que chaque geste fait au plancher** :
  - `gh pr update-branch` **sans conflit** : **inchangé** — fusion content-free, sautée.
  - `gh pr update-branch` **avec résolution de conflit** : **ré-armé** — l'arbre diffère de l'auto-merge.
  - rebase : **ré-armé** — fail-closed.
  - commit de contenu ordinaire : **ré-armé** — la tête change de date.
- **`update-branch` tue AUSSI le dossier de prévalidation, et c'est la moitié qu'on oublie** : il change la tête, donc le contrat exact-head (`[ADJOINT PREFLIGHT]`, empreinte `surfaces-sha256`, comptes `diff-files`/`additions`) est **périmé à la seconde**, et `check_adjoint_prevalidation.py` rend `head is stale` / `discussion surfaces changed` — c'est cette péremption, et non le DWELL, qui referme la boucle : [prevalidation-dossier-order-detail.md §1-§3](../../docs/reference/prevalidation-dossier-order-detail.md).

  **L'ordre qui sort de la boucle — le dossier vient APRÈS la stabilisation de la branche, jamais avant :**

  1. la lane `update-branch` si elle doit récupérer `main` ;
  2. on laisse les checks se ré-agréger à la nouvelle tête, puis **on rejoue** le job si besoin — personne ne re-pousse. Le plancher DWELL n'a **pas** été ré-armé par un `update-branch` sans conflit ; il ne l'est que par une **résolution manuelle de conflit**, cas où l'attente de 120 min redevient réelle ;
  3. **alors** l'adjoint écrit le dossier, à la tête exacte ;
  4. le coordinateur merge **immédiatement**, et **la branche est gelée entre 3 et 4**.

  La forme **opérationnelle** du contrat exact-head vit dans [`coordinate/SKILL.md`](../skills/coordinate/SKILL.md) (« un changement de head ou de surface le perime ») et n'est **pas** reformulée ici — deux surfaces qui redécrivent la même règle finissent par diverger (#16962). Verbatim de l'organe et réconciliation de l'issue fondatrice : [prevalidation-dossier-order-detail.md](../../docs/reference/prevalidation-dossier-order-detail.md).
- **`--force-with-lease` plutôt que `--force`** : il échoue si le remote a bougé depuis ta dernière lecture — précisément le cas « une autre lane a poussé sans que je le sache ». C'est le garde-fou qui rend le périmètre ci-dessus sûr.
- **Jamais de `reset --hard`** sur `main` ni sur une branche partagée.
- **Un secret déjà commité ne se répare PAS par réécriture d'historique** : branche propre + cherry-pick, et **rotation de la clé** (cf [secrets-hygiene.md](secrets-hygiene.md) règle 5).

**`allow_force_pushes` n'est PAS lisible sans droit admin** : `gh api .../branches/main/protection` renvoie **404** sous `myia-ai-01` (#9991). Un 404 y est **une question, pas une absence mesurée** — l'interpréter comme « pas de protection » conclut l'inverse de la vérité. Ce qu'une lane peut vérifier sans admin, c'est le comportement : un `push --force` sur `main` est rejeté par le serveur.

---

### Other Safety Rules

- Always commit incrementally to avoid needing force pushes
- Prefer adding specific files by name over `git add -A` or `git add .`

## Notebook-Specific

- When committing notebook files, always verify outputs are intentionally included
- Commit enrichment changes separately from execution output changes
- Use descriptive commit messages mentioning which notebooks were modified and why

## Orphan-branch scan (L576 ★★)

**S'applique quand** un worker voit une branche distante `jsboige/*` et **envisage de la self-pick**. Les ancres `pulls` **peuvent mentir** (faux négatif REST sur une branche pourtant attachée à une PR OPEN ; une branche squash-mergée n'est jamais ancêtre de `main`) — **quatre ancres, toutes à passer** : matrice de décision complète, faux positifs mesurés et incident fondateur (c.576, #7086-#7091) : [orphan-branch-scan-l576.md](../../docs/reference/orphan-branch-scan-l576.md).

```bash
git merge-base --is-ancestor <sha> origin/main          # 1. intégrée upstream ? (muette si squash)
gh api repos/jsboige/CoursIA/commits/<sha>/pulls        # 2. REST (faux négatif possible)
gh pr list --state all --search "head:<branch>"         # 3. autoritatif sur les PRs
git log origin/main --oneline --grep "<sujet>"          # 4. identité de CONTENU (squash → sujet préservé)
```

**Anti-pattern** : ne JAMAIS conclure « orpheline » sur `git fetch` + REST seul (coût ~10 s ; omission = cycle dupliqué ou écrasement d'un travail en cours).

## Worktree cleanup en fin de cycle (#14195)

**Problème** : chaque review de PR notebook / build Lean crée un worktree ; sans organe de retrait, ils s'accumulent ([mesures datées, détail §5](../../docs/reference/git-workflow-detail.md)).

**Solution** : `scripts/ci/prune_merged_worktrees.py`, dry-run par défaut, `--apply` explicite. À exécuter en fin de cycle worker (ou via cron) :

```bash
python scripts/ci/prune_merged_worktrees.py             # dry-run : liste ce qui serait retiré
python scripts/ci/prune_merged_worktrees.py --apply     # applique
python scripts/ci/prune_merged_worktrees.py --json      # sortie structuree pour sweep dashboard
```

**Cablage quotidien (#14473)** : `scripts/ci/install_prune_task.py` installe la tache planifiee locale (schtasks DAILY 03:17, journal `%LOCALAPPDATA%\CoursIA\prune_task\logs\`) qui execute la purge en `--apply` — l'appel manuel fin de cycle reste le filet (pourquoi une tache et pas la regle seule : [détail §5](../../docs/reference/git-workflow-detail.md)). Une fois par machine :

```bash
python scripts/ci/install_prune_task.py --install   # garde : REFUSE tant que le fix #14476 n'est pas merge
python scripts/ci/install_prune_task.py --status    # etat de la tache
python scripts/ci/install_prune_task.py --install --dry-run  # afficher argv schtasks sans installer
```

**Critères de retrait (cf issue #14195 acceptance)** :
- **REMOVE** : PR MERGED ou CLOSED, branche sans unpushed, pas d'édition source untracked.
- **REFUSE** : branche `main`/`master` (jamais le worktree de travail) · PR OPEN (l'itération continue) · commits non poussés vs upstream spécifique (`@{u}` non-`main`) · édition source untracked non tolérée (`.py`, `.ipynb`, `.lean`, `.md`, etc.).
- **SKIP_CURRENT** : le worktree depuis lequel le script est lancé.
- **Artefacts untracked tolérés** (`slides/images/`, `**/scripts/results/`, `.claude/agent-memory/*`, `*_output.ipynb`, `node_modules/`, `.cache/`, `.pytest_cache/`, `__pycache__/`, `_measurements/`, `.mypy_cache/`, `.ruff_cache/`, `dist/`, `build/`, `.eggs/`, `.tox/`) — d'après le dernier commentaire de #8924.

**Ancre PR autoritative** : `gh pr list --state all --search "head:<branch>"` (pas `--is-ancestor` seul, ni `commits/<oid>/pulls` REST — cf §Orphan-branch scan ci-dessus pour les faux négatifs mesurés).

**Refus ≠ échec + observabilité** : un REFUS est une **décision** de l'organe : exit 0, le rapport porte le décompte par classe (`refusals:` en texte, `refusal_reasons` en JSON) ; rc≠0 = panne gh/git ou échec d'application, uniquement. La tâche planifiée relaie `--warn-threshold 20` : au-delà, une ligne `[WARN][prune-task]` vit dans le journal (`%LOCALAPPDATA%\CoursIA\prune_task\logs\`). Attribution lane : un spawn peut poser `.lane-owner` (une ligne : `machine:workspace`) à la racine du worktree — l'organe l'affiche (`lane=...`) et l'agrège (`lane_refusals`) ; le fichier est toléré au nettoyage et n'influence AUCUNE décision (mesure : [détail §5](../../docs/reference/git-workflow-detail.md)).

**Mesure datée et contrôle positif** (po-2027, cycle #14195 ; tableau avant/après et contrôle positif du squash-merge) : [détail §5](../../docs/reference/git-workflow-detail.md).

## PR Body Generation

**L677-L4 ★★** — le **body de PR se génère HORS worktree** : scratchpad `<scratchpad-dir>/c<NNN>_pr_body.md` + `gh pr create --body-file <scratchpad-path>`. Jamais un `PR_BODY.md` / `BODY.md` **dans** le worktree, qu'un `git add .` stagerait et qu'un rebase ou amend ramènerait dans un commit de code. Vérifier `git status` avant tout `git add .` : pas de `*.md` orphelin de body dans les fichiers tracés.

Autres leçons ancrées (L721 stale-tracker, L740 cron 7 j, L898 collision cross-lane) : [proactive-coordination.md](proactive-coordination.md) §Leçons ancrées.
