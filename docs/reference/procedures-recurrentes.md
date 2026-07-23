# Procédures récurrentes — CoursIA

Détail des workflows référencés dans [CLAUDE.md](../../CLAUDE.md) section "PROCEDURES RECURRENTES".

## Workflow PR

1. Identifier la mission (issue GitHub ou directive RooSync)
2. Brancher : `git checkout -b feature/<sujet>` (ou `fix/<sujet>`) depuis `main` à jour
3. Implémenter
4. **Pour notebooks modifiés** : re-exécuter le notebook complet, vérifier outputs, vérifier scope strict (pas de re-exec gratuite des autres notebooks de la famille)
5. **Pour code production** : ajouter/modifier tests, lancer le build (PEP8 / `dotnet build`), zéro warning
6. Commit message : `type(scope): description courte` (Conventional commits)
7. Push, ouvrir la PR avec description claire (Summary + Test plan)
8. Auto-review selon les 5 points (CLAUDE.md section B). Si self-review échoue : revenir au point 4
9. Annoncer sur dashboard `[INFO]` ou poster en commentaire de l'issue
10. Attendre review/merge par ai-01. **Ne pas se merger soi-même** (les agents)

## Dispatch agents (coordinateur ai-01)

Pour assigner une tâche à une machine distante (po-2023/2024/2025/2026) :

1. Vérifier la disponibilité : `roosync_dashboard(action: "read", type: "workspace")` + heartbeat machine
2. Composer un message structuré :
   ```
   roosync_send(
     to: "myia-po-XXXX:CoursIA",
     subject: "[DIRECTIVE] <short>",
     priority: "MEDIUM" | "HIGH" | "URGENT",
     tags: ["po-XXXX", "<topic>"],
     body: "## Mission\n...\n## Deliverables\n...\n## Quality Criteria\n..."
   )
   ```
3. Logger le dispatch sur le dashboard workspace `[INFO]`
4. Suivre les rapports de l'agent et acquitter via `roosync_send(action: "reply", ...)`

## Validation notebook (avant commit)

```bash
# 1. Validation structure
python scripts/notebook_tools/notebook_tools.py validate <path>

# 2. Verifier les outputs sont presents (regle C.2)
python -c "import json; nb=json.load(open('<path>')); print(sum(1 for c in nb['cells'] if c['cell_type']=='code' and not c.get('outputs')))"
# 0 = OK, sinon re-executer le notebook

# 3. Verifier l'absence d'erreur volontaire (regle C.1)
grep -nE "raise NotImplementedError|assert False" <path>
# Aucune occurrence acceptable

# 4. Verifier le scope (regle C.3)
git diff <path> | grep -cE '^\+\s*"source"'
# > 0 = source change, OK pour commit. = 0 = uniquement outputs, NE PAS COMMIT
```

## Audit anti-régression (avant merge PR suspecte)

Pour une PR avec deletions > insertions sur code métier (Lean/Coq/Python core / tests) :

```bash
# 1. Comparer historique
git log --all -- <fichier>
git show <commit> -- <fichier>

# 2. Detecter sorry/stub introduits dans Lean
git diff <base>..<pr-branch> -- '*.lean' | grep -E "^\+.*sorry"
# Si presence : exiger justification explicite

# 3. Detecter cellule # Solution -> stub
git diff <base>..<pr-branch> -- '*.ipynb' | grep -E "^[-+].*Solution|^[-+].*pass"

# 4. Cross-check historique : si fichier mentionne en memoire/dashboard recemment, contenu probablement intentionnel
```

Patterns red-flag complets : [.claude/rules/anti-regression.md](../../.claude/rules/anti-regression.md).

## Exécution Quantbooks (règle user 2026-04-29)

Pour un notebook research utilisant `QuantBook()` (kernel QC Cloud uniquement) :

1. **MCP qc-mcp d'abord** : vérifier si un outil exécute le research notebook
2. **Fallback Playwright** : automatiser la session QC Cloud Web (login, navigation projet, Run All, téléchargement notebook exécuté)
3. **Pas de fallback markdown explicatif** : un Quantbook commit doit avoir des outputs réels QC Cloud

## Productivité pendant les opérations longues (règle HARD 2026-05-11)

Quand un processus long tourne (training GPU, backtest QC, build Lean, docker pull, prover BG iter, papermill batch, multi-seed run) : **ne pas attendre passivement**.

1. Lancer le BG, noter son ID + nature attendue
2. **Immédiatement continuer** avec autre travail : autres tracks dispatchées, audits parallèles, préparation PR suivante, review code, planification iter suivante, MAJ docs
3. Check le BG uniquement à intervalles utiles (5-10 min) via `tail -50 output | grep -E "FINAL|RESULT|ERROR"` ou monitor ciblé. **Jamais event-par-event réactif**
4. **Minimum 2 tracks en flight** à tout moment pour chaque agent (1 BG + 1 CPU/IO local). Si un agent n'a qu'un BG, il demande immédiatement une 2e track au coordinateur via `[ASK] capacity` dashboard

**Anti-patterns interdits** :
- "Monitor event arrived, je réponds 'j'attends'" — non, je travaille sur autre chose en parallèle
- "Le BG va prendre 30 min, je fais une pause" — non, j'ai 30 min de travail parallèle disponible
- Dispatcher 1 seule track BG à un agent + dire "reviens quand fini" — non, **2 tracks minimum** (1 BG + 1 CPU)

**Pourquoi** : un BG de 30-60 min consomme 30-60 events monitor si l'agent reste réactif, sans rien produire en parallèle. Le BG tourne même sans surveillance. Coordinateur = chef d'orchestre, pas spectateur.

Incident 2026-05-11 ai-01 (Lean prover iter 6 BG) : ~35 events monitor consommés à regarder BUILD-FAIL répétés, zéro autre track avancée pendant ce temps. User signal explicite "fais en sorte que les autres agents trainers ou prouveurs fassent pareil".

## Validation pré-commit notebook H.3 (regle HARD)

```bash
# Aucun notebook commité sans cellule exécutée (execution_count != null OR outputs non vides)
python -c "import json,sys; nb=json.load(open(sys.argv[1])); bad=[i for i,c in enumerate(nb['cells']) if c['cell_type']=='code' and c.get('execution_count') is None and not c.get('outputs')]; sys.exit(1 if bad else 0)" "$nb"
```

Si fail → (a) exécuter localement (env complet H.2), OU (b) dispatcher RooSync sur machine compatible, OU (c) déplacer dans `_pending_execution/` avec issue ouverte.

## Cycle merge coordinateur — leçons durables (ai-01)

Leçons récurrentes du cycle review+merge, consolidées depuis les logs de cycle. À relire plutôt que de les ré-apprendre incident par incident.

### Cascade catalogue (HARD)

Toute PR touchant `COURSE_CATALOG.generated.json` rend les autres PRs catalog-touchers DIRTY/CONFLICTING au merge (le catalogue est régénéré globalement). Donc :

- Merger les PRs **non-catalogue d'abord**, puis les catalog-touchers **un-par-un**.
- Conflit catalogue = l'auteur **rebase + régénère** : `python scripts/notebook_tools/generate_catalog.py --json --git-tracked-only` (parité CI = N entrées git-tracked ; `--json` nu inclut les `_output.ipynb` locaux = drift), puis `expand_catalog_markers.py`.
- **JAMAIS** force-resolve le conflit côté coord ; **JAMAIS** force-push la branche de l'auteur.
- Check CI **rouge "Notebook catalog drift" = NON mergeable** (propagerait le drift) → bounce à l'auteur pour re-régénérer.
- **Cascade-independence** : une PR dont le drift-check = SUCCESS **et** qui ne touche pas le catalogue est **indépendante** — ne pas la hold à tort dans la file cascade.

### Trap "APPROVED"

`reviewDecision=APPROVED` provient du bot **requis** `clusterManager-Myia` (Hermes/NanoClaw, même compte, distingués par préfixe body `[Hermes]`/`[NanoClaw]`). Mon `gh pr review --request-changes` en `myia-ai-01` **ne flippe PAS** le flag aggregate. Lever un hold = soit `--approve` documenté par evidence, soit admin-merge via `gh auth switch -u jsboige`. Toujours lire body + tous comments + diff (pas le seul flag).

### Qualité enrichissement

**Toujours** sampler le markdown ajouté avant merge : content-specific (interprétation réelle du résultat) = OK ; filler générique ("Suite du traitement", "Analyse des résultats") = REJET (gaming du détecteur, famille #1214).

### Dead-code

Vérifier qu'un script cible est **LIVE** (existe + exporté + ≥1 caller réel + catalogué) AVANT d'écrire/merger des tests dessus. Un test qui importe un module supprimé casse la suite.

### mergeable != ready

Un flip `MERGEABLE` (conflit résolu) ne lève PAS un hold qualité (gate P5, validation user). Distinguer "merge-conflict résolu" de "gate qualité franchi".

### Maturité catalogue = README au render-time

Les flips BETA→PRODUCTION se vérifient via le **badge counts** du README (`PRODUCTION=N→M`), PAS par grep `maturity` dans le JSON (champ vide au render). Ordering non-stable = diff symétrique = churn cosmétique ; `issue_pr_associee` non-préservé au regen.

### Métriques outputs

`output_type` count ≠ missing-outputs. Le vrai métrique "non-exécuté" = `execution_count: null` **ET** `outputs` vide. Un diff de reserialization (churn C.3) n'est pas une régression d'exécution.

### Commandes / vigilance

- Diff d'un fichier d'une PR : `gh pr diff N -- path` n'est **pas** supporté → `git fetch origin pull/N/head:prN` puis `git show prN:path`.
- Une self-review de worker peut **sur-alarmer** (ex. flag "API key exposée" sur un print masqué) → lire le diff réel avant de propager une consigne "rotate".
- Fast-merges (<9 min, compte `jsboige`) bypassent les bots (poll ~30 min) : low-risk mais le gate review est contourné — réserver au forensic/auto trivial.

### Worker discipline post-c.264 (L278-L286) — leçons cross-machine consolidées

Leçons consolidées depuis les incidents **ai-01 INCIDENT c.264 r.26th** (phantom-merger-self-declare) et les 3 cycles subséquents. **Durcies**, **non-délégables**, et **complémentaires** aux règles [proactive-coordination.md](../../.claude/rules/proactive-coordination.md) / [coordinator-discipline.md](../../.claude/rules/coordinator-discipline.md) / [verify-before-claiming.md](../../.claude/rules/verify-before-claiming.md).

**L278 — Worker ne merge JAMAIS** (phantom-merger-self-declare-honest). Une session worker qui invoque `/coordinate` ou `gh pr merge` = confusion de rôle. **Même** si sweep-ready + bots PASS, **même** si le worker se déclare "honest", le merge reste **coord-only**. Source : ai-01 INCIDENT c.264 r.26th où worker-session a tenté d'arbitrer sur PR déjà en sweep.

**L279 — Sweep-ready = DM HIGH vers ai-01, JAMAIS `gh pr merge` côté worker**. Si ta PR est §H.4 sweep-ready (11/11 SUCCESS bots + catalog-guard ✓ + link-check ✓ + propre-rebased origin/main), tu envoies un DM `roosync_send to:"myia-ai-01:CoursIA-2" priority:"HIGH"` avec le verdict §H.4, **et tu postes `[DISPATCH→inbox]` dashboard**. Le coordinateur arbitre, merge, et acquitte. Anti-pattern : "sweep-ready + bots PASS donc je merge" = worker INTERDIT.

**L280 — Cron `/coordinate` = ai-01 coordinateur ONLY**. Worker `CronCreate` = prompt worker-side (`/continue` ou `/executor`), cadence 3540s (clamp runtime ≤1h), **jamais** `/coordinate`. Cause documentée : po-2026:CoursIA-2 cron `/coordinate` worker-side (user 2026-07-07) — inversion de rôle silencieuse. Diagnostic : si ton agent voit `/coordinate` arriver dans son CronCreate, c'est un signe d'inversion.

**L281 — Rebase `origin/main` avant sweep ai-01** quand `gh pr view --json baseRefOid` ≠ merge-base. **3-dot canonique pour R2 substance** (`git diff origin/main...origin/<branch>`) ≠ 2-dot héritage (`git diff origin/main..origin/<branch>` peut montrer 9 fichiers vs 2 = héritage Wave-25/26 sur origin/main non-rebasé). Source : incident po-2023 c.271.

**L282 — Mirror-lanes collision**. Une machine avec **deux** lanes (CoursIA + CoursIA-2) = **deux workers distincts**. Avant de claim, **poster `[CLAIMED] <#issue> — <machine:workspace> <ts>` sur le dashboard** de la lane ciblée — pas l'inverse. Incident fondateur : #5640/#5641 doublon sur #5635, 6 min apart, ai-01 arbitrage 13:51Z.

**L283 — Condensation LLM hallucine état merge/contenu**. TOUT claim d'état (merge / OPEN / contenu main) **DOIT** être vérifié firsthand via `gh pr view --json state,mergedAt,mergeCommit` + `git ls-tree origin/main <file>` + `git log origin/main --oneline` **AVANT** propagation. Hiérarchie de confiance : `gh API > git log > dashboard intercom > status condensé`. Le status condensé auto-92% **peut halluciner** (po-2026 c.288 : "#5657 MERGED by jsboige" alors que PR OPEN CLEAN awaiting sweep).

**L284 — Commit amend légitime pour CI regression**. `git status` montre 1 fichier modifié post CI pass → `git commit --amend --no-edit` (préserve c.187 atomic), puis `git push --force-with-lease origin HEAD` sur **sa propre branche feature**. **Anti-pattern** : créer un 2ᵉ commit "fix CI" (violerait c.187 HARD). Documenter SHA rewrite + `--no-edit` dans body PR + DM ai-01. **Étendu** (c.294) : amend légitime aussi pour CHANGES_REQUESTED fondé sur défaut vérifié firsthand.

**L286 — CI check-links failure → link-depth fix via L284 amend**. (1) `gh run view <run-id> --log-failed | grep -B 2 -A 5 "REGRESSION\|broken link\|❌"` extrait les liens cassés firsthand ; (2) chemin en `../../<file>` trop court → ajouter `../` (3-up → 4-up) ; (3) lien intra-branche vers fichier absent origin/main **et** branche → réécrire URL externe pointant la PR livreuse. Anti-pattern : 2ᵉ commit (violerait c.187).

**L786 — Honest-drain diagnostic AVANT claim** (c.796). Partition drained + cross-famille tracks own par d'autres lanes → **NE PAS forcer low-substance LIGHT** pour combler un cycle. **REARMER wakeup suivant** quand grain DEEP/MED substance-available. Test : `gh issue list --state open | wc -l` > 0 ne suffit pas, il faut **identifier le grain exécutable pour ta capability** (CPU+vision OK, GPU-only exclu).

**L915 — PR OPEN MERGEABLE ≠ PR mergée**. Avant de claim un cycle N dépendant d'une PR OPEN MERGEABLE upstream, vérifier si elle a été mergée dans la fenêtre (`gh pr view --json mergedAt`). 2 options : (a) reporter c.N à `mergedAt` confirmé ; (b) redécouper le grain en substrate standalone + c.N+1.

**Opérationnel — check pré-cycle** :

```bash
# Vérifier 3-prong C715-L2 + L786-L2 + L915 AVANT claim
git log --all --oneline --grep "#<issue>"                    # 0 commit upstream
gh pr list --search "#<issue>" --state all                   # 0 PR antérieure
gh pr view <N> --json state,mergedAt,mergeStateStatus        # état réel PR
gh pr view <N> --json baseRefOid                             # rebase vs main
```
