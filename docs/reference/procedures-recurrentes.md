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
