# CLAUDE.md

Guidance pour Claude Code travaillant avec le repository CoursIA.

**Documentation deportee — `docs/` :**
- [docs/reference/common-commands.md](docs/reference/common-commands.md) - Setup environnement, validation notebooks, slash commands
- [docs/genai/genai-services.md](docs/genai/genai-services.md) - Architectures Qwen/Lumina, scripts genai-stack, mappings notebooks
- [docs/reference/claude-code-config.md](docs/reference/claude-code-config.md) - Agents, skills, rules, model selection
- [docs/qc/quantconnect.md](docs/qc/quantconnect.md) - Backtests, MCP Docker, structure, livre reference
- Notation etudiants (ECE / ESGF / EPITA / EPF) : moteur generique = [GradeBookApp/configs/README.md](GradeBookApp/configs/README.md) ; **pipelines + donnees par cohorte = prives sur GDrive** `G:\Mon Drive\MyIA\Formation\<ecole>\<annee>\grading\` (PII etudiants, hors repo public)
- [docs/reference/teaching-context.md](docs/reference/teaching-context.md) - Calendrier toutes ecoles, scope EPITA-IS, agents par ecole
- [docs/reference/cluster-agents.md](docs/reference/cluster-agents.md) - Machines cluster, GPU topology, agents par specialisation, dispatch Epic
- [docs/lean/](docs/lean/) - Prover iteration history, intractable diagnosis, LLM endpoints
- [docs/reference/architecture_mcp_roo.md](docs/reference/architecture_mcp_roo.md) - Architecture MCP roo-state-manager (34 outils, RooSync)
- [docs/reference/kernels-runtime.md](docs/reference/kernels-runtime.md) - .NET / Python / WSL kernels, conda envs (`coursia-ml-training`, `mcp-jupyter`, `epita_symbolic_ai`), dotnet-interactive PIN
- [docs/reference/procedures-recurrentes.md](docs/reference/procedures-recurrentes.md) - Workflow PR, dispatch agents, validation notebook, audit anti-regression, productivite operations longues, pre-commit H.3
- [docs/reference/subagents-reference.md](docs/reference/subagents-reference.md) - Catalogue 21 sous-agents + 15 skills, mapping side-tracks, usage async
- [docs/reference/scripts-reference.md](docs/reference/scripts-reference.md) - Catalogue scripts dépôt (notebook CLI, exécution, catalogue anti-drift, qualité, maintenance/env)
- [docs/reference/env-python-reparation.md](docs/reference/env-python-reparation.md) - Reparation env Python (regle F)
- [docs/reference/regles-vigilance-detail.md](docs/reference/regles-vigilance-detail.md) - Detail G.1-G.9 + incidents
- [docs/reference/regles-validation-detail.md](docs/reference/regles-validation-detail.md) - Detail H.1-H.7 + incident Sudoku-13 + plan P0-P4 + pre-commit script

**Regles modulaires `.claude/rules/` (auto-loaded a chaque session)** — chaque section critique ci-dessous renvoie a la regle complete :
- [.claude/rules/git-workflow.md](.claude/rules/git-workflow.md) - Branches, commits, force push (section A)
- [.claude/rules/pr-review-discipline.md](.claude/rules/pr-review-discipline.md) - Critères CHANGES_REQUESTED obligatoires reviewers humains+bots (section B+G)
- [.claude/rules/anti-regression.md](.claude/rules/anti-regression.md) - Patterns red-flag, audit historique (section D)
- [.claude/rules/notebook-conventions.md](.claude/rules/notebook-conventions.md) - Manipulation, structure pedagogique, execution kernel (section C)
- [.claude/rules/exercise-example-labeling.md](.claude/rules/exercise-example-labeling.md) - Labeling Exemple/Exercice content-based, stop flip-flop (mandat user 2026-05-20, incidents #1214/#1336)
- [.claude/rules/code-style.md](.claude/rules/code-style.md) - PEP 8, .NET 9.0, no emojis, langue (section E)
- [.claude/rules/genai-config.md](.claude/rules/genai-config.md) - GenAI Docker config, GPU, .env
- [.claude/rules/wsl-kernels.md](.claude/rules/wsl-kernels.md) - WSL pour kernels notebook (NoteBookApp Linux)
- [.claude/rules/student-pr-reviews.md](.claude/rules/student-pr-reviews.md) - Anti-fuite questions de soutenance sur PR etudiantes (incident 2026-05-17)
- [.claude/rules/lean-merge-discipline.md](.claude/rules/lean-merge-discipline.md) - Lake build SUCCESS local avant merge + BG iter systematique post-PR/msg po-2026 (incidents 2026-05-10/16)
- [.claude/rules/secrets-hygiene.md](.claude/rules/secrets-hygiene.md) - Pas de secrets inline (incident recurrent 2026-05-14)
- [.claude/rules/coordinator-discipline.md](.claude/rules/coordinator-discipline.md) - ai-01 merge actif + no-languishing demandes user
- [.claude/rules/proactive-coordination.md](.claude/rules/proactive-coordination.md) - 1 PR/wakeup + main track + side-track async via sous-agents spécialistes (mandat user 2026-05-23)
- [.claude/rules/user-blocker-signaling.md](.claude/rules/user-blocker-signaling.md) - Re-poke chaque fin de session quand le user bloque (mandat user 2026-05-28, anti-dilution wakeup)
- [.claude/rules/harness-hygiene.md](.claude/rules/harness-hygiene.md) - Info 3 tiers : harnais succinct / docs pérenne / dashboard éphémère (mandat user 2026-06-01)
- [.claude/rules/catalog-pr-hygiene.md](.claude/rules/catalog-pr-hygiene.md) - Catalogue = propriété de l'automatisation (cron main + CI par-PR + guard CI `catalog-guard.yml`), JAMAIS régén sur branche + rebase frais + atomique + `Closes #X` (mandat user 2026-06-06, #2632)
- [.claude/rules/model-delegation.md](.claude/rules/model-delegation.md) - **Tout `Agent()` DOIT avoir un `model` explicite** (`sonnet`/`haiku` par défaut, `opus` uniquement sur justification écrite) — mandat user 2026-06-09. Déléguer le read-heavy borné vérifiable, garder la décision + cross-check, local-git-only sous fenêtre `gh auth` (consolide mandat 2026-06-07, 7 tests confirmants)
- [.claude/rules/three-exercises-per-notebook.md](.claude/rules/three-exercises-per-notebook.md) - Convention >=3 exercices par notebook, rollout progressif (#2161)
- [.claude/rules/sota-not-workaround.md](.claude/rules/sota-not-workaround.md) - Vrai outil SOTA jamais workaround degrade (install/invoke/re-plug machine-env-user, 5 verdicts) + probleme non-trivial qui met le moteur en valeur (BFS vs A*) ; enforce bots §H ; registre EPIC #3801 (mandat user 2026-06-21)
- [.claude/rules/readme-french-first.md](.claude/rules/readme-french-first.md) - Doc nouvelle = FR (jamais "match surrounding EN") + bascule FR preserve l'original en `README.en.md` (separateur point) ; perimetre pedagogique ; EPIC #1650 Phase 0.5 (mandat user 2026-06-21)

---

## REGLES CRITIQUES (8 sections)

### A. Coordination & Git

**Coordination cross-machine = RooSync uniquement.** Dashboard workspace CoursIA + messages directs. GitHub = code, jamais de fichiers `*_TEST_REPORT.md` / `*_COORDINATION.md` / rapports d'audit dans le repo.

**Tour de coordination type** : (1) Lire le contenu **complet** du dashboard (`Read` sur le fichier persiste si la sortie est tronquee), (2) Verifier inbox RooSync non-lus, (3) Verifier heartbeat cluster, (4) Sans mission assignee : envoyer un message a ai-01, ne pas attendre passivement.

**Reporting dashboard** : poster au minimum debut/livraison/fin de session. Si > 30 min sans post = signe d'isolement. Posts `[INFO]` courts > silence.

**Git** : pas de push direct sur `main`, pas de force push (`--force` / `--force-with-lease`) ni `reset --hard` sans validation user. Branches `feature/<sujet>` ou `fix/<sujet>`, un sujet par PR. Le coordinateur (ai-01) review et merge ; les agents ne mergent pas eux-memes. Cf [.claude/rules/git-workflow.md](.claude/rules/git-workflow.md). Incident 2026-03-13 : force push accidentel sur main = commits potentiellement ecrases.

### B. Reviews PR (5 points obligatoires)

Avant tout merge (y compris ses propres PRs) :

| # | Point | Comment |
|---|-------|---------|
| 1 | **Scope reel** | La PR fait ce qu'elle annonce, rien de plus, rien de moins |
| 2 | **Validation automatisee post-fix** | Script qui check **le livrable** (pas le code source), relance APRES le dernier commit |
| 3 | **Coherence pedagogique** | Exercices alignes au contenu enseigne, pas de redondance, stubs `TODO` coherents, ordre cellules logique |
| 4 | **Execution reelle** | Papermill ou Jupyter pour notebooks (CI = syntaxe seule). Slidev `?clicks=99` pour slides |
| 5 | **Regression check** | Grep des symboles touches dans le reste du depot |

**Si un seul point n'est pas verifie : ne pas merger.**

**Preuves verifiables, pas mots-cles** : "Papermill SUCCESS" / "tests passed" / "sorry count -1" / "BEATS" / "FALSE POSITIVE" sans log/lien CI / `lake build SUCCESS` post-modif / multi-seed ≥4 + edge ≥2σ / 3 cellules-types verifiees = invalide.

**Honnetete des rapports** : pas de "DONE"/"fixed"/"validated" sans validation post-fix relancee. Rapporter "5/7, 2 restantes" pas "DONE". Pas de markdown "RAPPORT"/"AUDIT" comme preuve sans code valide.

**Reviewers (humains et bots)** : critères CHANGES_REQUESTED obligatoires (composite >3000 lignes / >15 fichiers / >4 features ; Lean sans `grep -c sorry` + Lake build SUCCESS ; ML sans multi-seed ≥4 + verdict BEATS/NO BEATS/INCONCLUSIVE ; notebook sans output Papermill colle ; docs-only PR <50 lignes). APPROVED malgre violation = complicite. Cf [.claude/rules/pr-review-discipline.md](.claude/rules/pr-review-discipline.md).

### C. Notebooks (3 regles user 2026-04-26)

**C.1 - Pas d'erreur volontaire.** `raise NotImplementedError`, `assert False`, `1/0`, et toute erreur intentionnelle sont **INTERDITS partout** dans un notebook (top-level, methode, fonction utilitaire). Patterns de stub corrects : `pass`, `print("Exercice a completer")`, `return None`, `result = None  # TODO etudiant`. Conserver tous les `# TODO`, `# Indice`, `# Etape N`. Le notebook doit s'executer de bout en bout meme exercices non completes. Detail patterns par cas + structure pedagogique + .NET cell-by-cell + BATCH_MODE : [.claude/rules/notebook-conventions.md](.claude/rules/notebook-conventions.md).

**C.2 - Notebooks committes AVEC outputs.** `execution_count: <int>` + `outputs: [...]` coherents pour chaque cellule code executable. Modification d'une cellule code = re-execution complete avant commit. Notebook non-executable en local (kernel manquant, GPU requis) : documenter en markdown, executer ailleurs, committer avec outputs reels. Exception : modifs uniquement markdown -> outputs precedents valides. Quantbooks (`QuantBook()` etc.) = exigence d'execution **via QC Cloud** (MCP qc-mcp / Playwright en fallback), pas de "markdown explicatif" comme contournement.

**C.3 - Scope strict des re-executions Papermill.** Un agent ne commit QUE les notebooks qu'il a effectivement modifies (cellule source code/markdown). Les re-executions Papermill de notebooks dont aucune cellule source n'a change ne doivent pas etre stagees (verification `git diff "$nb" | grep -cE '^\+\s*"source"' > 0`). Pour audit/inventaire : Papermill dans `/tmp/audit_<famille>_$(date +%s)/`, rapport sur dashboard, pas dans le repo. Incidents 2026-04-25 : 2 collisions PR par re-executions paralleles (#540 vs #541, #541 vs #542).

### D. Anti-regression (code de production)

S'applique aux **preuves Lean/Coq, fonctions metier appelees, tests, librairies**. **Pas** aux cellules d'exercice etudiant (qui doivent justement etre stubbees, cf C.1).

**INTERDIT** : remplacer une preuve formelle ou une implementation existante par `sorry` / stub vide / `return None` / `pass`, sans diagnostic explicite et tactiques d'adaptation tentees. Commits "fix compilation" / "Mathlib fix" / "lint fix" / "simplify" avec **deletions > insertions** sur code metier sont **red flag** par defaut.

Protocole avant suppression (4 etapes : erreur exacte / 3 tactiques / PR `debt` + sign-off / diff coherent) + detection `grep -c sorry` : [.claude/rules/anti-regression.md](.claude/rules/anti-regression.md). Incident 2026-04-24 : commit "Mathlib compilation fixes" (#524) a remplace 9 preuves d'Arrow.lean par `sorry`, perte d'une semaine de port Lean ; restoration via #527.

### E. Code style (resume)

| Aspect | Regle |
|--------|-------|
| Emojis | Interdits dans code, variables, fichiers generes, messages de commit |
| Python | PEP 8, type hints, Python 3.10+, `venv` + `requirements.txt` |
| C# / .NET | .NET 9.0, .NET Interactive pour notebooks, `Microsoft.SemanticKernel` |
| Notebooks | Documentation primaire en francais, code en francais ou anglais |
| Naming | Pas de prefixes "Pure"/"Enhanced"/"Advanced"/"Ultimate" |

Detail complet : [.claude/rules/code-style.md](.claude/rules/code-style.md).

### F. Environnement — REPARER, ne JAMAIS contourner (HARD)

**Regle user 2026-05-06 (Python) + 2026-05-26 (kernels)** : un env degrade ou un kernel manquant ne se contourne **jamais** par delegation, fallback ou skip. On **installe** le kernel/env manquant sur la machine locale, on demande UAC user au besoin.

**Kernels installables partout** : .NET Interactive (`dotnet tool install --global Microsoft.dotnet-interactive`), Python 3 (via conda env dedie), Lean 4 (`elan toolchain install stable`). Verification : `jupyter kernelspec list`. Versions/paths exacts + envs Conda `coursia-ml-training` / `mcp-jupyter` / `epita_symbolic_ai` : [docs/reference/kernels-runtime.md](docs/reference/kernels-runtime.md). Reparation Python : [docs/reference/env-python-reparation.md](docs/reference/env-python-reparation.md).

**Anti-patterns INTERDITS** (incident PR #1591 ML.Net, commit `4ca477e`) :
- "kernel not available locally" dans un body PR = **manquement grave** à H.2
- Déleguer la re-exécution à ai-01 au lieu d'installer le kernel = **contournement** de la règle F
- Committer un notebook sans re-exécuter les cells modifiées = violation C.2
- "je n'ai pas le temps d'installer" = pas une excuse
- Skip env local + delegation, "j'ignore le warning", reinstall en boucle sans cleanup `~xxx/`, `except Exception: pass` sur imports

**Exception** : GPU-only notebooks (CUDA requis sur machine CPU-only) — documenter explicitement et demander re-exécution sur machine GPU. Mais .NET Interactive, Python, Lean = installables **partout**.

### G. Vigilance permanente — anti-complaisance

S'applique a **tous les agents** (executants, coordinateur, reviewers humains et bots). Detail G.1-G.9 + incidents : [docs/reference/regles-vigilance-detail.md](docs/reference/regles-vigilance-detail.md).

| # | Regle | Resume |
|---|-------|--------|
| G.1 | Verifier claims ET verdicts contre la source | `grep`/`Read` avant d'affirmer une absence. **Un verdict d'un autre agent se relit contre le scope reel de l'issue AVANT d'agir : le label n'est pas la preuve.** Pas de propagation par confiance |
| G.2 | Metriques honnetes pas binaires | sorry=0 sans lake build SUCCESS = invalide. BEATS sans multi-seed = invalide |
| G.3 | Pas de "DONE" sur progres marginal | Pourcentage explicite + liste residuelle obligatoires |
| G.4 | Composites trop larges = split | > 3000 lignes / 15 fichiers / 4 features / 1 domaine = CHANGES_REQUESTED |
| G.5 | Shopping cart interdit | 2 deep tracks max par agent + criteres de sortie verifiables |
| G.6 | Audit avant merge cascade | Lire le diff + verifier 1 claim par PR avant merge |
| G.7 | Stagnation cross-cycle = escalade | Pas d'acceptation "BLOCKED" sans preuve concrete |
| G.8 | Bots reviewers pas de rubber-stamp | APPROVE > 3 PRs en < 10 min = contester. APPROVED sur composite = CHANGES_REQUESTED |
| G.9 | Culture du doute | Se demander "puis-je avoir tort ?" avant rapport/merge/**close d'issue**. Fermer une issue = lire body complet + confronter verdict invoque, jamais sur le label seul (incident #274) |

### H. Validation REELLE — pas de complaisance, jamais

S'applique a TOUS les agents. Aucune derogation. Detail H.1-H.7 + incident Sudoku-13 + plan P0-P4 + pre-commit bash script H.3 : [docs/reference/regles-validation-detail.md](docs/reference/regles-validation-detail.md). Workflow pre-commit egalement deporte : [docs/reference/procedures-recurrentes.md](docs/reference/procedures-recurrentes.md#validation-pré-commit-notebook-h3-regle-hard).

| # | Regle | Resume |
|---|-------|--------|
| H.1 | Validation = exec complete + outputs verifies | 4 preuves : exec_count!=null, 0 error, Papermill end-to-end, trailer body PR |
| H.2 | Tous les agents installent l'env complet | Python+Conda+.NET 9+WSL+Lean+Docker. Reparation > contournement |
| H.3 | Aucun commit de notebook non-execute | Pre-commit check `execution_count is None and not outputs` = fail bloquant (script : voir [detail](docs/reference/regles-validation-detail.md)) |
| H.4 | Merges coord JAMAIS complaisants | git checkout + Papermill local OU body PR avec log + scope OK (relax JSON forensic) |
| H.5 | Bots reviewers audit forensique | Verdict EXEC_PROVED / STRUCTURAL_ONLY / SUSPECT_REGRESSION par parsing JSON diff |
| H.6 | Audit historique = responsabilite bot | `audit-history` bot retourne `LAST_REAL_EXEC` ou `NEVER_EXECUTED_SINCE_<creation>` |
| H.7 | Plan P0-P4 sortie cycle perpetuel | P0 gel + P1 STABLE_SNAPSHOT + P2 exec/archive + P3 GH Actions + P4 regen mensuelle |

---

## CARTOGRAPHIE & OUTILS

```
MyIA.AI.Notebooks/                      # Series pedagogiques par theme
- GenAI/{Image,Audio,Video,Texte}/      # 60+ notebooks Python (cf docs/genai/genai-services.md)
- ML/                                    # ML.NET tutorials (.NET C#)
- Search/{Part1-Foundations, Part2-CSP, Part3-Advanced}/  # Search/CSP (Mixed)
- Sudoku/                                # Constraint solving (.NET C#)
- SymbolicAI/{Lean, Tweety, SemanticWeb, Planning, SmartContract}/
- Probas/                                # Infer.NET probabilistic (.NET C#)
- GameTheory/                            # OpenSpiel + Lean (cf 16b/16c/16d Social Choice)
  - social_choice_lean/                  # Lean 4 port Arrow/Sen/Voting
- IIT/                                   # PyPhi (Python)
- QuantConnect/                          # 27 notebooks + 50 strategies (cf docs/qc/quantconnect.md)
- Config/settings.json                   # API settings

scripts/notebook_tools/notebook_tools.py # CLI multi-famille (validate/execute/skeleton/analyze)
scripts/smartcontracts/                  # SC-specifique
scripts/genai-stack/genai.py             # GenAI Docker + validation (cf docs/genai/genai-services.md)

.claude/{agents, skills, rules}/         # 21 sous-agents, 15 skills, rules auto-loaded
GradeBookApp/                            # Notation etudiants : moteur generique (pipelines+donnees par cohorte prives sur GDrive)
docker-configurations/                   # ComfyUI + Qwen Docker
docs/                                    # Documentation deportee de ce CLAUDE.md
```

**Tables detaillees** (scripts reutilisables, skills slash commands, MCP servers, GenAI services, kernels & runtime) : [docs/reference/common-commands.md](docs/reference/common-commands.md), [docs/reference/claude-code-config.md](docs/reference/claude-code-config.md), [docs/reference/kernels-runtime.md](docs/reference/kernels-runtime.md), [docs/genai/genai-services.md](docs/genai/genai-services.md).

**Regle generale outils** : ne jamais ecrire un script ad-hoc d'execution / validation : il existe presque toujours un outil dedie dans `scripts/notebook_tools/`. Si manquant, l'ajouter la (pas dans la racine `scripts/`).

### Catalogue agents / skills / scripts — USAGE MANDATÉ (mandat user 2026-05-23)

**Règle HARD.** Là où un **sous-agent** spécialiste, un **skill** slash-command, ou un **script** dédié couvre une tâche, **l'utiliser plutôt que de réimproviser le workflow à la main**. Les Epics side-tracks **DOIVENT** déléguer aux sous-agents async (`run_in_background: true`) quand un specialist existe.

- **Sous-agents `.claude/agents/`** : invoquer via `Agent(subagent_type: "<nom>")`. Familles : orchestrateurs side-track async, notebooks (designer/enricher/cleaner/cell-iterator/modernizer/executor/validator), trading QC, training ML (#1454), GenAI (#1385), prover Lean (#1453), README/slides, génériques. **Roster complet + mapping side-track Epic → specialists** : [docs/reference/subagents-reference.md](docs/reference/subagents-reference.md).
- **Skills `.claude/skills/`** : invoquer en slash-command `/<nom>` (`/coordinate`, `/review-student-prs`, `/build-notebook`, `/enrich-notebooks`, … — **liste complète** : [docs/reference/subagents-reference.md](docs/reference/subagents-reference.md)).
- **Scripts dédiés** : catalogue complet (notebook CLI, catalogue anti-drift, qualité/conformité C.1-C.3, exécution, environnement, genai-stack) : [docs/reference/scripts-reference.md](docs/reference/scripts-reference.md). **Ne jamais** réécrire un script d'exécution/validation/maintenance.

**Règle collision** : sous-agents read-only en parallèle OK ; sous-agents **éditeurs = un seul à la fois par notebook/série**.

**Usage async (pattern side-track)** : `Agent(subagent_type: "<specialist>", run_in_background: true, description: "<3-5 mots>", prompt: "<contexte repo + Epic + livrable + contraintes>")`. Le message final revient en notification ; l'intégrer/PR au wakeup suivant. Cf [.claude/rules/proactive-coordination.md](.claude/rules/proactive-coordination.md).

**Modèle explicite obligatoire** (mandat user 2026-06-09) : tout `Agent()` DOIT spécifier `model: "sonnet"` ou `model: "haiku"`. `model: "opus"` uniquement sur justification écrite dans le prompt (décision architecturale cross-fichier, synthèse contradictoire, investigation régression profonde). Un sous-agent sans `model` explicite hérite du parent (opus) = violation. Cf [.claude/rules/model-delegation.md](.claude/rules/model-delegation.md).

---

## PROCEDURES RECURRENTES

**Workflows detailles** (Workflow PR 10 etapes, Dispatch agents template, Validation notebook bash, Audit anti-regression bash, Execution Quantbooks, **Productivite operations longues** - 2 tracks min, pre-commit notebook H.3) : [docs/reference/procedures-recurrentes.md](docs/reference/procedures-recurrentes.md).

**Productivite operations longues — HARD 2026-05-11** : quand un processus long tourne (training GPU, backtest QC, build Lean, prover BG iter, papermill batch), **ne pas attendre passivement**. Lancer BG, immediatement continuer autre travail, check uniquement intervalles utiles (5-10 min), **minimum 2 tracks en flight**. Detail 4 etapes + anti-patterns + incident Lean prover iter 6 (~35 events monitor consommes) : [docs/reference/procedures-recurrentes.md](docs/reference/procedures-recurrentes.md#productivité-pendant-les-opérations-longues-règle-hard-2026-05-11).

---

## REGLES AGENTS (Roo Code distants)

| Regle | Resume |
|-------|--------|
| **Code avant documentation** | Code fonctionnel > tests/validation > documentation. Pas de markdown (README, MAPPING, RAPPORT) sans code fonctionnel associe. Rapports d'audit / inventaires / status → dashboard RooSync, pas dans le repo. Pas de `EXTEND_*.md` / `PROCEDURE_*.md`. |
| **Slides : images en overlay** | Layout `image-overlay` avec texte par-dessus, jamais en colonne droite (regle issue #221, confirmee 5+ fois). Verification visuelle Slidev sur **CHAQUE** slide modifie, `?clicks=99`, absence d'overflow. |
| **Pas de duplication** | Avant de creer un fichier (README, docs, lib), verifier qu'il n'existe pas (`grep`, `find`). Mettre a jour plutot qu'en creer un nouveau. |
| **Enrichissement notebooks** | Cellules de transition : contenu pedagogique specifique (pas "Suite du traitement" generique). Cellules d'interpretation APRES la cellule de code interpretee. Pas d'enrichissement parallele du meme notebook dans deux sessions. |

---

## QUANTCONNECT (resume)

- **Backtest obligatoire** apres modification (`create_compile` -> `create_backtest` -> `read_backtest`). Reporter Sharpe/CAGR/MaxDD dans commit + RooSync.
- **API uniquement via MCP Docker** `quantconnect/mcp-server` (config `.mcp.json`, jamais committer le token). Pas de scripts REST directs.
- **Rate limiting** : MAX 10 appels/min entre TOUS les agents. Annoncer sur dashboard avant un backtest.
- **Quantbooks** = exigence d'execution **via QC Cloud** (MCP / Playwright en fallback), pas d'execution locale fictive.
- **Livre reference** : *Hands-On AI Trading* (Jared Broad), https://www.hands-on-ai-trading.com/

Cf [docs/qc/quantconnect.md](docs/qc/quantconnect.md) pour structure complete.

---

## PROJECT OVERVIEW

CoursIA = plateforme educative AI : Jupyter notebooks (C# .NET Interactive + Python), Docker infrastructure GenAI (ComfyUI + Qwen), GradeBookApp evaluation etudiants. Repository : https://github.com/jsboige/CoursIA. Documentation primaire en francais ; commentaires code en francais ou anglais.

Stack : OpenAI/Anthropic APIs, Qwen 2.5-VL, Semantic Kernel, Python 3.10+ + .NET 9.0 Interactive, Papermill + MCP Jupyter, ComfyUI GPU (RTX 3090).
