# CLAUDE.md

Guidance pour Claude Code travaillant avec le repository CoursIA.

**Documentation deportee — `docs/` :**
- [docs/common-commands.md](docs/common-commands.md) - Setup environnement, validation notebooks, slash commands
- [docs/genai-services.md](docs/genai-services.md) - Architectures Qwen/Lumina, scripts genai-stack, mappings notebooks
- [docs/claude-code-config.md](docs/claude-code-config.md) - Agents, skills, rules, model selection
- [docs/quantconnect.md](docs/quantconnect.md) - Backtests, MCP Docker, structure, livre reference
- [docs/ece-grading.md](docs/ece-grading.md) - Pipeline GradeBookApp (notation collegiale, bonus CC, compilation), repos etudiants
- [docs/teaching-context.md](docs/teaching-context.md) - Calendrier toutes ecoles, scope EPITA-IS, agents par ecole
- [docs/cluster-agents.md](docs/cluster-agents.md) - Machines cluster, GPU topology, agents par specialisation, dispatch Epic
- [docs/lean/](docs/lean/) - Prover iteration history, intractable diagnosis, LLM endpoints
- [docs/architecture_mcp_roo.md](docs/architecture_mcp_roo.md) - Architecture MCP roo-state-manager (34 outils, RooSync)
- [docs/kernels-runtime.md](docs/kernels-runtime.md) - .NET / Python / WSL kernels, conda envs, dotnet-interactive PIN
- [docs/procedures-recurrentes.md](docs/procedures-recurrentes.md) - Workflow PR, dispatch agents, validation notebook, audit anti-regression

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
- [.claude/rules/lean-lake-build-required.md](.claude/rules/lean-lake-build-required.md) - Lake build SUCCESS local obligatoire avant merge Lean PR (incident 2026-05-10)
- [.claude/rules/lean-prover-bg-systematic.md](.claude/rules/lean-prover-bg-systematic.md) - BG iter systematique post-PR/msg po-2026 sur sorry Lean
- [.claude/rules/secrets-hygiene.md](.claude/rules/secrets-hygiene.md) - Pas de secrets inline (incident recurrent 2026-05-14)
- [.claude/rules/coordinator-discipline.md](.claude/rules/coordinator-discipline.md) - ai-01 merge actif + no-languishing demandes user

---

## REGLES CRITIQUES (7 sections)

### A. Coordination & Git

**Coordination cross-machine = RooSync uniquement.** Dashboard workspace CoursIA + messages directs. GitHub = code, jamais de fichiers `*_TEST_REPORT.md` / `*_COORDINATION.md` / rapports d'audit dans le repo.

**Tour de coordination type** :
1. Lire le contenu **complet** du dashboard (`Read` sur le fichier persiste si la sortie est tronquee)
2. Verifier inbox RooSync pour les non-lus
3. Verifier le heartbeat cluster (machines actives)
4. Sans mission assignee : envoyer un message a ai-01, ne pas attendre passivement

**Reporting dashboard** : poster sur le dashboard workspace CoursIA au minimum au debut de session, apres chaque livraison significative, et en fin de session. Le coordinateur (ai-01) ne doit jamais constater un silence > 2h d'un agent actif. Si une session depasse 30 min sans post dashboard, c'est un signe d'isolement. Les posts `[INFO]` courts sont preferables au silence.

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

**Preuves verifiables, pas mots-cles** :
- "Papermill SUCCESS" en mot-cle = insuffisant. Coller les premieres lignes des outputs ou un lien CI.
- "tests passed" sans lien CI = insuffisant. Lien obligatoire.
- "sorry count -1" sans `lake build SUCCESS` post-modification = invalide. Build log obligatoire.
- "BEATS" / "improvement" sans 5-fold walk-forward × ≥4 seeds + edge ≥ 2σ documente = invalide.
- "Migration NOT recommended" / "FALSE POSITIVE" sans 3 cellules-types verifiees avec preuve = invalide.

**Honnetete des rapports** : pas de "DONE"/"fixed"/"validated" sans validation post-fix relancee. Si fix corrige 5/7 cellules : rapporter "5/7, 2 restantes identifiees", pas "DONE". Si N sorrys passent a M < N : rapporter "N→M (X% restant)", pas "DONE Voting". Pas de markdown "RAPPORT"/"AUDIT" comme preuve sans code valide.

**Reviewers (humains et bots)** : critères CHANGES_REQUESTED obligatoires si composite >3000 lignes hors notebooks ou >15 fichiers ou >4 features melangees, si Lean PR sans `grep -c sorry` avant/apres + Lake build SUCCESS, si ML PR sans multi-seed ≥4 + verdict explicite (BEATS/NO BEATS/INCONCLUSIVE), si notebook PR sans output Papermill colle, si docs-only PR <50 lignes (group obligatoire). APPROVED malgre violation = complicite. Cf [.claude/rules/pr-review-discipline.md](.claude/rules/pr-review-discipline.md).

### C. Notebooks (3 regles user 2026-04-26)

**C.1 - Pas d'erreur volontaire.** `raise NotImplementedError`, `assert False`, `1/0`, et toute erreur intentionnelle sont **INTERDITS partout** dans un notebook (top-level, methode, fonction utilitaire). Raison : Papermill plante sur la suite, validation traque les erreurs comme bugs, agents tentent de "resoudre" pour faire passer.

Patterns de stub d'exercice corrects :

| Cas | Pattern |
|-----|---------|
| Cellule top-level a completer | `print("Exercice a completer")` ou `pass` |
| Methode classe a implementer | `def foo(self): pass  # TODO etudiant : <description>` |
| Fonction utilitaire stub | `def helper(...): return None  # TODO etudiant` |
| Bloc avec valeur attendue | `result = None  # TODO etudiant : remplacer par compute_thing()` |

Conserver tous les `# TODO`, `# Indice`, `# Etape N`. Le notebook doit s'executer de bout en bout meme exercices non completes.

**C.2 - Notebooks committes AVEC outputs.** `execution_count: <int>` + `outputs: [...]` coherents pour chaque cellule code executable. Modification d'une cellule code = re-execution complete avant commit. Notebook non-executable en local (kernel manquant, GPU requis) : documenter en markdown, executer ailleurs, committer avec outputs reels. Exception : modifs uniquement markdown -> outputs precedents valides. Quantbooks (`QuantBook()` etc.) = exigence d'execution **via QC Cloud** (MCP qc-mcp / Playwright en fallback), pas de "markdown explicatif" comme contournement.

**C.3 - Scope strict des re-executions Papermill.** Un agent ne commit QUE les notebooks qu'il a effectivement modifies (cellule source code/markdown). Les re-executions Papermill de notebooks dont aucune cellule source n'a change ne doivent pas etre stagees (verification `git diff "$nb" | grep -cE '^\+\s*"source"' > 0`). Pour audit/inventaire : Papermill dans `/tmp/audit_<famille>_$(date +%s)/`, rapport sur dashboard, pas dans le repo. Incidents 2026-04-25 : 2 collisions PR par re-executions paralleles (#540 vs #541, #541 vs #542).

**Patterns notebook detailles** (manipulation, structure pedagogique, .NET cell-by-cell, BATCH_MODE, working directory) : cf [.claude/rules/notebook-conventions.md](.claude/rules/notebook-conventions.md).

### D. Anti-regression (code de production)

S'applique aux **preuves Lean/Coq, fonctions metier appelees, tests, librairies**. **Pas** aux cellules d'exercice etudiant (qui doivent justement etre stubbees, cf C.1).

**INTERDIT** : remplacer une preuve formelle ou une implementation existante par `sorry` / stub vide / `return None` / `pass`, sans diagnostic explicite et tactiques d'adaptation tentees. Commits "fix compilation" / "Mathlib fix" / "lint fix" / "simplify" avec **deletions > insertions** sur code metier sont **red flag** par defaut.

**Protocole avant suppression** :
1. Citer l'erreur compilateur exacte ou test echoue nomme (pas "ca compilait pas")
2. Tenter 3 adaptations tactiques avant la suppression (instance ajoutee, tactique alternative, hypothese ajoutee)
3. PR dediee labellisee `debt`/`regression-accepted` avec sign-off user pour toute regression assumee
4. `git diff --stat` coherent avec l'intention

**Detection** : `grep -c sorry` avant/apres sur fichiers Lean/Coq, suppressions de corps de fonction metier appelee, cellules `# Solution` (exemple resolu) -> stubs.

Incident 2026-04-24 : commit "Mathlib compilation fixes" (#524) a remplace 9 preuves d'Arrow.lean par `sorry`, perte d'une semaine de port Lean ; restoration via #527. Cf [.claude/rules/anti-regression.md](.claude/rules/anti-regression.md).

### E. Code style (resume)

| Aspect | Regle |
|--------|-------|
| Emojis | Interdits dans code, variables, fichiers generes, messages de commit |
| Python | PEP 8, type hints, Python 3.10+, `venv` + `requirements.txt` |
| C# / .NET | .NET 9.0, .NET Interactive pour notebooks, `Microsoft.SemanticKernel` |
| Notebooks | Documentation primaire en francais, code en francais ou anglais |
| Naming | Pas de prefixes "Pure"/"Enhanced"/"Advanced"/"Ultimate" |

Detail complet : [.claude/rules/code-style.md](.claude/rules/code-style.md) (auto-loaded a chaque session).

### F. Environnement Python — REPARER, ne JAMAIS contourner

**Regle user 2026-05-06** : un env Python degrade ne se contourne **jamais** par delegation, fallback ou skip. On repare, on demande UAC user au besoin. Detail : [docs/env-python-reparation.md](docs/env-python-reparation.md).

**Envs Conda dedies sur ai-01** (utiliser AVANT de toucher Python systeme) :

| Env | Usage | Path |
|-----|-------|------|
| `coursia-ml-training` | ML training (PyTorch CUDA, sklearn, scipy) | `C:\Users\MYIA\miniconda3\envs\coursia-ml-training` |
| `mcp-jupyter` | MCP Jupyter server | `C:\Users\MYIA\miniconda3\envs\mcp-jupyter` |
| `epita_symbolic_ai` | EPITA SymbolicAI series | `C:\Users\MYIA\.conda\envs\epita_symbolic_ai` |

Pour `train_*.py` : **toujours** activer `coursia-ml-training` (`& "C:\Users\MYIA\miniconda3\envs\coursia-ml-training\python.exe"`). Anti-patterns interdits : skip env local + delegation, workarounds "j'ignore le warning", reinstall en boucle sans cleanup `~xxx/`, `except Exception: pass` sur imports.

### G. Vigilance permanente — anti-complaisance

S'applique a **tous les agents** (executants, coordinateur, reviewers humains et bots). Ces regles sont permanentes. Detail G.1-G.9 + incidents : [docs/regles-vigilance-detail.md](docs/regles-vigilance-detail.md).

| # | Regle | Resume |
|---|-------|--------|
| G.1 | Verifier claims contre code | `grep`/`Read` avant d'affirmer une absence. Pas de propagation par confiance |
| G.2 | Metriques honnetes pas binaires | sorry=0 sans lake build SUCCESS = invalide. BEATS sans multi-seed = invalide |
| G.3 | Pas de "DONE" sur progres marginal | Pourcentage explicite + liste residuelle obligatoires |
| G.4 | Composites trop larges = split | > 3000 lignes / 15 fichiers / 4 features / 1 domaine = CHANGES_REQUESTED |
| G.5 | Shopping cart interdit | 2 deep tracks max par agent + criteres de sortie verifiables |
| G.6 | Audit avant merge cascade | Lire le diff + verifier 1 claim par PR avant merge |
| G.7 | Stagnation cross-cycle = escalade | Pas d'acceptation "BLOCKED" sans preuve concrete |
| G.8 | Bots reviewers pas de rubber-stamp | APPROVE > 3 PRs en < 10 min = contester. APPROVED sur composite = CHANGES_REQUESTED |
| G.9 | Culture du doute | Se demander "puis-je avoir tort ?" avant rapport/merge. Reproduire les "breakthrough" |

### H. Validation REELLE — pas de complaisance, jamais

S'applique a TOUS les agents. Aucune derogation. Detail H.1-H.7 + incident Sudoku-13 + plan P0-P4 : [docs/regles-validation-detail.md](docs/regles-validation-detail.md).

| # | Regle | Resume |
|---|-------|--------|
| H.1 | Validation = exec complete + outputs verifies | 4 preuves obligatoires : exec_count!=null, 0 error, Papermill end-to-end, trailer body PR |
| H.2 | Tous les agents installent l'env complet | Python+Conda+.NET 9+WSL+Lean+Docker. Reparation > contournement |
| H.3 | Aucun commit de notebook non-execute | Pre-commit check `execution_count is None and not outputs` = fail bloquant |
| H.4 | Merges coord JAMAIS complaisants | git checkout + Papermill local OU body PR avec log + scope OK (relax JSON forensic) |
| H.5 | Bots reviewers audit forensique | Verdict EXEC_PROVED / STRUCTURAL_ONLY / SUSPECT_REGRESSION par parsing JSON diff |
| H.6 | Audit historique = responsabilite bot | `audit-history` bot retourne `LAST_REAL_EXEC` ou `NEVER_EXECUTED_SINCE_<creation>` |
| H.7 | Plan P0-P4 sortie cycle perpetuel | P0 gel + P1 STABLE_SNAPSHOT + P2 exec/archive + P3 GH Actions + P4 regen mensuelle |

Pre-commit check H.3 :

```bash
python -c "import json,sys; nb=json.load(open(sys.argv[1])); \
bad=[i for i,c in enumerate(nb['cells']) if c['cell_type']=='code' \
 and c.get('execution_count') is None and not c.get('outputs')]; \
sys.exit(1 if bad else 0)" "$nb"
```

---

## CARTOGRAPHIE & OUTILS

```
MyIA.AI.Notebooks/                      # Series pedagogiques par theme
- GenAI/{Image,Audio,Video,Texte}/      # 60+ notebooks Python (cf docs/genai-services.md)
- ML/                                    # ML.NET tutorials (.NET C#)
- Search/{Part1-Foundations, Part2-CSP, Part3-Advanced}/  # Search/CSP (Mixed)
- Sudoku/                                # Constraint solving (.NET C#)
- SymbolicAI/{Lean, Tweety, SemanticWeb, Planning, SmartContract}/
- Probas/                                # Infer.NET probabilistic (.NET C#)
- GameTheory/                            # OpenSpiel + Lean (cf 16b/16c/16d Social Choice)
  - social_choice_lean/                  # Lean 4 port Arrow/Sen/Voting
- IIT/                                   # PyPhi (Python)
- QuantConnect/                          # 27 notebooks + 50 strategies (cf docs/quantconnect.md)
- Config/settings.json                   # API settings

scripts/notebook_tools/notebook_tools.py # CLI multi-famille (validate/execute/skeleton/analyze)
scripts/smartcontracts/                  # SC-specifique
scripts/genai-stack/genai.py             # GenAI Docker + validation (cf docs/genai-services.md)

.claude/{agents, skills, rules}/         # 18 agents, 14 skills, 9 regles auto-loaded
GradeBookApp/                            # Notation etudiants (cf docs/ece-grading.md)
docker-configurations/                   # ComfyUI + Qwen Docker
docs/                                    # Documentation deportee de ce CLAUDE.md
```

**Tables detaillees** (scripts reutilisables, skills slash commands, MCP servers, GenAI services, kernels & runtime) : [docs/common-commands.md](docs/common-commands.md), [docs/claude-code-config.md](docs/claude-code-config.md), [docs/kernels-runtime.md](docs/kernels-runtime.md), [docs/genai-services.md](docs/genai-services.md).

**Regle generale outils** : ne jamais ecrire un script ad-hoc d'execution / validation : il existe presque toujours un outil dedie dans `scripts/notebook_tools/`. Si manquant, l'ajouter la (pas dans la racine `scripts/`).

---

## PROCEDURES RECURRENTES

**Workflows detailles** (Workflow PR 10 etapes, Dispatch agents template, Validation notebook bash, Audit anti-regression bash, Execution Quantbooks) : [docs/procedures-recurrentes.md](docs/procedures-recurrentes.md).

### Productivite pendant les operations longues — REGLE HARD (2026-05-11)

Quand un processus long tourne (training GPU, backtest QC, build Lean, docker pull, **prover BG iter**, papermill batch, multi-seed run) : **ne pas attendre passivement**.

**Regle stricte (HARD)** :
1. Lancer le BG, noter son ID + nature attendue
2. **Immediatement continuer** avec autre travail : autres tracks dispatchees, audits paralleles, preparation PR suivante, review code, planification iter suivante, MAJ docs
3. Check le BG uniquement a intervalles utiles (5-10 min) via `tail -50 output | grep -E "FINAL|RESULT|ERROR"` ou monitor cible. **Jamais event-par-event reactif**
4. **Minimum 2 tracks en flight** a tout moment pour chaque agent (1 BG + 1 CPU/IO local). Si un agent n'a qu'un BG, il demande immediatement une 2e track au coordinateur via `[ASK] capacity` dashboard

**Anti-patterns interdits** :
- "Monitor event arrived, je reponds 'j'attends'" — non, je travaille sur autre chose en parallele
- "Le BG va prendre 30 min, je fais une pause" — non, j'ai 30 min de travail parallele disponible
- Dispatcher 1 seule track BG a un agent + dire "reviens quand fini" — non, **2 tracks minimum** (1 BG + 1 CPU)

**Pourquoi** : un BG de 30-60 min consomme 30-60 events monitor si l'agent reste reactif, sans rien produire en parallele. Le BG tourne meme sans surveillance. Coordinateur = chef d'orchestre, pas spectateur.

Incident 2026-05-11 ai-01 (Lean prover iter 6 BG) : ~35 events monitor consommes a regarder BUILD-FAIL repetes, zero autre track avancee pendant ce temps. User signal explicite "fais en sorte que les autres agents trainers ou prouveurs fassent pareil".

---

## REGLES AGENTS (Roo Code distants)

### Code avant documentation

Priorite : code fonctionnel > tests/validation > documentation. Pas de markdown (README, MAPPING, RAPPORT) sans code fonctionnel associe. Les rapports d'audit / inventaires / status vont sur le **dashboard RooSync**, pas dans le repo. Pas de fichiers de planification (`EXTEND_*.md`, `PROCEDURE_*.md`) dans le repo.

### Slides : images en overlay uniquement

Layout `image-overlay` avec texte par-dessus, jamais en colonne droite (regle issue #221, confirmee 5+ fois). Verification visuelle obligatoire : Slidev sur **CHAQUE** slide modifie (pas un echantillon), `?clicks=99`, absence d'overflow.

### Pas de duplication

Avant de creer un fichier (README, docs, lib), verifier qu'il n'existe pas (`grep`, `find`). Si fichier similaire existe : le mettre a jour plutot qu'en creer un nouveau.

### Enrichissement notebooks

Cellules de transition : contenu pedagogique specifique (pas de "Suite du traitement" generique). Cellules d'interpretation : APRES la cellule de code interpretee. Pas d'enrichissement parallele du meme notebook dans deux sessions.

---

## QUANTCONNECT (resume)

- **Backtest obligatoire** apres modification (`create_compile` -> `create_backtest` -> `read_backtest`). Reporter Sharpe/CAGR/MaxDD dans commit + RooSync.
- **API uniquement via MCP Docker** `quantconnect/mcp-server` (config `.mcp.json`, jamais committer le token). Pas de scripts REST directs.
- **Rate limiting** : MAX 10 appels/min entre TOUS les agents. Annoncer sur dashboard avant un backtest.
- **Quantbooks** = exigence d'execution **via QC Cloud** (MCP / Playwright en fallback), pas d'execution locale fictive.
- **Livre reference** : *Hands-On AI Trading* (Jared Broad), https://www.hands-on-ai-trading.com/

Cf [docs/quantconnect.md](docs/quantconnect.md) pour structure complete.

---

## PROJECT OVERVIEW

CoursIA = plateforme educative AI : Jupyter notebooks (C# .NET Interactive + Python), Docker infrastructure GenAI (ComfyUI + Qwen), GradeBookApp evaluation etudiants. Repository : https://github.com/jsboige/CoursIA. Documentation primaire en francais ; commentaires code en francais ou anglais.

Stack : OpenAI/Anthropic APIs, Qwen 2.5-VL, Semantic Kernel, Python 3.10+ + .NET 9.0 Interactive, Papermill + MCP Jupyter, ComfyUI GPU (RTX 3090).
