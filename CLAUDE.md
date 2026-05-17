# CLAUDE.md

Guidance pour Claude Code travaillant avec le repository CoursIA.

**Documentation deportee — `docs/` :**
- [docs/common-commands.md](docs/common-commands.md) - Setup environnement, validation notebooks, slash commands
- [docs/genai-services.md](docs/genai-services.md) - Architectures Qwen/Lumina, scripts genai-stack, mappings notebooks
- [docs/claude-code-config.md](docs/claude-code-config.md) - Agents, skills, rules, model selection
- [docs/quantconnect.md](docs/quantconnect.md) - Backtests, MCP Docker, structure, livre reference
- [docs/ece-grading.md](docs/ece-grading.md) - ECE student repos, autres ecoles
- [docs/architecture_mcp_roo.md](docs/architecture_mcp_roo.md) - Architecture MCP roo-state-manager (34 outils, RooSync)
- [docs/kernels-runtime.md](docs/kernels-runtime.md) - .NET / Python / WSL kernels, conda envs, dotnet-interactive PIN
- [docs/procedures-recurrentes.md](docs/procedures-recurrentes.md) - Workflow PR, dispatch agents, validation notebook, audit anti-regression

**Regles modulaires `.claude/rules/` (auto-loaded a chaque session)** — chaque section critique ci-dessous renvoie a la regle complete :
- [.claude/rules/git-workflow.md](.claude/rules/git-workflow.md) - Branches, commits, force push (section A)
- [.claude/rules/pr-review-discipline.md](.claude/rules/pr-review-discipline.md) - Critères CHANGES_REQUESTED obligatoires reviewers humains+bots (section B+G)
- [.claude/rules/anti-regression.md](.claude/rules/anti-regression.md) - Patterns red-flag, audit historique (section D)
- [.claude/rules/notebook-conventions.md](.claude/rules/notebook-conventions.md) - Manipulation, structure pedagogique, execution kernel (section C)
- [.claude/rules/code-style.md](.claude/rules/code-style.md) - PEP 8, .NET 9.0, no emojis, langue (section E)
- [.claude/rules/genai-config.md](.claude/rules/genai-config.md) - GenAI Docker config, GPU, .env
- [.claude/rules/wsl-kernels.md](.claude/rules/wsl-kernels.md) - WSL pour kernels notebook (NoteBookApp Linux)

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

**Regle user 2026-05-06 (incident scipy DLL/sklearn force-reinstall) :** un environnement Python degrade ne se contourne **jamais** par delegation, fallback ou skip. On repare **coute que coute**, en demandant un UAC user au besoin pour les operations privilegiees.

**Symptomes red-flag** : `ModuleNotFoundError` apres install qui se dit "Successfully installed", `ImportError: DLL load failed`, `Access is denied` sur force-reinstall, distributions corrompues prefixees `~` (ex: `~cipy/`, `~umpy/`), conflits Python 3.12 vs 3.14 vs 3.13 dans `which pip` vs `python --version`.

**Workflow de reparation obligatoire** :
1. Identifier l'env vise (Python systeme vs **env Conda dedie** — voir ci-dessous, **utiliser le bon env d'abord** plutot que reparer le mauvais)
2. Lister les processes Python actifs (`Get-Process python*`) qui pourraient locker des DLLs, killer si necessaire
3. Cleanup distributions corrompues (`~xxx/` dirs dans site-packages) via `Remove-Item -Recurse -Force`
4. Force-reinstall avec `python -m pip install --force-reinstall <pkg>` (assure le bon Python)
5. Si Access denied persiste → demander UAC user (executer `Start-Process powershell -Verb RunAs ...`) ou desactivation antivirus temporaire
6. Tester import end-to-end avant de relancer le job

**Anti-patterns interdits** :
- Skip de l'env local et delegation a un agent quand le user a explicitement demande l'execution locale
- Workarounds genre "je passe a un autre env" ou "j'ignore le warning"
- Reinstall en boucle sans cleanup des residus `~xxx/`
- Continuer a importer un module en silencant les exceptions (`except Exception: pass`)

**Envs Conda dedies sur ai-01** (a utiliser AVANT de toucher Python systeme) :

| Env | Usage | Path |
|-----|-------|------|
| `coursia-ml-training` | **ML training (PyTorch CUDA, sklearn, scipy, hmmlearn)** | `C:\Users\MYIA\miniconda3\envs\coursia-ml-training` |
| `mcp-jupyter` | MCP Jupyter server | `C:\Users\MYIA\miniconda3\envs\mcp-jupyter` |
| `epita_symbolic_ai` | EPITA SymbolicAI series | `C:\Users\MYIA\.conda\envs\epita_symbolic_ai` |

Pour `train_moe.py`, `train_lstm.py`, `train_mamba.py` etc. : **toujours** activer `coursia-ml-training` (`& "C:\Users\MYIA\miniconda3\envs\coursia-ml-training\python.exe"` ou `conda activate coursia-ml-training`). Liste complete via `conda env list`.

### G. Vigilance permanente — anti-complaisance

S'applique a **tous les agents** (executants, coordinateur, reviewers humains et bots). Ces regles sont permanentes : elles ne se relachent ni avec la pression deadline, ni avec la confiance accumulee, ni avec un APPROVED bot.

**G.1 — Verifier les claims contre le code, pas contre les rapports**

Avant de croire qu'un feature manque, qu'une API n'existe pas, qu'un fichier est introuvable, qu'un agent X "n'est pas connecte" : `grep` / `Glob` / `Read` le codebase. Affirmer une absence sans verification = source #1 de faux diagnostics qui se propagent en cascade.

Avant de relayer un diagnostic technique d'un autre agent dans un dispatch ou un bilan : exiger la preuve (ligne de code citee, log d'erreur copie, output compilateur). Pas de propagation par confiance. Si le diagnostic se revele faux apres relais, le coordinateur partage la responsabilite.

**G.2 — Metriques honnetes, pas binaires**

`sorry count = 0` n'a aucune valeur sans `lake build SUCCESS` post-modification. Un theoreme supprime, un identifiant inexistant injecte, une preuve qui ne compile pas = sorry count peut etre 0 ET le port casse. Pour Lean / Coq / Agda, **trois preuves obligatoires** dans le body PR : `grep -c sorry` avant/apres + `lake build` SUCCESS log + Proof integrity check SUCCESS.

Pour ML/trading : `BEATS majority` n'a aucune valeur sur 1 seed × 1 fold. Multi-seed ≥4 + walk-forward 5-fold + edge ≥ 2σ cross-seed + transaction costs documentes ou le verdict est **invalide** (pas "promising", pas "encouraging" — invalide).

Pour notebooks : `Papermill SUCCESS` en mot-cle ne prouve rien. Coller les premieres lignes des outputs reels.

Pour services ops : `200 OK` sur /health ne prouve pas que le service fait son travail. Test E2E reproductible obligatoire (curl + verification du payload retourne).

**G.3 — Pas de "DONE" sur progres marginal**

Si N tracks dispatchees → M < N livrees : rapporter `M/N livrees, (N-M) restantes : <liste>`. Pas de `Cycle X complete` quand Track 1 (le HIGH) n'est pas fait et 7 LOW le sont.

Si sorry count passe de N a N-1 : rapporter `1/N elimine, (N-1) restants`. Pas de "DONE Voting".

Si fix corrige 5/7 cellules : rapporter `5/7, 2 restantes : <liste>`. Pas de "DONE notebook".

Pourcentage explicite ou liste residuelle obligatoires.

**G.4 — Composites trop larges = split obligatoire**

Une PR qui depasse l'un de ces seuils doit etre fractionnee en PRs coherentes par feature avant merge :
- `additions + deletions` > 3000 lignes hors notebooks
- `changedFiles` > 15 (hors `_output.ipynb` et donnees)
- > 4 features distinctes mentionnees dans le `## Summary`
- > 1 domaine (ML + Lean + GenAI melanges)

Le coordinateur **conteste** (commentaire CHANGES_REQUESTED) au lieu de merger. Le reviewer bot DOIT poster CHANGES_REQUESTED.

**G.5 — Shopping cart interdit**

Un dispatch >5 tracks par agent encourage le shopping (LOW d'abord, HIGH reportes). Cibler **2 deep tracks max par agent** par cycle, avec **criteres de sortie verifiables** (compile log, multi-seed verdict, build SUCCESS, healthcheck E2E). Pas de Track LOW pour combler.

Si un agent finit ses 2 tracks avant la coord finale : il attend, il n'invente pas une 3e mission. Laisser les LOW au cycle suivant.

**G.6 — Coordinateur : audit avant merge cascade**

Avant un batch de merges : lire les bodies, verifier au moins **un claim** de chaque PR contre le diff reel. Pas de "5 PRs APPROVED par bot, je merge en 5 minutes".

Si une PR a 0 review humain ET le bot APPROVE : c'est le **minimum** acceptable, mais le coordinateur reste responsable du contenu. Si le claim est faux, c'est le merge qui est en cause, pas le bot.

Lire le diff > lire le titre. Lire le body > lire le mergeStateStatus. Verifier le claim > faire confiance au rapport.

**G.7 — Stagnation cross-cycle = escalade**

Si un blocage technique persiste sur N cycles consecutifs (ex: rebase qui ne se fait pas, sorry qui ne baisse pas, service qui reste DOWN) : le coordinateur **n'attend pas un cycle de plus**. Il prend l'action lui-meme (rebase, fix, escalade user) ou ferme la PR/issue.

Si un agent rapporte "BLOCKED" sans preuve concrete (compile log, error message, screenshot) : ne pas accepter. Demander la preuve avant de re-dispatcher.

**G.8 — Bots reviewers : pas de rubber-stamp**

Pattern interdit : APPROVE >3 PRs en <10 minutes. Probable rubber-stamp. Le coordinateur conteste systematiquement et bloque les PRs jusqu'a re-review serieuse.

Pattern interdit : APPROVED sur composite >3000 lignes / 15 fichiers. Le bot DOIT detecter et poster CHANGES_REQUESTED.

Pattern interdit : APPROVED sur micro PR docs <20 lignes isolee. Le bot DOIT detecter et exiger groupement.

Cf [.claude/rules/pr-review-discipline.md](.claude/rules/pr-review-discipline.md) pour la grille complete.

**G.9 — Culture du doute**

Avant d'envoyer un rapport ou de merger : se demander explicitement "est-ce que je pourrais avoir tort ?". Si oui, verifier. Une affirmation surprenante (ex: "le multi-agent prover existe deja") merite verification avant relais.

Avant d'accepter une "breakthrough" rapportee par un agent (sorry 5→0, BEATS magique, service restaure en 5min) : reproduire au moins 1 element du resultat. Les vrais succes resistent a la verification ; les faux positifs s'effondrent.

### H. Validation REELLE — pas de complaisance, jamais

S'applique a TOUS les agents (executants, coordinateur, reviewers humains, bots). Aucune derogation. Cette section formalise l'incident 2026-05-09 : 5+ vagues de "fix" cosmetiques sur Sudoku-13 (5 commits structurels depuis mars 2026, exec_count=null sur 11/11 cellules code -> jamais execute depuis sa creation) ne l'ont jamais detecte, parce que toutes les "validations" ont ete superficielles (rule C.2 verifiee sur structure JSON, jamais sur l'execution reelle).

**H.1 — Validation = execution complete + outputs verifies (HARD)**

"Validate", "fix", "OK", "completed", "DONE" sur un notebook = uniquement si TOUS les criteres :
- Toutes les code cells ont `execution_count != null` ET `outputs` non vide (sauf assignation pure prouvee via log Papermill)
- ZERO cellule avec `output_type: error`
- Papermill `<nb>` ou kernel cell-by-cell (.NET / WSL) execute end-to-end SANS skip
- Body PR colle la trailer Papermill (30 dernieres lignes log) OU les outputs sont commites + visibles dans la diff

Sans ces 4 preuves : la PR n'est PAS validee. Peu importe qui la signe. La verification "structure JSON OK" (rule C.2 historique) est UN sous-ensemble de H.1, pas un substitut.

**H.2 — Tous les agents installent l'env complet (HARD)**

Chaque machine cluster (po-2023, po-2024, po-2025, po-2026, ai-01) doit pouvoir executer N'IMPORTE QUEL notebook du repo. Inventaire minimum (cf [docs/kernels-runtime.md](docs/kernels-runtime.md)) :
- Python 3.10+ + envs Conda dedies (`coursia-ml-training`, `epita_symbolic_ai`, `mcp-jupyter`)
- .NET 9.0 SDK + `dotnet-interactive` Jupyter kernels (.NET notebooks Sudoku/SymbolicAI/ML/Probas/Search/SmartContract)
- WSL kernels (GameTheory + OpenSpiel + Lean 4)
- Lean `elan` toolchain
- Docker + acces aux services GenAI (po-2023 host) ou env de bypass

Si un agent ne peut pas executer un notebook -> il INSTALLE l'env (peut demander UAC user). Pas de "skip car env manquant", pas de "delegation a un autre agent". Reparation env > contournement (extension de la regle F).

**H.3 — Aucun commit de notebook non-execute (HARD)**

Interdit de commiter un notebook ou n'importe quelle cellule code a `execution_count: null` ET `outputs: []`. Verification pre-commit obligatoire :

```bash
python -c "import json,sys; nb=json.load(open(sys.argv[1])); bad=[i for i,c in enumerate(nb['cells']) if c['cell_type']=='code' and c.get('execution_count') is None and not c.get('outputs')]; sys.exit(1 if bad else 0)" "$nb"
```

Si fail -> agent doit : (a) executer localement (env complet H.2), OU (b) executer via dispatch RooSync sur machine compatible, OU (c) deplacer le notebook dans `_pending_execution/` avec issue ouverte detaillant le blocage. Pas de 4eme option, pas de "je commit quand meme c'est juste structurel".

**H.4 — Merges coordinateur ne sont JAMAIS complaisants (HARD)**

ai-01 (ou tout coordinateur) ne merge PAS une PR notebook sans :
1. Lire le body PR + trailer Papermill colle
2. `git fetch && git checkout <branch>` puis `python scripts/notebook_tools/notebook_tools.py execute <nb>` LOCALEMENT
3. Verifier `execution_count != null` + `errors == 0` apres execution locale

Cascade merge sans audit individuel = violation H.4 = revert + post-mortem dashboard. Le contre-exemple a ne pas reproduire : cascade 8 PRs de la nuit 8->9/05 mergee en ~30min en confiant l'audit aux body-PRs sans re-execution locale.

**H.5 — Bots reviewers : audit commit-level forensique (HARD)**

Tout bot reviewer (clusterManager-Myia, jsboige self-bot, futurs) doit poster sur chaque PR notebook une analyse statique structuree :
- Diff par cellule : source modifiee oui/non, execution_count avant/apres, outputs ajoutes/retires/modifies, output_type:error present
- Detection "fix superficiel" : source code cell change ET execution_count reste null OU identique, OU outputs vides apres modification source = RED FLAG
- Detection "regression silencieuse" : outputs avec `error_type`, execution_count decremente, kernel mismatch dans metadata
- Verdict explicite : `EXEC_PROVED` / `STRUCTURAL_ONLY` / `SUSPECT_REGRESSION`

Si STRUCTURAL_ONLY ou SUSPECT_REGRESSION et le PR claim "fix" / "validate" / "OK" -> CHANGES_REQUESTED automatique. Le coordinateur ne peut PAS merger sans que le bot ait poste EXEC_PROVED. Les bots ne peuvent pas executer les notebooks (pas d'env complet) mais ils peuvent et DOIVENT prouver l'execution via parsing JSON de la diff.

**H.6 — Audit historique notebook = responsabilite bot, pas humain**

Avant ouverture d'une issue ou PR "le notebook X est casse" / "X n'a jamais marche" : obligation d'invoquer d'abord un bot reviewer avec `audit-history MyIA.AI.Notebooks/path/to/X.ipynb`. Le bot retourne :
- Liste des N derniers commits (hash, date, auteur, type modif: source/output/both)
- Date du dernier commit avec preuve d'execution (Papermill log presence OU outputs non-vides apres source change)
- Verdict : `LAST_REAL_EXEC <date> <commit>` ou `NEVER_EXECUTED_SINCE_<creation>`

Sudoku-13 aurait du sortir `NEVER_EXECUTED_SINCE_<creation>` au premier appel — ca aurait economise les 5 PRs cosmetiques accumulees depuis mars 2026.

**H.7 — Plan de sortie du cycle perpetuel (incident 2026-05-09)**

L'audit du 2026-05-09 a revele un pattern systemique : 988 notebooks repo, dont une fraction inconnue n'a jamais ete reellement executee malgre des dizaines de commits "fix" cosmetiques. Plan de remediation 4 phases :
- **P0** : gel des "vagues de fix C.x / cosmetique / enrichissement" sur tous les agents jusqu'a inventaire complet
- **P1** (48h) : forensique massif sur HEAD courant -> `STABLE_SNAPSHOT.md` (matrice 988 notebooks : `ALL_NULL` / `ALL_EXEC` / `PARTIAL` + errors_count + LAST_REAL_EXEC)
- **P2** (1 semaine) : pour chaque NEVER_EXECUTED -> soit slot agent dedie executant pour de vrai, soit archive avec mention pedagogique explicite "non executable en l'etat"
- **P3** (2 semaines) : workflow GitHub Actions `notebook-execution-required.yml` qui execute via Papermill toute notebook touchee dans une PR. Failure -> merge bloque. Runner = Docker compose (.NET + Python + Lean + WSL bypass)
- **P4** (continu) : `STABLE_SNAPSHOT.md` regenere mensuel, gravant `sha + date + matrice exec_status` -> point de reference factuel quand quelqu'un dit "X est valide"

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
