# CLAUDE.md

Guidance pour Claude Code travaillant avec le repository CoursIA.

**Documentation deportee — `docs/` :**
- [docs/common-commands.md](docs/common-commands.md) - Setup environnement, validation notebooks, slash commands
- [docs/genai-services.md](docs/genai-services.md) - Architectures Qwen/Lumina, scripts genai-stack, mappings notebooks
- [docs/claude-code-config.md](docs/claude-code-config.md) - Agents, skills, rules, model selection
- [docs/quantconnect.md](docs/quantconnect.md) - Backtests, MCP Docker, structure, livre reference
- [docs/ece-grading.md](docs/ece-grading.md) - ECE student repos, autres ecoles
- [docs/architecture_mcp_roo.md](docs/architecture_mcp_roo.md) - Architecture MCP roo-state-manager (34 outils, RooSync)

**Regles modulaires `.claude/rules/` (auto-loaded a chaque session)** — chaque section critique ci-dessous renvoie a la regle complete :
- [.claude/rules/git-workflow.md](.claude/rules/git-workflow.md) - Branches, commits, force push (section A)
- [.claude/rules/anti-regression.md](.claude/rules/anti-regression.md) - Patterns red-flag, audit historique (section D)
- [.claude/rules/notebook-conventions.md](.claude/rules/notebook-conventions.md) - Manipulation, structure pedagogique, execution kernel (section C)
- [.claude/rules/code-style.md](.claude/rules/code-style.md) - PEP 8, .NET 9.0, no emojis, langue (section E)
- [.claude/rules/genai-config.md](.claude/rules/genai-config.md) - GenAI Docker config, GPU, .env
- [.claude/rules/wsl-kernels.md](.claude/rules/wsl-kernels.md) - WSL pour kernels notebook (NoteBookApp Linux)

---

## REGLES CRITIQUES (4 sections)

### A. Coordination & Git

**Coordination cross-machine = RooSync uniquement.** Dashboard workspace CoursIA + messages directs. GitHub = code, jamais de fichiers `*_TEST_REPORT.md` / `*_COORDINATION.md` / rapports d'audit dans le repo.

**Tour de coordination type** :
1. Lire le contenu **complet** du dashboard (`Read` sur le fichier persiste si la sortie est tronquee)
2. Verifier inbox RooSync pour les non-lus
3. Verifier le heartbeat cluster (machines actives)
4. Sans mission assignee : envoyer un message a ai-01, ne pas attendre passivement

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

**Honnetete des rapports** : pas de "DONE"/"fixed"/"validated" sans validation post-fix relancee. Si fix corrige 5/7 cellules : rapporter "5/7, 2 restantes identifiees", pas "DONE". Pas de markdown "RAPPORT"/"AUDIT" comme preuve sans code valide. Incidents 2026-04-08 (slides EPITA) et 2026-04-20 (Sudoku-8 + 27 cellules cassees rapportees DONE).

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

---

## CARTOGRAPHIE & OUTILS

### Structure du depot

```
MyIA.AI.Notebooks/                      # Series pedagogiques par theme
- GenAI/{Image,Audio,Video,Texte}/      # 60+ notebooks Python (cf docs/genai-services.md)
- ML/                                    # ML.NET tutorials (.NET C# notebooks)
- Search/{Part1-Foundations, Part2-CSP, Part3-Advanced}/   # Search/CSP (Mixed)
- Sudoku/                                # Constraint solving (.NET C#)
- SymbolicAI/{Lean, Tweety, SemanticWeb, Planning, SmartContract}/  # Symbolic AI
- Probas/                                # Infer.NET probabilistic (.NET C#)
- GameTheory/                            # OpenSpiel + Lean (Mixed, voir 16b/16c/16d Social Choice)
  - social_choice_lean/                  # Lean 4 port Arrow/Sen/Voting
- IIT/                                   # PyPhi (Python)
- QuantConnect/                          # 27 notebooks Python + 50 strategies (cf docs/quantconnect.md)
- Config/settings.json                   # API settings

scripts/
- notebook_tools/notebook_tools.py       # CLI : validate/execute/skeleton/analyze (multi-famille)
- smartcontracts/validate_sc_notebooks.py # SC-specifique
- genai-stack/genai.py                   # GenAI Docker + validation (cf docs/genai-services.md)
- notebook_helpers.py                    # NotebookHelper, CellIterator (lib reutilisable)
- extract_notebook_skeleton.py           # Generation README

.claude/
- agents/    # 18 sub-agents specialises (cf docs/claude-code-config.md)
- skills/    # 14 skills user-invocables + reference
- rules/     # 6 regles auto-loaded

GradeBookApp/                            # Notation etudiants (cf docs/ece-grading.md)
docker-configurations/                   # ComfyUI + Qwen Docker
notebook-infrastructure/                 # Papermill + MCP maintenance
docs/                                    # Documentation deportee de ce CLAUDE.md
```

### Scripts reutilisables (toujours preferer aux scripts ad-hoc)

| Script | Usage | Notes |
|--------|-------|-------|
| `scripts/notebook_tools/notebook_tools.py validate [target]` | Validation structure notebook | Auto-detection kernel via metadata |
| `scripts/notebook_tools/notebook_tools.py execute [target]` | Execution Papermill | Ajouter `--cell-by-cell` pour .NET/Lean |
| `scripts/notebook_tools/notebook_tools.py analyze [path]` | Analyse structure | Stats cellules, outputs, NIE |
| `scripts/notebook_tools/notebook_tools.py skeleton [path]` | Generation skeleton | Pour bootstrap nouveau notebook |
| `scripts/smartcontracts/validate_sc_notebooks.py` | SmartContracts validation | `--quick` (struct only) ou `--execute --anvil` |
| `scripts/genai-stack/genai.py docker status` | Etat services GenAI | Voir docs/genai-services.md pour la liste complete |
| `scripts/genai-stack/genai.py validate --full` | Validation stack ComfyUI | |
| `scripts/notebook_helpers.py` | Lib NotebookHelper, CellIterator | Importer dans scripts custom |

**Ne jamais** ecrire un script ad-hoc d'execution / validation : il existe presque toujours un outil dedie. Si manquant, l'ajouter dans `scripts/notebook_tools/` (pas dans la racine `scripts/`).

### Skills (slash commands)

Les skills user-invocables sont disponibles via slash commands en session Claude Code :

| Skill | Usage |
|-------|-------|
| `/verify-notebooks [target] [--quick] [--fix]` | Verify and test notebooks |
| `/enrich-notebooks [target] [--execute] [--strict]` | Add pedagogical content |
| `/cleanup-notebooks [target] [--dry-run]` | Clean markdown structure |
| `/build-notebook <action> <path> [--quality=90]` | Create/improve/fix notebooks |
| `/execute-notebook <path> [--batch] [--save]` | Execute via MCP |
| `/validate-genai [target] [--local]` | Validate GenAI stack |
| `/coordinate` | Multi-agent coordination hub (lecture dashboards + dispatches) |
| `/review-student-prs` | Workflow review PRs etudiantes |
| `/qc-iterative-improve` | Workflow QC research notebooks |
| `/analyze-slides` | Analyse Slidev/PPTX |

Cf [docs/claude-code-config.md](docs/claude-code-config.md) pour la liste complete des agents et leur model selection (haiku/sonnet/inherit).

### MCP servers

Trois MCP majeurs configures dans `.mcp.json` (root) ou `~/.claude.json` (global) :

- **roo-state-manager** (34 outils) : dashboards RooSync, conversation_browser, codebase_search, Qdrant indexing
- **qc-mcp** (Docker `quantconnect/mcp-server`) : creation projets/backtests QC Cloud, lecture resultats. Rate limit MAX 10 appels/min entre TOUS les agents
- **playwright** (22 outils) : automatisation web (utile pour Quantbooks online quand qc-mcp insuffisant)

### GenAI services (notebooks `MyIA.AI.Notebooks/GenAI/`)

| Service | Modele | VRAM | URL prod |
|---------|--------|------|----------|
| Qwen Image Edit | qwen_image_edit_2509 | ~29GB | qwen-image-edit.myia.io |
| Z-Image / Lumina | Lumina-Next-SFT | ~10GB | z-image.myia.io |
| Whisper STT | large-v3 (FunASR upgrade en cours) | ~5GB | whisper-api.myia.io |
| Kokoro TTS, MusicGen, Demucs | (audio stack) | varie | port-forwarded |
| ComfyUI Video | ComfyUI core | varie | comfyui-video |

API keys dans `MyIA.AI.Notebooks/GenAI/.env` (template `.env.example`). Validation : `/validate-genai [target] [--local]` ou `python scripts/genai-stack/genai.py validate --full`.

Detail config (services hostes po-2023 GPUs, .env keys, scripts) : [.claude/rules/genai-config.md](.claude/rules/genai-config.md) + [docs/genai-services.md](docs/genai-services.md).

### Kernels WSL (notebooks Lean / GameTheory / OpenSpiel)

Notebooks dans `GameTheory/` et `SymbolicAI/Lean/` requierent un kernel WSL specifique :
- `Python (GameTheory WSL + OpenSpiel)` pour GameTheory
- `Python 3 (WSL)` ou `Lean 4 (WSL)` pour SymbolicAI/Lean

Pieges connus : backslashes consommes par WSL shell, paths sans separateurs, kernel timeout 60s au cold start, heredoc variables interpolees. Wrapper bash obligatoire (Python wrapper ne marche PAS).

Detail diagnostic + workarounds : [.claude/rules/wsl-kernels.md](.claude/rules/wsl-kernels.md).

---

## PROCEDURES RECURRENTES

### Workflow PR

1. Identifier la mission (issue GitHub ou directive RooSync)
2. Brancher : `git checkout -b feature/<sujet>` (ou `fix/<sujet>`) depuis `main` a jour
3. Implementer
4. **Pour notebooks modifies** : re-executer le notebook complet, verifier outputs, verifier scope strict (pas de re-exec gratuite des autres notebooks de la famille)
5. **Pour code production** : ajouter/modifier tests, lancer le build (PEP8 / `dotnet build`), zero warning
6. Commit message : `type(scope): description courte` (Conventional commits)
7. Push, ouvrir la PR avec description claire (Summary + Test plan)
8. Auto-review selon les 5 points (sec. B). Si self-review echoue : revenir au point 4
9. Annoncer sur dashboard `[INFO]` ou poster en commentaire de l'issue
10. Attendre review/merge par ai-01. **Ne pas se merger soi-meme** (les agents)

### Dispatch agents (coordinateur ai-01)

Pour assigner une tache a une machine distante (po-2023/2024/2025/2026) :

1. Verifier la disponibilite : `roosync_dashboard(action: "read", type: "workspace")` + heartbeat machine
2. Composer un message structure :
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

### Validation notebook (avant commit)

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

### Audit anti-regression (avant merge PR suspecte)

Pour une PR avec deletions > insertions sur code metier (Lean/Coq/Python core / tests) :

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

Cf [.claude/rules/anti-regression.md](.claude/rules/anti-regression.md) pour les patterns red-flag complets.

### Execution Quantbooks (regle user 29/04)

Pour un notebook research utilisant `QuantBook()` (kernel QC Cloud uniquement) :

1. **MCP qc-mcp d'abord** : verifier si un outil execute le research notebook
2. **Fallback Playwright** : automatiser la session QC Cloud Web (login, navigation projet, Run All, telechargement notebook execute)
3. **Pas de fallback markdown explicatif** : un Quantbook commit doit avoir des outputs reels QC Cloud

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

CoursIA = plateforme educative AI :
- **Jupyter notebooks** (C# .NET Interactive + Python) pour apprentissage AI
- **Docker** infrastructure pour services GenAI (ComfyUI + Qwen)
- **GradeBookApp** evaluation etudiants

Repository : https://github.com/jsboige/CoursIA

### Key technologies

- **AI/ML** : OpenAI API, Anthropic Claude, Qwen 2.5-VL, Hugging Face, Semantic Kernel
- **Notebooks** : Python 3.10+, .NET 9.0 Interactive, Papermill, MCP Jupyter
- **Docker** : ComfyUI GPU services (RTX 3090, 24GB VRAM)
- **GenAI Models** : DALL-E 3, GPT-5, Qwen Image Edit, Lumina/Z-Image

### Language

Documentation primaire : francais. Commentaires code : francais ou anglais.
