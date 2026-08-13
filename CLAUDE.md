# CLAUDE.md

Guidance pour Claude Code travaillant avec le repository CoursIA.

## Principes de collaboration (5)

Cadre de travail (adapté de Karpathy + ajout user) : ces principes gouvernent **comment** travailler ; les RÈGLES CRITIQUES ci-dessous disent **quoi** respecter.

1. **Demander, ne pas supposer.** Si quelque chose n'est pas clair, demander avant d'écrire une ligne. **En mode non-supervisé** (agent schedulé/cron, worker), prendre l'interprétation la plus raisonnable, avancer, et **consigner l'hypothèse** plutôt que de bloquer.
2. **Solution la plus simple pour un problème simple, meilleure solution pour un problème difficile.** Ne pas sur-concevoir ni ajouter de la flexibilité dont on n'a pas encore besoin.
3. **Ne pas toucher au code non lié** — mais **signaler** le mauvais code découvert, pour le traiter en sujet séparé (issue/PR dédiée).
4. **Expliciter l'incertitude.** En cas de doute, voir le point 1. Quand c'est pertinent, mener une **expérience locale, petite et à faible risque**, puis apporter hypothèse + résultats. La confiance sans certitude fait plus de dégâts qu'admettre une lacune.
5. **Toujours ouvert aux meilleures idées.** Proposer une meilleure approche, ou une à impact durable plutôt qu'un correctif tactique. Claude est un **partenaire de raisonnement, pas un preneur de notes**.

---

## Documentation déportée — `docs/`

| Fichier | Contenu |
|---|---|
| [reference/common-commands.md](docs/reference/common-commands.md) | Setup env, validation notebooks, slash commands |
| [genai/genai-services.md](docs/genai/genai-services.md) | Architectures Qwen/Lumina, scripts genai-stack, mappings |
| [reference/claude-code-config.md](docs/reference/claude-code-config.md) | Agents, skills, rules, model selection |
| [qc/quantconnect.md](docs/qc/quantconnect.md) | Backtests, MCP Docker, structure, livre référence |
| [reference/teaching-context.md](docs/reference/teaching-context.md) | Calendrier écoles, scope EPITA-IS, agents par école |
| [reference/cluster-agents.md](docs/reference/cluster-agents.md) | Machines, GPU topology, agents par spécialisation, dispatch |
| [reference/kernels-runtime.md](docs/reference/kernels-runtime.md) | .NET / Python / WSL kernels, conda envs, dotnet-interactive PIN |
| [reference/procedures-recurrentes.md](docs/reference/procedures-recurrentes.md) | Workflow PR, dispatch, validation notebook, audit anti-régression, pre-commit H.3 |
| [reference/subagents-reference.md](docs/reference/subagents-reference.md) | 21 sous-agents + 17 skills, mapping side-tracks, usage async |
| [reference/scripts-reference.md](docs/reference/scripts-reference.md) | Catalogue scripts (notebook CLI, exécution, qualité, maintenance) |
| [reference/architecture_mcp_roo.md](docs/reference/architecture_mcp_roo.md) | Cycle de vie, logs et diagnostic des serveurs MCP (inventaire des 15 outils roo-state-manager : [HARNESS-OVERVIEW.md](https://github.com/jsboige/roo-extensions/blob/main/docs/harness/HARNESS-OVERVIEW.md) §2) |
| [reference/regles-vigilance-detail.md](docs/reference/regles-vigilance-detail.md) · [regles-validation-detail.md](docs/reference/regles-validation-detail.md) | Détail G.1-G.9 et H.1-H.7 + incidents |
| [reference/env-python-reparation.md](docs/reference/env-python-reparation.md) | Réparation env Python (règle F) |
| [reference/stale-tree-drift-scan.md](docs/reference/stale-tree-drift-scan.md) · [orphan-branch-scan-l576.md](docs/reference/orphan-branch-scan-l576.md) | Scans anti-phantom (drift, branche orpheline) |
| [lean/](docs/lean/) | Prover iteration history, intractable diagnosis, LLM endpoints, pièges tactiques (propagation d'instance `Decidable`) |

Notation étudiants : moteur générique = [GradeBookApp/configs/README.md](GradeBookApp/configs/README.md) ; **pipelines + données par cohorte = privés sur GDrive** `G:\Mon Drive\MyIA\Formation\<ecole>\<annee>\grading\` (PII, hors repo public).

## Règles modulaires `.claude/rules/` (auto-loaded chaque session)

`git-workflow` (branches, commits, force push) · `pr-review-discipline` (critères CHANGES_REQUESTED) · `anti-regression` (patterns red-flag) · `notebook-conventions` (structure, exécution kernel) · `exercise-example-labeling` (content-based, stop flip-flop) · `code-style` (PEP 8, .NET 9, no emojis) · `genai-config` · `wsl-kernels` · `student-pr-reviews` (anti-fuite soutenance) · `lean-merge-discipline` · `secrets-hygiene` · `secrets-roosync-policy` · `audit-reassessment` · `audit-cross-source-distillation` · `verify-before-claiming` · `coordinator-discipline` · `proactive-coordination` · `user-blocker-signaling` · `harness-hygiene` · `catalog-pr-hygiene` · `model-delegation` · `three-exercises-per-notebook` · `sota-not-workaround` · `readme-french-first` · `variation-protocol` · `lane-claim-protocol` (claim = commentaire d'issue, anti-collision cross-lane) · `cell-interpretation-ordering` (ancrage sémantique des cellules interp, anti-angle-mort #10678).

---

## RÈGLES CRITIQUES (8 sections)

### A. Coordination & Git

**Coordination cross-machine = RooSync uniquement.** Dashboard workspace CoursIA + messages directs. GitHub = code, **jamais** de `*_TEST_REPORT.md` / `*_COORDINATION.md` / rapports d'audit dans le repo.

**Tour de coordination type** : (1) lire le dashboard **complet** (`Read` sur le fichier persisté si tronqué), (2) inbox RooSync non-lus, (3) heartbeat cluster, (4) sans mission assignée : envoyer un message à ai-01, ne pas attendre passivement.

**Reporting dashboard** : poster au minimum début/livraison/fin de session. > 30 min sans post = signe d'isolement. Posts `[INFO]` courts > silence.

**Git** : pas de push direct sur `main`. **Force push** : interdit sur `main` (porté par `allow_force_pushes: false`), autorisé sur une branche de PR qu'une **seule** lane manipule (`--force-with-lease`, l'alternative merge d'abord) — décision user 2026-08-08. Pas de `reset --hard` sur `main` ni sur une branche partagée. Branches `feature/<sujet>` ou `fix/<sujet>`, un sujet par PR. Le coordinateur (ai-01) review et merge ; les agents ne mergent pas eux-mêmes. Cf [git-workflow.md](.claude/rules/git-workflow.md).

### B. Reviews PR (5 points obligatoires)

Avant tout merge (y compris ses propres PRs) :

| # | Point | Comment |
|---|---|---|
| 1 | **Scope réel** | La PR fait ce qu'elle annonce, rien de plus, rien de moins |
| 2 | **Validation automatisée post-fix** | Script qui check **le livrable** (pas le code source), relancé APRÈS le dernier commit |
| 3 | **Cohérence pédagogique** | Exercices alignés au contenu, pas de redondance, stubs `TODO` cohérents, ordre logique |
| 4 | **Exécution réelle** | Papermill ou Jupyter pour notebooks (CI = syntaxe seule). Slidev `?clicks=99` pour slides |
| 5 | **Regression check** | Grep des symboles touchés dans le reste du dépôt |

**Si un seul point n'est pas vérifié : ne pas merger.**

**Preuves vérifiables, pas mots-clés** : « Papermill SUCCESS » / « tests passed » / « sorry count -1 » / « BEATS » / « FALSE POSITIVE » sans log/lien CI / `lake build SUCCESS` post-modif / multi-seed ≥4 + edge ≥2σ / 3 cellules-types vérifiées = **invalide**.

**Honnêteté des rapports** : pas de « DONE »/« fixed »/« validated » sans validation post-fix relancée. Rapporter « 5/7, 2 restantes », pas « DONE ». Pas de markdown « RAPPORT »/« AUDIT » comme preuve sans code valide.

**Reviewers (humains ET bots)** : critères CHANGES_REQUESTED par domaine → [pr-review-discipline.md](.claude/rules/pr-review-discipline.md) §A-H. **APPROVED malgré violation = complicité.**

### C. Notebooks (3 règles user 2026-04-26)

**C.1 — Pas d'erreur volontaire.** `raise NotImplementedError`, `assert False`, `1/0` et toute erreur intentionnelle sont **INTERDITS partout** (top-level, méthode, fonction utilitaire). Stubs corrects : `pass`, `print("Exercice a completer")`, `return None`, `result = None  # TODO etudiant`. Conserver `# TODO`, `# Indice`, `# Etape N`. Le notebook doit s'exécuter de bout en bout même exercices non complétés. Détail : [notebook-conventions.md](.claude/rules/notebook-conventions.md).

**C.2 — Notebooks committés AVEC outputs.** `execution_count: <int>` + `outputs: [...]` cohérents pour chaque cellule code exécutable. Modification d'une cellule code = re-exécution complète avant commit. Notebook non-exécutable en local (kernel manquant, GPU requis) : documenter, exécuter ailleurs, committer avec outputs réels. Exception : modifs uniquement markdown. Quantbooks = exigence d'exécution **via QC Cloud** (MCP qc-mcp / Playwright en fallback), pas de « markdown explicatif » comme contournement.

**C.3 — Scope strict des re-exécutions Papermill.** Un agent ne commit QUE les notebooks dont il a modifié une cellule source (`git diff "$nb" | grep -cE '^\+\s*"source"' > 0`). Audit/inventaire : Papermill dans `/tmp/audit_<famille>_$(date +%s)/`, rapport sur dashboard, pas dans le repo. Incidents 2026-04-25 : 2 collisions de PR par re-exécutions parallèles (#540 vs #541, #541 vs #542).

### D. Anti-régression (code de production)

S'applique aux **preuves Lean/Coq, fonctions métier appelées, tests, librairies**. **Pas** aux cellules d'exercice étudiant (qui doivent justement être stubbées, cf C.1).

**INTERDIT** : remplacer une preuve formelle ou une implémentation existante par `sorry` / stub vide / `return None` / `pass`, sans diagnostic explicite et tactiques d'adaptation tentées. Commits « fix compilation » / « Mathlib fix » / « lint fix » / « simplify » avec **deletions > insertions** sur code métier = **red flag** par défaut.

Protocole avant suppression (4 étapes : erreur exacte / 3 tactiques / PR `debt` + sign-off / diff cohérent) : [anti-regression.md](.claude/rules/anti-regression.md).

### E. Code style (résumé)

| Aspect | Règle |
|---|---|
| Emojis | Interdits dans code, variables, fichiers générés, messages de commit |
| Python | PEP 8, type hints, Python 3.10+, `venv` + `requirements.txt` |
| C# / .NET | .NET 9.0, .NET Interactive pour notebooks, `Microsoft.SemanticKernel` |
| Notebooks | Documentation primaire en français, code en français ou anglais |
| Naming | Pas de préfixes « Pure »/« Enhanced »/« Advanced »/« Ultimate » |

Détail (+ convention i18n Lean FR/EN siblings) : [code-style.md](.claude/rules/code-style.md).

### F. Environnement — RÉPARER, ne JAMAIS contourner (HARD)

**Règle user 2026-05-06 (Python) + 2026-05-26 (kernels)** : un env dégradé ou un kernel manquant ne se contourne **jamais** par délégation, fallback ou skip. On **installe** le kernel/env manquant sur la machine locale, on demande UAC user au besoin.

**Kernels installables partout** : .NET Interactive (`dotnet tool install --global Microsoft.dotnet-interactive`), Python 3 (conda env dédié), Lean 4 (`elan toolchain install stable`). Vérification : `jupyter kernelspec list`. Versions/paths + envs Conda : [kernels-runtime.md](docs/reference/kernels-runtime.md).

**Anti-patterns INTERDITS** : « kernel not available locally » dans un body PR = **manquement grave à H.2** · déléguer la re-exécution à ai-01 au lieu d'installer = **contournement** · committer un notebook sans re-exécuter les cellules modifiées = violation C.2 · « je n'ai pas le temps d'installer » · skip env local + délégation · `except Exception: pass` sur imports.

**Exception** : GPU-only notebooks (CUDA requis sur machine CPU-only) — documenter et demander re-exécution sur machine GPU. Mais .NET Interactive, Python, Lean = installables **partout**.

### G. Vigilance permanente — anti-complaisance

Détail G.1-G.9 + incidents : [regles-vigilance-detail.md](docs/reference/regles-vigilance-detail.md).

| # | Règle | Résumé |
|---|---|---|
| G.1 | Vérifier claims ET verdicts contre la source | `grep`/`Read` avant d'affirmer une absence. **Un verdict d'un autre agent se relit contre le scope réel AVANT d'agir : le label n'est pas la preuve** |
| G.2 | Métriques honnêtes pas binaires | sorry=0 sans lake build SUCCESS = invalide. BEATS sans multi-seed = invalide |
| G.3 | Pas de « DONE » sur progrès marginal | Pourcentage explicite + liste résiduelle obligatoires |
| G.4 | Composites trop larges = split | > 3000 lignes / 15 fichiers / 4 features / 1 domaine = CHANGES_REQUESTED |
| G.5 | Shopping cart interdit | 2 deep tracks max par agent + critères de sortie vérifiables |
| G.6 | Audit avant merge cascade | Lire le diff + vérifier 1 claim par PR avant merge |
| G.7 | Stagnation cross-cycle = escalade | Pas d'acceptation « BLOCKED » sans preuve concrète |
| G.8 | Bots reviewers pas de rubber-stamp | APPROVE > 3 PRs en < 10 min = contester. APPROVED sur composite = CHANGES_REQUESTED |
| G.9 | Culture du doute | « Puis-je avoir tort ? » avant rapport/merge/**close d'issue**. Fermer une issue = lire le body complet + confronter le verdict invoqué, jamais sur le label seul |

### H. Validation RÉELLE — pas de complaisance, jamais

Détail H.1-H.7 + plan P0-P4 + script pre-commit : [regles-validation-detail.md](docs/reference/regles-validation-detail.md).

| # | Règle | Résumé |
|---|---|---|
| H.1 | Validation = exec complète + outputs vérifiés | 4 preuves : exec_count != null, 0 error, Papermill end-to-end, trailer body PR |
| H.2 | Tous les agents installent l'env complet | Python+Conda+.NET 9+WSL+Lean+Docker. Réparation > contournement |
| H.3 | Aucun commit de notebook non-exécuté | Pre-commit `execution_count is None and not outputs` = fail bloquant |
| H.4 | Merges coord JAMAIS complaisants | git checkout + Papermill local OU body PR avec log + scope OK |
| H.5 | Bots reviewers audit forensique | Verdict EXEC_PROVED / STRUCTURAL_ONLY / SUSPECT_REGRESSION par parsing JSON diff |
| H.6 | Audit historique = responsabilité bot | `audit-history` retourne `LAST_REAL_EXEC` ou `NEVER_EXECUTED_SINCE_<creation>` |
| H.7 | Plan P0-P4 sortie cycle perpétuel | P0 gel · P1 STABLE_SNAPSHOT · P2 exec/archive · P3 GH Actions · P4 regen mensuelle |

---

## CARTOGRAPHIE & OUTILS

```
MyIA.AI.Notebooks/                      # Séries pédagogiques par thème
- GenAI/{Image,Audio,Video,Texte}/      # 60+ notebooks Python
- ML/                                    # ML.NET tutorials (.NET C#)
- Search/{Part1-Foundations,Part2-CSP,Part3-Advanced}/
- Sudoku/                                # Constraint solving (.NET C#)
- SymbolicAI/{Lean,Tweety,SemanticWeb,Planning,SmartContract}/
- Probas/                                # Infer.NET probabilistic (.NET C#)
- GameTheory/                            # OpenSpiel + Lean (social_choice_lean/)
- IIT/                                   # PyPhi (Python)
- QuantConnect/                          # 27 notebooks + 50 stratégies
- Config/settings.json

scripts/notebook_tools/notebook_tools.py # CLI multi-famille (validate/execute/skeleton/analyze)
scripts/genai-stack/genai.py             # GenAI Docker + validation
.claude/{agents,skills,rules}/           # 21 sous-agents, 17 skills, rules auto-loaded
GradeBookApp/                            # Notation étudiants (pipelines/données privés GDrive)
docker-configurations/                   # ComfyUI + Qwen Docker
docs/                                    # Documentation déportée de ce fichier
```

**Règle générale outils** : ne jamais écrire un script ad-hoc d'exécution/validation — il existe presque toujours un outil dédié dans `scripts/notebook_tools/`. Si manquant, l'ajouter **là** (pas dans la racine `scripts/`).

### Catalogue agents / skills / scripts — USAGE MANDATÉ

**Règle HARD.** Là où un **sous-agent** spécialiste, un **skill** slash-command, ou un **script** dédié couvre une tâche, **l'utiliser plutôt que de réimproviser le workflow**. Les Epics side-tracks **DOIVENT** déléguer aux sous-agents async (`run_in_background: true`) quand un specialist existe.

- **Sous-agents** : `Agent(subagent_type: "<nom>")`. Roster + mapping side-track : [subagents-reference.md](docs/reference/subagents-reference.md).
- **Skills** : slash-command `/<nom>` (`/coordinate`, `/review-student-prs`, `/build-notebook`, `/enrich-notebooks`, …).
- **Scripts** : catalogue complet → [scripts-reference.md](docs/reference/scripts-reference.md). **Ne jamais** réécrire un script d'exécution/validation/maintenance.

**Collision** : sous-agents read-only en parallèle OK ; sous-agents **éditeurs = un seul à la fois par notebook/série**.

**Modèle explicite obligatoire** : tout `Agent()` DOIT spécifier `model: "sonnet"` ou `"haiku"`. `"opus"` uniquement sur justification écrite dans le prompt. Sous-agent sans `model` explicite = hérite d'opus = violation. Cf [model-delegation.md](.claude/rules/model-delegation.md).

---

## PROCÉDURES RÉCURRENTES

Workflows détaillés (PR 10 étapes, dispatch agents, validation notebook, audit anti-régression, exécution Quantbooks, pre-commit H.3) : [procedures-recurrentes.md](docs/reference/procedures-recurrentes.md).

**Productivité opérations longues — HARD 2026-05-11** : quand un processus long tourne (training GPU, backtest QC, build Lean, prover BG iter, papermill batch), **ne pas attendre passivement**. Lancer BG, continuer immédiatement autre travail, check uniquement à intervalles utiles (5-10 min), **minimum 2 tracks en flight**.

---

## RÈGLES AGENTS (Roo Code distants)

| Règle | Résumé |
|---|---|
| **Code avant documentation** | Code fonctionnel > tests > documentation. Pas de markdown (README, MAPPING, RAPPORT) sans code fonctionnel associé. Rapports d'audit / inventaires / status → dashboard RooSync, pas dans le repo |
| **Slides : images en overlay** | Layout `image-overlay` avec texte par-dessus, jamais en colonne droite (issue #221). Vérification visuelle Slidev sur **CHAQUE** slide modifié, `?clicks=99`, absence d'overflow |
| **Pas de duplication** | Avant de créer un fichier, vérifier qu'il n'existe pas (`grep`, `find`). Mettre à jour plutôt que créer |
| **Enrichissement notebooks** | Cellules de transition : contenu pédagogique spécifique (pas « Suite du traitement »). Interprétation APRÈS la cellule interprétée. Pas d'enrichissement parallèle du même notebook |

---

## QUANTCONNECT (résumé)

- **Backtest obligatoire** après modification (`create_compile` → `create_backtest` → `read_backtest`). Reporter Sharpe/CAGR/MaxDD dans commit + RooSync.
- **API uniquement via MCP Docker** `quantconnect/mcp-server` (config `.mcp.json`, jamais committer le token). Pas de scripts REST directs.
- **Rate limiting** : MAX 10 appels/min entre TOUS les agents. Annoncer sur dashboard avant un backtest.
- **Quantbooks** = exécution **via QC Cloud** (MCP / Playwright en fallback), pas d'exécution locale fictive.
- **Livre référence** : *Hands-On AI Trading* (Jared Broad), https://www.hands-on-ai-trading.com/

Structure complète : [quantconnect.md](docs/qc/quantconnect.md).

---

## PROJECT OVERVIEW

CoursIA = plateforme éducative AI : Jupyter notebooks (C# .NET Interactive + Python), infrastructure Docker GenAI (ComfyUI + Qwen), GradeBookApp évaluation étudiants. Repository : https://github.com/jsboige/CoursIA. Documentation primaire en français ; commentaires code en français ou anglais.

Stack : OpenAI/Anthropic APIs, Qwen 2.5-VL, Semantic Kernel, Python 3.10+ + .NET 9.0 Interactive, Papermill + MCP Jupyter, ComfyUI GPU (RTX 3090).
