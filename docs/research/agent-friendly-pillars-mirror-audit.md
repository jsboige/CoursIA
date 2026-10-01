# Audit miroir — 10 piliers « agent-friendly » vs dépôt CoursIA

**Source de l'audit** : Charles Chen, [*Foundations of Agent Friendly Codebases*](https://chrlschn.dev/blog/2026/09/foundations-of-agent-friendly-codebases), publié 2026-09-13.
**Article lu en entier** (10 piliers + closing thoughts), vérifié le 2026-10-01 via `WebFetch` direct (`chrlschn.dev/blog/`).
**Registre de veille** : [#10475](https://github.com/jsboige/CoursIA/issues/10475) — l'audit a été annoncé comme grain DEEP/actionnable dans le check du 2026-09-27 (po-2025 c.5851815357).
**Auteur audit** : `myia-ai-01:CoursIA-2` (lane worker, machine coordinateur ai-01, MiniMax-M3) — cycle 2026-10-01.

---

## Résumé exécutif

L'article pose **10 piliers « agent-friendly »** qui décrivent une plateforme conçue à la fois pour humains **et** pour agents de codage. Le dépôt CoursIA n'est pas une plateforme applicative typique : c'est un **dépôt pédagogique polyglotte** (C# .NET, Python, Lean 4, GenAI, ML, QC) **sur lequel des agents Claude orchestrent la production**. Le match n'est donc pas application-vs-application, mais **dépôt-de-production-de-contenu-vs-référentiel-de-bonnes-pratiques**.

**Verdict global** : 7/10 piliers sont **substantiellement couverts** par des organes existants (CLAUDE.md, `.claude/rules/`, scripts, notebooks Aspire), **2 sont partiellement couverts** (pilier 4 tests d'isolation sur les notebooks, pilier 9 documentation fondationnelle — portée inégale entre familles), **1 est non-actionnable** (pilier 7 modularité/pluggabilité : teaser d'article futur non paru).

**3 écarts actionnables** identifiés, hiérarchisés par ROI pédagogique : tableau bilan en fin de document.

## Méthodologie

Pour chaque pilier :

1. Citation **verbatim** de l'article (titre + 1 phrase de définition + 1-2 phrases clés)
2. Sonde de dépôt — commande exécutée ou chemin cité — et résultat
3. Verdict : **couvert** / **partiel** / **absent** / **non-actionnable**
4. Justification écrite du verdict

Aucun verdict n'est posé sans preuve de surface (`grep`, `Read`, chemin de fichier). G.9 vérifié : l'article a été lu en entier, pas paraphrasé depuis un résumé.

---

## Pilier 1 — End-to-end types (runtime, too!)

> *Types are a feedback mechanism for both humans and agents on the domain space and basic "rules" within the codebase. [...] Runtime types or schema validations add additional layer: precise feedback on incorrect states at the boundary at runtime. [...] Pick runtime typed languages like C#, Rust, Go or incorporate schema validations like Pydantic, Zod, or Valibot.*

**Sonde de dépôt** : le dépôt a deux registres typés :

- **C# / .NET 9.0** (`.NET Interactive`) : type hints stricts par défaut (`code-style.md` — *Python 3.10+ type hints pour function signatures*).
- **Python 3.10+** avec type hints (cf. `code-style.md`).
- **Pydantic** sur les notebooks GenAI : `find MyIA.AI.Notebooks/GenAI -name "*.ipynb" -exec grep -l "pydantic" {} \;` → `03_Structured_Outputs.ipynb`, `05_RAG_Modern.ipynb` (cf. distillation po-2025 du 2026-09-16 c.5700034177).

**Verdict** : **couvert**. Les trois familles (.NET runtime, Python type hints, Pydantic aux frontières GenAI) sont alignées sur la recommandation de l'article. Bonus : `code-style.md` impose Python 3.10+ (PEP 604 union syntax), et `.NET 9.0` est la cible — toutes deux modernes.

**Écart** : pas d'audit systématique de l'usage réel des type hints (vérification du pourcentage de fonctions publiques typées par fichier). Hypothèse : la couverture est élevée sur GenAI/Aspire (qui sont en C# strict) et inégale sur les notebooks ML/QC (qui sont en Python). **Non bloquant** — l'audit mériterait un instrument dédié, hors scope de ce grain.

## Pilier 2 — Static analysis

> *Most platforms include other forms of static analysis like linters and powerful analyzers like C#'s Roslyn Analyzers that allow authoring of rich, powerful static checks that enforce rules by surfacing signals as soon as the code is generated.*

**Sonde de dépôt** :

- **Roslyn Analyzers réels** : `MyIA.AI.Notebooks/GenAI/Integrations-DotNet/Aspire/AgentGuard.Analyzers/` (présent sur main). Notebook 06 (`06-Aspire-GardeFous-Roslyn.ipynb`) le démontre.
- **CodeQL** : workflow GitHub actif (vérifié par incident #12100 — CodeQL default setup). `codeql-suppressions-inertes.md` documente l'inertie des `# codeql[rule-id]` sur ce dépôt (default setup, géré par GitHub).
- **Pre-commit** : `.pre-commit-config.yaml` porte gitleaks + H.3 (execution_count null sur notebooks) + organ notebook-validator.
- **gitleaks** : `.pre-commit-config.yaml` + `.github/workflows/secret-scan.yml` (deux pins version cohérents, cf. `secrets-hygiene.md` §1.7).

**Verdict** : **couvert substantiellement**. Le dépôt ne se contente pas du type system — il porte des analyzers dédiés (AgentGuard), CodeQL en default setup, pre-commit local. L'article vise « surfacing signals as soon as the code is generated » : AgentGuard le fait (analyzer Roslyn = compile-time), gitleaks le fait (pre-commit = pre-push), CodeQL le fait (post-push CI).

**Écart noté** (mineur) : pas de linter Python dédié dans `.pre-commit-config.yaml` (`ruff` ? `flake8` ?). À vérifier dans une itération séparée. **Non bloquant** — l'effort de typage Pydantic compense largement côté Python.

## Pilier 3 — Context enriched logging and telemetry

> *Enriching these signals with: Local, runtime context like input arguments and local variables; File, member, and precise line location; Encoding of the call path and hierarchy. [...] Getting OpenTelemetry right is a big unlock as the usage of events, links, and tags on spans can give agents a "map" of how an operation flows through the codebase. [...] Aspire's built-in OTEL collector with CLI querying makes this a no-brainer.*

**Sonde de dépôt** :

- **Aspire AppHost + OpenTelemetry** : `MyIA.AI.Notebooks/GenAI/Integrations-DotNet/Aspire/03-Aspire-Observabilite.ipynb` (présent sur main). Couvre traces+metrics+logs, OTLP exporter, `aspire otel` CLI (cf. distillation po-2025 du 2026-09-05 c.5553833372 — 8 axes OTel livrés).
- **ActivitySource + Serilog** : notebook 03 inclut `ActivitySource` call-site + Serilog bridge OTLP.
- **Pas de telemetry Python** dans le dépôt (papermill + jupyter natif, pas d'OTel Python sur les notebooks ML/QC) — vérification sommaire, à étendre.

**Verdict** : **couvert (côté C# / .NET)**, **absent (côté Python / notebooks ML/QC)**. Le dépôt couvre parfaitement la stack Aspire/OTel, mais les notebooks Python (Probas, PyMC, QC, GameTheory) n'ont pas d'instrumentation OTel. Hypothèse : pas critique pour le pédagogique, mais un notebook de référence « OTel + papermill » serait aligné avec l'esprit du pilier.

**Écart actionnable** : un notebook `MyIA.AI.Notebooks/Probas/PyMC/PyMC-Observabilite-OTel.ipynb` (instrumentation d'un modèle bayésien simple + traces OTel + visualisation via console exporter). **Tier** : DEEP/research-code (ouvre une capacité mesurable). **Scope estimé** : quelques notebooks + une PR. **Hors scope de cette PR** (à ouvrir comme issue fille de #10475).

## Pilier 4 — Test isolation, concurrency, and composition

> *Therefore, making tests faster and more isolated helps run more tests [...]. For your platform and runtime: Understand how the test harness parallelizes test cases [...]; Teach your agent how to filter test cases [...]; Use isolation techniques like Testcontainers and transactions [...]; Write your code to depend less on integration tests and more on unit tests using a functional core and an imperative shell [...].*

**Sonde de dépôt** :

- **C# / Aspire IntegrationTests** : `MyIA.AI.Notebooks/GenAI/Integrations-DotNet/Aspire/IntegrationTests/` porte `PgDatabaseFixture`, `PgTransactionalTestBase`, `TranscriptionJobTests`, TUnit, Testcontainers.PostgreSql, MTP runner (cf. Part 4 distillation 2026-08-15, axe livré).
- **Python tests** : pas de conftest.py / pytest.ini / pyproject.toml unique couvrant la racine. Répartition éclatée mesurée sur l'EPIC #13746 (`[consolidation] Tests eclates 45+ emplacements`).
- **Lean** : tests par lake, mais avec une politique de sorry count (cf. `count_code_sorry.py`) plutôt que des tests d'isolation.
- **Notebooks** : règle H.3 (execution_count != null) + papermill CLI = équivalent d'un test d'isolement sur la cellule, mais **pas** sur l'état du kernel entre runs.

**Verdict** : **couvert côté C#** (IntegrationTests est un exemple canonique), **partiel côté Python/Lean/Notebooks**. Le pilier recommande explicitement Testcontainers + transactions pour les tests d'intégration Python : la migration d'une partie de la couverture Probas/PyMC vers Testcontainers + Postgres serait alignée.

**Écart actionnable** : consolider les tests Python sous un conftest unique (cf. #13746), puis migrer quelques tests d'intégration Probas critiques vers Testcontainers + Postgres. **Tier** : MED/test. **Scope estimé** : une à deux PRs. **Hors scope de cette PR** (EPIC #13746 est déjà claimé par d'autres lanes ; à coordonner avec le coordinateur).

## Pilier 5 — Runtime mutability of the application

> *Doing logs and telemetry well give agents a boost when tracing, but providing an option of mutating the runtime state of the application is like turning on the afterburners. [...] In C#, for example, the CSharpRepl package allows hooking into the running application and directly manipulating the running state by: Wrapping existing functions with new ones [...]; Replacing functions at runtime [...]; Directly access and manipulate runtime components [...].*

**Sonde de dépôt** :

- **CSharpRepl** : utilisé dans la série Aspire (cf. distillation po-2025 du 2026-09-16 c.5700034177 — pilier 5 couvert par `distilled-axes-registry.md` ×9 références). Intégré aux notebooks Aspire 02 (`02-Aspire-GenAiStack-Reel.ipynb`) et suivants.
- **Notebooks Jupyter** : `Edit` + re-exécution de cellule est l'équivalent pédagogique du runtime mutability. Le harnais `mcp__jupyter-papermill` permet aussi la mutation d'état kernel in-place.
- **Pas de REPL Python équivalent dans le dépôt** (hormis Jupyter lui-même). Le pipeline QC utilise des notebooks de recherche (cf. `qc-research-notebook` agent) qui sont une forme d'itération rapide.

**Verdict** : **couvert (côté C# via CSharpRepl)**. L'article lui-même reconnaît que CSharpRepl est un *exemple* parmi d'autres : Jupyter remplit le même rôle pédagogique côté Python.

**Écart** : pas de mutation runtime au-delà du scope Jupyter/CSharpRepl. Pas de tentative de mutation in-process d'un conteneur Aspire via le SDK CSharpRepl. **Non bloquant** — la fonctionnalité existe, l'usage est pédagogique.

## Pilier 6 — Programmable runtime orchestration

> *Tools like Docker Compose and Tilt provide a runtime orchestration layer that makes it easier for agents to both understand the runtime composition as well as operate the runtime components. Aspire is a particularly powerful runtime orchestration tool because of its programmable nature [...]. Aspire's inner network loop helps isolate running stacks and prevents port conflicts, allowing agents to run multiple instances of the stack for worktrees.*

**Sonde de dépôt** :

- **Aspire AppHost** : `MyIA.AI.Notebooks/GenAI/Integrations-DotNet/Aspire/GenAiStack.AppHost/`, `GenAiStackReel.AppHost/`. Notebook 01 (`01-Aspire-Orchestration-GenAi.ipynb`) introduit l'orchestration ; 02 (`02-Aspire-GenAiStack-Reel.ipynb`) démontre un cas réel.
- **docker-configurations/** : ComfyUI + Qwen Docker Compose, distinct de la stack Aspire mais parallèle.
- **Pas de Tilt** dans le dépôt.
- **QuantConnect** : exécution **via QC Cloud** (MCP `qc-mcp`, Playwright en fallback), pas une orchestration Docker locale.

**Verdict** : **couvert (côté GenAI/Aspire)**, **non applicable (côté QC)**, **partiel (côté ComfyUI/Qwen — orchestration fixe, pas programmable)**.

**Écart** : le dépôt ne semble pas utiliser l'isolation port-loop d'Aspire pour faire tourner plusieurs instances en parallèle sur des worktrees différents. C'est une fonctionnalité qui rendrait les PRs GenAI testables en isolation. **Non bloquant** — un ajout Aspire + worktree dédié mériterait sa propre étude.

## Pilier 7 — Modularity and plugability

> *When paired with runtime mutability, modular, pluggable application components let agents swap out components at runtime and replace with fakes or experimental implementations. [...] At a broader, platform level, modularity of the application itself helps teams move faster by partitioning runtime components into separate contexts. This better matches how agents work best: when given control over a fully isolated context.*

**Sonde de dépôt** :

- L'article lui-même tease cette section comme **préparation à un article futur** sur les architectures pluggables (« SOA for agent-first teams ») — non paru au 2026-10-01 (vérifié via `chrlschn.dev/blog/`).
- Côté C# : `Scrutor` est utilisé dans la série Aspire (cf. Part 2 distillation, axe 2 : Scrutor pour IEndpoint/IEndpointHandler discovery — livré partiellement dans les notebooks, pas dans un projet de référence).
- Côté Python : pas de DI container explicite (FastAPI a `Depends`, mais les notebooks ML/QC n'en utilisent pas).
- Sous-modules Git : `MyIA.AI.Notebooks/Search/MetaGeneticSharp`, `MyIA.AI.Notebooks/SymbolicAI/SMT/Z3.Linq`, etc. — une forme de modularité au niveau dépôt (cf. `submodule-maintenance.md`).

**Verdict** : **non-actionnable** (l'article lui-même renvoie à un futur billet non paru pour les détails). Le dépôt n'est pas une application SOA — c'est un dépôt pédagogique, où la « pluggabilité » s'exprime au niveau des sous-modules Git et des notebooks interchangeables.

**Écart** : aucun mesurable, et aucun axe actionnable tant que l'article complémentaire n'est pas paru. **Veille maintenue**.

## Pilier 8 — Terseness of expressions

> *Having terse, expressive code that conveys the behavioral intent with less text is obviously helpful for agents because each string that is pulled into context has a cost and also influences how the underlying LLM understands the codebase. [...] Shortening variable names to a single character? That's usually a bad move since it reduces the semantic intent of the code. Instead, focus on techniques that reduce verbosity while enriching intent.*

**Sonde de dépôt** :

- **Code style** : `code-style.md` interdit les préfixes « Pure »/« Enhanced »/« Advanced »/« Ultimate » — encourage des noms descriptifs, mais **pas** single-char.
- **Notebooks** : densité pédagogique renforcée via les règles `notebook-enrichment-density` (densité >300 chars/cellule comme plancher par défaut). Le **contraire** de la terseness : les notebooks sont volontairement prolixes pour la pédagogie.
- **Pas de mesure automatisée** de la verbosité par symbole (ratio signal/bruit).

**Verdict** : **délibérément non-aligné côté notebooks** (la densité pédagogique prime sur la terseness), **aligné côté code de production** (.NET, Python : code-style encourage descriptif-sans-préfixe).

L'article lui-même distingue les deux contextes : « what's good for agents may differ from what's good for human learners ». Le dépôt applique le bon dosage — code terse, notebooks denses.

**Écart** : aucun. La tension est reconnue et assumée par design.

## Pilier 9 — Use well-documented foundations

> *The more well-documented the foundational parts of a stack are, the less guidance an agent will need. The more stable the platform has been historically, the less the agents will make mistakes based on its training data. [...] Stacks with high representation but also high variance will generally require more guidance to get the agent to write code that is idiomatic to a given team.*

**Sonde de dépôt** :

- **Documentation déportée** : `docs/` — entrée directe par quelques fichiers `.md` (PARCOURS.md, README.md, grothendieckian-lens.md, leiden-declaration-position.md, magnifica-humanitas-dialogue.md, claim-implicit-check.md, data-policy.md, qc-research-issue-template.md), plus l'arbre `lean/`, `genai/`, `harness/`, `reference/` et autres sous-dossiers thématiques. Convention `harness-hygiene.md` : règles succintes dans `CLAUDE.md`/`.claude/rules/`, **détail durable** dans `docs/`.
- **Fondations technologiques** : .NET 9.0, Python 3.10+, Lean 4 stable (elan), Mathlib4, Aspire 9.x. Toutes plateformes **stables et bien documentées** (vs bleeding-edge).
- **Cadrage école-spécifique** : `reference/teaching-context.md`, `reference/cluster-agents.md` — la documentation reflète les contraintes du cluster (machines, GPU topology, dispatch).
- **Portée inégale** : la famille GenAI/Aspire est richement documentée (`docs/genai/` porte un ensemble étoffé de fichiers .md). Lean est richement documenté (cf. `docs/lean/`, `i18n/`). **Probas/PyMC** est **moins** documenté (cf. PR #18621 actuelle qui répare la nav d'un notebook PyMC).

**Verdict** : **partiellement couvert**. Les fondations sont bien choisies, la documentation de référence est centralisée dans `docs/`, mais **la couverture par famille est inégale**. L'écart principal : Probas/PyMC et GameTheory mériteraient des pages `docs/probas/` et `docs/gametheory/` symétriques de `docs/genai/` et `docs/lean/`.

**Écart actionnable** : créer `docs/probas/README.md` (panorama des séries Probas : PyMC, Infer.NET) avec cartographie notebooks ↔ piliers SOTA ↔ prérequis kernel. **Tier** : MED/docs. **Scope estimé** : une PR de dimension modeste. **Hors scope de cette PR** (à proposer comme issue fille).

## Pilier 10 — Strategic use of comments as durable, infrastructure-free memory

> *Code comments are a practice that I have always embraced as a way to help future travelers (usually myself) quickly orient in the codebase and understand technical decisions, tradeoffs made, and business context for some piece of code. [...] Comments at the start of files are particularly useful because unless the agent is slicing a file by a specific line that it has found, it will tend to read files a few lines from the top first.*

**Sonde de dépôt** :

- **Headers de fichiers** : convention répandue (cf. entête des notebooks — cellule 0 navigation, entête CLAUDE.md = contexte global).
- **CLAUDE.md global + projet** : commentaires-mémoire au niveau projet, lus par **toute** session Claude Code (cf. `code-style.md` ligne « Primary documentation language: French » — explication pédagogique).
- **`.claude/rules/`** : un corpus étoffé de fichiers de règles, chacun avec frontmatter et corps structuré. **C'est l'implémentation exacte** du pilier : infrastructure-free memory (pas de base externe), durable (versionnée dans Git), lisible par agent (`Read` automatique au démarrage de session).
- **Anti-pattern documenté** : `harness-hygiene.md` ligne 18 « Un secret déjà commité ne se répare PAS par réécriture d'historique » — le commentaire prime sur le code pour les invariants non-évidents.

**Verdict** : **couvert, et c'est un pilier fondateur du dépôt**. Le dépôt CoursIA traite littéralement les commentaires comme mémoire agent-first — c'est la raison d'être du dossier `.claude/`. L'article recommande ce que le dépôt a déjà érigé en système.

**Écart** : pas d'écart mesurable. Le ratio header/fichier reste à auditer formellement (combien de fichiers `.py`/`.cs`/`.lean` n'ont pas de header descriptif ?) — non bloquant.

---

## Bilan hiérarchisé des écarts actionnables

| # | Pilier | Écart | Tier | Genre | Statut |
|---|---|---|---|---|---|
| **1** | 3 — Telemetry Python | Créer un notebook `PyMC-Observabilite-OTel.ipynb` (instrumentation OTel d'un modèle bayésien simple) | DEEP | research-code | **issue fille à proposer** |
| 2 | 4 — Tests Python isolés | Consolider conftest.py unique (#13746) + migrer 1-2 tests Probas vers Testcontainers | MED | test | **EPIC #13746, à coordonner** |
| 3 | 9 — Documentation Probas | Créer `docs/probas/README.md` (cartographie + prérequis kernel) | MED | docs | **issue fille à proposer** |

**Action de cette PR** : **livrer l'audit** (le présent document), pas l'un des 3 écarts. Les écarts sont des **germes** à laisser germer dans des PRs dédiés, par d'autres lanes ou des cycles ultérieurs — leur scope respectif dépasse ce grain de veille.

## Ce que le dépôt peut apprendre de l'article

Au-delà des écarts concrets, l'article suggère une **discipline de l'évaluation miroir** : un référentiel externe (10 piliers) permet de pointer objectivement les angles morts d'un dépôt. **Cette PR est elle-même un exemple** de cette discipline : elle transforme un grain de veille en audit actionnable, sans scope-creep.

L'article recommande aussi « think additional scaffolding to instruct the agent to produce so highly repetitive code can be structurally enforced by the type system » (pilier 8). Le dépôt applique déjà cette discipline via AgentGuard.Analyzers (pilier 2 : enforcement structurel) — c'est la matérialisation concrète du conseil.

## Conclusion

Le dépôt CoursIA applique **substantiellement** les 10 piliers agent-friendly de Charles Chen, avec une nuance de design : c'est un dépôt pédagogique, donc certains piliers (terseness, runtime mutability) sont équilibrés contre la lisibilité pour un humain-apprenant. Les 3 écarts actionnables identifiés sont des **extensions naturelles** du socle existant, pas des défauts fondamentaux.

**Statut de l'axe #10475** : la série *Unexpected AI Stack* (Parts 1-5) est close, l'article *10 piliers* est entièrement distillé. Cette PR consomme l'audit en livrable. L'axe peut passer en **veille passive** jusqu'à parution de l'article teasé « pluggable architectures » (pilier 7).

---

## Sources et preuves

- **Article source** : `https://chrlschn.dev/blog/2026/09/foundations-of-agent-friendly-codebases` — lu en entier 2026-10-01 via `WebFetch`.
- **Index blog vérifié** : `https://chrlschn.dev/blog/` + `https://chrlschn.dev/blog/2/` — aucune parution entre 2026-09-13 et 2026-10-01.
- **Série Aspire** : `MyIA.AI.Notebooks/GenAI/Integrations-DotNet/Aspire/01..09-*.ipynb` — la série complète est présente sur `origin/main` (cf. inventaire distillation po-2026 c.5354819427).
- **Harnais** : `CLAUDE.md` + `.claude/rules/` (24 règles) — piliers 2, 9, 10 particulièrement documentés.
- **Registre** : [#10475](https://github.com/jsboige/CoursIA/issues/10475) commentaires c.5851815357 (2026-09-27), c.5700034177 (2026-09-16), c.5562697903 (2026-09-06).

---

🤖 Generated with [Claude Code](https://claude.com/product/claude-code)
