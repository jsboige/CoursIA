# PR Review Discipline — anti-complaisance

S'applique à **tous les reviewers**, humains et bots (clusterManager-Myia, jsboige self-bot, ai-01 coordinateur).

**Exception — PRs de TP étudiantes (mandat user 2026-05-20).** Les critères A-H ci-dessous visent les PRs **internes/contributeurs**. Les PRs **étudiantes** suivent [student-pr-reviews.md](student-pr-reviews.md) : review **bienveillante**, bypass template + CI, **pas de CHANGES_REQUESTED** sur scaffolding. Ne PAS appliquer A-H à un TP étudiant.

**Contexte, incidents fondateurs, workflow ai-01, anti-patterns détaillés** : [docs/reference/pr-review-context.md](../../docs/reference/pr-review-context.md).

## Critères CHANGES_REQUESTED obligatoires (HARD)

Un reviewer **DOIT** poster `state: CHANGES_REQUESTED` (pas COMMENTED, pas APPROVED) si **un seul** point est violé. APPROVED malgré violation = **complicité de complaisance**.

### A. Composites trop larges (split obligatoire)

| Métrique | Seuil « split required » |
|---|---|
| `additions + deletions` | > 3000 lignes hors notebooks |
| `changedFiles` | > 15 fichiers (hors `_output.ipynb` et données) |
| Features distinctes dans `## Summary` | > 4 |
| Domaines différents (ML + Lean + GenAI mêlés) | > 1 domaine |

### B. Lean : preuve de progrès vérifiable

Toute PR touchant `*.lean` ou `agent_tests/prover/` **DOIT** inclure dans le body :

1. `grep -c sorry` avant/après par fichier modifié
2. Lien vers `Lake build SUCCESS` (CI ou commit local prouvable)
3. Lien vers `Proof integrity SUCCESS` (job CI `proof-integrity` → `LeanVerifier.check_axioms(module, fail_on_sorry=True)`)
4. Si refactor du prover Python : justifier pourquoi il est nécessaire au claim Lean (sinon split)

**Trois classes d'axiomes sont `forbidden`**, pas seulement le `sorry` :

| Classe | Ce qu'elle signale |
|---|---|
| `native_decide.*` | réduction par le noyau natif **sans preuve** — vide le théorème de son contenu |
| `sorryAx` | `sorry` **transitif** dans la chaîne de dépendances, qu'un `grep -c sorry` ne verra jamais |
| `Classical.choice` | base non-constructive (souvent légitime — se whiteliste au câblage, avec justification écrite) |

**Un `proof-integrity SUCCESS` antérieur au 2026-07-28 ne prouve PAS l'absence de `native_decide`** (parser ligne-à-ligne aveugle aux noms longs wrappés ; corrigé par #8740). Ne pas ré-invoquer un vert plus ancien comme preuve.

**Whitelist = noms explicites, jamais de wildcard** — `allow-axioms` liste les axiomes un par un (cliquet : tout nouveau `native_decide` produit un nom absent → rouge). Un motif générique détruirait cette propriété ; un gate qui ne peut plus rougir n'est pas un gate.

**Tant que le job n'est pas câblé sur le lake de la PR**, B.3 se lit **non applicable** (à écrire explicitement dans le body), jamais comme un gate silencieusement sauté (#8677). État du câblage : les lakes câblés sont **exactement les workflows qui appellent** `lean-axiom.yml` (`grep -ln 'lean-axiom' .github/workflows/*.yml`, moins le fichier lui-même) — mesure mécanique, pas un compte recopié. Triage par lake : [docs/reference/lean-axiom-coverage.md](../../docs/reference/lean-axiom-coverage.md).

### C. ML : multi-seed obligatoire

Toute PR claim « BEATS » / « improvement » sur métriques ML/trading **DOIT** inclure : (1) walk-forward 5-fold ; (2) **≥4 seeds** parmi 0/1/7/42/99 ; (3) edge ≥ 2σ cross-seed sinon flag « noise » ; (4) comparaison à majority baseline + coûts de transaction (5bps SPY, 10bps crypto) ; (5) **pas de FAANG/Mag7** en training ; (6) verdict honnête « BEATS » / « NO BEATS » / « INCONCLUSIVE » — jamais « promising ».

Single-seed ou single-fold = **CHANGES_REQUESTED** sauf flag explicite `[POC]` dans le titre.

### D. Notebooks : preuve d'exécution réelle

1. Sortie de `papermill` ou kernel exec (coller les premières lignes)
2. Vérification 0 erreur volontaire (`grep -nE "raise NotImplementedError|assert False|1/0"`)
3. Cellules code = `execution_count: <int>` ET `outputs: [...]` cohérents (C.2)
4. Le diff ne supprime pas de cellule `# Solution` / `# Exemple résolu` sans issue référencée
5. **PR « alignement doc-honesty » (#8052/#3801) : diagnostic C.4 obligatoire** — le body **DOIT** porter la section `## Diagnostic dérive` ([notebook-conventions.md](notebook-conventions.md)) : POURQUOI l'output a dérivé (**a** env/kernel · **b** claim antérieure fabriquée · **c** moteur upstream · **d** régression dépendance · **e** stochasticité non-seedée) + verdict `CAUSE_FIXED` / `CAUSE_DOCUMENTED_ONLY` / `CAUSE_INTRINSIC`.

**Refus si :** le body **ne contient pas** `## Diagnostic dérive` (citer #8364 en label ne suffit pas) · verdict `CAUSE_DOCUMENTED_ONLY` **sans** issue fille traitant la cause (= « jambe de bois repeinte ») · la valeur ré-alignée est un **nombre de perf/timing/accuracy/coût** ET le notebook est **re-exécutable localement** (règle F) : elle doit alors venir d'une **re-exécution fraîche**, jamais d'un byte-surgical markdown-align — enshriner un nombre qui changera au prochain passage kernel *est* la dérive que C.4 interdit. A fortiori si une re-exec est **déjà due** : **folder** l'alignement dedans.

**Advisory `.NET execution_count` ≠ outputs vides autorisés (#5214).** La CI ne peut pas Papermill-exécuter les notebooks .NET — l'advisory autorise à sauter la ré-exécution **CI**, **pas** à committer des sorties vides. `.NET Interactive` s'exécute **localement** sur chaque worker → une cellule .NET committée **DOIT** porter `execution_count != null`. `validate_pr_notebooks.py` FAIL sur `.NET` + `null` (verdict H.5 `STRUCTURAL_ONLY`), et ne tolère `null` que là où l'exécution locale est aussi impossible (QC Cloud, Lean). Verdict attendu dans le body : `EXEC_PROVED` vs `STRUCTURAL_ONLY` (refus).

### E. Documentation / Admin : groupement obligatoire

PRs uniquement docs/README/CLAUDE.md/rules : < 50 lignes → exiger groupement ; < 20 lignes → refuser systématiquement ; multiples READMEs sans cohérence cross-series → refuser.

**Feuille README (#3973/#3975) — audit fichier ENTIER obligatoire.** Une PR qui met à jour un compte / une statistique / un paragraphe dans un README de série DOIT prouver dans le body qu'elle a ré-audité le **fichier entier** contre le disque : (a) `ls`/`find` count par sous-dossier cité ; (b) réconciliation **disque ↔ `CATALOG-STATUS` ↔ prose** (si le catalogue lui-même est faux : **signaler**, ne PAS s'aligner dessus) ; (c) listes de notebooks, arbres de structure, breakdowns vérifiés à jour.

Corriger l'intro en laissant une liste obsolète 100 lignes plus bas = `CHANGES_REQUESTED`. Le format « slim +5/−5 » ne **dispense pas** de l'audit fichier-entier ; il le **plafonne à tort**.

### F. Audit reassessment / « false positive »

DOIT documenter : (1) critère exact violé par l'audit initial (pattern cité) ; (2) méthodologie de vérification (pas « j'ai regardé visuellement ») ; (3) ≥3 cellules-types vérifiées avec preuve. Cf [audit-reassessment.md](audit-reassessment.md).

### G. QC : backtest obligatoire

Toute PR touchant `MyIA.AI.Notebooks/QuantConnect/projects/` DOIT inclure : (1) backtest run (`create_compile` + `create_backtest` via MCP) ; (2) Sharpe/CAGR/MaxDD dans le body ; (3) période OOS distincte du training.

### H. Vrai outil SOTA + problème non-trivial

Refus (`CHANGES_REQUESTED`) si :

1. **Workaround dégradé sans verdict SOTA écrit** — sortie de substitution (ASCII au lieu d'image générée, réimplémentation jouet au lieu de la lib, stub au lieu d'un appel de service, sortie fabriquée au lieu d'un backtest) **alors que l'outil réel est installable/invocable/rebranchable**, sans un des 5 verdicts (SOTA-OK / RECOVERABLE-LOCAL / RECOVERABLE-MACHINE / RECOVERABLE-USER-HAND / INTRINSIC) écrit dans le body.
2. **Problème dégénéré** — moteur démontré sur un cas trivial où le SOTA équivaut à une baseline (BFS vs A* sur coût uniforme) → exiger complexification ou problème additionnel.
3. **Sortie de cellule hand-éditée** au lieu de corriger la cause + re-exécuter (Stop & Repair, [secrets-hygiene.md](secrets-hygiene.md) règle 6) — hors quantbook QC, `metadata.papermill`, et `probeAddresses` strip post-re-exec .NET.

Détail des 5 verdicts : [sota-not-workaround.md](sota-not-workaround.md).

## Voir aussi

- [docs/reference/pr-review-context.md](../../docs/reference/pr-review-context.md) — contexte, incidents, workflow ai-01, anti-patterns
- [student-pr-reviews.md](student-pr-reviews.md) — exception PRs étudiantes
- [sota-not-workaround.md](sota-not-workaround.md) · [notebook-conventions.md](notebook-conventions.md) · [anti-regression.md](anti-regression.md)
