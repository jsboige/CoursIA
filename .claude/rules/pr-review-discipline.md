# PR Review Discipline — anti-complaisance

S'applique à **tous les reviewers**, humains et bots (clusterManager-Myia, jsboige self-bot, ai-01 coordinateur).

**Exception — PRs de TP étudiantes (mandat user 2026-05-20).** Les critères A-H ci-dessous visent les PRs **internes/contributeurs**. Les PRs **étudiantes** suivent [student-pr-reviews.md](student-pr-reviews.md) : review **bienveillante**, bypass template + CI, **pas de CHANGES_REQUESTED** sur scaffolding. Ne PAS appliquer A-H à un TP étudiant.

**Contributeurs publics.** Les critères de fond A-H restent applicables à une PR publique ordinaire, mais le triage, le ton et l'escalade suivent [public-contribution-triage.md](public-contribution-triage.md) : aider à qualifier et corriger, jamais opposer un verdict abrupt ou impersonnel. Une correction volontaire d'exercice suit en plus [exercise-example-labeling.md](exercise-example-labeling.md).

**Contexte, incidents fondateurs, workflow ai-01, anti-patterns détaillés** : [docs/reference/pr-review-context.md](../../docs/reference/pr-review-context.md).

## Émission du verdict — un point qui tient le merge porte un marqueur (HARD, #14682)

Toute review (bot ou humaine) formulant **un point tenant le merge** porte un **marqueur reconnu** : préfixe de verdict (`[Hermes] COMMENT_WITH_CONCERNS`, `CHANGES_REQUESTED`) ou glyphe de sévérité (🟡, 🔴). L'organe B.0 (`scripts/check_unaddressed_nits.py`, `CONCERN_MARKERS`) ne lit **que** ces marqueurs : une réserve bloquante posée en prose libre **sans** marqueur lui est invisible et rend `rc=0`. **Ne pas élargir** le filet à des mots de prose : il sur-accuse d'un facteur 5 (mesure #14682) — le contrat est côté émission, pas côté filet. Instance #14658 + scan 80 PRs : [pr-review-context.md](../../docs/reference/pr-review-context.md).

### Répondre à une réserve — la forme sûre (HARD, #17071)

Une réponse d'auteur qui **cite** le token de verdict le redevient elle-même (régime absorbant) : la PR reste bloquée **à fond réparé**. La forme sûre : **encager le token lui-même** (backticks, `« »`, apostrophes, bloc de code) ou le nommer en position de **mention** (`suite à ta réserve`, `verdict X` sans deux-points) — jamais le gras (forme d'**émission**), jamais le token nu (muet par résidu assumé, pas par filet), et encager un mot **voisin** ne protège rien. Table de vérité mesurée, mécanique trois couches et instances fondatrices : [pr-review-context.md](../../docs/reference/pr-review-context.md).

## Lecture de l'état des checks — à la source, dans les DEUX sens (HARD, #16765)

`statusCheckRollup` est une **liste plate non triée** qui contient toutes les jambes du head, **y compris celles supersedées** par une tentative plus récente (rouges périmés compris — 12/160 PRs mesurées, dont les fondateurs #16232/#16499/#16579 : six rouges tous supersedés sur le même head). **Ne jamais refuser un merge sur le premier rouge de la liste**, ni acquitter sur son premier vert : re-lire à la source `commits/<headRefOid>/check-runs` et plier **dernier `started_at` par nom** — `python scripts/check_run_state.py --pr <N>` fait la lecture (fold canonique `pr_gate.py::dedupe_latest`, contrat dossier `checks: latest-wins-green`). Un `latest` vert n'est **pas** une preuve de mergeabilité : une jambe rouge résiduelle d'une suite distincte a déjà bloqué une PR verte (#11532, CodeQL) — le helper rend ces `residual_reds`, le verdict de merge reste `mergeStateStatus`.

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

1. Compte de `sorry` **réel** avant/après — `python scripts/lean/count_code_sorry.py --json`, champ `distinct_code_sorry`. **Pas `grep -c sorry`** : il compte la prose, pas les preuves (mesure du 2026-08-14 : 484 naïfs pour 21 réels sur les 21 lakes, [pr-review-context.md](../../docs/reference/pr-review-context.md)). Le gate CI mesure déjà juste (`sorry-filter-mode: real`) : c'est le texte de cette règle qui pointait le mauvais instrument.
2. Lien vers `Lake build SUCCESS` (CI ou commit local prouvable)
3. Lien vers `Proof integrity SUCCESS` (job CI `proof-integrity` → `LeanVerifier.check_axioms(module, fail_on_sorry=True)`)
4. Si refactor du prover Python : justifier pourquoi il est nécessaire au claim Lean (sinon split)

**Trois classes d'axiomes sont `forbidden`**, pas seulement le `sorry` : `native_decide.*` (réduction par le noyau natif **sans preuve** — vide le théorème), `sorryAx` (`sorry` **transitif**, qu'un `grep -c sorry` ne verra jamais), `Classical.choice` (non-constructif, souvent légitime — se whiteliste **par nom explicite**, jamais par wildcard : le cliquet qui fait rougir sur tout nouveau nom est toute la valeur du gate).

**Un `proof-integrity SUCCESS` antérieur au 2026-07-28 ne prouve PAS l'absence de `native_decide`** (parser aveugle aux noms longs wrappés ; corrigé #8740). Ne pas ré-invoquer un vert plus ancien comme preuve.

**B.3 se lit « non applicable » — et s'ÉCRIT tel quel dans le body** dans deux cas, jamais sauté en silence : (a) le job n'est pas câblé sur le lake de la PR (#8677) ; (b) il l'est, mais ses `target-modules` n'atteignent pas le module modifié (#8782) — un vert hors-cible est indiscernable d'un vert sur cible dans le rollup (job advisory `target-coverage`). Câblage = **exactement** les workflows appelant `lean-axiom.yml` (`grep -ln 'lean-axiom' .github/workflows/*.yml`, moins le fichier lui-même). Triage : [lean-axiom-coverage.md](../../docs/reference/lean-axiom-coverage.md) ; incidents : [pr-review-context.md](../../docs/reference/pr-review-context.md).

### C. ML : multi-seed obligatoire

Toute PR claim « BEATS » / « improvement » sur métriques ML/trading **DOIT** inclure : (1) walk-forward 5-fold ; (2) **≥4 seeds** parmi 0/1/7/42/99 ; (3) **la conjonction** edge ≥ 2σ cross-seed **ET** Diebold-Mariano `dm_p_median < 0.05` — les deux, pas σ seul (σ mesure la dispersion inter-seeds, pas la significativité) — le DM portant sur une **perte de précision** (`loss_fn="mse"` ou `"mae"`) ; `loss_fn="linear"` est un **contrôle de biais**, jamais la jambe de la conjonction (aveugle à la dispersion : un modèle plus précis peut « perdre » face à une baseline plus biaisée, #10961 CE1) ; (4) comparaison à majority baseline + coûts de transaction (5bps SPY, 10bps crypto) ; (5) **pas de FAANG/Mag7** en training ; (6) verdict honnête « BEATS » / « NO BEATS » / « INCONCLUSIVE » — jamais « promising » ; (7) **rapport de biais par modèle** dans le body (`mean(e)` signé ou biais OOS, modèle ET baseline) — un edge porté par le biais (pas par la précision) se déclare comme tel.

Les trois contre-exemples inscrits qui fondent (3) — `+19.97σ` avec `DM p = 0.236` ; `dm_stat` bit-identique sous `mse` pour `e` et `-e` ; et le modèle 11× plus précis « BEATEN » sous `linear` face à une baseline biaisée (#10961, CE1) — sont mesurés dans [pr-review-context.md §C](../../docs/reference/pr-review-context.md).

Single-seed ou single-fold = **CHANGES_REQUESTED** sauf flag explicite `[POC]` dans le titre.

### D. Notebooks : preuve d'exécution réelle

1. Sortie de `papermill` ou kernel exec (coller les premières lignes)
2. Vérification 0 erreur volontaire (`grep -nE "raise NotImplementedError|assert False|1/0"`)
3. Cellules code = `execution_count: <int>` ET `outputs: [...]` cohérents (C.2)
4. Le diff ne supprime pas de cellule `# Solution` / `# Exemple résolu` sans issue référencée
4bis. **Enrichissement markdown-only : vérifier de l'œil la POSITION de chaque `### Lecture du résultat` / `### Interprétation`** — elle doit suivre la cellule de code dont l'output porte la valeur citée, jamais un id voisin. Aucun check automatique ne le fait (~99 % de FP) ; le regard humain est l'organe. [cell-interpretation-ordering.md](cell-interpretation-ordering.md) (path-gated notebooks).
4ter. **Prose ajoutée : du contenu, pas un récit de correction** (Epic #20250). Lire ce que la PR **ajoute** en markdown : une section qui raconte la correction (corrigendum, cycle, lane, DM, réserve, horodatage, « cellule N corrigée ») au lieu d'enseigner = `CHANGES_REQUESTED`, la substance part dans le body ou l'issue. Le critère est la **part** du carnet, pas la présence d'un mot (une mention de provenance passe). Instrument : `python scripts/notebook_tools/check_activity_leak.py --diff origin/main...HEAD`. Cas fondateur : SC-09, environ un tiers du carnet en récit de cycle, mergé avec toutes les gates vertes.
5. **PR « alignement doc-honesty » (#8052/#3801) : diagnostic C.4 obligatoire** — le body **DOIT** porter la section `## Diagnostic dérive` ([notebook-conventions.md](notebook-conventions.md)) : POURQUOI l'output a dérivé (**a** env/kernel · **b** claim antérieure fabriquée · **c** moteur upstream · **d** régression dépendance · **e** stochasticité non-seedée) + verdict `CAUSE_FIXED` / `CAUSE_DOCUMENTED_ONLY` / `CAUSE_INTRINSIC`.

**Refus si :** le body **ne contient pas** `## Diagnostic dérive` (citer #8364 en label ne suffit pas) · verdict `CAUSE_DOCUMENTED_ONLY` sur une cause **réparable par la flotte** (environnement, dépendance, clé, machine : un verdict RECOVERABLE-* de [sota-not-workaround.md](sota-not-workaround.md)), même avec une issue fille (= « jambe de bois repeinte ») · la valeur ré-alignée est un **nombre de perf/timing/accuracy/coût** ET le notebook est **re-exécutable localement** (règle F) : elle doit venir d'une **re-exécution fraîche**, jamais d'un byte-surgical markdown-align — enshriner un nombre qui changera au prochain passage kernel *est* la dérive que C.4 interdit. Si une re-exec est **déjà due** : **folder** l'alignement dedans (incident #8479, [détail](../../docs/reference/pr-review-context.md)).

6. **PRs notebook : vérifier le verdict du check-run `Output-failure ratchet (base vs PR)`** (organe `scripts/notebook_tools/check_output_failure_text.py`, **bloquant** dans `scripts/ci/fast_lane_registry.py`) — il DOIT être `success`. `TOOL_FAILURE` (bannières « `program is not installed` ») ou `MACHINE_PATH` qui **augmente** sur la PR (ex. `0 → 21`) = **régression → `CHANGES_REQUESTED`**, même si les points 1-3 passent (les bannières ne déclenchent ni `exec_count` nul ni le grep de 2). Récurrences fondatrices — #3473/#11685 (rendu SVG remplacé par bannière), #13517 (LDA, approuvée par Hermes malgré `rc=1`) : [pr-review-context.md](../../docs/reference/pr-review-context.md).

7. **PRs notebook : lire le check-run `Output-collapse ratchet (base vs PR)`** (organe `scripts/notebook_tools/check_output_collapse.py`, **bloquant** dans `scripts/ci/fast_lane_registry.py` depuis T2 de #21424, #15327). Le verdict est dans le statut du check. Un finding `SIGNATURE` (sortie base substantielle remplacée par « `Execution sautee (API non configuree)` » et consœurs) = **re-exécution sans les clés → `CHANGES_REQUESTED`** : la dégradation gracieuse (`if api_ok:`) est le contournement de C.2 par la porte de secours, toutes gates d'exécution vertes (contre-exemple fondateur #15209 : 11 → 11 cellules, 0 erreur, **10637 → 2985** caractères de sortie — récit : [pr-review-context.md](../../docs/reference/pr-review-context.md)). Un finding `MAGNITUDE` (perte d'un ordre de grandeur par cellule, non couvert par les exemptions automatiques contenu-déplacé/purge-diagnostic) exige une **justification dans le body** (allègement déclaré) — sans elle : `CHANGES_REQUESTED`.

8. **PRs notebook : lire le check-run ADVISORY `Source-collapse ratchet (base vs PR, advisory)`** (organe `scripts/notebook_tools/check_source_collapse.py`, enregistré `blocking=False` dans `scripts/ci/fast_lane_registry.py`, #15901). Le point 7 mesure la perte de **sortie**, celui-ci la perte de **source** : les deux sont indépendantes, et c'est tout l'intérêt — une table supprimée et un `assert` reduit ne produisent **aucune sortie**, la perte est invisible par construction aux ratchets de sortie (contre-exemple fondateur #15862 : **−37 %** de source, 0 organe rouge). Un finding `MAGNITUDE` exige une **justification dans le body** (allègement déclaré) — sans elle : `CHANGES_REQUESTED`. Les exemptions automatiques (contenu déplacé vers une AUTRE cellule du **même** notebook, purge de texte de diagnostic type `CS####`/`warning`) blanchissent le signal : leur silence n'est **pas** un acquittement, et un `exempt-moved` qui ne déplace que quelques lignes doit être recontrôlé à l'œil. Le **même** check-run porte depuis #16110 le **second mécanisme** de la famille : la source survit en volume et perd sa **forme**. Un finding `STRUCTURE` signale `emptied` (la cellule avait des instructions, elle n'en a plus) et/ou `orphan-output` (elle porte une sortie qu'aucune instruction ne peut avoir produite) : le code est parti, la preuve d'exécution est restée → **restaurer la source ou retirer la sortie**, sinon `CHANGES_REQUESTED` (contre-exemple fondateur #16097 : la cellule **grossit** pendant que `ast.parse(...).body` tombe **10 → 0** — récits #15862/#16097 : [pr-review-context.md](../../docs/reference/pr-review-context.md)).

**Advisory `.NET execution_count` ≠ outputs vides autorisés (#5214).** L'advisory autorise à sauter la ré-exécution **CI** seulement (pas de kernel .NET en CI) : `.NET Interactive` s'exécute **localement** sur chaque worker → une cellule .NET committée **DOIT** porter `execution_count != null` (`validate_pr_notebooks.py` FAIL sur `.NET` + `null` ; `null` toléré seulement là où l'exécution locale est impossible : QC Cloud, Lean). Verdict attendu dans le body : `EXEC_PROVED` vs `STRUCTURAL_ONLY` (refus). Récit #5214 : [pr-review-context.md](../../docs/reference/pr-review-context.md).

### E. Documentation / Admin : groupement obligatoire

PRs uniquement docs/README/CLAUDE.md/rules : quand le diff est **fin**, le reflexe n'est pas le refus mais la question « **le geste peut-il etre etendu ?** » — proposer l'elargissement qui evite le saucissonnage (les fichiers voisins de la meme serie, les occurrences sœurs du meme defaut). Le refus reste la sortie quand l'extension a ete proposee et ecartee sans motif, et pour de multiples READMEs sans coherence cross-series.

**Feuille README — les totaux ne se mettent pas à jour à la main (arbitrage user 2026-09-24, #17029 revertée).** Total de notebooks, comptes par langage ou par sous-dossier, comptes de cellules, bandeaux « N notebooks » : ces statistiques dérivent à chaque ajout et relèvent de la **régénération du catalogue** (`CATALOG-STATUS` ; mandat user du 2026-08-04, #9377). Une PR de README dont la substance est une mise à jour de totaux = `CHANGES_REQUESTED`, quelle que soit la qualité de son audit. L'organe qui les repère est `python scripts/notebook_tools/check_prose_quantitative_claims.py --diff origin/main...HEAD` : son check-run `prose-counts` est **bloquant sur les lignes ajoutées** depuis #17636 (durci par #17645) — un compte faux en ligne ajoutée rougit la PR ; une ligne de compte fausse se **supprime** au profit du renvoi au catalogue, elle ne se remet pas à jour. Après l'ajout d'un notebook, la PR de README livre le **corps qui le présente** : sa section (ce qu'il démontre, ses outils, sa place dans le fil de la série), ses lignes dans les tables de navigation, les acquis et les parcours — contenu fidèle au notebook, lu avant d'écrire. Une PR qui corrige un passage d'un README ne laisse pas d'incohérence ailleurs dans le fichier (listes, arbres, liens) ; corriger l'intro en laissant une liste obsolète 100 lignes plus bas = `CHANGES_REQUESTED`.

### F. Audit reassessment / « false positive »

DOIT documenter : (1) critère exact violé par l'audit initial (pattern cité) ; (2) méthodologie de vérification (pas « j'ai regardé visuellement ») ; (3) ≥3 cellules-types vérifiées avec preuve. Cf [audit-reassessment.md](audit-reassessment.md).

### G. QC : backtest obligatoire

Toute PR touchant `MyIA.AI.Notebooks/QuantConnect/projects/` DOIT inclure : (1) backtest run (`create_compile` + `create_backtest` via MCP) ; (2) Sharpe/CAGR/MaxDD dans le body ; (3) période OOS distincte du training.

### H. Vrai outil SOTA + problème non-trivial

Refus (`CHANGES_REQUESTED`) si :

1. **Workaround dégradé sans verdict SOTA écrit** — sortie de substitution (ASCII au lieu d'image générée, réimplémentation jouet au lieu de la lib, stub au lieu d'un appel de service, sortie fabriquée au lieu d'un backtest) **alors que l'outil réel est installable/invocable/rebranchable**, sans un des 5 verdicts (SOTA-OK / RECOVERABLE-LOCAL / RECOVERABLE-MACHINE / RECOVERABLE-USER-HAND / INTRINSIC) écrit dans le body. **Un verdict `INTRINSIC` ne s'approuve qu'après que le reviewer a vérifié lui-même sa prémisse à la source** (l'outil existe-t-il, est-il public, installable ?) : une grille remplie sur une prémisse non vérifiée n'est pas une preuve (#21121 : TorchLean déclaré « non public », il l'était depuis cinq mois).
2. **Problème dégénéré** — moteur démontré sur un cas trivial où le SOTA équivaut à une baseline (BFS vs A* sur coût uniforme) → exiger complexification ou problème additionnel.
3. **Sortie de cellule hand-éditée** au lieu de corriger la cause + re-exécuter (Stop & Repair, [secrets-hygiene.md](secrets-hygiene.md) règle 6) — hors quantbook QC, `metadata.papermill`, et `probeAddresses` strip post-re-exec .NET.

Détail des 5 verdicts : [sota-not-workaround.md](sota-not-workaround.md).

## Voir aussi

- [docs/reference/pr-review-context.md](../../docs/reference/pr-review-context.md) — contexte, incidents, workflow ai-01, anti-patterns
- [student-pr-reviews.md](student-pr-reviews.md) — exception PRs étudiantes
- [sota-not-workaround.md](sota-not-workaround.md) · [notebook-conventions.md](notebook-conventions.md) · [anti-regression.md](anti-regression.md)
