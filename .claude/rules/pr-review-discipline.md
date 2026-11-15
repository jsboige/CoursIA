# PR Review Discipline — anti-complaisance

S'applique à **tous les reviewers**, humains et bots (clusterManager-Myia, jsboige self-bot, ai-01 coordinateur).

**Exception — PRs de TP étudiantes (mandat user 2026-05-20).** Les critères A-H ci-dessous visent les PRs **internes/contributeurs**. Les PRs **étudiantes** suivent [student-pr-reviews.md](student-pr-reviews.md) : review **bienveillante**, bypass template + CI, **pas de CHANGES_REQUESTED** sur scaffolding. Ne PAS appliquer A-H à un TP étudiant.

**Contributeurs publics.** Les critères de fond A-H restent applicables à une PR publique ordinaire, mais le triage, le ton et l'escalade suivent [public-contribution-triage.md](public-contribution-triage.md) : aider à qualifier et corriger, jamais opposer un verdict abrupt ou impersonnel. Une correction volontaire d'exercice suit en plus [exercise-example-labeling.md](exercise-example-labeling.md).

**Contexte, incidents fondateurs, workflow ai-01, anti-patterns détaillés** : [docs/reference/pr-review-context.md](../../docs/reference/pr-review-context.md).

**Provenance** : fragments déportés = lignes de la base `36c27857ad109` — [détail §Levier B](../../docs/reference/pr-review-context.md).

## Émission du verdict — un point qui tient le merge porte un marqueur (HARD, #14682)

Toute review (bot ou humaine) formulant **un point tenant le merge** porte un **marqueur reconnu** : préfixe de verdict (`[Hermes] COMMENT_WITH_CONCERNS`, `CHANGES_REQUESTED`) ou glyphe de sévérité (🟡, 🔴). L'organe B.0 (`scripts/check_unaddressed_nits.py`, `CONCERN_MARKERS`) ne lit **que** ces marqueurs : une réserve bloquante posée en prose libre **sans** marqueur lui est invisible et rend `rc=0`. **Ne pas élargir** le filet à des mots de prose : le contrat est côté émission, pas côté filet (instance #14658, mesure #14682, scan 80 PRs : [pr-review-context.md](../../docs/reference/pr-review-context.md)).

### Commentaires de diagnostic — taxonomie `[ACTION]` / `[DIAG]` / `[ASK]` (#15511 P1)

Tout commentaire agent **de diagnostic** sur une PR porte, en **première ligne non vide**, l'un des trois tags : `[ACTION]` (le commentaire porte une action — patch, rebase, rerun, fix), `[DIAG]` (diagnostic pur, sans action attachée), `[ASK]` (attente d'une décision tierce). Les commentaires **de protocole**, dont le marqueur occupe déjà la première ligne, la gardent et ne portent aucun des trois tags : dossier `[ADJOINT PREFLIGHT]` (`check_adjoint_prevalidation.py` exige le marqueur en tête), claims et livraisons (`[CLAIMED]`, `[CLAIMED-AMEND]`, `[RELEASED]`, `[DELIVERED]`), levées `[OVERRIDE]`, verdicts `[Hermes]`. Le contrat est **côté émission**, comme pour les marqueurs de verdict : un commentaire non tagué est invisible au détecteur, et le filet ne se lit pas dans la prose. L'organe B.0 (`check_unaddressed_nits.py`) bloque la PR à **plus de 3 `[DIAG]` consécutifs sans `[ACTION]` intercalé** (`DIAG-LOOP` — mesure fondatrice : [pr-review-context.md](../../docs/reference/pr-review-context.md)). La règle worker qui lie commentaire et action vit dans [feedback_comment_action_link.md](feedback_comment_action_link.md).

### Répondre à une réserve — la forme sûre (HARD, #17071)

Une réponse d'auteur qui **cite** le token de verdict ou un marqueur de prose reconnu par `CONCERN_MARKERS` (p. ex. `avant merge`) peut elle-même devenir une réserve B.0 : la PR reste bloquée **à fond réparé**. Pour le marqueur de prose, encager **ce marqueur lui-même** avec des backticks ou `« »` (formes mesurées) le neutralise ; un bloc de citation `>` ne le protège pas. Pour le token de verdict, la forme sûre reste de l'encager (backticks, `« »`, apostrophes, bloc de code) ou de le nommer en position de **mention** (`suite à ta réserve`, `verdict X` sans deux-points) — jamais le gras (forme d'**émission**), jamais le token nu (muet par résidu assumé, pas par filet), et encager un mot **voisin** ne protège rien. Table de vérité mesurée, mécanique trois couches et instances fondatrices : [pr-review-context.md](../../docs/reference/pr-review-context.md).

## Lecture de l'état des checks — à la source, dans les DEUX sens (HARD, #16765)

`statusCheckRollup` est une **liste plate non triée** qui contient toutes les jambes du head, **y compris celles supersedées** par une tentative plus récente (rouges périmés compris). **Ne jamais refuser un merge sur le premier rouge de la liste**, ni acquitter sur son premier vert : re-lire à la source `commits/<headRefOid>/check-runs` et plier **dernier `started_at` par nom** — `python scripts/check_run_state.py --pr <N>` fait la lecture (fold canonique `pr_gate.py::dedupe_latest`, contrat dossier `checks: latest-wins-green`). Un `latest` vert n'est **pas** une preuve de mergeabilité : une jambe rouge résiduelle d'une suite distincte a déjà bloqué une PR verte — le helper rend ces `residual_reds`, le verdict de merge reste `mergeStateStatus`.

## Critères CHANGES_REQUESTED obligatoires (HARD)

Un reviewer **DOIT** poster `state: CHANGES_REQUESTED` (pas COMMENTED, pas APPROVED) si **un seul** point est violé. APPROVED malgré violation = **complicité de complaisance**.

### A. Composites trop larges (split obligatoire)

| Métrique | Seuil « split required » |
|---|---|
| `additions + deletions` | > 3000 lignes hors notebooks |
| `changedFiles` | > 15 fichiers (hors `_output.ipynb` et données) |
| Features distinctes dans `## Summary` | > 4 |
| Domaines différents (ML + Lean + GenAI mêlés) | > 1 domaine |

**Fournée homogène : exemptée des seuils (décision user 2026-11-03, Q162 a).** Une PR qui applique **une seule classe de correction**, produite par un fixer déterministe et vérifiée par l'organe de cette classe, a pour plafond **une série entière**. Le body nomme le fixer, l'organe et la sortie de l'organe avant et après. Si la PR ajoute une deuxième classe ou une retouche à la main, l'exemption tombe et les seuils s'appliquent.

### A bis. PR trop fine : elle attend sa fournée (décision user 2026-11-03, Q162 b)

Le coût d'une PR se paie **par PR**, pas par ligne (mesure du 2026-11-03 : [pr-review-context.md](../../docs/reference/pr-review-context.md)). D'où deux règles :

- Une PR de **moins de 20 lignes** de diff ne s'ouvre pas seule, sauf urgence CI ou correctif bloquant. Elle rejoint la fournée de sa classe ou de sa série, par cherry-pick, et n'est jamais jetée.
- Le constat qui la motive, quand il est **petit et local**, s'écrit en **une ligne dans l'issue de série ou de famille**, et non dans une issue neuve.

Devant une PR fine, le reviewer ne commence pas par refuser. Il demande « **le geste peut-il être étendu ?** » et propose l'élargissement qui évite le saucissonnage : les fichiers voisins de la même série, les occurrences sœurs du même défaut. Le refus ne vient que si l'extension proposée est écartée sans motif.

**Symptôme répété** (PRs fines d'une même classe, une issue de tranche par PR) : le reviewer écrit la fournée dans le body de l'issue de série, de famille ou d'Epic, sous un bloc d'état daté (mesure, commande, rafraîchi à chaque fournée mergée, 7 jours au plus) ; les PRs suivantes s'y renvoient ([détail](../../docs/reference/pr-review-context.md)).

### B. Lean : preuve de progrès vérifiable

Toute PR touchant `*.lean` ou `agent_tests/prover/` **DOIT** inclure dans le body :

1. Compte de `sorry` **réel** avant/après — `python scripts/lean/count_code_sorry.py --json`, champ `distinct_code_sorry`. **Pas `grep -c sorry`** : il compte la prose, pas les preuves (mesure du 2026-08-14 : [pr-review-context.md](../../docs/reference/pr-review-context.md)).
2. Lien vers `Lake build SUCCESS` (CI ou commit local prouvable)
3. Lien vers `Proof integrity SUCCESS` (job CI `proof-integrity` → `LeanVerifier.check_axioms(module, fail_on_sorry=True)`)
4. Si refactor du prover Python : justifier pourquoi il est nécessaire au claim Lean (sinon split)

**Trois classes d'axiomes sont `forbidden`**, pas seulement le `sorry` : `native_decide.*` (réduction par le noyau natif **sans preuve** — vide le théorème), `sorryAx` (`sorry` **transitif**, qu'un `grep -c sorry` ne verra jamais), `Classical.choice` (non-constructif, souvent légitime — se whiteliste **par nom explicite**, jamais par wildcard — [pr-review-context.md](../../docs/reference/pr-review-context.md)).

**Un `proof-integrity SUCCESS` antérieur au 2026-07-28 ne prouve PAS l'absence de `native_decide`** ([pr-review-context.md](../../docs/reference/pr-review-context.md)).

**B.3 se lit « non applicable » — et s'ÉCRIT tel quel dans le body** dans deux cas, jamais sauté en silence : (a) le job n'est pas câblé sur le lake de la PR (#8677) ; (b) il l'est, mais ses `target-modules` n'atteignent pas le module modifié (#8782 — [pr-review-context.md](../../docs/reference/pr-review-context.md)). Câblage = **exactement** les workflows appelant `lean-axiom.yml` (`grep -ln 'lean-axiom' .github/workflows/*.yml`, moins le fichier lui-même). Triage : [lean-axiom-coverage.md](../../docs/reference/lean-axiom-coverage.md) ; incidents : [pr-review-context.md](../../docs/reference/pr-review-context.md).

### C. ML : multi-seed obligatoire

Toute PR claim « BEATS » / « improvement » sur métriques ML/trading **DOIT** inclure : (1) walk-forward 5-fold ; (2) **≥4 seeds** parmi 0/1/7/42/99 ; (3) **la conjonction** edge ≥ 2σ cross-seed **ET** Diebold-Mariano `dm_p_median < 0.05` — les deux, pas σ seul ([pr-review-context.md](../../docs/reference/pr-review-context.md)) — le DM portant sur une **perte de précision** (`loss_fn="mse"` ou `"mae"`) ; `loss_fn="linear"` est un **contrôle de biais**, jamais la jambe de la conjonction ; (4) comparaison à majority baseline + coûts de transaction (5bps SPY, 10bps crypto) ; (5) **pas de FAANG/Mag7** en training ; (6) verdict honnête « BEATS » / « NO BEATS » / « INCONCLUSIVE » — jamais « promising » ; (7) **rapport de biais par modèle** dans le body (`mean(e)` signé ou biais OOS, modèle ET baseline) — un edge porté par le biais (pas par la précision) se déclare comme tel.

Contre-exemples qui fondent (3) : [pr-review-context.md §C](../../docs/reference/pr-review-context.md).

Single-seed ou single-fold = **CHANGES_REQUESTED** sauf flag explicite `[POC]` dans le titre.

### D. Notebooks : preuve d'exécution réelle

1. Sortie de `papermill` ou kernel exec (coller les premières lignes)
2. Vérification 0 erreur volontaire (`grep -nE "raise NotImplementedError|assert False|1/0"`)
3. Cellules code = `execution_count: <int>` ET `outputs: [...]` cohérents (C.2)
4. Le diff ne supprime pas de cellule `# Solution` / `# Exemple résolu` sans issue référencée
4bis. **Enrichissement markdown-only : vérifier de l'œil la POSITION de chaque `### Lecture du résultat` / `### Interprétation`** — elle doit suivre la cellule de code dont l'output porte la valeur citée, jamais un id voisin. Le regard humain est l'organe ([pr-review-context.md](../../docs/reference/pr-review-context.md)). [cell-interpretation-ordering.md](cell-interpretation-ordering.md) (path-gated notebooks).
4ter. **Prose ajoutée : du contenu, pas un récit de correction** (Epic #20250). Lire ce que la PR **ajoute** en markdown : une section qui raconte la correction (corrigendum, cycle, lane, DM, réserve, horodatage, « cellule N corrigée ») au lieu d'enseigner = `CHANGES_REQUESTED`, la substance part dans le body ou l'issue. Le critère est la **part** du carnet, pas la présence d'un mot (une mention de provenance passe). Instrument : `python scripts/notebook_tools/check_activity_leak.py --diff origin/main...HEAD` (cas fondateur : [pr-review-context.md](../../docs/reference/pr-review-context.md)).
5. **PR « alignement doc-honesty » (#8052/#3801) : diagnostic C.4 obligatoire** — le body **DOIT** porter la section `## Diagnostic dérive` ([notebook-conventions.md](notebook-conventions.md)) : POURQUOI l'output a dérivé (**a** env/kernel · **b** claim antérieure fabriquée · **c** moteur upstream · **d** régression dépendance · **e** stochasticité non-seedée) + verdict `CAUSE_FIXED` / `CAUSE_DOCUMENTED_ONLY` / `CAUSE_INTRINSIC`.

**Refus si :** le body **ne contient pas** `## Diagnostic dérive` (citer #8364 en label ne suffit pas) · verdict `CAUSE_DOCUMENTED_ONLY` sur une cause **réparable par la flotte** (environnement, dépendance, clé, machine : un verdict RECOVERABLE-* de [sota-not-workaround.md](sota-not-workaround.md)), même avec une issue fille ([pr-review-context.md](../../docs/reference/pr-review-context.md)) · la valeur ré-alignée est un **nombre de perf/timing/accuracy/coût** ET le notebook est **re-exécutable localement** (règle F) : elle doit venir d'une **re-exécution fraîche**, jamais d'un byte-surgical markdown-align — enshriner un nombre qui changera au prochain passage kernel *est* la dérive que C.4 interdit. Si une re-exec est **déjà due** : **folder** l'alignement dedans ([détail](../../docs/reference/pr-review-context.md)).

6. **PRs notebook : vérifier le verdict du check-run `Output-failure ratchet (base vs PR)`** (organe `scripts/notebook_tools/check_output_failure_text.py`, **bloquant** dans `scripts/ci/fast_lane_registry.py`) — il DOIT être `success`. `TOOL_FAILURE` (bannières « `program is not installed` ») ou `MACHINE_PATH` qui **augmente** sur la PR (ex. `0 → 21`) = **régression → `CHANGES_REQUESTED`**, même si les points 1-3 passent (les bannières ne déclenchent ni `exec_count` nul ni le grep de 2). Récurrences fondatrices : [pr-review-context.md](../../docs/reference/pr-review-context.md).

7. **PRs notebook : lire le check-run `Output-collapse ratchet (base vs PR)`** (organe `scripts/notebook_tools/check_output_collapse.py`, **bloquant** dans `scripts/ci/fast_lane_registry.py` depuis T2 de #21424, #15327). Le verdict est dans le statut du check. Un finding `SIGNATURE` (sortie base substantielle remplacée par « `Execution sautee (API non configuree)` » et consœurs) = **re-exécution sans les clés → `CHANGES_REQUESTED`** : la dégradation gracieuse (`if api_ok:`) est le contournement de C.2 par la porte de secours ([pr-review-context.md](../../docs/reference/pr-review-context.md)). Un finding `MAGNITUDE` (perte d'un ordre de grandeur par cellule, non couvert par les exemptions automatiques contenu-déplacé/purge-diagnostic) exige une **justification dans le body** (allègement déclaré) — sans elle : `CHANGES_REQUESTED`.

8. **PRs notebook : lire le check-run ADVISORY `Source-collapse ratchet (base vs PR, advisory)`** (organe `scripts/notebook_tools/check_source_collapse.py`, enregistré `blocking=False` dans `scripts/ci/fast_lane_registry.py`, #15901). Le point 7 mesure la perte de **sortie**, celui-ci la perte de **source** : les deux sont indépendantes, et c'est tout l'intérêt ([pr-review-context.md](../../docs/reference/pr-review-context.md)). Un finding `MAGNITUDE` exige une **justification dans le body** (allègement déclaré) — sans elle : `CHANGES_REQUESTED`. Les exemptions automatiques (contenu déplacé vers une AUTRE cellule du **même** notebook, purge de texte de diagnostic type `CS####`/`warning`) blanchissent le signal : leur silence n'est **pas** un acquittement, et un `exempt-moved` qui ne déplace que quelques lignes doit être recontrôlé à l'œil. Le **même** check-run porte depuis #16110 le **second mécanisme** de la famille : la source survit en volume et perd sa **forme**. Un finding `STRUCTURE` signale `emptied` (la cellule avait des instructions, elle n'en a plus) et/ou `orphan-output` (elle porte une sortie qu'aucune instruction ne peut avoir produite) : le code est parti, la preuve d'exécution est restée → **restaurer la source ou retirer la sortie**, sinon `CHANGES_REQUESTED` ([pr-review-context.md](../../docs/reference/pr-review-context.md)).

**Advisory `.NET execution_count` ≠ outputs vides autorisés (#5214).** L'advisory autorise à sauter la ré-exécution **CI** seulement (pas de kernel .NET en CI) : `.NET Interactive` s'exécute **localement** sur chaque worker → une cellule .NET committée **DOIT** porter `execution_count != null` (`validate_pr_notebooks.py` FAIL sur `.NET` + `null` ; `null` toléré seulement là où l'exécution locale est impossible : QC Cloud, Lean). Verdict attendu dans le body : `EXEC_PROVED` vs `STRUCTURAL_ONLY` (refus). Récit #5214 : [pr-review-context.md](../../docs/reference/pr-review-context.md).

### E. Documentation / Admin : groupement obligatoire

PRs uniquement docs/README/CLAUDE.md/rules : un diff **fin** suit le §A bis. Le refus reste aussi la sortie pour de multiples READMEs sans cohérence entre séries.

**Feuille README — les totaux ne se mettent pas à jour à la main (arbitrage user 2026-09-24, #17029 revertée).** Ces statistiques dérivent à chaque ajout et relèvent de la **régénération du catalogue** (`CATALOG-STATUS` ; mandat user du 2026-08-04, #9377). Une PR de README dont la substance est une mise à jour de totaux = `CHANGES_REQUESTED`, quelle que soit la qualité de son audit. L'organe qui les repère est `python scripts/notebook_tools/check_prose_quantitative_claims.py --diff origin/main...HEAD` : son check-run `prose-counts` est **bloquant sur les lignes ajoutées** — un compte faux en ligne ajoutée rougit la PR ; une ligne de compte fausse se **supprime** au profit du renvoi au catalogue, elle ne se remet pas à jour. Après l'ajout d'un notebook, la PR de README livre le **corps qui le présente** : sa section (ce qu'il démontre, ses outils, sa place dans le fil de la série), ses lignes dans les tables de navigation, les acquis et les parcours — contenu fidèle au notebook, lu avant d'écrire. Une PR qui corrige un passage d'un README ne laisse pas d'incohérence ailleurs dans le fichier (listes, arbres, liens) ; corriger l'intro en laissant une liste obsolète plus bas = `CHANGES_REQUESTED` ([pr-review-context.md](../../docs/reference/pr-review-context.md)).

### F. Audit reassessment / « false positive »

DOIT documenter : (1) critère exact violé par l'audit initial (pattern cité) ; (2) méthodologie de vérification (pas « j'ai regardé visuellement ») ; (3) ≥3 cellules-types vérifiées avec preuve. Cf [audit-reassessment.md](audit-reassessment.md).

### G. QC : backtest obligatoire

Toute PR touchant `MyIA.AI.Notebooks/QuantConnect/projects/` DOIT inclure : (1) backtest run (`create_compile` + `create_backtest` via MCP) ; (2) Sharpe/CAGR/MaxDD dans le body ; (3) période OOS distincte du training.

### H. Vrai outil SOTA + problème non-trivial

Refus (`CHANGES_REQUESTED`) si :

1. **Workaround dégradé sans verdict SOTA écrit** — sortie de substitution (ASCII au lieu d'image générée, réimplémentation jouet au lieu de la lib, stub au lieu d'un appel de service, sortie fabriquée au lieu d'un backtest) **alors que l'outil réel est installable/invocable/rebranchable**, sans un des 5 verdicts (SOTA-OK / RECOVERABLE-LOCAL / RECOVERABLE-MACHINE / RECOVERABLE-USER-HAND / INTRINSIC) écrit dans le body. **Un verdict `INTRINSIC` ne s'approuve qu'après que le reviewer a vérifié lui-même sa prémisse à la source** (l'outil existe-t-il, est-il public, installable ?) : une grille remplie sur une prémisse non vérifiée n'est pas une preuve ([pr-review-context.md](../../docs/reference/pr-review-context.md)).
2. **Problème dégénéré** — moteur démontré sur un cas trivial où le SOTA équivaut à une baseline (BFS vs A* sur coût uniforme) → exiger complexification ou problème additionnel.
3. **Sortie de cellule hand-éditée** au lieu de corriger la cause + re-exécuter (Stop & Repair, [secrets-hygiene.md](secrets-hygiene.md) règle 6) — hors quantbook QC, `metadata.papermill`, et `probeAddresses` strip post-re-exec .NET.

Détail des 5 verdicts : [sota-not-workaround.md](sota-not-workaround.md).

### I. Organe neuf : avec son plan de fournées (décision user 2026-11-03, Q162 d)

Un nouvel organe (détecteur, census, garde) ne se merge qu'avec son **plan de remédiation** écrit dans le body : la lane qui corrige, le nombre de PRs de fournée prévues, l'issue qui les porte. Il doit aussi mesurer une classe de défaut **substantielle**. Un census qui ouvrirait des issues sans lane pour les traiter = `CHANGES_REQUESTED`.

## Voir aussi

- [docs/reference/pr-review-context.md](../../docs/reference/pr-review-context.md) — contexte, incidents, workflow ai-01, anti-patterns
- [student-pr-reviews.md](student-pr-reviews.md) — exception PRs étudiantes
- [sota-not-workaround.md](sota-not-workaround.md) · [notebook-conventions.md](notebook-conventions.md) · [anti-regression.md](anti-regression.md)
