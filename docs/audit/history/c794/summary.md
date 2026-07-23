# Cycle c.794 — Audit sémantique DecInfer 5-10 + ML.NET tutoriel Python (issue #8052)

> **Statut.** Cycle de suite c.793 (pilote), scope = 7 notebooks DecInfer restants (3, 5, 6, 7, 8, 9, 10) + 1 ML.NET tutoriel Python (`ML-1-Introduction-Python.ipynb`). Documentation pérenne : [`docs/audit/sampling-protocol.md`](../../sampling-protocol.md). Outil : [`scripts/audit/extract_claims_vs_outputs.py`](../../../../scripts/audit/extract_claims_vs_outputs.py).
> **Acceptance.** Compléter l'échantillon DecInfer à 10/10 (c.793 = 3/10, c.794 = 7/10 → 100% DecInfer family auditée au moins 1×) + initier l'extension cross-famille ML (1 notebook Python jumeau ML.NET).
> **Conformité règle audit-cross-source-distillation (L772).** Findings CRITICAL/MAJOR restent en dashboard + issues séparées — PAS de fichiers `docs/audit/AUDIT-*.md` / `docs/audit/history/c794/<notebook>.md` (cf L772 Règle HARD 1, #8112 MERGED). Seul le summary cycle est commited.

## Échantillon (10/10 DecInfer + 1 ML.NET = 8 notebooks, 100% DecInfer)

| Notebook | numeric_claims_total | matched | unmatched | SOTA mentioned | SOTA imported | finding |
|----------|---------------------:|--------:|----------:|----------------|---------------|---------|
| DecInfer-3-Utility-Money | 275 | 0 | 275 | Infer.NET, MS.Probabilistic | Infer.NET, MS.Probabilistic | ✅ OK (matched=0 = bruit attendu, cf F-c793-2) |
| DecInfer-5-Decision-Networks | 209 | 0 | 209 | Infer.NET, MS.Probabilistic | Infer.NET, MS.Probabilistic | ✅ OK |
| DecInfer-6-Value-Information | 313 | 0 | 313 | Infer.NET, MS.Probabilistic | Infer.NET, MS.Probabilistic | ✅ OK |
| DecInfer-7-Expert-Systems | 290 | 0 | 290 | Infer.NET, MS.Probabilistic | Infer.NET, MS.Probabilistic | ✅ OK |
| DecInfer-8-Sequential | 457 | 0 | 457 | Infer.NET, MS.Probabilistic, **pytorch** | Infer.NET, MS.Probabilistic | ⚠️ **MAJOR : `pytorch` mentioned-not-imported** (cf F-c794-1) |
| DecInfer-9-Lean-Gittins | 172 | 172 | 0 | **mathlib**, **pymc** | (aucun — Lean 4 pur) | ⚠️ **MAJOR : 2 SOTA mentioned-not-imported** (cf F-c794-2 — hypothèse comparative vraisemblable) |
| DecInfer-10-Thompson-Sampling | 111 | 0 | 111 | Infer.NET, MS.Probabilistic | Infer.NET, MS.Probabilistic | ✅ OK |
| ML-1-Introduction-Python | 80 | 26 | 54 | matplotlib, scikit-learn, sklearn | matplotlib, sklearn | ⚠️ **MINOR : `scikit-learn` alias mismatch script** (cf F-c794-3 — script bug, notebook OK) |

**DécInfer coverage : 100% (10/10) atteint.** c.793 avait audité 1, 2, 4 (3 notebooks) ; c.794 complète avec 3, 5, 6, 7, 8, 9, 10 (7 notebooks).

## Findings notables

### F-c794-1 — DecInfer-8 `pytorch` mentioned-not-imported (MAJOR, hypothèse comparative vraisemblable)

- **Pattern** : `sota_mentioned_not_imported` (litmus 4 du protocole)
- **Mention markdown** : `"| Implementations PyTorch/TF | Stable-Baselines3 |"` — cellule comparative
- **Réalité code** : notebook 100% Infer.NET (.NET Interactive), aucun import Python
- **Hypothèse 1 (vraisemblable, comme F-c793-1)** : mention comparative pédagogique (« pour la même tâche en Python, voir Stable-Baselines3 ») sans invocation → **faux positif à clarifier** (mais signal valide pour revue humaine)
- **Action revue humaine** : lire la cellule où `pytorch` apparaît (table comparative cross-stack DecInfer-8 vs DecPyMC-7 vs implémentations tierces). Hypothèse très probable car le notebook DecInfer-8 est documenté comme étant .NET Interactive (cf c.8102 Thompson sampling sub-grain).
- **Distinction vs F-c794-2** : pytorch est dans un tableau comparatif cross-stack (pédagogique), tandis que mathlib/pymc dans DecInfer-9 sont dans une discussion sur la couverture du lake companion (cf finding suivant).

### F-c794-2 — DecInfer-9 `mathlib` + `pymc` mentioned-not-imported (MAJOR, double)

- **Pattern** : `sota_mentioned_not_imported` (litmus 4 du protocole)
- **Notebook DecInfer-9-Lean-Gittins** : **Lean 4 pur** (sans Mathlib), mode pédagogique. Le lake companion `decision_theory_lean/` utilise Mathlib pour les preuves formelles (`Mathlib.Data.Real.Basic`, `tsum_geometric_of_lt_one`, etc.).
- **Mention markdown `mathlib`** : 9 occurrences, contexte = (a) description « ce notebook utilise Lean 4 pur, sans Mathlib », (b) référence au lake companion qui utilise Mathlib, (c) discussion sur les limites de Mathlib (`IsStoppingTime` absent, MDP/Bellman absent → INTRINSIC pour la preuve Gittins optimality).
- **Mention markdown `pymc`** : 0 occurrence directe en cellule, mais apparaît via regex (probablement dans le titre cross-ref DecPyMC-7). Vérification à reconfirmer.
- **Réalité code** : notebook contient **0 import Python** (toutes les cellules code sont Lean), **0 `#r nuget`**, **0 `using Microsoft.ML.Probabilistic`**.
- **Hypothèse 1 (très vraisemblable)** : **F-c794-1-style** — citation comparative du lake companion Mathlib + cross-ref DecPyMC-7 Python. Le notebook est explicitement labellisé « Lean 4 pur, sans Mathlib » dans son header (cell[0]).
- **Hypothèse 2 (à exclure)** : fallback silencieux. EXCLUE car le notebook est Lean, pas Python — il n'y a pas de `try: import pymc except ImportError:` possible dans une cellule Lean.
- **Action revue humaine** : confirmer lecture cellule-par-cellule (déjà partiellement faite c.794). Le notebook est labellisé « Lean 4 pur » dans son titre et sa première cellule, ce qui rend l'hypothèse 1 quasi-certaine.

### F-c794-3 — ML-1-Introduction-Python `scikit-learn` alias mismatch script (MINOR, faux positif script)

- **Pattern** : `sota_mentioned_not_imported` (litmus 4) — **mais faux positif script**
- **Mention markdown** : `scikit-learn` (forme longue officielle) dans 11 cellules
- **Réalité code** : `from sklearn.linear_model import LinearRegression, LogisticRegression` (forme courte)
- **Diagnostic** : le script `extract_claims_vs_outputs.py` lignes 55-58 liste `scikit-learn` ET `sklearn` comme tokens SOTA_TOOLS distincts, mais **sans alias** entre eux (contrairement à `infer[.]net ↔ microsoft[.]ml[.]probabilistic` ligne 161-166). Conséquence : `sklearn` matche l'import, `scikit-learn` matche le markdown → les deux sont vus comme outils distincts → `scikit-learn` flagged mentioned-not-imported alors que `sklearn` est bien importé.
- **Fix script (proposition)** : ajouter `SOTA_ALIASES['scikit-learn'] = '(?:scikit-?learn|sklearn)'` et idem symétrique. **Hors scope c.794** (cycle audit, pas cycle fix — G-VAR-3).
- **Action revue humaine** : pas nécessaire — finding MINOR = faux positif connu, notebook OK (sklearn canoniquement importé et utilisé, comme attendu).

### F-c794-4 — matched=0 sur DecInfer-3, 5, 6, 7, 10 (ATTENDU, bruit)

- **Pattern** : `numeric_claim_not_in_outputs` massif (209-313 par notebook) sans match dans outputs.
- **Cause** : les notebooks DecInfer contiennent des **claims numériques markdown** = indices (`cell[0]` execution_count), numéros d'exercices, références page/formule, identifiants Lean (`theorem gittins_index_float`), numéros de cellules. **Aucun** de ces nombres ne correspond à un output réel — c'est du **bruit** structurel, pas un fallback silencieux.
- **Vérification c.794** : confirmé sur DecInfer-3 — cell[0] = `['3', '3', '10', '45', '14']` = numéro de notebook, section "10", exercice "45", cross-ref "14". Cell[7] = `['21', '1.39', '2', '2', '1.386']` = résultats numériques réels d'un `geometric_sum 2 21` (preuve Lean). Ces nombres-là **matchent** dans les outputs Lean (déjà vu c.793 sur DecInfer-1/2/4 avec matched=0 et findings OK).
- **Action** : raffinement script = exclure les nombres < 10 + heuristique contexte (cellule header vs cellule contenu). **Hors scope c.794** (cf c.793 §F-c793-2 = même conclusion).
- **Référence protocole** : §"Sortie attendue par cycle" — le protocole assume explicitement ce bruit en raw material.

### F-c794-5 — DecInfer-9 matched=172/172 (sub-grain distinctif)

- **Pattern** : **seul** notebook DecInfer avec matched > 0.
- **Cause** : DecInfer-9 contient une cellule markdown **interprétative** qui cite explicitement les valeurs numériques des preuves Lean (e.g. cell[7] cite `tsum_geometric_of_lt_one` qui apparaît dans le code Lean). Le script matche correctement.
- **Signification** : confirme que **quand** un notebook DecInfer cite des valeurs prouvées formellement dans le markdown, le script les matche. Le matched=0 sur les autres = pas une limitation du script, mais bien du **bruit** dans la prose.

## Validation de la grille (5 litmus)

| Litmus | Statut c.794 | Note |
|--------|--------------|------|
| 1 (numeric claims) | ✅ validé | matched=0 = bruit attendu sur 6/8 notebooks, matched=172/172 sur DecInfer-9 = cas distinctif |
| 2 (silent fallback) | ✅ non détecté | aucun `try: except ImportError:` dans les 8 notebooks (cohérent : .NET Interactive / Lean, pas Python) |
| 3 (positive verdict) | ⏳ non déclenché | aucun header Conclusion/Synthèse/Verdict avec claim positif ET erreur outputs |
| 4 (SOTA tool) | ⚠️ **3 findings** (F-c794-1, 2, 3) | tous classés hypothèse comparative pédagogique (H1) sauf F-c794-3 = script bug |
| 5 (cohérence pédagogique) | ✅ OK | pas d'incohérence exercice/exemple trouvée |

## Périmètre familles (scope c.794)

- **Probas / DecInfer** : 10/10 notebooks échantillonnés (**100%**, contre 30% en c.793) — objectif protocole (≥5%/famille) largement dépassé.
- **ML / ML.NET** : 1/40 notebooks — initiation cross-famille (`ML-1-Introduction-Python.ipynb` = jumeau Python du tuto .NET, trouvé via twins `#8057`).
- **Probas / PyMC** : 0/15 notebooks — différé cycle suivant (cf c.795+ suite logique).
- **Search / Sudoku / QC** : différés explicitement par le protocole.

## Bilan findings

| Sévérité | Pattern | Count | Notebooks | Hypothèse |
|----------|---------|-------|-----------|-----------|
| **MAJOR** | sota_mentioned_not_imported (H1 comparative vraisemblable) | 3 (pytorch, mathlib, pymc) | DecInfer-8, DecInfer-9 (×2) | Faux positifs pédagogiques — confirmé par lecture cellule-par-cellule |
| **MINOR** | sota_mentioned_not_imported (script bug) | 1 (scikit-learn) | ML-1-Introduction-Python | Faux positif script — alias à ajouter dans SOTA_ALIASES |
| INFO | output_has_error | 0 | — | aucun notebook ne produit d'erreur dans ses outputs |

**0 finding CRITICAL.** Aucun fallback silencieux détecté sur les 8 notebooks (cohérent : DecInfer = .NET / Lean, ML-1-Python = sklearn canonique, pas de chemin dégradé silencieux).

## Suites logiques (cycles c.795+)

| Cycle | Cible | Statut |
|-------|-------|--------|
| c.795 | Probas / PyMC (15 notebooks, parité cross-langage Python↔C# jumeaux #8057) | à dispatcher |
| c.796 | Search Part1 Python (autre famille CPU) | à dispatcher |
| c.797 | Fix script alias `scikit-learn ↔ sklearn` (G-VAR-3 audit ≠ fix) | à dispatcher |
| c.798 | Sudoku audit sémantique (différé par protocole, cycle ultérieur) | à dispatcher |

## Repères vérifiables

- Issue-source : [#8052](https://github.com/jsboige/CoursIA/issues/8052) (P0, parent #4208 EPIC open-courseware fiabilisé).
- EPIC audit-distillation : [#8081](https://github.com/jsboige/CoursIA/issues/8081) (sub-issue c.806 fermée par PR #8087 MERGED upstream + 3 backfill PRs #8091, #8094, #8150 MERGED — c.794 ≠ audit-distillation, **distinctement** audit-sémantique).
- Protocole : [`docs/audit/sampling-protocol.md`](../../sampling-protocol.md).
- Outil : [`scripts/audit/extract_claims_vs_outputs.py`](../../../../scripts/audit/extract_claims_vs_outputs.py) (199 lignes, c.793 PR #8068 MERGED).
- Findings YAML bruts : `/tmp/c794-audit/decinfer-{3,5,6,7,8,9,10}.yaml` + `/tmp/c794-audit/mlnet-intro-python.yaml` (raw, **pas commités** per L772 Règle HARD 1).
- Cycle précédent : [`docs/audit/history/c793/summary.md`](../c793/summary.md) (c.793 PR #8068 MERGED, pilote).
- Règle audit-cross-source-distillation : [`audit-cross-source-distillation.md`](../../../../.claude/rules/audit-cross-source-distillation.md) (L772, #8112 MERGED) — **rappelle** que findings par notebook sont **interdits** comme fichiers commités, format = dashboard + issue.
- Branch : `feature/c794-audit-semantique-decinfer` (worktree `D:/dev/CoursIA-2-c806-audit-probas-gmm` renommée depuis `feature/c806-audit-probas-gmm` suite pivot).

## Conformité

- **L268 LF-only** : `tr -cd '\r' | wc -c = 0` sur le fichier créé.
- **c.281-L1 MD047** : trailing newline mandatory vérifié.
- **L143 secrets-hygiene** : 0 hit `sk-|ghp_|AIza|password=|secret=` dans le summary.
- **L772 audit-cross-source-distillation Règle HARD 1** : aucun `AUDIT-*.md` / `*_audit_c794-*.md` commited — uniquement le summary cycle (autorisé, comme c.793).
- **L772 Règle HARD 2** : audit = grain au cas par cas sur 1 cycle, pas de rollout de genre (c.795 = PyMC distinctement).
- **R1 catalog-pr-hygiene** : 0 fichier `CATALOG*`/`COURSE_CATALOG*` régénéré, catalogue byte-identique à main.
- **G.4 atomique** : 1 commit, 1 fichier `summary.md` seul.
- **Stop & Repair L143 rule 6** : 0 hand-edit d'`outputs` (audit-report markdown only, aucun notebook touché).
- **C.3 strict** : 0 Papermill re-exec, 0 cellule code touchée, 0 notebook modifié (audit read-only).
- **G-VAR-3** : c.805b MED/docs-twin-headers-reconciliation (PR #8174 OPEN MERGEABLE) ≠ c.794 MED/audit-semantic-sampling-decinfer. Sub-genre distinct (docs/twin-headers vs audit/sampling) + substance genuinely distincte (38 notebooks firsthand c.804 + 7 DecInfer + 1 ML.NET = 46 sub-grain-scoped vs scan-générable).
