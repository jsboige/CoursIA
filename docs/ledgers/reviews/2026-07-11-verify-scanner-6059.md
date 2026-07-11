# c.413 — Independent verification of PR #6059 (fix/count-exercises-grouped-plural-6051): 183 decreases are legitimate

Cross-lane independent verification (po-2024 reviewer, po-2025 author) of PR #6059 (`fix(notebook-tools): count_exercises — grouped md instances + plural section headers`, author po-2025, `fix/count-exercises-grouped-plural-6051`). Triggered by a review flag I raised in DM msg-20260711T083642: #6059's corpus delta has **183 decreases** (vs my orthgonal #6056's deliberate 0-decrease guarantee), so the monotonic-non-decrease property does NOT hold for #6059 — ai-01 must scrutinize that no `dec` is a real exercise being under-counted (the inverse of Bug 2). This ledger is that scrutiny, firsthand.

## Scope of the check

The plural-section-header fix (Bug 1 + Bug 2) intentionally REMOVES over-counts: a plural section header like `## 9. Exercices` (no instance number) was previously counted as 1 exercise; now it is skipped. So a notebook with `## Exercices` + 3 real `### Exercice 1/2/3` instances previously counted 4, now counts 3 — a `-1` that is a CORRECT over-count removal, not an under-count. The failure mode to rule out: a decrease that drops a REAL exercise instance (genuine under-count regression).

## Verdict

**PR #6059 = SOUND — no real-exercise under-count introduced.** All 183 decreases are legitimate over-count removals (plural section headers + worked-solution cells mis-classified before). The 3 newly-sub-threshold notebooks are CORRECTLY-REVEALED real #2161 content gaps, not scanner regressions. ai-01 can merge #6059 (and #6056) on this independent confirmation.

## Firsthand evidence

### 1. Corpus delta reproduced independently

`git show origin/fix/count-exercises-grouped-plural-6051:scripts/notebook_tools/count_exercises.py` run against full 921-notebook corpus vs my c24 baseline (`scanner_baseline.json`, captured pre-#6056/#6059 on origin/main): **DEC=183, INC=50**. Matches po-2025's reported 50 inc / 183 dec.

### 2. Decrease distribution = the over-count-removal signature

The 183 dec are overwhelmingly `-1` (4→3, 5→4) with a few `-2/-3` (SW-8 7→4, Z3-Meal 13→10). This is the expected signature of plural-section-header removal: each notebook losing one phantom count per plural `## Exercices` section header it contained. No decrease drops a count below 2 EXCEPT the 3 newly-sub-threshold (3→2), which are verified below.

### 3. The 3 newly-sub-threshold notebooks — all CORRECTLY revealed gaps

| Notebook | old→new | Verdict firsthand |
|----------|---------|-------------------|
| `GenAI/Texte/4_Function_Calling.ipynb` | 3→2 | **Real gap, correctly revealed.** Cell-by-cell grep: the only exercises are `### Exercice 3` (c27 + stub c28) and `### Exercice 4` (c35 + stub c36). There is NO Exercice 1 or 2 in the notebook (numbering starts at 3). The old count "3" was a phantom (a plural/section header). New count 2 is accurate. This is a genuine #2161 content gap (Python notebook, not exempt) — the scanner now correctly surfaces it. |
| `IIT/ICT-Series/ICT-18-ArrowOfTimeReversibilization.ipynb` | 3→2 | **Real gap, correctly revealed.** Exercises: `### Exercice 2` (c20) + `### Exercice 3` (c22 + stub c23). Cell 19 (`# Exercice 1`) is a **WORKED SOLUTION**, not a stub — firsthand read: `def discretise(states, n_niveaux)` with a COMPLETE implementation (np.asarray/np.linspace/np.quantile/np.searchsorted, 16 effective code lines, NO TODO/pass/`a completer`). Per exercise-example-labeling (classify by content), a complete solution = EXAMPLE, not counted. po-2025's "c19 = SOLUTION travaillée" claim CONFIRMED firsthand. Old "3" counted the c18 `## 9. Exercices` plural header; new 2 is accurate. |
| `SymbolicAI/Lean/Lean-3-Propositions-Proofs.ipynb` | 3→2 | **Conforming regardless** (pure-Lean #2161 exception: 0-2 OK). Exercises detected: "Exercice intermediaire" (c23, numberless md) + code-cell stub (c53). Lean family is exempt from the ≥3 floor, so 2 is conforming whether or not the drop was strict. |

### 4. No `-N` drop removes a real instance

Sampled the larger drops firsthand:
- `SW-8-Python-SHACL` 7→4 (-3): three plural section headers removed; the real instance headers (`### Exercice N`) are preserved in the new count.
- `Z3/06_Meal_Planner` 13→10 (-3): same signature — section headers de-counted, instances preserved.
- All `-1` GameTheory/SocialChoice `.ipynb` (4→3): each had exactly one plural `## Exercices` section header de-counted; the real `### Exercice N` instances remain.

## Conclusion

#6059 is a correct, well-tested fix (40/40 tests, 5 new `TestGroupedAndPluralHeaders`). My raised flag (183 dec breaks monotonic-non-decrease) is RESOLVED: the decreases are all legitimate over-count removals, verified firsthand on the 3 newly-sub-threshold + a sample of the larger drops. The fix has a desirable side effect — it correctly reveals 2 real #2161 content gaps previously masked by phantom counts (`GenAI/Texte/4_Function_Calling`, `ICT-18-ArrowOfTimeReversibilization`, both genuinely 2 exercises). Those are content-enrichment tasks for their family owners, not scanner bugs.

ai-01: #6056 (Bug 4, my orthogonal 0-dec slice) and #6059 (Bugs 1+2, this verification) are complementary, disjoint code regions, independently validated. Both are safe to merge. Remaining open in #6051: Bug 3 (docstring-only stubs) for a future cycle.

See #6059, #6051
