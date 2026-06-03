# Gale-Shapley proof strategies (extracted from mmaaz-git/stable-marriage-lean)

## Source attribution

- Original repository: https://github.com/mmaaz-git/stable-marriage-lean
- Branch fetched: `main` (5 commits total; specific commit hash not exposed by GitHub raw
  endpoint at fetch time, 2026-05-15). Lean toolchain noted in our port header as v4.25.0.
- License: **NOT stated** in the repository (no `LICENSE` file, no license line in
  `README.md` or source headers as of 2026-05-15). Treat as "all rights reserved by the
  author" — this document only records the high-level proof STRATEGY (mathematical
  argument structure and lemma names), not verbatim code. No source code from the original
  repository is reproduced here.
- Files consulted via `raw.githubusercontent.com`: `StableMarriageLean/GaleShapley.lean`,
  `StableMarriageLean/Lemmas.lean`, `StableMarriageLean/Properties.lean`,
  `StableMarriageLean/README.md`.

## How the original repo is structured (vs our port)

| Original (`StableMarriageLean/`) | Our port (`stable_marriage_lean/StableMarriage/`) |
|---|---|
| `Basic.lean` — preferences, matchings, stability, `prefersOpt`, acceptability | `Definitions.lean` — `PrefProfile`, `Matching`, `IsBlockingPair`, `IsStable`, `IsManOptimal` |
| `GaleShapley.lean` — state machine: `GSState`, `step`, `runSteps`, `galeShapley`, `chooseMaxCandidate` | `GSState.lean` — `GSState`, `GSMatching`, `gsStep`, `gsRunSteps`, `gsGaleShapley`, `gsChooseMax` |
| `Lemmas.lean` — invariant defs + step/runSteps preservation lemmas | `Lemmas.lean` — same invariants, ported |
| `Properties.lean` — `galeShapley_stable`, `galeShapley_noBlockingPairs`, termination, IR | `GaleShapley.lean` — `gale_shapley_stable` etc. as **scaffolds with `sorry`** |

Important difference: the original models **incomplete preference lists** (an `acceptable`
filter, `prefersOpt`, `menAcceptableState` / `womenAcceptableState` invariants and the
`individuallyRational` theorem). Our port simplifies to **total bijective preferences** —
so the acceptability machinery is dropped, and any proof step that the original justifies
via "acceptable" is, for us, either trivial or unnecessary.

## The three intractable sorrys in our codebase

These are the `sorry`s the prover targets (`GaleShapley.lean`, DEMOS 15/16/17):

- L73 `gale_shapley_stable : ∃ μ, IsStable prof μ`
- L91 `gale_shapley_man_optimal : ∃ μ, IsManOptimal prof μ`
- L119 `gale_shapley_woman_pessimal` (Knuth 1976 lattice duality)

### 1. `gale_shapley_stable` — stability / no blocking pairs

**This is the one the original repo actually proves**, as `galeShapley_stable` (which bundles
`galeShapley_consistent`, `galeShapley_individuallyRational`, `galeShapley_noBlockingPairs`).
For our total-preferences port, consistency + no-blocking-pairs suffice (no IR needed).

**Witness.** Use `gsGaleShapley prof` (our `GSState.lean` L116) — i.e.
`(gsRunSteps prof (gsProposalBound n)).matching` — as the constructive witness `μ`. It must
first be turned from a `GSMatching` (Option-valued partial matching) into a total bijective
`Matching`. The original gets totality from termination: at `terminated`, every man is
matched. Our port would need a `GSMatching -> Matching` conversion lemma proving the final
matching is total and bijective; this conversion is currently **missing** from our
`Lemmas.lean` and is the first real obstacle.

**Key lemmas in the original (names) feeding `galeShapley_noBlockingPairs`:**
`runSteps_menProposedDownward`, `runSteps_menMatchedProposed`, `runSteps_womenBest`,
`runSteps_womenUnmatchedReject`, plus `terminated`. Our port already has the analogues:
`menProposedDownward.runSteps`, `menMatchedProposed.runSteps`, `womenBestState.runSteps`,
`womenProposedImpliesMatched.runSteps`, `GSConsistent.runSteps` — all PROVEN (see
`existing_proofs.lean`). We do NOT yet have a `womenUnmatchedReject` analogue, but with total
preferences `womenProposedImpliesMatched` plays the equivalent role.

**High-level argument (`noBlockingPairs`).** Suppose `(m, w)` is a blocking pair: `m`
prefers `w` to his partner `μ.spouse m`, and `w` prefers `m` to her partner `μ.inverse w`.
- Since `m` prefers `w` over his final partner, by `menProposedDownward` (men propose in
  decreasing preference order, and at termination `m` has exhausted his candidate set) `m`
  must have proposed to `w` at some step.
- By `menMatchedProposed` / `womenProposedImpliesMatched`, once `m` proposed to `w`, `w` was
  matched from that point on and stayed matched (matches only improve for women).
- By `womenBestState`, `w`'s final partner is at least as preferred (for `w`) as **every**
  man who ever proposed to her — including `m`. So `w` does NOT prefer `m` to her final
  partner. Contradiction with the blocking-pair assumption.
- Case-split on `w`'s match status at termination is the structural skeleton: the original
  `galeShapley_noBlockingPairs` "case-splits on w's match status".

**Tactic shape to expect.** `intro m w hblock`; `obtain` the two preference facts from
`IsBlockingPair`; derive `σ.proposed m w` from `menProposedDownward` + termination; then
`womenBestState` gives `womenPref w (final partner) ≤ womenPref w m`, contradicting the
strict `WomanPrefers w m (μ.inverse w)`. The hard sub-goal is connecting `μ.inverse w`
(Definitions-level bijection inverse) to `σ.matching.womenMatch w` (Option-valued GS state)
— that needs the `GSMatching -> Matching` conversion correctness lemma.

### 2. `gale_shapley_man_optimal` — man-optimality

**NOT proven in the original repo.** `Properties.lean` stops at stability; there is no
man-optimality theorem in `mmaaz-git/stable-marriage-lean`. So for this sorry there is **no
reference proof to port** — it has to be done from the mathematical literature
(Gale-Shapley 1962, Dubins-Freedman / Roth). The strategy below is the standard textbook
argument, reconstructed; flag it as such to the agents.

**Witness.** Same `gsGaleShapley prof` matching as in (1). `IsManOptimal` = `IsStable ∧
(∀ μ' stable, ∀ m, menPref m (μ.spouse m) ≤ menPref m (μ'.spouse m))`. The `IsStable`
conjunct is exactly theorem (1).

**High-level argument (standard "no man is ever rejected by an achievable woman").**
Define a woman `w` as *achievable* for man `m` if some stable matching pairs them. Claim: in
GS, no man is ever rejected by an achievable woman. Prove by induction on the proposal
sequence:
- Suppose, for contradiction, the first time a man `m` is rejected by an achievable woman
  `w` (he proposed, she kept/took someone `m'` she prefers). `w` achievable for `m` means
  some stable `μ'` has `μ'.inverse w = m`.
- `m'` (the man `w` kept) prefers `w` to whoever he was previously matched to in the GS run;
  and because this is the *first* rejection-by-achievable-woman, `m'` has not yet been
  rejected by any woman achievable for him — so in `μ'`, `m'`'s partner `μ'.spouse m'` is
  someone `m'` likes no more than `w`. Then `(m', w)` blocks `μ'` (m' prefers w to his μ'
  partner; w prefers m' to m = her μ' partner). Contradicts stability of `μ'`.
- Therefore no man is rejected by an achievable woman ⇒ each man ends GS with the *best*
  (lowest `menPref` rank) woman achievable for him ⇒ GS is man-optimal.

**Invariant used (our port):** `menProposedDownward` is the key — it guarantees a man's GS
partner is his most-preferred among everyone who did NOT reject him, and the argument above
shows the rejecters are exactly the non-achievable women. There is currently **no Lean
infrastructure** in our `Lemmas.lean` for the notion "achievable woman" or this induction;
this sorry is genuinely a multi-day port even with guidance.

### 3. `gale_shapley_woman_pessimal` — woman-pessimality (Knuth 1976 duality)

**NOT proven in the original repo** either. This is the Knuth 1976 lattice-duality result.
Our theorem statement is already in the convenient pointwise form:
`IsManOptimal prof μ → IsStable prof μ' → womenPref w (μ'.inverse w) ≤ womenPref w (μ.inverse w)`.

**High-level argument (the clean duality proof, by contradiction).**
- Assume `w` does strictly better under the man-optimal `μ` than under some stable `μ'`,
  i.e. `womenPref w (μ.inverse w) < womenPref w (μ'.inverse w)` — `w` strictly prefers her
  `μ` partner `m := μ.inverse w` to her `μ'` partner.
- `m` is matched to `w` in `μ`. Consider `m`'s partner in `μ'`, `μ'.spouse m`. By
  man-optimality of `μ`, `m`'s `μ` partner is his BEST achievable partner, so `m` weakly
  prefers `μ.spouse m = w` over `μ'.spouse m`. Two sub-cases:
  - If `m` strictly prefers `w` to `μ'.spouse m`: then `m` prefers `w` to his `μ'` partner,
    and `w` prefers `m` to her `μ'` partner — `(m, w)` blocks `μ'`. Contradicts stability of
    `μ'`.
  - If `m`'s `μ'` partner equals `w` (`μ'.spouse m = w`): then `μ'.inverse w = m = μ.inverse w`,
    so `w`'s partners coincide and she cannot strictly prefer one — contradicts the
    assumption.
- Either way, contradiction. Hence `womenPref w (μ'.inverse w) ≤ womenPref w (μ.inverse w)`.

**Key insight (from our `config.py` DEMO 17):** the `inverse` field swaps the man/woman
perspective — `μ.inverse w` is the man matched to `w`. The proof never re-runs the
algorithm; it only uses (a) `IsManOptimal` (the universally-quantified optimality clause)
and (b) `IsStable prof μ'` (no blocking pair). So unlike (1) and (2), this sorry needs **no
new GS-state machinery** — it is a pure consequence of the two `Def`s in `Definitions.lean`
plus careful `Fin n` rank inequality reasoning (trichotomy on the `womenPref`/`menPref`
Nat values, `lt_irrefl`, transitivity). It is the most tractable of the three for the
prover and should be attempted first.

## Summary for the Director agent

**⚠ AMENDMENT 2026-05-16 — empirical prover verdict** (cf [project_prover_c35_01_woman_pessimal](.../memory/project_prover_c35_01_woman_pessimal.md)) :

- C34-01 (L73 stable), C34-02 (L91 man_optimal), C35-01 (L119 woman_pessimal) all yielded **INTRACTABLE** within 100-250s with reference docs grounding active. The Coordinator cites the same Knuth 1976 lattice duality both as suggested strategy AND as intractability reason. The "Attack first" ordering below was **theoretical-feasibility ordering**, not empirically validated. Three sorrys are reproducibly intractable on our current prover without the upstream proofs.
- **NEW unlock (2026-05-16)** : `upstream/` directory now contains the **complete mmaaz-git Lean source** (commit `111e42c5`, v4.25.0). `Properties.lean L125` has the **full proof of `galeShapley_stable`** — translate-and-adapt path opens for DEMO 15 / L73.

**Revised priority order** (translate-and-adapt approach) :

- `gale_shapley_stable` (L73): **REFERENCE PROOF AVAILABLE** in `upstream/StableMarriageLean/Properties.lean` L125 (`galeShapley_stable`). Strategy : (1) read upstream proof structure, (2) identify lemma name mapping mmaaz → our port, (3) handle `acceptable` filter elimination (we have total bijective preferences). Most tractable now.
- `gale_shapley_man_optimal` (L91): not in upstream Properties.lean. Derive from `galeShapley_stable` + induction on `runSteps` + observation that GS gives each man his most preferred achievable woman. Hardest of the three because no reference proof exists in either codebase.
- `gale_shapley_woman_pessimal` (L119): not in upstream Properties.lean. Derive from `man_optimal` via Knuth 1976 lattice duality (stable matchings form a distributive lattice, m-optimal = w-pessimal). Empirically intractable via direct "blocking-pair contradiction" — see C35-01 verdict.
