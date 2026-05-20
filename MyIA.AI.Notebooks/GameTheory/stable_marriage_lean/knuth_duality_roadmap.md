# Knuth Lattice / Duality Roadmap for StableMarriage

**Issue:** #1188
**Date:** 2026-05-19
**Status:** 3 sorry remaining in Lattice.lean (L130 no_cross_match, L437 meetSpouse, L777 doctor_optimal)
**Total project sorrys:** 6 (3 Lattice + 2 GaleShapley INTRACTABLE + 1 hCore + 0 Shapley)

> **Update (2026-05-19 Sprint D):** The `no_cross_match` lemma has been re-added to Lattice.lean
> at L102-130 with the m₁=m₂ sub-case proved and 3-distinct-women derivation established.
> The general case (m₁≠m₂, 3 distinct women) is confirmed INTRACTABLE by both manual analysis
> and Sonnet multi-agent prover (1400s, 0 progress). Root cause: cross-pair stability constraints
> involve unknown men (μ⁻¹(w₂), ν⁻¹(w₁)) producing unconstrained preference variables.
> **Requires rural hospitals theorem (Knuth 1.6.3) or lattice-theoretic global argument.**
> The L437 sorry now calls `no_cross_match` (also unproved). L777 needs GS execution.

## Current State

### Proved (0 sorry)
- ManLE refl/trans/antisymm (partial order)
- joinSpouse_injective (join produces a bijection)
- meetSpouse_injective same-woman sub-cases
- meet_inverse_anti_pref (FULLY proved)
- meet_inverse_anti_pref' (FULLY proved)
- join_isStable (stability of join)
- meet_isStable (stability of meet)
- join_inverse_anti (join anti-complementarity)

### Remaining Sorrys (3)

#### S1: L130 — no_cross_match (anti-crossing lemma)
**Context:** `no_cross_match` lemma at L102-130. If μ.sp m₁ = w and ν.sp m₂ = w, then μ.sp m₂ = ν.sp m₁. This is Knuth's decomposition lemma (anti-crossing property).

**Proved sub-cases:**
- m₁ = m₂: trivial (subst + rw)
- 3-distinct-women derivation: w ≠ ν.sp m₁ and w ≠ μ.sp m₂ proved via injectivity

**INTRACTABLE (confirmed Sprint D, 2026-05-19):**
Applied stability of μ, ν to all 4 relevant pairs: (m₁,w), (m₂,w), (m₁,w₂), (m₂,w₁). The pairs (m₁,w) and (m₂,w) give useful constraints with known inverses (μ⁻¹(w)=m₁, ν⁻¹(w)=m₂). But cross-pairs (m₁,w₂) and (m₂,w₁) involve μ⁻¹(w₂) and ν⁻¹(w₁) which are unknown men — preference variables remain unconstrained. Both manual analysis and Sonnet multi-agent prover (1400s, 8 iterations, Director enabled) confirm: local stability conditions are insufficient.

**Classification:** INTRACTABLE_UNTIL_RURAL_HOSPITALS

**Strategy (future):**
1. **Rural hospitals theorem**: Prove unmatched agents are the same across all stable matchings. In our perfect matching setting, this gives structural constraints that resolve the cross-pair unknowns.
2. **Decomposition lemma**: Show stable matchings decompose into cycles where partners permute — directly implies anti-crossing.
3. **Lattice argument**: Use join/meet properties (already proved) to derive no-cross structurally.

#### S2: L437 — meetSpouse symmetric "different women" cross-case

**Context:** Symmetric to S1 but with the roles of mu and nu swapped in the case analysis. The sorry now calls `no_cross_match` (which is itself unproved).

**Classification:** INTRACTABLE_UNTIL_RURAL_HOSPITALS (shares blocker with S1)

**Strategy:** Once `no_cross_match` is proved via rural hospitals, this sorry resolves immediately.

#### S3: L727 — doctor_optimal_eq_top
**Context:** The GS man-proposing output is the bottom of the ManLE lattice: every man gets his best achievable stable partner.

**Blocker:** Requires executing the GS algorithm and proving no stable matching gives any man a better partner. This is Knuth's Theorem 1.6.1.

**Strategy:**
1. **GS algorithm execution**: Use our `GaleShapley.galeShapley` definition to get a concrete matching
2. **Inductive invariant**: At each GS step, the current matching is man-optimal among all matchings reachable by the proposals made so far
3. **Key lemma needed**: `gs_step_optimal`: If sigma is a state where men have proposed downward (only to their best remaining candidate), then no stable matching gives any man a better partner than sigma.matching
4. **Downward-closure**: Already proved in upstream as `menProposedDownwardState` and `runSteps_menProposedDownward`

**Estimated difficulty:** VERY HARD (requires GS execution + inductive invariant, essentially new file worth of lemmas)

## Wu-Roth Phasage

### Phase 1: Rural Hospitals (unblocks S1, S2)
Port Knuth's rural hospitals theorem to our Fin n setting:

```
theorem rural_hospitals (mu nu : Matching n)
    (hmu : IsStable prof mu) (hnu : IsStable prof nu) :
    ∀ m, mu.spouse m = nu.spouse m ∨
      prof.manPrefers m (mu.spouse m) (nu.spouse m) ∨
      prof.manPrefers m (nu.spouse m) (mu.spouse m) := ...
```

Actually, rural hospitals in one-to-one says: the set of matched agents is the same across all stable matchings. In our perfect matching setting (bijections), this is trivially true (all agents matched). The real content is that in many-to-one, the same hospitals get the same number of doctors. For one-to-one with perfect matchings, the relevant lemma is:

```
theorem lattice_join_meet_cross (mu nu : Matching n)
    (hmu : IsStable prof mu) (hnu : IsStable prof nu)
    (m1 m2 : Fin n) (w1 w2 : Fin n)
    (hw1 : mu.spouse m1 = w1) (hw2 : nu.spouse m1 = w2)
    (hw1' : nu.spouse m2 = w1) (hw2' : mu.spouse m2 = w2)
    (hne : w1 != w2) :
    False := ...
```

This says: if mu assigns m1->w1 and m2->w2, and nu assigns m1->w2 and m2->w1, then stability forces w1 = w2 (contradiction). This is the "no crossing" property of stable matchings.

**Proof sketch:**
- mu stable: w1 doesn't block with m2 (she already has m1 who she prefers to m2, or she prefers m2 to m1)
- nu stable: w2 doesn't block with m1 (similarly)
- By stability of mu and nu, and the fact that m1 and m2 swap partners, we get women's preference constraints that lead to a contradiction

**Dependencies:** IsStable definition (blocking pair), manPrefers/womanPrefers

### Phase 2: doctor_optimal (unblocks S3)
Prove the GS output is the man-optimal stable matching:

```
theorem gs_man_optimal (mu_gs : Matching n)
    (hgs : IsStable prof mu_gs)
    (hgs_algo : mu_gs = GaleShapley.galeShapley prof)
    (mu' : Matching n) (hstable : IsStable prof mu') :
    ManLE prof mu_gs mu' := ...
```

**Proof approach (Knuth 1976, Theorem 1.6.1):**
1. Prove by contradiction: suppose some man m gets a worse partner in mu_gs than in mu'
2. In the GS algorithm, m proposed to every woman he prefers over his mu_gs partner
3. By downward-closure (already proved), all these women rejected m
4. Each rejection means the woman had a better partner at that point
5. By induction, each woman's final GS partner is at least as good as any proposer she rejected
6. So mu'.spouse m is matched in GS to someone she prefers over m
7. This contradicts mu' being a matching (m's mu' partner is already taken by someone she prefers)

**Dependencies:** GaleShapley module, downward-closure invariant, womenBest invariant

### Phase 3: Distributive Lattice Instance (future)
Once S1-S3 resolved:
- Prove join and meet distribute: `mu.join nu |.meet sigma = (mu.meet sigma).join (nu.meet sigma)`
- Instantiate `Lattice (StableMatching prof)` with distributive instance
- Prove the lattice is complete (finite set of stable matchings has sup/inf)

## Upstream Reference (mmaaz-git)

The upstream at `prover/session_state/reference_docs/stable_marriage/upstream/StableMarriageLean/` contains:
- `Basic.lean`: Preferences, Problem, Matching, blocking pair, stable
- `GaleShapley.lean`: GS state, step function, runSteps, galeShapley
- `Lemmas.lean`: All invariants (proposedCount, acceptable, downward-closure, womenBest, etc.)
- `Properties.lean`: Consistency, termination, individual rationality, no blocking pairs, stability

Key upstream lemmas we can reference for our port:
1. `runSteps_menProposedDownward` — men propose downward in preferences
2. `runSteps_womenBest` — women's current match is best among proposers
3. `runSteps_menMatchedProposed` — matched men have proposed to their match
4. `runSteps_womenUnmatchedReject` — unmatched women reject unacceptable proposers
5. `galeShapley_stable` — GS output is stable

These are Mathlib-dependent (Classical.choose, Finset.filter, etc.) and need translation to our Fin n setting.

## Key Lemmas to Port (Priority Order)

### 1. `no_cross_match` (unblocks S1, S2)
```
lemma no_cross_match (mu nu : Matching n)
    (hmu : IsStable prof mu) (hnu : IsStable prof nu)
    {m1 m2 w : Fin n}
    (h1 : mu.spouse m1 = w) (h2 : nu.spouse m2 = w) :
    mu.spouse m2 = nu.spouse m1 := ...
```
If two stable matchings share a woman's partner, the other partners are also shared. This is the "anti-crossing" property.

### 2. `gs_man_optimal` (unblocks S3)
Already described above. Requires GS execution trace.

### 3. `woman_pessimal_of_man_optimal`
Dual of doctor_optimal: the man-optimal matching is woman-pessimal.
```
theorem woman_pessimal_of_man_optimal (mu_gs : Matching n)
    (hgs : IsStable prof mu_gs) (hopt : ...)
    (mu' : Matching n) (hstable : IsStable prof mu') :
    ManLE (swapPrefs prof) mu' mu_gs := ...
```

### 4. `join_meet_distributive`
```
theorem join_meet_distributive (mu nu sigma : Matching n)
    (hmu : IsStable prof mu) (hnu : IsStable prof nu) (hsigma : IsStable prof sigma) :
    (mu.join hmu hnu).meet hsigma ... =
      (mu.meet hmu hsigma).join ... (nu.meet hnu hsigma) := ...
```

### 5. `stable_set_finite` / `stable_set_card`
```
theorem stable_set_card_le (prof : PrefProfile n) [NeZero n] :
    { mu : Matching n // IsStable prof mu }.Finite ∧
    Finset.card { mu : Matching n // IsStable prof mu } ≤ 2^(n^2) := ...
```

## File Organization Plan

```
StableMarriage/
  Definitions.lean     -- core types (existing)
  GSState.lean         -- GS algorithm state (existing)
  GaleShapley.lean     -- GS algorithm + INTRACTABLE sorrys (existing)
  Lemmas.lean          -- GS invariants (existing, 0 sorry)
  Lattice.lean         -- lattice structure (existing, 3 sorry)
  RuralHospitals.lean  -- NEW: no-cross, rural hospitals lemmas
  ManOptimal.lean      -- NEW: GS man-optimal proof (depends on RuralHospitals + GSState)
```

## Timeline Estimate

| Phase | Task | Difficulty | Time |
|-------|------|-----------|------|
| P1 | no_cross_match lemma | MEDIUM | 2-3h |
| P1 | Resolve S1, S2 via no_cross | EASY (after lemma) | 30min |
| P2 | GS execution trace invariants | HARD | 4-6h |
| P2 | doctor_optimal proof | VERY HARD | 6-8h |
| P2 | Resolve S3 | EASY (after proof) | 15min |
| P3 | Distributive lattice instance | MEDIUM | 3-4h |

**Total estimated:** 16-23h of focused Lean proving work.

## Proof Attempt: no_cross_match (P1)

This is the most impactful lemma — it resolves 2/3 sorrys. Let me attempt a Lean 4 proof sketch.

```lean
/-- Anti-crossing: if mu assigns m1->w and nu assigns m2->w,
    then mu assigns m2 to whoever nu assigns m1 to. -/
lemma no_cross_match (mu nu : Matching n)
    (hmu : IsStable prof mu) (hnu : IsStable prof nu)
    {m1 m2 w : Fin n} (hm1 : mu.spouse m1 = w) (hm2 : nu.spouse m2 = w) :
    mu.spouse m2 = nu.spouse m1 := by
  have hm1' := mu.bijective.2 hm1
  have hm2' := nu.bijective.2 hm2
  -- Both matchings have w matched to someone
  -- mu: m1 <-> w, nu: m2 <-> w
  -- We need: mu.spouse m2 = nu.spouse m1
  -- Let w1 = nu.spouse m1, w2 = mu.spouse m2
  -- Suppose w1 != w2 (toward contradiction)
  by_contra hne
  -- mu: m1 <-> w, m2 <-> w2
  -- nu: m1 <-> w1, m2 <-> w
  -- Since mu is stable, (m2, w) is not a blocking pair in mu
  -- But mu.spouse m2 = w2 and mu.spouse m1 = w
  -- For (m2, w) to not block mu: either m2 doesn't prefer w to w2, or w doesn't prefer m2 to m1
  have hblock_mu := hmu.2.2 m2 w  -- not a blocking pair in mu
  have hblock_nu := hnu.2.2 m1 w1  -- not a blocking pair in nu
  sorry  -- Need stability conditions to derive contradiction
```

The key insight is: stability of mu says (m2, w) doesn't block mu, and stability of nu says (m1, w1) doesn't block nu. With the crossing structure, these give contradictory preference constraints.

**Manual proof:**
- Let w1 = nu.spouse m1, w2 = mu.spouse m2 (w1 != w2, w != w1, w != w2 possible)
- mu stable, pair (m2, w): either m2 prefers w2 to w, or w prefers m1 to m2
- nu stable, pair (m1, w): either m1 prefers w1 to w, or w prefers m2 to m1
- Case 1: m2 prefers w2 to w AND m1 prefers w1 to w
  - nu stable, pair (m1, w2): since m1 prefers w1 to w, and w1 != w2...
  - This gets complicated. Need more careful case analysis.

Actually, the standard proof uses the "decomposition lemma" (Knuth): the set of stable matchings can be decomposed into cycles, and within each cycle, the matchings agree on which men are matched to which women (just permuted). This is deeper than a simple case analysis.

**Revised strategy for P1:** For n <= 2, do case analysis (decidable). For general n, prove the no-cross lemma via the anti-complementarity of join/meet (already partially proved in our meet_inverse_anti_pref).

## Conclusion

The 3 Lattice sorrys are interconnected:
- S1, S2 share a blocker (no-cross / rural hospitals)
- S3 is independent but harder (needs GS execution)

Priority: S1+S2 first (smaller scope, higher chance of success with current prover), then S3.
