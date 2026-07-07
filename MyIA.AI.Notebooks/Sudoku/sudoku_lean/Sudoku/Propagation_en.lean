import Mathlib
import Sudoku.Basic_en

/-!
# Sudoku.Propagation — soundness of propagation rules

Issue #4055. Sudoku solvers (backtracking, OR-Tools, .NET of the `Sudoku` series)
speed up solving by **propagating** constraints: as soon as a value is placed, the
now-impossible candidates are eliminated. Two canonical rules:

- **Naked single**: a cell whose only remaining candidate is `v` must contain `v`.
- **Hidden single**: a value that can only go into a single cell of a scope must go
  there.

This module proves the **soundness** of these rules: they **remove no valid solution**
— eliminating a candidate via propagation means eliminating an assignment that **no
solution uses**. The keystone is `peer_excludes_value`: an assigned cell excludes its
value from all its peers.

**Honest framing (G.3/G.9).** The soundness of both propagation rules is proven in
full (0 `sorry`). The **Sudoku ⇔ exact cover reduction** (Knuth, 4 constraint
families), as well as completeness (do the rules suffice to solve every Sudoku? no in
general — hence backtracking), are natural milestones left **open**, deliberately
**not `sorry`-backed**: the library stays entirely `sorry`-free. The massive
computational result "17 clues minimum" is out of scope (not formalizable).
-/

namespace Sudoku_en

/-! ## Keystone: exclusion by peers -/

/-- **Keystone.** In a solution, a cell `c` carrying value `v` excludes `v` from every
    **peer** cell `c'` (same scope): `σ c' ≠ v`. This is the fundamental fact from
    which all propagation rules derive.

    **Proof** (0 `sorry`): `c` and `c'` share a scope `s`; `σ` is all-distinct on `s`,
    so `σ c = σ c'` would imply `c = c'`, contradicting `c ≠ c'` (peer definition). -/
theorem peer_excludes_value {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V]
    [DecidableEq V] (scopes : Scopes ι) (σ : Solution ι V)
    (hσ : IsSolution scopes σ) (c c' : ι) (v : V)
    (hpeer : IsPeer scopes c c') (hcv : σ c = v) :
    σ c' ≠ v := by
  obtain ⟨hcc', s, hs, hcs, hc's⟩ := hpeer
  intro hc'v
  have hcc : c = c' := hσ s hs hcs hc's (hcv.trans hc'v.symm)
  exact hcc' hcc

/-! ## Naked single -/

/-- **Naked single (soundness).** If, in a solution `σ`, every value except `v` is
    already carried by **peers** of `c` (i.e. each `w ≠ v` appears on a peer cell of
    `c`), then `σ c = v`.

    This formalizes the "naked single": cell `c` has only `v` left as a possible
    candidate (all other values are excluded by its peers), so every solution places
    `v` there. The rule removes no solution because it identifies a **forced** value.

    **Proof** (0 `sorry`): by contradiction, `σ c = w ≠ v`. By the coverage hypothesis,
    `w` appears on a peer `c'` of `c`; but `peer_excludes_value` forbids `c'` from
    carrying `σ c`. Contradiction. -/
theorem naked_single_sound {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V]
    [DecidableEq V] (scopes : Scopes ι) (σ : Solution ι V)
    (hσ : IsSolution scopes σ) (c : ι) (v : V)
    (hcover : ∀ w : V, w ≠ v → ∃ c' : ι, IsPeer scopes c c' ∧ σ c' = w) :
    σ c = v := by
  by_contra hne
  obtain ⟨c', hpeer, hc'w⟩ := hcover (σ c) hne
  exact peer_excludes_value scopes σ hσ c c' (σ c) hpeer rfl hc'w

/-! ## Hidden single -/

/-- **Hidden single (soundness).** If, in a solution `σ` of structure `scopes`, value
    `v` is present in scope `s` (`PresentIn σ s v`), that `c ∈ s`, and that `v` is
    **excluded** from every other cell `c' ∈ s` (each `c' ≠ c` has a peer carrying
    `v`), then `σ c = v`.

    This formalizes the "hidden single": within a scope, `v` can only go into `c`, so
    every solution places it there. For a "full house" scope (`|s| = |V|`), the
    `PresentIn σ s v` hypothesis is automatic (every value appears).

    **Proof** (0 `sorry`): `v` appears at `c0 ∈ s`. If `c0 ≠ c`, the exclusion
    hypothesis gives a peer `c''` of `c0` carrying `v`; but `peer_excludes_value`
    forbids `c''` from carrying `σ c0 = v`. Contradiction. Hence `c0 = c`, `σ c = v`. -/
theorem hidden_single_sound {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V]
    [DecidableEq V] (scopes : Scopes ι) (σ : Solution ι V)
    (hσ : IsSolution scopes σ) (s : Finset ι) (_hs : s ∈ scopes)
    (c : ι) (v : V) (_hcs : c ∈ s)
    (hvin : PresentIn σ s v)
    (hexcl : ∀ c' ∈ s, c' ≠ c → ∃ c'' : ι, IsPeer scopes c' c'' ∧ σ c'' = v) :
    σ c = v := by
  obtain ⟨c0, hc0s, hc0v⟩ := hvin
  by_contra hne
  have hc0c : c0 ≠ c := fun heq => hne (heq ▸ hc0v)
  obtain ⟨c'', hpeer, hc''v⟩ := hexcl c0 hc0s hc0c
  exact peer_excludes_value scopes σ hσ c0 c'' v hpeer hc0v hc''v

end Sudoku_en
