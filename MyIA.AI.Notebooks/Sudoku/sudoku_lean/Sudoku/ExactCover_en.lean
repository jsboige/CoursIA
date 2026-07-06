import Mathlib
import Sudoku.Basic_en

-- The section variable `[Fintype V] [DecidableEq V]` is required by the
-- "full house" milestone lemmas (`toSelection_scopeVal_unique`,
-- `solution_imp_exact_cover` via `full_house_present` which cites `Fintype.card V`)
-- but not by the structural lemmas (`toSelection`, `mem_toSelection_iff`,
-- `toSelection_cell_unique`) which only mobilize the image structure on `ι`.
set_option linter.unusedSectionVars false

/-!
# Sudoku.ExactCover — Sudoku ⇔ exact cover reduction (Knuth)

Issue #4055 (remaining milestone after `Propagation.lean`). **Exact cover**
(exact cover, Knuth 2000, "Dancing Links") is the canonical encoding of a Sudoku into
a universal problem: we express each Sudoku constraint as an "element" to be covered,
each possible placement `(cell, value)` as an option covering a small subset of
elements, and a Sudoku solution as an **exact cover** — a selection of options where
each element is covered **exactly once**.

## The encoding (Knuth, 4 constraint families)

For a concrete Sudoku (9×9), the universe of constraints counts `4 × 81 = 324`
elements split into 4 families:

1. **Cell** — `cell c`: "cell `c` receives exactly one value" (81 constraints);
2. **Row** — `scopeVal ℓ v`: "row `ℓ` contains value `v`";
3. **Column** — likewise;
4. **Block** — likewise.

In our abstract framework (`Sudoku.Basic`), families 2–4 merge into a single one:
`scopeVal s v` for a scope `s ∈ scopes`. The constraint universe reduces to two
families: `cell c` and `scopeVal s v`.

An option `(c, v) : ι × V` covers `{cell c} ∪ {scopeVal s v | s ∈ scopes, c ∈ s}`.
The selection associated with an assignment `σ` is `toSelection σ = {(c, σ c) | c}`.

## Result

The capstone theorem `sudoku_iff_exact_cover` (under the "full house" hypothesis
`∀ s ∈ scopes, s.card = card V`, satisfied by the 9×9 Sudoku where each scope has 9
cells for 9 values) establishes the **complete equivalence** between solving the
Sudoku and solving an exact-cover problem:

  `(∃ σ, IsSolution scopes σ) ↔ (∃ sel, IsExactCover sel scopes)`.

**Forward direction** `solution_imp_exact_cover` — a solution is an exact cover:

- Each **cell** is covered exactly once — by construction of `toSelection` (one option
  `(c, σ c)` per cell), via `mem_toSelection_iff`.
- Each **(scope, value)** is covered **at most** once — this is exactly `AllDistinctOn`
  (the definition of `IsSolution`);
- and **at least** once — by the full house lemma `full_house_present`
  (`Sudoku.Basic`), which says that in a full scope every value appears.

**Backward direction** `exact_cover_imp_solution` — an exact cover yields a solution:
the reconstructed assignment `fromSelection` (the unique value of each cell) is
all-distinct on each scope, since two cells of the same scope carrying the same value
would violate the `∃!` uniqueness of the (scope, value) pair; and its selection gives
back exactly `sel` (`toSelection_fromSelection`).

**Honest framing (G.3/G.9).** The equivalence is proven in full (0 `sorry`). The
axioms are the standard Lean 4 kernel trio (`propext`, `Classical.choice`,
`Quot.sound`) — `Classical.choice` shows up for the non-constructive construction
`fromSelection` (extracting a witness per cell from the cover `∃!`), as in any
Mathlib-dependent proof; no ad hoc axiom. The massive computational result "17 clues
minimum" remains out of scope (not formalizable).
-/

namespace Sudoku_en

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V]

/-- A selection of placements (cell, value) — the analogue of a subfamily of options
    in Knuth's encoding. -/
abbrev ExactCover.Sel (ι V : Type*) := Finset (ι × V)

/-- `sel` is an **exact cover** of the structure `scopes` if each cell is covered
    exactly once (a single value per cell) AND each (scope, value) pair — for every
    declared scope — is covered exactly once (a single cell of the scope carries the
    value). -/
def ExactCover.IsExactCover (sel : Sel ι V) (scopes : Scopes ι) : Prop :=
  (∀ c : ι, ∃! v : V, (c, v) ∈ sel) ∧
  (∀ s ∈ scopes, ∀ v : V, ∃! c : ι, c ∈ s ∧ (c, v) ∈ sel)

/-- The selection associated with an assignment `σ`: one placement `(c, σ c)` per
    cell. By construction, each cell appears there exactly once. -/
def toSelection (σ : Solution ι V) : ExactCover.Sel ι V :=
  Finset.univ.image (fun c : ι => (c, σ c))

/-- **Membership characterization.** `(c, v)` is in the selection associated with `σ`
    if and only if `v = σ c`. This is the key lemma that reduces any question about the
    selection to a question about `σ` itself. -/
theorem mem_toSelection_iff (σ : Solution ι V) (c : ι) (v : V) :
    (c, v) ∈ toSelection σ ↔ σ c = v := by
  constructor
  · intro h
    rw [toSelection, Finset.mem_image] at h
    obtain ⟨x, -, hx⟩ := h
    injection hx with h1 h2
    subst h1
    exact h2
  · intro h
    rw [toSelection, Finset.mem_image]
    refine ⟨c, Finset.mem_univ _, ?_⟩
    rw [h]

/-! ## Forward direction: a solution is an exact cover -/

/-- **Cell covered exactly once.** In `toSelection σ`, each cell `c` receives a unique
    value (`σ c`) — the cell-exhaustiveness of the encoding, by construction. -/
theorem toSelection_cell_unique (σ : Solution ι V) (c : ι) :
    ∃! v : V, (c, v) ∈ toSelection σ := by
  refine ⟨σ c, (mem_toSelection_iff σ c (σ c)).mpr rfl, ?_⟩
  rintro v hv
  exact ((mem_toSelection_iff σ c v).mp hv).symm

/-- **(scope, value) pair covered exactly once (solution + full house).** If `σ` is
    all-distinct on `s` and `s` is full (`s.card = card V`), then for any value `v`
    there is a **unique** cell `c ∈ s` carrying `v`: existence by the full house lemma
    (`full_house_present`), uniqueness by `AllDistinctOn` (injectivity). -/
theorem toSelection_scopeVal_unique (σ : Solution ι V) (s : Finset ι) (v : V)
    (hcard : s.card = Fintype.card V) (hAD : AllDistinctOn σ s) :
    ∃! c : ι, c ∈ s ∧ (c, v) ∈ toSelection σ := by
  obtain ⟨c, hcs, hσcv⟩ := full_house_present σ s v hcard hAD
  refine ⟨c, ⟨hcs, (mem_toSelection_iff σ c v).mpr hσcv⟩, ?_⟩
  rintro c' ⟨hc's, hcv'⟩
  rw [mem_toSelection_iff] at hcv'
  exact hAD hc's hcs (hcv'.trans hσcv.symm)

/-- **Forward direction of the equivalence.** A solution of a "full house" structure
    (every scope has as many cells as values — the 9×9 Sudoku case) is an exact cover
    in Knuth's sense. -/
theorem solution_imp_exact_cover (scopes : Scopes ι) (σ : Solution ι V)
    (hσ : IsSolution scopes σ)
    (hfull : ∀ s ∈ scopes, s.card = Fintype.card V) :
    ExactCover.IsExactCover (toSelection σ) scopes :=
  ⟨fun c => toSelection_cell_unique σ c,
   fun s hs v => toSelection_scopeVal_unique σ s v (hfull s hs) (hσ s hs)⟩

/-! ## Backward direction: an exact cover is a solution -/

/-- **Inverse construction.** From a selection where each cell is covered exactly once,
    we recover the assignment: the unique value carried by each cell. Non-constructive
    (extracting a witness per cell from the cover `∃!`) — relies on the
    `Classical.choice` axiom. -/
noncomputable def fromSelection (sel : ExactCover.Sel ι V)
    (hcell : ∀ c : ι, ∃! v : V, (c, v) ∈ sel) : Solution ι V :=
  fun c => Classical.choose (ExistsUnique.exists (hcell c))

/-- Cell `c` indeed carries its reconstructed value in `sel`. -/
theorem fromSelection_mem (sel : ExactCover.Sel ι V)
    (hcell : ∀ c : ι, ∃! v : V, (c, v) ∈ sel) (c : ι) :
    (c, fromSelection sel hcell c) ∈ sel :=
  Classical.choose_spec (ExistsUnique.exists (hcell c))

/-- **Dual characterization of `mem_toSelection_iff`.** `(c, v)` is in `sel` if and
    only if the reconstructed value of `c` equals `v` — by uniqueness of the value
    covering `c`. -/
theorem mem_fromSelection_iff (sel : ExactCover.Sel ι V)
    (hcell : ∀ c : ι, ∃! v : V, (c, v) ∈ sel) (c : ι) (v : V) :
    (c, v) ∈ sel ↔ fromSelection sel hcell c = v := by
  refine ⟨fun hcv => ?_, fun h => ?_⟩
  · obtain ⟨w, hw, huniq⟩ := hcell c
    have h1 : fromSelection sel hcell c = w := huniq _ (fromSelection_mem sel hcell c)
    have h2 : v = w := huniq v hcv
    rw [h1, h2]
  · rw [← h]; exact fromSelection_mem sel hcell c

/-- **The reconstructed selection is the original selection.** `toSelection` applied to
    the assignment reconstructed from `sel` gives back exactly `sel`: the two membership
    characterizations coincide. -/
theorem toSelection_fromSelection (sel : ExactCover.Sel ι V)
    (hcell : ∀ c : ι, ∃! v : V, (c, v) ∈ sel) :
    toSelection (fromSelection sel hcell) = sel := by
  ext ⟨c, v⟩
  rw [mem_toSelection_iff, mem_fromSelection_iff]

/-- **Backward direction of the equivalence.** An exact cover yields a solution: the
    reconstructed assignment is all-distinct on each scope (since two cells of the same
    scope carrying the same value would violate the `∃!` uniqueness of the
    (scope, value) pair), and its selection is the original selection. -/
theorem exact_cover_imp_solution (scopes : Scopes ι) (sel : ExactCover.Sel ι V)
    (hec : ExactCover.IsExactCover sel scopes) :
    ∃ σ, IsSolution scopes σ ∧ toSelection σ = sel :=
  ⟨fromSelection sel hec.1,
   (fun s hs c c' hcs hc's hcc' => by
      have hcv : (c, fromSelection sel hec.1 c) ∈ sel := fromSelection_mem sel hec.1 c
      have hc'v : (c', fromSelection sel hec.1 c) ∈ sel := by
        rw [hcc']; exact fromSelection_mem sel hec.1 c'
      obtain ⟨c0, ⟨hc0s, hc0v⟩, hc0uniq⟩ := hec.2 s hs (fromSelection sel hec.1 c)
      rw [hc0uniq c ⟨hcs, hcv⟩, hc0uniq c' ⟨hc's, hc'v⟩]),
   toSelection_fromSelection sel hec.1⟩

/-- **Sudoku ⇔ exact cover equivalence (Knuth).** Under the "full house" hypothesis
    (the 9×9 Sudoku case), a structure admits a solution if and only if it admits an
    exact cover. This is the complete equivalence theorem — the forward direction
    (`solution_imp_exact_cover`) plus the backward direction
    (`exact_cover_imp_solution`). -/
theorem sudoku_iff_exact_cover (scopes : Scopes ι)
    (hfull : ∀ s ∈ scopes, s.card = Fintype.card V) :
    (∃ σ : Solution ι V, IsSolution scopes σ) ↔
      (∃ sel : ExactCover.Sel ι V, ExactCover.IsExactCover sel scopes) := by
  refine ⟨fun ⟨σ, hσ⟩ => ⟨toSelection σ, solution_imp_exact_cover scopes σ hσ hfull⟩,
          fun ⟨sel, hec⟩ => ?_⟩
  obtain ⟨σ, hσ, _⟩ := exact_cover_imp_solution scopes sel hec
  exact ⟨σ, hσ⟩

end Sudoku_en
