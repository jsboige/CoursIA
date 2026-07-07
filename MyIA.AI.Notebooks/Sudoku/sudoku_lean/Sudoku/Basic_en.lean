import Mathlib

/-!
# Sudoku.Basic — constraint structure, solutions, peers

Abstract formalization of a Sudoku (more generally: any constraint-satisfaction
problem with "all-distinct scopes"). A concrete 9×9 Sudoku is one instance of this
framework: the **scopes** are its 27 families (9 rows, 9 columns, 9 blocks), each of
which must carry **all-distinct** values.

The abstraction is deliberate: the soundness theorems of propagation
(`Propagation.lean`) hold for **any** structure of this type, not only the 9×9. This is
the right level of formalization — the propagation logic does not depend on there being
9 values or 3×3 blocks, only on the invariant "all-distinct per scope".

Cross-reference: the `Sudoku` series (backtracking, OR-Tools, .NET, Infer.NET) whose
solvers this lake formally grounds by propagation. See issue #4055.
-/

namespace Sudoku_en

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V]

/-- The constraint structure of a Sudoku: a finite set of **scopes** (each a
    `Finset` of cells) that must carry all-distinct values. -/
abbrev Scopes (ι : Type*) := Finset (Finset ι)

/-- A complete assignment: one value per cell. -/
abbrev Solution (ι V : Type*) := ι → V

/-- `σ` is **all-distinct on `s`** if two distinct cells of `s` never carry the same
    value (injectivity of `σ` on `s`). -/
def AllDistinctOn (σ : Solution ι V) (s : Finset ι) : Prop :=
  ∀ ⦃c c'⦄, c ∈ s → c' ∈ s → σ c = σ c' → c = c'

/-- `σ` is a **solution** of the structure `scopes` if it is all-distinct on each
    scope. This is the fundamental Sudoku invariant (each row, column and block
    contains each value at most once). -/
def IsSolution (scopes : Scopes ι) (σ : Solution ι V) : Prop :=
  ∀ s ∈ scopes, AllDistinctOn σ s

/-- `σ` **agrees** with a partial assignment `a` wherever `a` is defined. -/
def AgreesWith (σ : Solution ι V) (a : ι → Option V) : Prop :=
  ∀ i, ∀ v, a i = some v → σ i = v

/-- `c'` is a **peer** of `c` if they are distinct and share at least one scope. Two
    peer cells cannot carry the same value in a solution. -/
def IsPeer (scopes : Scopes ι) (c c' : ι) : Prop :=
  c ≠ c' ∧ ∃ s ∈ scopes, c ∈ s ∧ c' ∈ s

/-- A value `v` is **present in scope `s`** if some cell of `s` carries it. For a
    "full house" scope (|s| = |V|) of a solution, every value is present there (full
    house lemma). -/
def PresentIn (σ : Solution ι V) (s : Finset ι) (v : V) : Prop :=
  ∃ c ∈ s, σ c = v

/-- **Full house lemma.** If a scope `s` contains as many cells as there are possible
    values (`s.card = card V`) and an assignment `σ` is all-distinct on `s`, then
    **every** value `v` is present in `s`.

    This is the pigeonhole argument: `σ` restricted to `s` is injective, so its image
    has `card s = card V` distinct elements — the entirety of `V` — hence every value
    appears there. This lemma makes the `PresentIn σ s v` hypothesis of the "hidden
    single" (`Propagation.hidden_single_sound`) automatic in the full-house case
    (cf #4055). -/
theorem full_house_present {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V]
    [DecidableEq V] (σ : Solution ι V) (s : Finset ι) (v : V)
    (hcard : s.card = Fintype.card V) (hAD : AllDistinctOn σ s) : PresentIn σ s v := by
  -- `AllDistinctOn σ s` ⟺ `Set.InjOn σ s` (same shape, Finset/Set membership defeq)
  have hinj : Set.InjOn σ s := by
    intros c hc c' hc' heq
    exact hAD hc hc' heq
  -- The image `σ '' s` has the same cardinality as `s` (injectivity)
  have hcard_img : (Finset.image σ s).card = s.card := Finset.card_image_of_injOn hinj
  -- `σ '' s ⊆ univ`, same cardinality as `univ` (= card V) ⟹ `σ '' s = univ`
  have hsub : Finset.image σ s ⊆ (Finset.univ : Finset V) := Finset.subset_univ _
  have heq_img : Finset.image σ s = (Finset.univ : Finset V) := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hcard_img, hcard]; simp
  -- `v ∈ σ '' s` (= univ), then `mem_image` ⟺ `∃ c ∈ s, σ c = v` = `PresentIn`
  have hmem : v ∈ Finset.image σ s := heq_img ▸ Finset.mem_univ v
  rw [Finset.mem_image] at hmem
  exact hmem

end Sudoku_en
