/-
Knots.ReidemeisterInvariance — Invariance of invariants under Reidemeister moves
================================================================================

Home of the invariance theorem: `alexanderPolynomialSigned` is invariant under
the three Reidemeister moves (issue #16650, tranche 3 of the Alexander socle,
strategy `docs/lean/alexander-strategy/c652-reidemeister-invariance.md`).

Why a separate module: the theorem crosses `Reidemeister3Connected`
(`Knots.Reidemeister`) and `alexanderPolynomialSigned` (`Knots.Conway`).
`Knots.Conway` imports `Knots.Invariant`, which imports `Knots.Reidemeister` —
so importing `Knots.Conway` suffices to see both, and the converse would be a
cycle. This module is where the two theories meet.

English mirror of `ReidemeisterInvariance.lean` (FR canonical). Convention EPIC
#4980 (ratified 2026-07-04, cf `code-style.md` §Lean i18n): distinct FR + EN
sibling files — no inline bilingual block. The module docstring and the theorem
docstrings below differ from the FR version; the body signatures, proofs and
tactics remain byte-identical between the two files.
-/

import Knots.Conway

namespace Knots

/-! ## 1. The `i = 0` / `i ≥ 1` split (a point the strategy misses)

Strategy c652 (§4.1) presents R3 as "trivial by reindexation". That holds **under
a condition it does not state**: that the triangle lies entirely outside the row
the designated minor deletes.

`alexanderPolynomialSigned` deletes the **first** row (`rest` = tail of
`crossings`) and the last column of the minor. Hence:

* **`i ≥ 1`** — the three rewritten rows of the triangle lie in the body of the
  matrix; invariance is a reindexation argument: the surgery changes neither the
  number of crossings nor the number of edges, and the arc partition is
  preserved (section 2 below). The minor is unchanged up to the transport of
  columns.
* **`i = 0`** — row 0 carries a vertex of the triangle, and that is precisely
  the row the designated minor **deletes**. Reindexation no longer suffices: the
  minor changes shape (coefficients leave the triangle's columns for others),
  and invariance can only be read up to a **unit** `±t^k` — this is the
  determinantal argument of sections 4.2-4.3 of the strategy (non-shared column,
  rank of the augmented minor).

The two cases are therefore of different nature and must be distinct theorems.
Conflating them would make `i = 0` look like a missing proof when it is in fact
the case where the designated minor genuinely changes shape.

## 2. The arc-partition preservation obligation

The reindexation argument (`i ≥ 1`) rests on a premise the strategy **assumes
without proving**: `arcPartition` is preserved by the surgery.

Let us make the obstacle precise on the witness: the connected R3 surgery
rewrites the `(e2, e4)` pairs of the triangle's three crossings (cf
`Conway_en.lean`, `pairs := d.crossings.map (fun c => (c.e2, c.e4))`). On the
lake's witness (`reidemeister3Connected_satisfiable`), those pairs coincide as
**unordered** pairs —

    X : (2,8), (7,4), (8,6)      Y : (4,7), (2,8), (8,6)

— but only the **orientation** of the middle pair differs ((7,4) versus (4,7)),
and the rewritten crossings change **position** in the fold's list. The fold
sees oriented pairs taken in list order: the preservation is therefore **not
vacuous** — it requires absorbing both differences, through insensitivity to a
pair's orientation (`mergePair_symm`, #17429) and through commutation of the
fusions at the class level (`mergePair_mergePair_comm_equiv`, #17646). What is
preserved besides is the **multiset of labels** (docstring of
`Reidemeister3Connected`), whence `wf`.

This witness alone does not, however, ground the general preservation: a
diagram where the triangle's `(e2, e4)` pairs genuinely differ as a multiset
remains to be exhibited. This is the first lock of the tranche, before any
reindexation argument.
-/

/-! ## 3. Control: the R3 witness's arc partition is preserved

The witness is that of `reidemeister3Connected_satisfiable` (literals copied
verbatim): both diagrams are well formed (`decide` on `wf` in the lake), and
their arc partition — 5 classes for 10 edges — is **the same** on both sides of
the surgery. This is the positive control of section 2: the triangle's `(e2,e4)`
pairs there coincide unordered, with differing orientation and fold position —
the fold still yields the same partition, and it is `foldl_mergePair_swap`
(orientation) then `foldl_mergePair_permute_adjacent` (transposition of
positions) that justify it. The general form (on diagrams where the triangle's
pairs differ) is established in section 5.
-/

/-- Control of tranche 3 (step 1): on the witness pair of the connected R3 move,
    the surgery preserves `arcPartition` — the triangle's `(e2,e4)` pairs
    coincide unordered, and the fold absorbs their orientation and position
    differences (`foldl_mergePair_swap`, `foldl_mergePair_permute_adjacent`).
    This is the first premise the reindexation argument (case `i ≥ 1`) assumes;
    the general form is established by
    `Reidemeister3Connected.arcPartition_sameRel` (section 5). -/
theorem reidemeister3Connected_arcPartition_witness :
    arcPartition
        { crossings := [⟨1, 2, 7, 8⟩, ⟨3, 7, 9, 4⟩, ⟨9, 8, 5, 6⟩,
                        ⟨1, 2, 10, 10⟩, ⟨3, 4, 5, 6⟩], numEdges := 10 }
      = arcPartition
        { crossings := [⟨3, 4, 9, 7⟩, ⟨9, 2, 5, 8⟩, ⟨7, 8, 1, 6⟩,
                        ⟨1, 2, 10, 10⟩, ⟨3, 4, 5, 6⟩], numEdges := 10 } := by
  decide

/-! ## 4. Negative control: the designated minor collapses on the Y witness

Section 3 establishes the **first premise** of the reindexation argument (the
arc partition is preserved). The expected **conclusion** control — the signed
polynomial of the witness is the same on both sides — is **refuted on this
witness**, and that is framing information, not a proof failure:

* on the X side, the designated minor is `t³ - t²` (all-positive chirality);
* on the Y side, the designated minor is **identically zero** — and the Python
  probe faithful to the construction (validated against the kernel values of
  the signed `trefoil` and `figureEight`) measures the same nullity for each
  of the five deletable columns and each of the 32 chirality assignments.

The cause reads off the matrix rows: the surgery rewrites `(9, 8, 5, 6)` into
`(7, 8, 1, 6)`, whose non-singleton labels (`7`, `8`, `6`) all fall into the
witness's big class — its row, like the kink row `(1, 2, 10, 10)` (an exact
R1 kink: `e3 = e4`), now only touches the singleton arc column `{1}` and the
deleted big-class column. Two proportional rows: the rank drops to 3 and
every `4 × 4` minor vanishes.

The classical "every `(n-1) × (n-1)` minor of the Alexander matrix equals
`± t^k · Δ`" assumes the matrix has rank `n - 1`; the kink adds a relation,
and the designated normalization (first row and last column deleted,
**fixed**) does not survive the surgery. Consequence for section 1: the
reindexation argument of the `i ≥ 1` case must either restrict to kink-free
diagrams or make the deleted (row, column) pair adaptive.
-/

/-- Generic 4×4 determinant, same spirit as `det_two_aux` / `det_three_aux`
    from `Conway.lean`: Laplace expansion along the first column, the 3×3
    minors being handled by `det_three_aux`. -/
theorem det_four_aux (A : Matrix (Fin 4) (Fin 4) (Polynomial ℤ)) :
    A.det = A 0 0 * (A.submatrix (Fin.succAbove 0) (Fin.succAbove 0)).det
          - A 1 0 * (A.submatrix (Fin.succAbove 1) (Fin.succAbove 0)).det
          + A 2 0 * (A.submatrix (Fin.succAbove 2) (Fin.succAbove 0)).det
          - A 3 0 * (A.submatrix (Fin.succAbove 3) (Fin.succAbove 0)).det := by
  rw [Matrix.det_succ_column_zero]
  simp (config := { decide := true }) [Fin.sum_univ_succ]
  simp (config := { decide := true }) [det_three_aux, Matrix.submatrix_apply,
    Fin.succAbove]
  ring

/-- Tranche 3 control: on the X side, the designated minor of the signed
    polynomial (all-positive chirality) equals `t³ - t²` — it is not
    degenerate. This is the positive counterpart of the negative control
    below: it is the surgery that collapses the minor, not a prior
    degeneracy. -/
theorem reidemeister3Connected_alexanderSigned_witness_X :
    alexanderPolynomialSigned
        { crossings := [⟨1, 2, 7, 8⟩, ⟨3, 7, 9, 4⟩, ⟨9, 8, 5, 6⟩,
                        ⟨1, 2, 10, 10⟩, ⟨3, 4, 5, 6⟩], numEdges := 10 }
        [true, true, true, true, true]
      = Polynomial.X ^ 3 - Polynomial.X ^ 2 := by
  simp only [alexanderPolynomialSigned]
  simp (config := { decide := true })
  rw [det_four_aux]
  simp only [det_three_aux]
  simp only [Matrix.submatrix_apply, Fin.succAbove, Matrix.of_apply]
  simp (config := { decide := true }) [alexanderEntrySigned, alexanderEntry,
    alexanderEntryNeg]
  ring

/-- Tranche 3 negative control: on the Y side, **the same designated minor is
    identically zero** — the witness's R3 surgery aligns the rewritten
    crossing's row `(7, 8, 1, 6)` with the kink row `(1, 2, 10, 10)` (both now
    only touch the singleton arc `{1}` and the deleted big class), the rank
    drops to 3 and the determinant vanishes (probe: null for all five
    deletable columns and all 32 chirality assignments). The designated
    normalization does not survive the surgery on a kink-carrying witness —
    cf section 4 of the module. -/
theorem reidemeister3Connected_alexanderSigned_witness_Y_zero :
    alexanderPolynomialSigned
        { crossings := [⟨3, 4, 9, 7⟩, ⟨9, 2, 5, 8⟩, ⟨7, 8, 1, 6⟩,
                        ⟨1, 2, 10, 10⟩, ⟨3, 4, 5, 6⟩], numEdges := 10 }
        [true, true, true, true, true]
      = 0 := by
  simp only [alexanderPolynomialSigned]
  simp (config := { decide := true })
  rw [det_four_aux]
  simp only [det_three_aux]
  simp only [Matrix.submatrix_apply, Fin.succAbove, Matrix.of_apply]
  simp (config := { decide := true }) [alexanderEntrySigned, alexanderEntry,
    alexanderEntryNeg]
/-! ## 5. General preservation of the arc partition (first lock, #16650)

The connected R3 surgery rewrites the triangle's three crossings X into the
triangle Y. Read on the over-strand pairs `(e2, e4)` that feed the
`arcPartition` fold, the surgery only changes **positions `i` and `i+1`** of
the pair list:

* triangle X — `⟨a₂,a₁,g₁,g₂⟩, ⟨a₃,g₁,g₃,b₃⟩, ⟨g₃,g₂,b₂,b₁⟩` — pairs
  `(a₁,g₂), (g₁,b₃)`, then `(g₂,b₁)` unchanged at position `i+2`;
* triangle Y — `⟨a₃,b₃,g₃,g₁⟩, ⟨g₃,a₁,b₂,g₂⟩, ⟨g₁,g₂,a₂,b₁⟩` — pairs
  `(b₃,g₁), (a₁,g₂)`, same `(g₂,b₁)` at `i+2`.

Going from X to Y is therefore exactly: an **adjacent transposition** of the
first two pairs, composed with an **internal symmetry** of the pair at
position `i` (`(g₁,b₃)` becoming `(b₃,g₁)`). The internal symmetry is absorbed
by `mergePair_symm` / `foldl_mergePair_swap`; the adjacent transposition is
absorbed by the class-level commutation `mergePair_mergePair_comm_equiv`
(#17646): the two intermediate partitions differ as lists (counterexample
documented on #16650) but carry the same "share a class" relation.

The remaining step established here: this class-level equivalence **traverses
the rest of the fold** — two partitions carrying the same relation still do
after any common suffix of merges (`sameRel_foldl`), under the
`ClassesDisjoint` hypothesis (guaranteed for any partition arising from the
fold over the singletons, `foldl_partition_inv`). The result is the
**general** preservation of the arc partition — the "first lock" named in
section 2, now established at the class level.

What remains outside this theorem: the ascent to the **matrix** level (the
class equivalence gives a permutation of the minor's columns, hence invariance
of the determinant up to sign — an argument to write for the
`alexanderSigned_invariant_under_R3` tranche).
-/

/-- Under class disjointness, the first disjunct of the post-merge `SameClass`
    characterization reads in pure `SameClass`: a common untouched class is
    `x ~ y` without `x ~ u` nor `x ~ v` (uniqueness of x's class comes from
    disjointness). -/
lemma exists_class_not_hit_iff {P : List (List Nat)} (hd : ClassesDisjoint P)
    {x y u v : Nat} :
    (∃ C ∈ P, x ∈ C ∧ y ∈ C ∧ ¬((C.contains u || C.contains v) = true)) ↔
      SameClass P x y ∧ ¬ SameClass P x u ∧ ¬ SameClass P x v := by
  constructor
  · rintro ⟨C, hC, hx, hy, hnot⟩
    refine ⟨⟨C, hC, hx, hy⟩, ?_, ?_⟩ <;> rintro ⟨D, hD, hxD, hzD⟩
    · by_cases hCD : C = D
      · have : (C.contains u || C.contains v) = true := by
          rw [hit_iff_mem]; exact Or.inl (by rw [hCD]; exact hzD)
        exact hnot this
      · exact hd C hC D hD hCD x hx hxD
    · by_cases hCD : C = D
      · have : (C.contains u || C.contains v) = true := by
          rw [hit_iff_mem]; exact Or.inr (by rw [hCD]; exact hzD)
        exact hnot this
      · exact hd C hC D hD hCD x hx hxD
  · rintro ⟨⟨C, hC, hx, hy⟩, h1, h2⟩
    refine ⟨C, hC, hx, hy, ?_⟩
    rw [hit_iff_mem]
    push_neg
    exact ⟨fun huC => h1 ⟨C, hC, hx, huC⟩, fun hvC => h2 ⟨C, hC, hx, hvC⟩⟩

/-- `SameClass` after one merge, characterized purely in `SameClass` of the
    original partition (under class disjointness): either a common class
    outside the merged group, or two labels caught by the merge. This is the
    form that makes partition equivalence transportable. -/
lemma sameClass_mergePair_iff_rel {P : List (List Nat)} (hd : ClassesDisjoint P)
    {u v x y : Nat} :
    SameClass (mergePair P u v) x y ↔
      (SameClass P x y ∧ ¬ SameClass P x u ∧ ¬ SameClass P x v) ∨
      ((SameClass P u x ∨ SameClass P v x) ∧ (SameClass P u y ∨ SameClass P v y)) := by
  rw [sameClass_mergePair_iff, exists_class_not_hit_iff hd,
    touches_iff_sameClass, touches_iff_sameClass]

/-- Two partitions are equivalent when they carry the same "share a class"
    relation. This is the right invariance level of `arcPartition` under the
    R3 surgery: list equality is refuted by the counterexample documented on
    #16650, but the class relation — the one the Alexander matrix depends on —
    is preserved. -/
def SameRel (P Q : List (List Nat)) : Prop :=
  ∀ x y : Nat, SameClass P x y ↔ SameClass Q x y

/-- Partition equivalence traverses one merge step: the characterization
    `sameClass_mergePair_iff_rel` speaks only in `SameClass` of the original
    partition, so two equivalent partitions remain so after the same merge. -/
lemma sameRel_mergeStep {P Q : List (List Nat)} (hrel : SameRel P Q)
    (hdP : ClassesDisjoint P) (hdQ : ClassesDisjoint Q) (p : Nat × Nat) :
    SameRel (mergeStep P p) (mergeStep Q p) := by
  intro x y
  simp only [mergeStep]
  rw [sameClass_mergePair_iff_rel hdP, sameClass_mergePair_iff_rel hdQ]
  simp only [SameRel] at hrel
  simp only [hrel]

/-- Partition equivalence traverses a whole fold: two equivalent (and
    disjoint) partitions remain so after any common suffix of merges. -/
lemma sameRel_foldl {P Q : List (List Nat)} (hrel : SameRel P Q)
    (hdP : ClassesDisjoint P) (hdQ : ClassesDisjoint Q)
    (pairs : List (Nat × Nat)) :
    SameRel (pairs.foldl mergeStep P) (pairs.foldl mergeStep Q) := by
  induction pairs generalizing P Q with
  | nil => exact hrel
  | cons p ps ih =>
      rw [List.foldl_cons]
      exact ih (sameRel_mergeStep hrel hdP hdQ p)
        (classesDisjoint_mergePair hdP) (classesDisjoint_mergePair hdQ)

/-! ### Reading `List.set` in take/drop form

The surgery being a triple `List.set`, the take/cons/drop reading of these
rewrites is the tool of the fold decomposition. Three standard lemmas, proved
by induction — the bounds are needed: on a too-short list, `set` is a no-op
while the right-hand side truncates.
-/

/-- `List.set` in take/cons/drop reading (bounded index). -/
lemma set_take_drop {α : Type} (l : List α) (i : Nat) (x : α)
    (h : i < l.length) :
    l.set i x = l.take i ++ [x] ++ l.drop (i + 1) := by
  induction l generalizing i with
  | nil => exact absurd h (Nat.not_lt_zero i)
  | cons a as ih =>
      rcases i with _ | j
      · simp
      · have hj : j < as.length := by simpa using h
        simp only [List.set_cons_succ, List.take_succ_cons, List.cons_append,
          List.drop_succ_cons, ih j hj]

/-- Rewriting a value already in place: a bounded `set` with the current
    value is the identity. -/
lemma set_get_self {α : Type} (l : List α) (i : Nat) (h : i < l.length) :
    l.set i (l.get ⟨i, h⟩) = l := by
  rw [set_take_drop l i _ h, take_cons_drop_eq l i h]

/-- Double consecutive `List.set` in take/drop reading. -/
lemma set2_take_drop {α : Type} (l : List α) (i : Nat) (x₀ x₁ : α)
    (h1 : i + 1 < l.length) :
    (l.set i x₀).set (i + 1) x₁ = l.take i ++ [x₀, x₁] ++ l.drop (i + 2) := by
  induction l generalizing i with
  | nil => exact absurd h1 (Nat.not_lt_zero (i + 1))
  | cons a as ih =>
      rcases i with _ | j
      · have hA : 0 < as.length := by simpa using h1
        simp only [List.set_cons_zero, List.set_cons_succ, List.cons_append,
          List.drop_succ_cons, List.drop_drop, List.nil_append, List.cons_append]
        simpa using set_take_drop as 0 x₁ hA
      · have hj : j + 1 < as.length := by simpa using h1
        simp only [List.set_cons_succ, List.take_succ_cons, List.cons_append,
          List.drop_succ_cons, ih j hj]

/-- Triple consecutive `List.set` in take/drop reading — the exact shape of
    the connected R3 surgery read on the pair list. -/
lemma set3_take_drop {α : Type} (l : List α) (i : Nat) (x₀ x₁ x₂ : α)
    (h2 : i + 2 < l.length) :
    ((l.set i x₀).set (i + 1) x₁).set (i + 2) x₂ =
      l.take i ++ [x₀, x₁, x₂] ++ l.drop (i + 3) := by
  induction l generalizing i with
  | nil => exact absurd h2 (Nat.not_lt_zero (i + 2))
  | cons a as ih =>
      rcases i with _ | j
      · have hB : 0 + 1 < as.length := by
          simp only [List.length_cons] at h2 ⊢; omega
        have h2as := set2_take_drop as 0 x₁ x₂ hB
        simp only [List.set_cons_zero, List.set_cons_succ, List.cons_append]
        simpa using h2as
      · have hj : j + 2 < as.length := by
          simp only [List.length_cons] at h2 ⊢; omega
        simp only [List.set_cons_succ, List.take_succ_cons, List.cons_append,
          List.drop_succ_cons, ih j hj]

/-- `map` commutes with `List.set`: rewriting a crossing then projecting, or
    projecting then rewriting the projection, yields the same pair list. -/
lemma map_set {α β : Type} (f : α → β) (l : List α) (i : Nat) (x : α) :
    (l.set i x).map f = (l.map f).set i (f x) := by
  induction l generalizing i with
  | nil => simp
  | cons a as ih =>
      rcases i with _ | j
      · simp
      · simpa using ih j

/-! ### `wf` gives `EdgesInRange`

Coverage of the pairs by the singletons (`crossings_covered_singles`)
requires `EdgesInRange`; now the non-degenerate branch of `wf` contains
exactly that condition — extracting it avoids adding an ad hoc hypothesis to
the Reidemeister moves, which already carry `wf`. -/

/-- The non-degenerate branch of `wf` contains exactly `EdgesInRange`: a
    well-formed non-empty diagram has all its labels in the `1..numEdges`
    range. -/
lemma wf_edgesInRange {d : KnotDiagram} (hne : d.crossings ≠ [])
    (hwf : d.wf = true) : EdgesInRange d := by
  simp only [KnotDiagram.wf, if_neg hne, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at hwf
  intro c hc
  have hall : ∀ z ∈ [c.e1, c.e2, c.e3, c.e4], 1 ≤ z ∧ z ≤ d.numEdges := by
    intro z hz
    exact hwf.1 z (List.mem_flatMap.mpr ⟨c, hc, hz⟩)
  have h1 := hall c.e1 (by simp)
  have h2 := hall c.e2 (by simp)
  have h3 := hall c.e3 (by simp)
  have h4 := hall c.e4 (by simp)
  exact ⟨h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2⟩

/-- Consecutive triple `List.set` re-setting the values already in place:
    the R3 surgery seen from `d₁` rewrites each position with its current
    value. Generic tool lemma (terms closed over list variables), split out
    to keep elaboration cost bounded: the identity + decomposition machinery
    is elaborated once and for all here, on small terms. -/
private lemma set3_self_decomp {α : Type} (L : List α) (i : Nat) (x₀ x₁ x₂ : α)
    (h0 : i < L.length) (h1 : i + 1 < L.length) (h2 : i + 2 < L.length)
    (e0 : L.get ⟨i, h0⟩ = x₀) (e1 : L.get ⟨i + 1, h1⟩ = x₁)
    (e2 : L.get ⟨i + 2, h2⟩ = x₂) :
    ((L.set i x₀).set (i + 1) x₁).set (i + 2) x₂ = L ∧
    ((L.set i x₀).set (i + 1) x₁).set (i + 2) x₂ =
      L.take i ++ [x₀, x₁, x₂] ++ L.drop (i + 3) := by
  have s0 : L.set i x₀ = L := by
    have hs := set_get_self L i h0
    rwa [e0] at hs
  have s1 : (L.set i x₀).set (i + 1) x₁ = L := by
    rw [s0]
    have hs := set_get_self L (i + 1) h1
    rwa [e1] at hs
  have s2 : ((L.set i x₀).set (i + 1) x₁).set (i + 2) x₂ = L := by
    rw [s1]
    have hs := set_get_self L (i + 2) h2
    rwa [e2] at hs
  exact ⟨s2, set3_take_drop L i x₀ x₁ x₂ h2⟩

/-- get/map bridge: the `List.get` shape (the one produced by the
    `rw`s in this file) is not that of `List.getElem_map` (getElem), and moving
    the proof of `i < l.length` to `i < (l.map f).length` needs a transport
    that `rw` refuses. Generic lemma by induction, isolated here to keep the
    terms inside `pairs_append_forms` small. -/
private lemma map_get_bridge {α β : Type} (f : α → β) (l : List α) (i : Nat)
    (h : i < l.length) (h' : i < (l.map f).length) :
    (l.map f).get ⟨i, h'⟩ = f (l.get ⟨i, h⟩) := by
  induction l generalizing i with
  | nil => exact absurd h (Nat.not_lt_zero _)
  | cons a as ih =>
      rcases i with _ | j
      · simp
      · simpa using ih j (by simpa using h) (by simpa using h')


/-- Reading the R3 surgery on the (e2, e4) pair lists: the pair lists of
    `d₁` and `d₂` share prefix and suffix, differing only on two consecutive
    positions — adjacent transposition `(a₁,g₂) (g₁,b₃)` vs `(b₃,g₁) (a₁,g₂)`.
    Singleton coverage is carried over for both middles. Intermediate lemma
    of `arcPartition_sameRel`, split out to keep elaboration cost bounded: the
    big term `d₁.crossings.map (fun c => (c.e2, c.e4))` is folded by `set`,
    and the identity/decomposition machinery lives in `set3_self_decomp`. -/
private lemma pairs_append_forms {d₁ d₂ : KnotDiagram}
    (h : Reidemeister3Connected d₁ d₂) :
    ∃ A B : List (Nat × Nat), ∃ a₁ b₁ b₃ g₁ g₂ : Nat,
      d₁.crossings.map (fun c => (c.e2, c.e4)) = A ++ [(a₁, g₂), (g₁, b₃), (g₂, b₁)] ++ B ∧
      d₂.crossings.map (fun c => (c.e2, c.e4)) = A ++ [(b₃, g₁), (a₁, g₂), (g₂, b₁)] ++ B ∧
      (∀ q ∈ A ++ [(a₁, g₂), (g₁, b₃)],
        Covered ((List.range d₁.numEdges).map (fun k => [k + 1])) q.1 ∧
        Covered ((List.range d₁.numEdges).map (fun k => [k + 1])) q.2) ∧
      (∀ q ∈ A ++ [(b₃, g₁), (a₁, g₂)],
        Covered ((List.range d₁.numEdges).map (fun k => [k + 1])) q.1 ∧
        Covered ((List.range d₁.numEdges).map (fun k => [k + 1])) q.2) := by
  obtain ⟨hwf₁, _, _, _, i, hi, a₁, a₂, a₃, b₁, b₂, b₃, g₁, g₂, g₃,
      hnd, hg0, hg1, hg2, hsurg⟩ := h
  have hne : d₁.crossings ≠ [] := by
    intro hc
    rw [hc] at hi
    exact absurd hi (Nat.not_lt_zero _)
  have hEIR := wf_edgesInRange hne hwf₁
  set L := d₁.crossings.map (fun c => (c.e2, c.e4)) with hL
  have hlen : L.length = d₁.crossings.length := by
    rw [hL]
    exact List.length_map _
  have hi0 : i < L.length := by omega
  have hi1 : i + 1 < L.length := by omega
  have hi2 : i + 2 < L.length := by omega
  have hic0 : i < d₁.crossings.length := by omega
  have hic1 : i + 1 < d₁.crossings.length := by omega
  have hic2 : i + 2 < d₁.crossings.length := hi
  have hg0' : d₁.crossings.get ⟨i, hic0⟩ = { e1 := a₂, e2 := a₁, e3 := g₁, e4 := g₂ } := hg0
  have hg1' : d₁.crossings.get ⟨i + 1, hic1⟩ = { e1 := a₃, e2 := g₁, e3 := g₃, e4 := b₃ } := hg1
  have hg2' : d₁.crossings.get ⟨i + 2, hic2⟩ = { e1 := g₃, e2 := g₂, e3 := b₂, e4 := b₁ } := hg2
  have hgp0 : L.get ⟨i, hi0⟩ = (a₁, g₂) := by
    show (d₁.crossings.map (fun c => (c.e2, c.e4))).get ⟨i, hi0⟩ = (a₁, g₂)
    rw [map_get_bridge _ _ _ hic0 hi0, hg0']
  have hgp1 : L.get ⟨i + 1, hi1⟩ = (g₁, b₃) := by
    show (d₁.crossings.map (fun c => (c.e2, c.e4))).get ⟨i + 1, hi1⟩ = (g₁, b₃)
    rw [map_get_bridge _ _ _ hic1 hi1, hg1']
  have hgp2 : L.get ⟨i + 2, hi2⟩ = (g₂, b₁) := by
    show (d₁.crossings.map (fun c => (c.e2, c.e4))).get ⟨i + 2, hi2⟩ = (g₂, b₁)
    rw [map_get_bridge _ _ _ hic2 hi2, hg2']
  have hpairs₂' : d₂.crossings.map (fun c => (c.e2, c.e4)) =
      ((L.set i (b₃, g₁)).set (i + 1) (a₁, g₂)).set (i + 2) (g₂, b₁) := by
    rw [hsurg, map_set, map_set, map_set]
  obtain ⟨s2eq, hdec₁⟩ :=
    set3_self_decomp L i (a₁, g₂) (g₁, b₃) (g₂, b₁) hi0 hi1 hi2 hgp0 hgp1 hgp2
  have hdec₂ : ((L.set i (b₃, g₁)).set (i + 1) (a₁, g₂)).set (i + 2) (g₂, b₁) =
      L.take i ++ [(b₃, g₁), (a₁, g₂), (g₂, b₁)] ++ L.drop (i + 3) :=
    set3_take_drop L i _ _ _ hi2
  have hP1 : L = L.take i ++ [(a₁, g₂), (g₁, b₃), (g₂, b₁)] ++ L.drop (i + 3) := by
    rw [← hdec₁, s2eq]
  have hP2 : d₂.crossings.map (fun c => (c.e2, c.e4)) =
      L.take i ++ [(b₃, g₁), (a₁, g₂), (g₂, b₁)] ++ L.drop (i + 3) := by
    rw [hpairs₂', hdec₂]
  have hmem0 : d₁.crossings.get ⟨i, hic0⟩ ∈ d₁.crossings := List.getElem_mem hic0
  have hmem1 : d₁.crossings.get ⟨i + 1, hic1⟩ ∈ d₁.crossings := List.getElem_mem hic1
  have hEIR0 := hEIR _ hmem0
  have hEIR1 := hEIR _ hmem1
  rw [hg0] at hEIR0
  rw [hg1] at hEIR1
  obtain ⟨_, _, ha₁, ha₁', hg₁lo, hg₁hi, hg₂lo, hg₂hi⟩ := hEIR0
  obtain ⟨_, _, _, _, _, _, hb₃lo, hb₃hi⟩ := hEIR1
  have hcovA : ∀ q ∈ L.take i,
      Covered ((List.range d₁.numEdges).map (fun k => [k + 1])) q.1 ∧
      Covered ((List.range d₁.numEdges).map (fun k => [k + 1])) q.2 := by
    intro q hq
    refine crossings_covered_singles hEIR q ?_
    rw [← hL]
    exact List.mem_of_mem_take hq
  have hcovmid1 : ∀ q ∈ [(a₁, g₂), (g₁, b₃)],
      Covered ((List.range d₁.numEdges).map (fun k => [k + 1])) q.1 ∧
      Covered ((List.range d₁.numEdges).map (fun k => [k + 1])) q.2 := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨covered_singles ha₁ ha₁', covered_singles hg₂lo hg₂hi⟩
    · exact ⟨covered_singles hg₁lo hg₁hi, covered_singles hb₃lo hb₃hi⟩
  have hcovmid2 : ∀ q ∈ [(b₃, g₁), (a₁, g₂)],
      Covered ((List.range d₁.numEdges).map (fun k => [k + 1])) q.1 ∧
      Covered ((List.range d₁.numEdges).map (fun k => [k + 1])) q.2 := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨covered_singles hb₃lo hb₃hi, covered_singles hg₁lo hg₁hi⟩
    · exact ⟨covered_singles ha₁ ha₁', covered_singles hg₂lo hg₂hi⟩
  refine ⟨L.take i, L.drop (i + 3), a₁, b₁, b₃, g₁, g₂, hP1, hP2, ?_, ?_⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hcovA q hq
    · exact hcovmid1 q hq
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hcovA q hq
    · exact hcovmid2 q hq


/-- **General preservation of the arc partition under connected R3**
    (first lock of #16650): if `d₂` is obtained from `d₁` by the triangular
    move, the two arc partitions carry the same "share a class" relation — for
    any pair of labels, sharing a class in `arcPartition d₁` and sharing a
    class in `arcPartition d₂` are equivalent. The list form is NOT preserved
    (counterexample documented on #16650: two consecutive merges of the same
    pairs in reverse order produce different lists); the class form — the one
    the Alexander matrix depends on, column by column — is. -/
theorem Reidemeister3Connected.arcPartition_sameRel {d₁ d₂ : KnotDiagram}
    (h : Reidemeister3Connected d₁ d₂) :
    SameRel (arcPartition d₁) (arcPartition d₂) := by
  obtain ⟨A, B, a₁, b₁, b₃, g₁, g₂, hP1, hP2, hcov1, hcov2⟩ := pairs_append_forms h
  obtain ⟨hwf₁, _, _, henum, _, _⟩ := h
  rw [arcPartition_eq, arcPartition_eq, hP1, hP2]
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [← henum]
  set S := (List.range d₁.numEdges).map (fun k => [k + 1]) with hS
  have hfoldA1 : (A ++ [(a₁, g₂), (g₁, b₃)]).foldl mergeStep S =
      mergeStep (mergeStep (A.foldl mergeStep S) (a₁, g₂)) (g₁, b₃) := by
    simp
  have hfoldA2 : (A ++ [(b₃, g₁), (a₁, g₂)]).foldl mergeStep S =
      mergeStep (mergeStep (A.foldl mergeStep S) (b₃, g₁)) (a₁, g₂) := by
    simp
  have hd1 := (foldl_partition_inv (P := S) (pairs := A ++ [(a₁, g₂), (g₁, b₃)])
    classesDisjoint_singles pairwise_singles hcov1).1
  have hd2 := (foldl_partition_inv (P := S) (pairs := A ++ [(b₃, g₁), (a₁, g₂)])
    classesDisjoint_singles pairwise_singles hcov2).1
  rw [hfoldA1] at hd1
  rw [hfoldA2] at hd2
  have hmid : SameRel (mergeStep (mergeStep (A.foldl mergeStep S) (a₁, g₂)) (g₁, b₃))
      (mergeStep (mergeStep (A.foldl mergeStep S) (b₃, g₁)) (a₁, g₂)) := by
    intro x y
    have hq0 : mergeStep (A.foldl mergeStep S) (b₃, g₁) =
        mergeStep (A.foldl mergeStep S) (g₁, b₃) := by
      simp only [mergeStep]
      rw [mergePair_symm]
    show SameClass (mergeStep (mergeStep (A.foldl mergeStep S) (a₁, g₂)) (g₁, b₃)) x y ↔ _
    rw [hq0]
    exact mergePair_mergePair_comm_equiv _ a₁ g₂ g₁ b₃ x y
  have hmid3 : SameRel
      (mergeStep (mergeStep (mergeStep (A.foldl mergeStep S) (a₁, g₂)) (g₁, b₃)) (g₂, b₁))
      (mergeStep (mergeStep (mergeStep (A.foldl mergeStep S) (b₃, g₁)) (a₁, g₂)) (g₂, b₁)) :=
    sameRel_mergeStep hmid hd1 hd2 (g₂, b₁)
  exact sameRel_foldl hmid3 (classesDisjoint_mergePair hd1)
    (classesDisjoint_mergePair hd2) B

/-- Coverage corollary: the preserved class relation gives equivalence of the
    coverages — a label is carried by the arc partition of `d₁` if and only if
    it is by that of `d₂`. -/
theorem Reidemeister3Connected.arcPartition_covered_iff {d₁ d₂ : KnotDiagram}
    (h : Reidemeister3Connected d₁ d₂) (z : Nat) :
    Covered (arcPartition d₁) z ↔ Covered (arcPartition d₂) z := by
  have heq := h.arcPartition_sameRel z z
  constructor
  · rintro ⟨C, hC, hz⟩
    obtain ⟨D, hD, hzD, _⟩ := heq.mp ⟨C, hC, hz, hz⟩
    exact ⟨D, hD, hzD⟩
  · rintro ⟨D, hD, hzD⟩
    obtain ⟨C, hC, hz, _⟩ := heq.mpr ⟨D, hD, hzD, hzD⟩
    exact ⟨C, hC, hz⟩

end Knots

