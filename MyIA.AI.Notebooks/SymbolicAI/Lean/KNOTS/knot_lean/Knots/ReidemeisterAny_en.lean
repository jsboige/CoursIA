/-
Knots.ReidemeisterAny — extended move language: kink/bigon without freshness
=============================================================================

Issue #22359 (parent Epic #1453, designated successor of #18611 whose organ is
delivered by #22240). Tranche 1 of the multi-cycle grain: **the language** and
its verifiers, the R1/R2/R3 embedding of the existing language, kernel witnesses,
and the bounded decision frame. The witness search / extended negative
certificate on the 11n102 corpus (Python replica, bounds <= 13 crossings,
excursions <= +2) is the next tranche, not this file.

## Founding observation (measured, cf #22359)

The connected language of `Knots.ReidemeisterMoves` is **append-only with
fresh labels at the tail**: every descending move removes a kink `<a, b, c, c>`
whose labels `b`, `c` are exactly the two largest of the diagram. This is not
an added hypothesis, it is a **consequence of the `wf` parity**: each label
appears exactly twice, so a literal withdrawal (without renumbering) kills
exactly two labels, which must then empty the interval `[1, numEdges]` — that
is, be the two largest. The negative certificate
`no_fourDistinct_certificate_unknots_11n102` (#20017) and the provenance
measurement of #18611 (138,623 states, the 11 original crossings present in
every reached state) measure exactly this closure.

## What this module delivers

1. `canon` — the **canonical form up to renaming** (renumbering by order of
   first appearance): the quotient the connected language lacks;
2. `verifyKinkDownAny` / `verifyBigonDownAny` — R1/R2 withdrawals where the
   only shape constraint is the **silhouette** (kink `e3 = e4`, bigon
   `e2 = e3`) and where the result is compared **up to renaming** — this is
   the #22359 lever: label compaction becomes expressible, freshness stops
   being recovered by `wf`;
3. `AnyMove` + `verifyAnyMove` + `verifyAnyMoves` + `movesConnectsAny` — the
   certified Bool chain on the extended language (R3 reused as is: it knows
   nothing about freshness);
4. the **R1/R2/R3 embedding**: every R1, R2 or R3 step accepted by the old
   verifier is accepted by the new one (a theorem, not a measurement);
5. **kernel witnesses**: a genuine non-fresh `_any` descent (dying labels
   {2, 3} != the two largest {3, 4}, compaction 4 -> 2), the descents to
   the empty diagram (degenerate kink on the R1 side, a pair of terminal
   bigons on the R2 side), and the historical R1 pair passing
   through the new language;
6. `anyBoundedConnects` — the **bounded decision frame** on the `allDiagrams`
   enumeration (#22240): reachability in the `_any` move graph.

## Declared residuals (next tranches of the grain, not blind spots)

- **`_any` -> `ReidemeisterEquiv` soundness**: an `_any` withdrawal is an
  R1/R2 up to renaming; sealing it requires "renaming preserves the knot
  type" (an `AnyEquiv` + a bridge lemma);
- the equivalence `canon l = canon l' <-> exists label bijection` is the
  design justification, **not proved here** — the kernel only consumes
  `canon` equality;
- the completeness of the enumeration remains the residual of #22240,
  unchanged.

i18n convention (EPIC #4980, user decision 2026-07-04): this file is the
**EN sibling**, with the canonical French version in the sibling
`ReidemeisterAny.lean` (sibling-pair model). It is a *consumer* sibling: it
imports the French modules and operates on their types, as
`BoundedEnumeration_en.lean` already does — the bounded-search universe
`allDiagrams` is typed over the French `KnotDiagram`, so a mirror built on
`Knots_en.KnotDiagram` could not be connected to it. Theorem statements, Lean
tactics, lemma names and Mathlib references stay in English (Mathlib 4
compatibility); only the docstrings and comments differ.
-/

import Knots.Basic
import Knots.ReidemeisterMoves
import Knots.BoundedEnumeration

namespace Knots_en.AnyMoves

open Knots
open Knots.Bounded

/-! ## 1. The canonical form up to renaming

The quotient of the representation by label renaming: each label receives a
number by order of first appearance. Two crossing lists have the same `canon`
exactly when they correspond through a label bijection — a design
justification (not proved here, see the header); the kernel only consumes
the equality.
-/

/-- Label -> canonical number association: already-seen number, or
    `size + 1` on first appearance. -/
private def canonLabel (seen : List (Nat × Nat)) (x : Nat) :
    Nat × List (Nat × Nat) :=
  match seen.lookup x with
  | some v => (v, seen)
  | none => (seen.length + 1, seen ++ [(x, seen.length + 1)])

/-- Renumbers a label sequence, threading the seen-state. -/
private def canonSlots : List (Nat × Nat) → List Nat → List Nat × List (Nat × Nat)
  | _, [] => ([], [])
  | seen, x :: xs =>
    let (v, seen') := canonLabel seen x
    let (ys, seen'') := canonSlots seen' xs
    (v :: ys, seen'')

/-- Canonical form of a crossing list: each label replaced by its
    first-appearance rank. Total, structural function, kernel-evaluable on
    literals. -/
def canon (l : List PDCrossing) : List (List Nat) :=
  go l []
where
  go : List PDCrossing → List (Nat × Nat) → List (List Nat)
    | [], _ => []
    | c :: cs, seen =>
      let (ys, seen') := canonSlots seen [c.e1, c.e2, c.e3, c.e4]
      ys :: go cs seen'

/-- The canonical form of the empty list is empty. -/
theorem canon_nil : canon [] = [] := rfl

/-! ## 2. The `_any` withdrawals — silhouette only, comparison up to renaming

The `_any` R1 withdrawal: the large diagram carries a terminal crossing with
kink silhouette (`e3 = e4`), its withdrawal merges arc `K.e2` into arc `K.e1`
(one rewritten slot), and the rest is compared to the target **through
`canon`**. Unlike the connected withdrawal of `ReidemeisterMoves`, no freshness
equality is required: the `wf` parity of the target alone arbitrates the
bookkeeping of dying labels.
-/

/-- Replaces in a crossing every label equal to `x` by `y` (all four
    slots; `wf` guarantees at most one slot touched per label). -/
private def subLabel (c : PDCrossing) (x y : Nat) : PDCrossing :=
  ⟨if c.e1 = x then y else c.e1, if c.e2 = x then y else c.e2,
    if c.e3 = x then y else c.e3, if c.e4 = x then y else c.e4⟩

/-- Double replacement in one pass: `x₁ -> y₁` and `x₂ -> y₂` (R2). A single
    pass so as not to rewrite the result of the first replacement. -/
private def subLabel2 (c : PDCrossing) (x₁ y₁ x₂ y₂ : Nat) : PDCrossing :=
  ⟨sub1 c.e1, sub1 c.e2, sub1 c.e3, sub1 c.e4⟩
where
  sub1 (v : Nat) : Nat := if v = x₁ then y₁ else if v = x₂ then y₂ else v

/-- Bool verifier of the `_any` withdrawal of a terminal kink: silhouette
    `K.e3 = K.e4` alone (the label freshness of `verifyR1Fwd` is LIFTED),
    length `+1`, merge `K.e2 -> K.e1` in one rewritten slot, comparison of the
    rest to the target **up to renaming** (`canon`). The "rest empty" case
    covers the descent of a single crossing to the degenerate diagram. -/
def verifyKinkDownAny (D d : KnotDiagram) : Bool :=
  D.wf && d.wf &&
  match D.crossings.getLast? with
  | none => false
  | some K =>
    decide (K.e3 = K.e4 ∧ d.crossings.length + 1 = D.crossings.length) &&
    ((D.crossings.dropLast = [] &&
        decide (canon D.crossings.dropLast = canon d.crossings)) ||
      (List.range D.crossings.dropLast.length).any fun i =>
        let M := (D.crossings.dropLast).set i
          (subLabel (crossingAt D.crossings.dropLast i) K.e2 K.e1)
        decide (canon M = canon d.crossings))

/-- Bool verifier of the `_any` withdrawal of a pair of terminal bigons:
    silhouettes `e2 = e3` on both terminal crossings, common arc
    `K₁.e1 = K₂.e1`, length `+2`, double merge `o₁ -> a` / `o₂ -> a`
    (where `a = K₂.e1`, `o₁ = K₁.e4`, `o₂ = K₂.e4`) in one rewritten slot,
    rest compared up to renaming. -/
def verifyBigonDownAny (D d : KnotDiagram) : Bool :=
  D.wf && d.wf &&
  match D.crossings.getLast? with
  | none => false
  | some K₂ =>
    match D.crossings.dropLast.getLast? with
    | none => false
    | some K₁ =>
      decide (K₂.e2 = K₂.e3 ∧ K₁.e2 = K₁.e3 ∧ K₁.e1 = K₂.e1 ∧
        d.crossings.length + 2 = D.crossings.length) &&
      ((D.crossings.dropLast.dropLast = [] &&
          decide (canon D.crossings.dropLast.dropLast = canon d.crossings)) ||
        (List.range D.crossings.dropLast.dropLast.length).any fun i =>
          let M := (D.crossings.dropLast.dropLast).set i
            (subLabel2 (crossingAt D.crossings.dropLast.dropLast i)
              K₁.e4 K₂.e1 K₂.e4 K₂.e1)
          decide (canon M = canon d.crossings))

/-! ## 3. The `AnyMove` inductive and the certified chain

Same architecture as `ReidemeisterMove`: the nature of the move is the
constructor, well-formedness is not a field — it is the verifier's `= true`.
R3 is reused as is (`verifyR3` of `ReidemeisterMoves`): the triangular move
creates no labels, it has no freshness constraint to lift. The `_any` step is
direction-neutral: creation is the withdrawal read the other way round.
-/

/-- A move of the extended language: kink (R1) or bigon (R2) **without
    freshness constraint**, or triangle (R3, unchanged). -/
inductive AnyMove : Type where
  /-- Creation/withdrawal of a kink, up to renaming. -/
  | r1Any (source target : KnotDiagram) : AnyMove
  /-- Addition/withdrawal of a pair of bigons, up to renaming. -/
  | r2Any (source target : KnotDiagram) : AnyMove
  /-- Triangular slide (identical to the connected language). -/
  | r3Any (source target : KnotDiagram) : AnyMove
  deriving Repr

/-- Source diagram of the move. -/
def AnyMove.source : AnyMove → KnotDiagram
  | .r1Any s _ => s
  | .r2Any s _ => s
  | .r3Any s _ => s

/-- Target diagram of the move. -/
def AnyMove.target : AnyMove → KnotDiagram
  | .r1Any _ t => t
  | .r2Any _ t => t
  | .r3Any _ t => t

/-- Bool verifier of an `_any` step, direction-neutral: the withdrawal in
    either orientation (creation is the inverse of withdrawal). -/
def verifyAnyMove (m : AnyMove) : Bool :=
  match m with
  | .r1Any s t => verifyKinkDownAny t s || verifyKinkDownAny s t
  | .r2Any s t => verifyBigonDownAny t s || verifyBigonDownAny s t
  | .r3Any s t => verifyR3 s t

/-- Checks that an `_any` sequence forms a continuous chain from `start` to
    `end_` whose every link passes `verifyAnyMove`. Base case: the empty list
    requires `start = end_` (reflexivity), as in the connected language. -/
def verifyAnyMoves : List AnyMove → KnotDiagram → KnotDiagram → Bool
  | [], start, end_ => decide (start = end_)
  | m :: ms, start, end_ =>
    decide (m.source = start) && verifyAnyMove m && verifyAnyMoves ms m.target end_

/-- The #22359 connector: `movesConnectsAny d₁ d₂` is the proposition "the
    list `ms` is a certificate of the extended language connecting `d₁` to
    `d₂`" — a kernel-checkable list. Soundness towards `ReidemeisterEquiv`
    (`_any` withdrawal = R1/R2 up to renaming) is a designated residual, see
    the header. -/
def movesConnectsAny (ms : List AnyMove) (d₁ d₂ : KnotDiagram) : Prop :=
  verifyAnyMoves ms d₁ d₂ = true

/-! ## 4. R1/R2/R3 embedding — the connected language is a sub-language

The old R1 verifier requires the freshness equalities `K.e2 = m + 1`,
`K.e3 = K.e4 = m + 2`; the `_any` silhouette (`K.e3 = K.e4`) is an immediate
consequence, and the literal surgery of the old withdrawal leaves the result
**unchanged** (identity renumbering), hence `canon`-equal. Every connected R1
or R3 link is therefore an `_any` link. The R2 case is proved below, in the
same section: the freshness scheme there is a double renaming, undone in a
single pass by `subLabel2`.
-/

/-- Slot merge: if `v` is the fresh label `b` where the original carried
    `a`, the merge gives it back to `a`; otherwise it was unchanged. Generic
    brick of the R1 embedding (four slots, same proof). -/
private theorem slot_merge {v w a b : Nat}
    (hr : v = w ∨ (v = b ∧ w = a)) (hw : w ≠ b) :
    (if v = b then a else v) = w := by
  rcases hr with h | ⟨hb', hwa⟩
  · rw [h, if_neg hw]
  · rw [hb', if_pos rfl, hwa]

/-- The labels of a diagram crossing lie in `d.edges`
    (membership feeds the `<= numEdges` bound of the plumbing). -/
private theorem mem_edges_of_mem_crossings {d : KnotDiagram}
    {c : PDCrossing} (hc : c ∈ d.crossings) :
    c.e1 ∈ d.edges ∧ c.e2 ∈ d.edges ∧ c.e3 ∈ d.edges ∧ c.e4 ∈ d.edges := by
  unfold KnotDiagram.edges
  simp only [List.mem_flatMap]
  exact ⟨⟨c, hc, by simp⟩, ⟨c, hc, by simp⟩, ⟨c, hc, by simp⟩, ⟨c, hc, by simp⟩⟩

/-- The label bound: in a well-formed diagram, every label of a
    crossing lies in `[1, numEdges]`. -/
private theorem label_le_of_wf {d : KnotDiagram} (hwf : d.wf = true)
    {c : PDCrossing} (hc : c ∈ d.crossings) :
    1 ≤ c.e1 ∧ c.e1 ≤ d.numEdges ∧ 1 ≤ c.e2 ∧ c.e2 ≤ d.numEdges ∧
    1 ≤ c.e3 ∧ c.e3 ≤ d.numEdges ∧ 1 ≤ c.e4 ∧ c.e4 ≤ d.numEdges := by
  unfold KnotDiagram.wf at hwf
  by_cases hnil : d.crossings = []
  · rw [hnil] at hc; exact absurd hc (by simp)
  · rw [if_neg hnil, Bool.and_eq_true] at hwf
    obtain ⟨hall, _⟩ := hwf
    obtain ⟨m1, m2, m3, m4⟩ := mem_edges_of_mem_crossings hc
    have ball (l : Nat) (hl : l ∈ d.edges) : 1 ≤ l ∧ l ≤ d.numEdges :=
      of_decide_eq_true (List.all_eq_true.mp hall l hl)
    have b1 := ball _ m1
    have b2 := ball _ m2
    have b3 := ball _ m3
    have b4 := ball _ m4
    exact ⟨b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2⟩

/-- Reading of a rewritten crossing: in `l.set i Y`, index `i` reads
    `Y`. Mirror of the `getElem?` of `ReidemeisterMoves` for descending
    surgery. -/
private theorem crossingAt_set_self (l : List PDCrossing) (i : Nat)
    (Y : PDCrossing) (h : i < l.length) : crossingAt (l.set i Y) i = Y := by
  have h1 : (l.set i Y)[i]? = some Y :=
    List.getElem?_eq_some_iff.mpr ⟨by rwa [List.length_set], by simp⟩
  simp only [crossingAt, h1, Option.getD_some]

/-- Rewriting a crossing by itself is the identity (for `List.set`). -/
private theorem set_self_mem {l : List PDCrossing} {i : Nat}
    (h : i < l.length) : l.set i l[i] = l := by
  induction l generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ i' =>
      simp only [List.length_cons] at h
      have hi' : i' < xs.length := by omega
      have hget : (x :: xs)[i' + 1] = xs[i'] := by simp
      rw [hget]
      show x :: xs.set i' xs[i'] = x :: xs
      rw [ih hi']

/-- **R1 embedding**: every step accepted by `verifyR1Fwd` (small `d`, large
    `D`) is an accepted `_any` withdrawal. The proof unfolds the old
    verifier, records the silhouette (a consequence of the freshness
    equalities), and shows that the merge `K.e2 -> K.e1` exactly undoes the
    `isRenameOf` renaming — the rewritten rest is literally the small
    diagram, hence `canon`-equal to itself. -/
theorem verifyR1Fwd_implies_verifyKinkDownAny {d D : KnotDiagram}
    (h : verifyR1Fwd d D = true) : verifyKinkDownAny D d = true := by
  cases hK : D.crossings.getLast? with
  | none => simp [verifyR1Fwd, hK] at h
  | some K =>
    simp only [verifyR1Fwd, hK, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hwf1, hwf2⟩, hn⟩, hform, hanyi⟩ := h
    obtain ⟨hb, hc3, hc4, ha1, han, hmem⟩ := of_decide_eq_true hform
    rw [List.any_eq_true] at hanyi
    obtain ⟨i, hi_mem, hbody⟩ := hanyi
    have hi : i < d.crossings.length := List.mem_range.mp hi_mem
    have hY2 : d.crossings[i]? = some d.crossings[i] :=
      List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩
    simp only [Bool.and_eq_true, crossingAt, hY2, Option.getD_some] at hbody
    obtain ⟨⟨hsurg, hrename⟩, _⟩ := hbody
    -- the kink silhouette is a consequence of freshness
    have hsil : K.e3 = K.e4 := by omega
    -- terminal decomposition and length
    obtain ⟨M, hM⟩ := List.getLast?_eq_some_iff.mp hK
    have hdrop : D.crossings.dropLast
        = d.crossings.set i (crossingAt D.crossings.dropLast i) :=
      of_decide_eq_true hsurg
    have hlenM : M = d.crossings.set i (crossingAt D.crossings.dropLast i) := by
      have h2 : (M ++ [K]).dropLast
          = d.crossings.set i (crossingAt D.crossings.dropLast i) := by
        rw [← hM]; exact hdrop
      simpa using h2
    have hlen : d.crossings.length + 1 = D.crossings.length := by
      rw [hM, hlenM, List.length_append, List.length_singleton, List.length_set]
    -- the merge undoes the renaming, slot by slot
    have hsub : subLabel (crossingAt D.crossings.dropLast i) K.e2 K.e1
        = d.crossings[i] := by
      rw [hb]  -- K.e2 = d.numEdges + 1 : the renaming label
      -- the bound: every label of the rewritten crossing is ≤ numEdges
      have hmemi : d.crossings[i] ∈ d.crossings := by simp
      have hbounds := label_le_of_wf hwf1 hmemi
      obtain ⟨_, b2, _, b4, _, b6, _, b8⟩ := hbounds
      unfold subLabel
      have hrn := of_decide_eq_true hrename
      unfold PDCrossing.isRenameOf at hrn
      obtain ⟨r1, r2, r3, r4⟩ := hrn
      have hec : (d.crossings[i] : PDCrossing) =
          ⟨d.crossings[i].e1, d.crossings[i].e2, d.crossings[i].e3,
            d.crossings[i].e4⟩ := rfl
      rw [hec, PDCrossing.mk.injEq]
      exact ⟨slot_merge r1 (by omega), slot_merge r2 (by omega),
        slot_merge r3 (by omega), slot_merge r4 (by omega)⟩
    -- assembly of the _any verifier
    simp only [verifyKinkDownAny, hK, hwf2, hwf1, Bool.true_and]
    rw [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, List.any_eq_true]
    refine ⟨⟨hsil, hlen⟩, Or.inr ⟨i, ?_, ?_⟩⟩
    · rw [hdrop, List.length_set]
      exact hi_mem
    · show decide (canon ((D.crossings.dropLast).set i
          (subLabel (crossingAt D.crossings.dropLast i) K.e2 K.e1)) =
          canon d.crossings) = true
      rw [hdrop, crossingAt_set_self _ _ _ hi, List.set_set, hsub,
        set_self_mem hi]
      simp

/-- Embedding of the R1 step, orientation-neutral. -/
theorem verifyR1_implies_verifyAnyMove (s t : KnotDiagram)
    (h : verifyR1 s t = true) : verifyAnyMove (.r1Any s t) = true := by
  simp only [verifyAnyMove]
  rcases Bool.or_eq_true_iff.mp h with h' | h'
  · exact Bool.or_eq_true_iff.mpr (Or.inl (verifyR1Fwd_implies_verifyKinkDownAny h'))
  · exact Bool.or_eq_true_iff.mpr (Or.inr (verifyR1Fwd_implies_verifyKinkDownAny h'))

/-- Embedding of the R3 step: definitional (the verifier is reused as
    is). -/
theorem verifyR3_implies_verifyAnyMove (s t : KnotDiagram)
    (h : verifyR3 s t = true) : verifyAnyMove (.r3Any s t) = true := h

/-- Double slot fusion: if `v` is one of the fresh labels `o₁`/`o₂` where the
    original carried `a`, the fusion returns it to `a` ; otherwise it was
    unchanged. Generic brick of the R2 embedding (four slots, same proof as
    `slot_merge` for R1). -/
private theorem slot_merge2 {v w a o₁ o₂ : Nat}
    (hr : v = w ∨ (v = o₁ ∧ w = a) ∨ (v = o₂ ∧ w = a))
    (hw₁ : w ≠ o₁) (hw₂ : w ≠ o₂) (ho : o₂ ≠ o₁) :
    (if v = o₁ then a else if v = o₂ then a else v) = w := by
  rcases hr with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h, if_neg hw₁, if_neg hw₂]
  · rw [h1, if_pos rfl, h2]
  · rw [if_neg (by omega), h1, if_pos rfl, h2]

/-- **R2 embedding**: every step accepted by `verifyR2Fwd` (small `d`, large
    `D`) is an accepted `_any` removal. The proof unfolds the former
    verifier, reads the silhouettes of the terminal bigons (consequence of
    the freshness equalities), and shows that the double fusion
    `K₁.e4 → K₂.e1` / `K₂.e4 → K₂.e1` undoes exactly the `isDoubleRenameOf`
    double renaming — the rewritten crossing becomes literally the small
    diagram's, hence the rewritten rest is `canon`-equal to the target. The
    double arc `a` lives in a single crossing of the small diagram, and the
    single `subLabel2` pass (each slot tested against both fusion targets)
    suffices to undo the renaming of both slots. -/
theorem verifyR2Fwd_implies_verifyBigonDownAny {d D : KnotDiagram}
    (h : verifyR2Fwd d D = true) : verifyBigonDownAny D d = true := by
  cases hK₂ : D.crossings.getLast? with
  | none => simp [verifyR2Fwd, hK₂] at h
  | some K₂ =>
    cases hK₁ : D.crossings.dropLast.getLast? with
    | none => simp [verifyR2Fwd, hK₂, hK₁] at h
    | some K₁ =>
      simp only [verifyR2Fwd, hK₂, hK₁, Bool.and_eq_true] at h
      obtain ⟨⟨⟨hwf1, hwf2⟩, hn⟩, hform₂, hform₁, hanyi⟩ := h
      obtain ⟨hb2, hb3, hb4, ha1, han, hmem⟩ := of_decide_eq_true hform₂
      obtain ⟨hc1, hc2, hc3, hc4⟩ := of_decide_eq_true hform₁
      rw [List.any_eq_true] at hanyi
      obtain ⟨i, hi_mem, hbody⟩ := hanyi
      have hi : i < d.crossings.length := List.mem_range.mp hi_mem
      have hY2 : d.crossings[i]? = some d.crossings[i] :=
        List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩
      simp only [Bool.and_eq_true, crossingAt, hY2, Option.getD_some] at hbody
      obtain ⟨hsurg, hrename⟩ := hbody
      -- bigon silhouettes follow from freshness
      have hsil₂ : K₂.e2 = K₂.e3 := by omega
      have hsil₁ : K₁.e2 = K₁.e3 := by omega
      -- surgery and length (two dropLast remove the terminal pair)
      have hrest : D.crossings.dropLast.dropLast
          = d.crossings.set i (crossingAt D.crossings.dropLast.dropLast i) :=
        of_decide_eq_true hsurg
      have hrestlen : D.crossings.dropLast.dropLast.length
          = d.crossings.length := by
        rw [hrest, List.length_set]
      have hneD : D.crossings ≠ [] := fun hc => by
        rw [hc] at hK₂; simp at hK₂
      have hne₁ : D.crossings.dropLast ≠ [] := fun hc => by
        rw [hc] at hK₁; simp at hK₁
      have hlen : d.crossings.length + 2 = D.crossings.length := by
        have h1 : D.crossings.dropLast.length = D.crossings.length - 1 :=
          List.length_dropLast
        have h2 : D.crossings.dropLast.dropLast.length
            = D.crossings.dropLast.length - 1 := List.length_dropLast
        have hpD : 0 < D.crossings.length :=
          List.length_pos_iff_ne_nil.mpr hneD
        have hp₁ : 0 < D.crossings.dropLast.length :=
          List.length_pos_iff_ne_nil.mpr hne₁
        omega
      -- the double fusion undoes the renaming, slot by slot: the fresh
      -- labels o1 = K1.e4, o2 = K2.e4 are first realigned with the
      -- numbered spelling of the renaming (n+2 / n+4), then each slot
      -- fuses
      have hsub : subLabel2 (crossingAt D.crossings.dropLast.dropLast i)
            K₁.e4 K₂.e1 K₂.e4 K₂.e1 = d.crossings[i] := by
        rw [hc4, hb4]
        have hmemi : d.crossings[i] ∈ d.crossings := by simp
        have hbounds := label_le_of_wf hwf1 hmemi
        obtain ⟨_, b2, _, b4, _, b6, _, b8⟩ := hbounds
        have hrn := of_decide_eq_true hrename
        unfold PDCrossing.isDoubleRenameOf at hrn
        obtain ⟨r1, r2, r3, r4⟩ := hrn
        unfold subLabel2 subLabel2.sub1
        have hec : (d.crossings[i] : PDCrossing) =
            ⟨d.crossings[i].e1, d.crossings[i].e2, d.crossings[i].e3,
              d.crossings[i].e4⟩ := rfl
        rw [hec, PDCrossing.mk.injEq]
        exact ⟨slot_merge2 r1 (by omega) (by omega) (by omega),
          slot_merge2 r2 (by omega) (by omega) (by omega),
          slot_merge2 r3 (by omega) (by omega) (by omega),
          slot_merge2 r4 (by omega) (by omega) (by omega)⟩
      -- assembly of the _any verifier
      simp only [verifyBigonDownAny, hK₂, hK₁, hwf2, hwf1, Bool.true_and]
      rw [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, List.any_eq_true]
      refine ⟨⟨hsil₂, hsil₁, hc1, hlen⟩, Or.inr ⟨i, ?_, ?_⟩⟩
      · rw [hrestlen]
        exact hi_mem
      · show decide (canon ((D.crossings.dropLast.dropLast).set i
            (subLabel2 (crossingAt D.crossings.dropLast.dropLast i)
              K₁.e4 K₂.e1 K₂.e4 K₂.e1)) = canon d.crossings) = true
        rw [hrest, crossingAt_set_self _ _ _ hi, List.set_set, hsub,
          set_self_mem hi]
        simp

/-- Embedding of the R2 step, orientation-neutral. -/
theorem verifyR2_implies_verifyAnyMove (s t : KnotDiagram)
    (h : verifyR2 s t = true) : verifyAnyMove (.r2Any s t) = true := by
  simp only [verifyAnyMove]
  rcases Bool.or_eq_true_iff.mp h with h' | h'
  · exact Bool.or_eq_true_iff.mpr (Or.inl (verifyR2Fwd_implies_verifyBigonDownAny h'))
  · exact Bool.or_eq_true_iff.mpr (Or.inr (verifyR2Fwd_implies_verifyBigonDownAny h'))

/-! ## 5. Kernel witnesses

Four faces of the language: a **genuine** `_any` descent (non-fresh dying
labels, compaction), the descents to the empty diagram — degenerate kink on
the R1 side, a pair of terminal bigons on the R2 side (lower bounds of the
language) —, and the historical R1 pair
(`reidemeister1Connected_satisfiable`) passing through the new language — the
embedding in action.
-/

/-- **Non-fresh `_any` witness**: the large diagram carries the terminal kink
    `<1,2,3,3>`; its withdrawal merges arc `2` into arc `1` and kills labels
    `{2, 3}` — which are NOT the two largest (`{3, 4}`): the surviving target
    carries label `4`, renumbered `2` by the `canon` comparison. This step is
    REFUSED by the connected language (freshness recovered by `wf`) and
    accepted here — the #22359 lever in one step. -/
theorem verifyKinkDownAny_witness_nonFresh :
    verifyKinkDownAny
      { crossings := [⟨4, 1, 4, 2⟩, ⟨1, 2, 3, 3⟩], numEdges := 4 }
      { crossings := [⟨2, 1, 2, 1⟩], numEdges := 2 } := by
  decide

/-- The same step sealed into a chain certificate: the extended language
    connects the large diagram to the small one in a single link. -/
theorem movesConnectsAny_witness_nonFresh :
    movesConnectsAny
      [AnyMove.r1Any
        { crossings := [⟨4, 1, 4, 2⟩, ⟨1, 2, 3, 3⟩], numEdges := 4 }
        { crossings := [⟨2, 1, 2, 1⟩], numEdges := 2 }]
      { crossings := [⟨4, 1, 4, 2⟩, ⟨1, 2, 3, 3⟩], numEdges := 4 }
      { crossings := [⟨2, 1, 2, 1⟩], numEdges := 2 } := by
  unfold movesConnectsAny
  decide

/-- **Descent to the empty diagram**: the single crossing `<1,1,2,2>` is a
    degenerate kink (silhouette `e3 = e4`, trivial merge `a = b`), its
    withdrawal leaves the void — the verifier's "rest empty" case. -/
theorem verifyKinkDownAny_witness_empty :
    verifyKinkDownAny
      { crossings := [⟨1, 1, 2, 2⟩], numEdges := 2 }
      { crossings := [], numEdges := 0 } := by
  decide

/-- **R2 `_any` witness**: the pair of terminal bigons `<1,2,2,4>` /
    `<1,3,3,4>` (twin arcs `2` and `3`, shared entry `1` and exit `4`)
    withdraws entirely — target the empty diagram, the verifier's "rest
    empty" case. The `r2Any` surface exercised on a literal, symmetric to
    the degenerate kink above. -/
theorem verifyBigonDownAny_witness_empty :
    verifyBigonDownAny
      { crossings := [⟨1, 2, 2, 4⟩, ⟨1, 3, 3, 4⟩], numEdges := 4 }
      { crossings := [], numEdges := 0 } := by
  decide

/-- **The `r2Any` step sealed into a link**: the same pair passes the
    direction-neutral verifier of the extended language. -/
theorem verifyR2_witness_passes_any :
    verifyAnyMove (AnyMove.r2Any
      { crossings := [⟨1, 2, 2, 4⟩, ⟨1, 3, 3, 4⟩], numEdges := 4 }
      { crossings := [], numEdges := 0 }) := by
  decide

/-- **The embedding in action**: the R1 witness pair of the connected
    language (`verifyR1Fwd`, cf `ReidemeisterMoves` §7) passes the extended
    language — freshness makes the `canon` comparison trivial (identity). -/
theorem verifyR1_witness_passes_any :
    verifyAnyMove (AnyMove.r1Any
      { crossings := [⟨1, 2, 3, 4⟩, ⟨1, 2, 3, 4⟩], numEdges := 4 }
      { crossings := [⟨1, 2, 3, 4⟩, ⟨5, 2, 3, 4⟩, ⟨1, 5, 6, 6⟩],
                      numEdges := 6 }) := by
  decide

/-! ## 6. The bounded decision frame

The enumeration `allDiagrams n` (#22240) provides the universe; the `_any`
moves define the graph; reachability is decidable by neighbourhood closure
bounded by the size of the universe. The kernel only evaluates this frame at
small bounds; the effective search at the bounds of the 11n102 corpus (<= 13
crossings, excursions <= +2) goes through the Python replica — tranche 2 of
the grain, cf #20017 for the precedent.
-/

/-- `_any` neighbours in the bounded universe: all diagrams of the
    enumeration one `_any` step away from `d`. -/
private def anyNeighbors (n : Nat) (d : KnotDiagram) : List KnotDiagram :=
  (allDiagrams n).filter fun d' =>
    verifyAnyMove (AnyMove.r1Any d d') ||
    verifyAnyMove (AnyMove.r2Any d d') ||
    verifyAnyMove (AnyMove.r3Any d d')

/-- Neighbourhood closure: at most size-of-universe rounds
    (chains without repetition), deduplicated at each round. -/
private def anyClosure (n : Nat) : Nat → List KnotDiagram → List KnotDiagram
  | 0, reached => reached
  | k + 1, reached =>
    anyClosure n k ((reached.flatMap (anyNeighbors n) ++ reached).eraseDups)

/-- Bounded decision of `_any` connectivity: is `d₂` reachable from `d₁` in
    the `_any` move graph over `allDiagrams n`? Decidable frame — kernel
    evaluation is reserved for small bounds, the 11n102 corpus search goes
    through the Python replica (tranche 2). -/
def anyBoundedConnects (n : Nat) (d₁ d₂ : KnotDiagram) : Bool :=
  (anyClosure n ((allDiagrams n).length + 1) [d₁]).contains d₂

/-- The frame executes: in the universe `allDiagrams 1`, the degenerate kink
    `<1,1,2,2>` reaches the empty diagram — the descent of the §5 witness
    inside the enumeration, decided by the kernel. -/
theorem demo_anyBoundedConnects_empty :
    anyBoundedConnects 1
      { crossings := [⟨1, 1, 2, 2⟩], numEdges := 2 }
      { crossings := [], numEdges := 0 } = true := by
  decide

end Knots_en.AnyMoves
