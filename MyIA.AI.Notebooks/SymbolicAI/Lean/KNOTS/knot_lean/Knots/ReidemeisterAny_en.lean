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
- the equivalence `canon l = canon l' <-> exists label bijection`: the
  **invariance** half (`canon (mapC σ l) = canon l` for injective `σ`) is
  proved in section 7 (`canon_map_eq`); the converse (**extraction** of the
  renaming from `canon` equality) remains a residual — it will require a
  `SeenNodup` invariant on the seen-thread. Tranche 3 also fixes the
  `canonSlots` base (the state now survives the empty list): without it, the
  renumbering restarted at every crossing and `canon` equality accepted
  inter-crossing rewires — counterexample sealed in section 7;
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
number by order of **first appearance, threaded from crossing to crossing**.
Two crossing lists have the same `canon` exactly when they correspond through
a label bijection — a design justification (invariance half proved in
section 7, converse residual, see the header); the kernel only consumes the
equality.
-/

/-- Label -> canonical number association: already-seen number, or
    `size + 1` on first appearance. -/
private def canonLabel (seen : List (Nat × Nat)) (x : Nat) :
    Nat × List (Nat × Nat) :=
  match seen.lookup x with
  | some v => (v, seen)
  | none => (seen.length + 1, seen ++ [(x, seen.length + 1)])

/-- Renumbers a label sequence, threading the seen-state. The `[]` base
    **hands the thread back**: without it, every crossing restarted from an
    empty state and the renumbering became per-crossing — `canon` equality
    then accepted inter-crossing rewires (counterexample sealed in section 7).
    -/
private def canonSlots : List (Nat × Nat) → List Nat → List Nat × List (Nat × Nat)
  | seen, [] => ([], seen)
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

/-! ## 7. The canon bridge — threading fix + invariance half (tranche 3)

The seen-state threading was broken at the base: `canonSlots` returned
`([], [])` on the empty list, discarding the accumulated state — the
renumbering restarted at **every crossing**, and `canon` equality accepted
targets that rewire inter-crossing connections (the counterexample below was
accepted, and it corresponds to no renaming of the surgery result). The base
now hands the thread back (`| seen, [] => ([], seen)`), the semantics
documented since section 1 — a **global** first-appearance ranking.

This tranche seals the fix and delivers the **invariance half** of the
bridge:

* `canon_map_eq` — renaming by an **injection** does not change the canonical
  form: the first-appearance rank does not depend on the label's name, only on
  the order of appearance. This is the direction soundness (`_any` ->
  `ReidemeisterEquiv`) consumes: the certificate carried by the verifier is
  stable under renaming.

The converse (**extraction**: two lists with the same `canon` correspond
through an injection) remains a residual — it will require a `SeenNodup`
invariant on the seen-thread (the rank is injective only if the already-seen
keys are distinct).
-/

/-- Renaming a list of crossings: `π` applied to the four slots of each
    crossing. -/
private def mapC (π : Nat → Nat) (l : List PDCrossing) : List PDCrossing :=
  l.map fun c => ⟨π c.e1, π c.e2, π c.e3, π c.e4⟩

/-- `lookup` commutes with key renaming: looking up `π x` in the image of a
    list of pairs under `π` (on keys) is looking up `x` in the list — up to
    injectivity of `π` on the keys. -/
private theorem lookup_map_key {π : Nat → Nat} (hπ : Function.Injective π)
    (l : List (Nat × Nat)) (x : Nat) (w : Nat) (h : l.lookup x = some w) :
    (l.map fun p => (π p.1, p.2)).lookup (π x) = some w := by
  induction l with
  | nil => simp at h
  | cons p t ih =>
    -- `List.lookup` unfolds to a Bool `match` on `a == k`: reduce the
    -- discriminator with the core lemmas `beq_self_eq_true` /
    -- `beq_eq_false_iff_ne`, injectivity arbitrates the π case.
    by_cases hpx : x = p.1
    · subst hpx
      simp only [List.lookup, beq_self_eq_true] at h
      simp only [List.map_cons, List.lookup, beq_self_eq_true]
      exact h
    · have hb : (x == p.1) = false := by
        rw [beq_eq_false_iff_ne]; exact hpx
      simp only [List.lookup, hb] at h
      have hne : (π x == π p.1) = false := by
        rw [beq_eq_false_iff_ne]
        exact fun hc => hpx (hπ hc)
      simp only [List.map_cons, List.lookup, hne]
      exact ih h

/-- Mirror of the previous one for the absent case: if `x` is a key nowhere,
    neither is `π x` in the image — up to injectivity of `π`. -/
private theorem lookup_map_key_none {π : Nat → Nat} (hπ : Function.Injective π)
    (l : List (Nat × Nat)) (x : Nat) (h : l.lookup x = none) :
    (l.map fun p => (π p.1, p.2)).lookup (π x) = none := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    by_cases hpx : x = p.1
    · subst hpx
      simp only [List.lookup, beq_self_eq_true] at h
      simp at h
    · have hb : (x == p.1) = false := by
        rw [beq_eq_false_iff_ne]; exact hpx
      simp only [List.lookup, hb] at h
      have hne : (π x == π p.1) = false := by
        rw [beq_eq_false_iff_ne]
        exact fun hc => hpx (hπ hc)
      simp only [List.map_cons, List.lookup, hne]
      exact ih h

/-- One step of `canonSlots`, "label already seen" case: the number is the
    recorded value, the state is unchanged. `let`-free shape (both components
    of the result are projections of a single evaluation). -/
private theorem canonSlots_cons_of_some {seen : List (Nat × Nat)} {x v : Nat}
    {xs : List Nat} (h : seen.lookup x = some v) :
    canonSlots seen (x :: xs) =
      (v :: (canonSlots seen xs).1, (canonSlots seen xs).2) := by
  simp only [canonSlots, canonLabel, h]

/-- One step of `canonSlots`, "first appearance" case: number `size + 1`, the
    state gains the new association. -/
private theorem canonSlots_cons_of_none {seen : List (Nat × Nat)} {x : Nat}
    {xs : List Nat} (h : seen.lookup x = none) :
    canonSlots seen (x :: xs) =
      ((seen.length + 1) :: (canonSlots (seen ++ [(x, seen.length + 1)]) xs).1,
        (canonSlots (seen ++ [(x, seen.length + 1)]) xs).2) := by
  simp only [canonSlots, canonLabel, h]

/-- The heart of the bridge: when the state threads are correlated by `π`
    (keys renamed, canonical numbers unchanged), the numbers produced are
    **equal** on both sides and the threads stay correlated. The
    first-appearance rank does not depend on the label's name. -/
private theorem canonSlots_congr {π : Nat → Nat} (hπ : Function.Injective π)
    (xs : List Nat) :
    ∀ seen seen' : List (Nat × Nat),
      seen' = seen.map (fun p => (π p.1, p.2)) →
      (canonSlots seen' (xs.map π)).1 = (canonSlots seen xs).1 ∧
      (canonSlots seen' (xs.map π)).2 =
        (canonSlots seen xs).2.map (fun p => (π p.1, p.2)) := by
  induction xs with
  | nil =>
    intro seen seen' hcorr
    simp only [List.map_nil]
    exact ⟨rfl, hcorr⟩
  | cons x xs ih =>
    intro seen seen' hcorr
    simp only [List.map_cons]
    cases hlk : seen.lookup x with
    | some v =>
      have hlk' : seen'.lookup (π x) = some v := by
        rw [hcorr, lookup_map_key hπ seen x v hlk]
      rw [canonSlots_cons_of_some hlk, canonSlots_cons_of_some hlk']
      -- states unchanged: the correlation hcorr itself feeds the IH
      obtain ⟨ys, ys'⟩ := ih _ _ hcorr
      exact ⟨congrArg (List.cons v) ys, ys'⟩
    | none =>
      have hlk' : seen'.lookup (π x) = none := by
        rw [hcorr, lookup_map_key_none hπ seen x hlk]
      have hlen : seen'.length = seen.length := by
        rw [hcorr, List.length_map]
      have hcorr2 : seen' ++ [(π x, seen'.length + 1)] =
          (seen ++ [(x, seen.length + 1)]).map (fun p => (π p.1, p.2)) := by
        rw [hcorr, List.map_append, List.map_singleton]
        simp
      rw [canonSlots_cons_of_none hlk, canonSlots_cons_of_none hlk']
      obtain ⟨ys, ys'⟩ := ih _ _ hcorr2
      rw [hlen] at ys ys' ⊢
      exact ⟨congrArg (List.cons _) ys, ys'⟩

/-- One step of `canon.go`, `let`-free: the canonical form of a list of
    crossings is the quadruple of canonical numbers of the first crossing,
    then the thread of the rest. (Zeta + projections: definitional.) -/
private theorem canon_go_cons (c : PDCrossing) (cs : List PDCrossing)
    (seen : List (Nat × Nat)) :
    canon.go (c :: cs) seen =
      (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).1
        :: canon.go cs (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2 := rfl

/-- The heart of the bridge, crossing level: on correlated state threads, the
    canonical form of a renamed list is that of the list. -/
private theorem canon_go_congr {π : Nat → Nat} (hπ : Function.Injective π)
    (l : List PDCrossing) :
    ∀ seen seen' : List (Nat × Nat),
      seen' = seen.map (fun p => (π p.1, p.2)) →
      canon.go (mapC π l) seen' = canon.go l seen := by
  induction l with
  | nil => intro _ _ _; rfl
  | cons c cs ih =>
    intro seen seen' hcorr
    have hmap : mapC π (c :: cs) =
        ⟨π c.e1, π c.e2, π c.e3, π c.e4⟩ :: mapC π cs := by simp [mapC]
    obtain ⟨hnums, hcorr2⟩ :=
      canonSlots_congr hπ [c.e1, c.e2, c.e3, c.e4] seen seen' hcorr
    rw [hmap, canon_go_cons, canon_go_cons,
      show [π c.e1, π c.e2, π c.e3, π c.e4] = [c.e1, c.e2, c.e3, c.e4].map π from by
        simp,
      hnums, ih _ _ hcorr2]

/-- **Invariance half of the bridge**: renaming a list of crossings by an
    injection does not change its canonical form — the first-appearance rank
    does not depend on the label's name, only on the order of appearance.
    This is the direction soundness consumes: a verified step is verified for
    the whole renaming class of its operands. -/
theorem canon_map_eq {π : Nat → Nat} (hπ : Function.Injective π)
    (l : List PDCrossing) : canon (mapC π l) = canon l :=
  canon_go_congr hπ l [] [] rfl

/-- **Counterexample sealing the threading fix**: the source is the large
    side of the historical R1 pair (`verifyR1_witness_passes_any`); the
    target `d` keeps the same silhouettes but rewires the inter-crossing
    connections — the `e1` slot of the second crossing goes from `1` to `3`,
    which is the work of **no** renaming of the surgery result
    `[⟨1,2,3,4⟩, ⟨1,2,3,4⟩]` (a renaming would preserve the equality of the
    `e1` slots of both crossings). Under global threading, `canon`
    distinguishes the two and the verifier REFUSES. Before the fix, the
    `_, [] => ([], [])` base reset the numbering at every crossing: both
    canonical forms collapsed to `[[1,2,3,4], [1,2,3,4]]` and this step was
    ACCEPTED — the defect, sealed here by the kernel. -/
theorem verifyKinkDownAny_rejects_crossRewire :
    verifyKinkDownAny
      { crossings := [⟨1, 2, 3, 4⟩, ⟨5, 2, 3, 4⟩, ⟨1, 5, 6, 6⟩],
        numEdges := 6 }
      { crossings := [⟨1, 2, 3, 4⟩, ⟨3, 4, 1, 2⟩], numEdges := 4 } = false := by
  decide


/-! ## 8. Groundwork for the extraction half (slice 4, in progress)

The converse of `canon_map_eq` — same canonical form means the target is a
renaming of the source — requires the seen-state to be a **faithful** state:
distinct keys (one label, one rank), distinct and bounded values (one rank,
one label; ranks live between `1` and the state size). These invariants hold
by construction: `canonLabel` only adds a key when absent, and the rank
added is `size + 1`, hence fresh. This section introduces the vocabulary and
key preservation; value preservation and the extraction theorem itself
follow (next slices).
-/

/-- `List.lookup` only fails on an absent key — by induction, to avoid
    depending on uncertain core lemma names. -/
private theorem lookup_none_iff_not_mem_key (x : Nat) :
    ∀ seen : List (Nat × Nat),
      seen.lookup x = none ↔ x ∉ seen.map Prod.fst := by
  intro seen
  induction seen with
  | nil => simp
  | cons p t ih =>
    by_cases hpx : x = p.1
    · subst hpx
      simp
    · have hb : (x == p.1) = false := by
        rw [beq_eq_false_iff_ne]; exact hpx
      simp only [List.lookup, hb, List.map_cons, List.mem_cons, not_or]
      exact ⟨fun h => ⟨hpx, ih.mp h⟩, fun h => ih.mpr h.2⟩

/-- Faithful state, keys: a label has exactly one rank (the seen-state never
    duplicates keys). -/
private def SeenKeysNodup (seen : List (Nat × Nat)) : Prop :=
  (seen.map Prod.fst).Nodup

/-- Faithful state, values: a rank belongs to exactly one label. -/
private def SeenValsNodup (seen : List (Nat × Nat)) : Prop :=
  (seen.map Prod.snd).Nodup

/-- Faithful state, boundedness: ranks live between `1` and the state
    size. -/
private def SeenValsBounded (seen : List (Nat × Nat)) : Prop :=
  ∀ p ∈ seen, 0 < p.2 ∧ p.2 ≤ seen.length

/-- `canonLabel` preserves key faithfulness: a present key is not re-added,
    an absent key is added exactly once. -/
private theorem canonLabel_keys_nodup {seen : List (Nat × Nat)} {x : Nat}
    (h : SeenKeysNodup seen) : SeenKeysNodup (canonLabel seen x).2 := by
  unfold canonLabel
  cases hlk : seen.lookup x with
  | some v => exact h
  | none =>
    have hx : x ∉ seen.map Prod.fst :=
      (lookup_none_iff_not_mem_key x seen).mp hlk
    unfold SeenKeysNodup
    rw [List.map_append, List.map_singleton]
    exact List.Nodup.append h (by simp)
      (by intro a ha
          simp only [List.mem_singleton]
          exact fun hax => hx (hax ▸ ha))

/-- Threading a slot sequence preserves key faithfulness (induction on the
    sequence, arbitrary initial state). -/
private theorem canonSlots_keys_nodup {seen : List (Nat × Nat)} {xs : List Nat}
    (h : SeenKeysNodup seen) : SeenKeysNodup (canonSlots seen xs).2 := by
  induction xs generalizing seen with
  | nil => exact h
  | cons y ys ih =>
    cases hlk : seen.lookup y with
    | some v =>
      rw [canonSlots_cons_of_some hlk]
      exact ih h
    | none =>
      have hlab : (canonLabel seen y).2 = seen ++ [(y, seen.length + 1)] := by
        unfold canonLabel; rw [hlk]
      have hk' := canonLabel_keys_nodup (seen := seen) (x := y) h
      rw [hlab] at hk'
      rw [canonSlots_cons_of_none hlk]
      exact ih hk'


/-! ## 9. Faithfulness of the VALUES (slice 4, in progress)

The extraction half needs more than key preservation: the **values** of the
thread must be faithful too — one rank per label, and ranks inside
`1 … size`. These are the `SeenValsNodup` and `SeenValsBounded` invariants
introduced in §8.

The hinge of the argument is the **freshness of the added rank**: `canonLabel`
adds the rank `size + 1`, and `SeenValsBounded` places every rank already
carried inside `1 … size` — so `size + 1` is fresh. Once that point is
established, the addition preserves the faithfulness of the thread, and
threading a sequence of labels preserves it as well.

The extraction theorem itself (`canon l = canon l'` ⇒ there is an injective
renaming of `l` into `l'`) remains the residual of the slice.
-/

/-- A rank carried by the thread is at most the size of the thread. -/
private theorem snd_mem_le_length {seen : List (Nat × Nat)}
    (hb : SeenValsBounded seen) {v : Nat} (hv : v ∈ seen.map Prod.snd) :
    v ≤ seen.length := by
  obtain ⟨p, hp, hpv⟩ := List.mem_map.mp hv
  rw [← hpv]
  exact (hb p hp).2

/-- The added rank is fresh: `size + 1` is carried by no label of the thread
    yet. -/
private theorem fresh_rank_not_mem {seen : List (Nat × Nat)}
    (hb : SeenValsBounded seen) :
    seen.length + 1 ∉ seen.map Prod.snd := by
  intro hv
  have hle := snd_mem_le_length hb hv
  omega

/-- `canonLabel` preserves value faithfulness: the new rank is fresh, so it
    collides with no rank already carried. -/
private theorem canonLabel_vals_nodup {seen : List (Nat × Nat)} {x : Nat}
    (hn : SeenValsNodup seen) (hb : SeenValsBounded seen) :
    SeenValsNodup (canonLabel seen x).2 := by
  cases hlk : seen.lookup x with
  | some v =>
    simp only [canonLabel, hlk]
    exact hn
  | none =>
    have hlab : (canonLabel seen x).2 = seen ++ [(x, seen.length + 1)] := by
      unfold canonLabel; rw [hlk]
    rw [hlab]
    unfold SeenValsNodup
    rw [List.map_append, List.map_singleton]
    refine List.Nodup.append hn (by simp) ?_
    intro a ha hmem
    simp only [List.mem_singleton] at hmem
    subst hmem
    exact absurd ha (fresh_rank_not_mem hb)

/-- `canonLabel` preserves rank boundedness: the ranks already carried stay
    inside `1 … size`, and the new rank equals the size of the enriched
    thread. -/
private theorem canonLabel_vals_bounded {seen : List (Nat × Nat)} {x : Nat}
    (hb : SeenValsBounded seen) :
    SeenValsBounded (canonLabel seen x).2 := by
  cases hlk : seen.lookup x with
  | some v =>
    simp only [canonLabel, hlk]
    exact hb
  | none =>
    have hlab : (canonLabel seen x).2 = seen ++ [(x, seen.length + 1)] := by
      unfold canonLabel; rw [hlk]
    rw [hlab]
    intro p hp
    rw [List.mem_append] at hp
    rcases hp with hp | hp
    · obtain ⟨hpos, hle⟩ := hb p hp
      simp only [List.length_append]
      omega
    · simp only [List.mem_singleton] at hp
      rcases hp with rfl
      simp only [List.length_append, List.length_singleton]
      omega

/-- Threading a sequence of labels preserves value faithfulness (induction on
    the sequence, arbitrary initial state). -/
private theorem canonSlots_vals_nodup {seen : List (Nat × Nat)} {xs : List Nat}
    (hn : SeenValsNodup seen) (hb : SeenValsBounded seen) :
    SeenValsNodup (canonSlots seen xs).2 := by
  induction xs generalizing seen with
  | nil => exact hn
  | cons y ys ih =>
    cases hlk : seen.lookup y with
    | some v =>
      rw [canonSlots_cons_of_some hlk]
      exact ih hn hb
    | none =>
      have hlab : (canonLabel seen y).2 = seen ++ [(y, seen.length + 1)] := by
        unfold canonLabel; rw [hlk]
      have hn' := canonLabel_vals_nodup (seen := seen) (x := y) hn hb
      have hb' := canonLabel_vals_bounded (seen := seen) (x := y) hb
      rw [hlab] at hn' hb'
      rw [canonSlots_cons_of_none hlk]
      exact ih hn' hb'

/-- Threading a sequence of labels preserves rank boundedness (induction on
    the sequence, arbitrary initial state). -/
private theorem canonSlots_vals_bounded {seen : List (Nat × Nat)} {xs : List Nat}
    (hb : SeenValsBounded seen) :
    SeenValsBounded (canonSlots seen xs).2 := by
  induction xs generalizing seen with
  | nil => exact hb
  | cons y ys ih =>
    cases hlk : seen.lookup y with
    | some v =>
      rw [canonSlots_cons_of_some hlk]
      exact ih hb
    | none =>
      have hlab : (canonLabel seen y).2 = seen ++ [(y, seen.length + 1)] := by
        unfold canonLabel; rw [hlk]
      have hb' := canonLabel_vals_bounded (seen := seen) (x := y) hb
      rw [hlab] at hb'
      rw [canonSlots_cons_of_none hlk]
      exact ih hb'

/-- **Faithful thread.** A thread with distinct keys, distinct values and
    bounded values: this is the state threading between two crossings
    produces, and it is the condition the extraction half consumes. -/
private theorem canonSlots_faithful {seen : List (Nat × Nat)} {xs : List Nat}
    (hk : SeenKeysNodup seen) (hv : SeenValsNodup seen) (hb : SeenValsBounded seen) :
    SeenKeysNodup (canonSlots seen xs).2 ∧
      SeenValsNodup (canonSlots seen xs).2 ∧
      SeenValsBounded (canonSlots seen xs).2 := by
  exact ⟨canonSlots_keys_nodup hk,
    canonSlots_vals_nodup hv hb,
    canonSlots_vals_bounded hb⟩


/-! ## 10. Rank stability (tranche 5)

Extraction needs a property the previous tranches do not state: **the rank of
a label is the same everywhere it appears**. As long as the thread is carried
from one crossing to the next, a label already seen keeps its rank; that is
what makes the renaming `π` well defined — extraction is about labels, not
about positions.

The key is that the thread only ever **grows**: `canonLabel` adds a new
association, or returns the existing one, and never changes the value carried
by a key already present.

- `ThreadExt`: two compatible threads;
- `lookup_append_ne` / `lookup_append_self`: what adding an association does
  to the other keys, and to its own;
- `canonSlots_ext`: the thread produced by `canonSlots` extends the thread
  received;
- `canonSlots_ranks`: **characterisation** — the numbers produced by
  `canonSlots` are, for every label, the value the final thread carries for
  it.

Two Lean core details govern the wording (measured, cf. the probes):
`List.lookup` compares the **query** with the stored key (`x == p.1`) and
unfolds into a boolean `match`; `List.append` is a well-founded recursion
definition (`appendTR`), which `simp` does not unfold — the head of an
appended list is therefore exposed by `show` (definitional), not by `rw`.
Finally hypotheses are reduced with `simp only`: the full `simp` rewrites
`lookup … = none` into an membership form, which would hide the `lookup`
shape the induction hypothesis expects.

The extraction theorem itself remains the residue of the tranche.
-/

/-- Two threads are compatible if every association carried by the first is
    still carried by the second, with the same value. -/
private def ThreadExt (seen seen' : List (Nat × Nat)) : Prop :=
  ∀ x v, seen.lookup x = some v → seen'.lookup x = some v

/-- The canonical rank of a label in a thread: the value the thread carries
    for it, `0` if the thread does not carry it. -/
private def threadRank (seen : List (Nat × Nat)) (x : Nat) : Nat :=
  match seen.lookup x with
  | some v => v
  | none => 0

/-- A key foreign to the addition does not move: `lookup` on the extended
    list answers as on the original list. -/
private theorem lookup_append_ne {l : List (Nat × Nat)} {x a : Nat} {v w : Nat}
    (h : l.lookup x = some v) (_hne : x ≠ a) :
    (l ++ [(a, w)]).lookup x = some v := by
  induction l with
  | nil => simp at h
  | cons p t ih =>
    simp only [List.lookup] at h
    by_cases hk : x == p.1
    · simp only [hk] at h
      have hv : p.2 = v := Option.some.inj h
      show List.lookup x (p :: (t ++ [(a, w)])) = some v
      simp only [List.lookup]
      simp only [hk]
      exact congrArg some hv
    · have hk' : (x == p.1) = false := by
        cases hb : x == p.1 with
        | true => exact False.elim (hk hb)
        | false => rfl
      simp only [hk'] at h
      show List.lookup x (p :: (t ++ [(a, w)])) = some v
      simp only [List.lookup]
      simp only [hk']
      exact ih h

/-- A key absent from the thread is found in the addition carrying it. -/
private theorem lookup_append_self {l : List (Nat × Nat)} {x : Nat} {w : Nat}
    (h : l.lookup x = none) :
    (l ++ [(x, w)]).lookup x = some w := by
  induction l with
  | nil => simp
  | cons p t ih =>
    simp only [List.lookup] at h
    by_cases hk : x == p.1
    · simp only [hk] at h
      cases h
    · have hk' : (x == p.1) = false := by
        cases hb : x == p.1 with
        | true => exact False.elim (hk hb)
        | false => rfl
      simp only [hk'] at h
      show List.lookup x (p :: (t ++ [(x, w)])) = some w
      simp only [List.lookup]
      simp only [hk']
      exact ih h

/-- The thread produced by `canonSlots` extends the thread received: no
    association already carried changes value. -/
private theorem canonSlots_ext (seen : List (Nat × Nat)) (xs : List Nat) :
    ThreadExt seen (canonSlots seen xs).2 := by
  induction xs generalizing seen with
  | nil =>
    intro x v h
    exact h
  | cons x xs ih =>
    cases hlk : seen.lookup x with
    | some v =>
      rw [canonSlots_cons_of_some hlk]
      intro y w hy
      exact ih seen y w hy
    | none =>
      rw [canonSlots_cons_of_none hlk]
      intro y w hy
      have hne : y ≠ x := by
        intro hyx
        subst hyx
        rw [hlk] at hy
        simp at hy
      have hy' : (seen ++ [(x, seen.length + 1)]).lookup y = some w :=
        lookup_append_ne hy hne
      exact ih (seen ++ [(x, seen.length + 1)]) y w hy'

/-- **Characterisation of the emitted numbers.** The numbers `canonSlots`
    produces are, for every label, the value the final thread carries for it:
    the rank of a label therefore does not depend on when it appears. -/
private theorem canonSlots_ranks (seen : List (Nat × Nat)) (xs : List Nat) :
    (canonSlots seen xs).1 = xs.map (fun x => threadRank (canonSlots seen xs).2 x) := by
  induction xs generalizing seen with
  | nil => rfl
  | cons x xs ih =>
    cases hlk : seen.lookup x with
    | some v =>
      have hpair : canonSlots seen (x :: xs) =
          (v :: (canonSlots seen xs).1, (canonSlots seen xs).2) :=
        canonSlots_cons_of_some hlk
      have h1 : (canonSlots seen (x :: xs)).1 = v :: (canonSlots seen xs).1 := by
        rw [hpair]
      have h2 : (canonSlots seen (x :: xs)).2 = (canonSlots seen xs).2 := by
        rw [hpair]
      rw [h1, h2]
      rw [List.map_cons]
      rw [ih seen]
      have hext := canonSlots_ext (seen := seen) (xs := xs)
      have hx : (canonSlots seen xs).2.lookup x = some v := hext x v hlk
      have hrank : threadRank (canonSlots seen xs).2 x = v := by
        simp only [threadRank, hx]
      rw [hrank]
    | none =>
      have hpair : canonSlots seen (x :: xs) =
          ((seen.length + 1) :: (canonSlots (seen ++ [(x, seen.length + 1)]) xs).1,
            (canonSlots (seen ++ [(x, seen.length + 1)]) xs).2) :=
        canonSlots_cons_of_none hlk
      have h1 : (canonSlots seen (x :: xs)).1 =
          (seen.length + 1) :: (canonSlots (seen ++ [(x, seen.length + 1)]) xs).1 := by
        rw [hpair]
      have h2 : (canonSlots seen (x :: xs)).2 =
          (canonSlots (seen ++ [(x, seen.length + 1)]) xs).2 := by
        rw [hpair]
      rw [h1, h2]
      rw [List.map_cons]
      rw [ih (seen ++ [(x, seen.length + 1)])]
      have hx' : (seen ++ [(x, seen.length + 1)]).lookup x = some (seen.length + 1) :=
        lookup_append_self hlk
      have hext := canonSlots_ext (seen := seen ++ [(x, seen.length + 1)]) (xs := xs)
      have hx : (canonSlots (seen ++ [(x, seen.length + 1)]) xs).2.lookup x =
          some (seen.length + 1) := hext x (seen.length + 1) hx'
      have hrank : threadRank (canonSlots (seen ++ [(x, seen.length + 1)]) xs).2 x =
          seen.length + 1 := by
        simp only [threadRank, hx]
      rw [hrank]


/-! ## 11. The final thread of a crossing list (tranche 6)

Extraction needs two things the previous tranches do not yet deliver: the
**final thread** of a crossing list (the view thread as it stands after the
last crossing), and the fact that the canonical row of a crossing is exactly
the list of the **ranks of its labels** in that final thread.

- `canonThreaded`: the canonical rows *and* the final thread;
- `go_eq_rows` / `canon_eq_rows`: `canon` carries the same rows as
  `canonThreaded`;
- `canonThreaded_faithful`: the final thread is faithful if the starting
  thread was;
- `canonThreaded_ext`: the final thread **extends** the starting thread;
- `canonSlots_lookup_some`: a threaded label is carried by the resulting
  thread;
- `canonThreaded_row_ranks`: **the row of a crossing is the list of the ranks
  of its four labels in the final thread**.

This last property is what links the two halves: the equality
`canon l = canon l'` then bears on *ranks*, not on positions.
-/

/-- Two lists agree point by point. -/
private theorem map_eq_of_pointwise {l : List Nat} {f g : Nat → Nat}
    (h : ∀ x ∈ l, f x = g x) : l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons]
    have hx := h x (by simp)
    have hxs : ∀ y ∈ xs, f y = g y := by
      intro y hy
      exact h y (by simp [hy])
    rw [hx, ih hxs]

/-- The canonical rows of a crossing list, and the view thread as it stands
    after the last crossing. -/
private def canonThreaded :
    List PDCrossing → List (Nat × Nat) → List (List Nat) × List (Nat × Nat)
  | [], seen => ([], seen)
  | c :: cs, seen =>
      let (ys, seen') := canonSlots seen [c.e1, c.e2, c.e3, c.e4]
      let (rows, seen'') := canonThreaded cs seen'
      (ys :: rows, seen'')

/-- `canon.go` and `canonThreaded` carry the same rows. -/
private theorem go_eq_rows (l : List PDCrossing) (seen : List (Nat × Nat)) :
    canon.go l seen = (canonThreaded l seen).1 := by
  induction l generalizing seen with
  | nil => rfl
  | cons c cs ih =>
    have hgo : canon.go (c :: cs) seen =
        (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).1 ::
          canon.go cs (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2 := rfl
    have hct : (canonThreaded (c :: cs) seen).1 =
        (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).1 ::
          (canonThreaded cs (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2).1 := rfl
    rw [hgo, hct, ih]

/-- `canon` and `canonThreaded` carry the same rows. -/
private theorem canon_eq_rows (l : List PDCrossing) :
    canon l = (canonThreaded l []).1 := by
  exact go_eq_rows l []

/-- The final thread is faithful if the starting thread was. -/
private theorem canonThreaded_faithful {l : List PDCrossing} {seen : List (Nat × Nat)}
    (hk : SeenKeysNodup seen) (hv : SeenValsNodup seen) (hb : SeenValsBounded seen) :
    SeenKeysNodup (canonThreaded l seen).2 ∧
      SeenValsNodup (canonThreaded l seen).2 ∧
      SeenValsBounded (canonThreaded l seen).2 := by
  induction l generalizing seen with
  | nil => exact ⟨hk, hv, hb⟩
  | cons c cs ih =>
    have hcs := canonSlots_faithful (seen := seen) (xs := [c.e1, c.e2, c.e3, c.e4]) hk hv hb
    have hct : (canonThreaded (c :: cs) seen).2 =
        (canonThreaded cs (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2).2 := rfl
    rw [hct]
    exact ih hcs.1 hcs.2.1 hcs.2.2

/-- Thread compatibility is transitive. -/
private theorem ThreadExt.trans {a b c : List (Nat × Nat)}
    (hab : ThreadExt a b) (hbc : ThreadExt b c) : ThreadExt a c := by
  intro x v h
  exact hbc x v (hab x v h)

/-- The final thread **extends** the starting thread: every association
    carried by the starting thread is still carried by the final one, with the
    same value. -/
private theorem canonThreaded_ext :
    ∀ (l : List PDCrossing) (seen : List (Nat × Nat)),
      ∀ x v, seen.lookup x = some v → (canonThreaded l seen).2.lookup x = some v := by
  intro l
  induction l with
  | nil =>
    intro seen x v h
    exact h
  | cons c cs ih =>
    intro seen x v h
    have h1 := canonSlots_ext (seen := seen) (xs := [c.e1, c.e2, c.e3, c.e4]) x v h
    have h2 := ih (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2 x v h1
    have hct : (canonThreaded (c :: cs) seen).2 =
        (canonThreaded cs (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2).2 := rfl
    rw [hct]
    exact h2

/-- A threaded label is carried by the resulting thread. -/
private theorem canonSlots_lookup_some {seen : List (Nat × Nat)} {xs : List Nat} {x : Nat}
    (hx : x ∈ xs) : ∃ v, (canonSlots seen xs).2.lookup x = some v := by
  induction xs generalizing seen with
  | nil => simp at hx
  | cons y ys ih =>
    cases hlk : seen.lookup y with
    | some v =>
      have hpair := congrArg Prod.snd
        (canonSlots_cons_of_some (seen := seen) (x := y) (v := v) (xs := ys) hlk)
      have hext := canonSlots_ext (seen := seen) (xs := ys)
      rw [hpair]
      simp only [List.mem_cons] at hx
      rcases hx with hxy | hx
      · exact ⟨v, hext x v (hxy ▸ hlk)⟩
      · obtain ⟨w, hw⟩ := ih (seen := seen) hx
        exact ⟨w, hw⟩
    | none =>
      have hpair := congrArg Prod.snd
        (canonSlots_cons_of_none (seen := seen) (x := y) (xs := ys) hlk)
      have hy : (seen ++ [(y, seen.length + 1)]).lookup y = some (seen.length + 1) :=
        lookup_append_self hlk
      have hext := canonSlots_ext (seen := seen ++ [(y, seen.length + 1)]) (xs := ys)
      rw [hpair]
      simp only [List.mem_cons] at hx
      rcases hx with hxy | hx
      · exact ⟨seen.length + 1, hxy ▸ hext y (seen.length + 1) hy⟩
      · obtain ⟨w, hw⟩ := ih (seen := seen ++ [(y, seen.length + 1)]) hx
        exact ⟨w, hw⟩

/-- **The row of a crossing is the list of the ranks of its four labels in
    the final thread.** This is the property linking the two halves of the
    bridge: the canonical number of a slot is the rank of its label in the
    resulting thread, not a position. -/
private theorem canonThreaded_row_ranks {c : PDCrossing} {cs : List PDCrossing}
    {seen : List (Nat × Nat)} :
    (canonThreaded (c :: cs) seen).1 =
      [c.e1, c.e2, c.e3, c.e4].map (fun x => threadRank (canonThreaded (c :: cs) seen).2 x) ::
        (canonThreaded cs (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2).1 := by
  have hranks := canonSlots_ranks (seen := seen) (xs := [c.e1, c.e2, c.e3, c.e4])
  have hct : (canonThreaded (c :: cs) seen).1 =
      (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).1 ::
        (canonThreaded cs (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2).1 := rfl
  have hext : ∀ x v,
      (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2.lookup x = some v →
        (canonThreaded (c :: cs) seen).2.lookup x = some v := by
    intro x v h
    have hct2 : (canonThreaded (c :: cs) seen).2 =
        (canonThreaded cs (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2).2 := rfl
    rw [hct2]
    exact canonThreaded_ext cs (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2 x v h
  have hcarried : ∀ x ∈ [c.e1, c.e2, c.e3, c.e4],
      ∃ v, (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2.lookup x = some v := by
    intro x hx
    exact canonSlots_lookup_some hx
  have hrank : ∀ x ∈ [c.e1, c.e2, c.e3, c.e4],
      threadRank (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2 x =
        threadRank (canonThreaded (c :: cs) seen).2 x := by
    intro x hx
    obtain ⟨v, hv⟩ := hcarried x hx
    have hT : (canonThreaded (c :: cs) seen).2.lookup x = some v := hext x v hv
    simp only [threadRank, hv, hT]
  rw [hct, hranks]
  exact congrArg (fun l => l :: (canonThreaded cs (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2).1)
    (map_eq_of_pointwise (l := [c.e1, c.e2, c.e3, c.e4]) hrank)

/-! ## 12. Injectivity of the rank (tranche 7)

Extraction needs the renaming `π` to be **well defined**: a label must
correspond to exactly one rank, and a rank to exactly one label. The first
half is `SeenKeysNodup` (§8); this is the second — a given rank is carried by
exactly one label.

- `mem_of_lookup`: what `lookup` returns is actually carried by the thread;
- `pair_eq_of_mem_of_snd_eq`: in a thread whose **values** are distinct, two
  associations with the same value are the same association;
- `threadRank_inj`: **the rank is injective** on the labels carried.
-/

/-- What `lookup` returns is actually carried by the thread. -/
private theorem mem_of_lookup {l : List (Nat × Nat)} {x v : Nat}
    (h : l.lookup x = some v) : (x, v) ∈ l := by
  induction l with
  | nil => simp at h
  | cons p t ih =>
    simp only [List.lookup] at h
    by_cases hk : x == p.1
    · simp only [hk] at h
      have hx : x = p.1 := by simpa using hk
      have hv : p.2 = v := Option.some.inj h
      have hp : (x, v) = p := by
        rcases p with ⟨a, b⟩
        simp only at hx hv
        subst hx
        subst hv
        rfl
      rw [hp]
      exact List.mem_cons_self
    · simp only [hk] at h
      exact List.mem_cons_of_mem p (ih h)

/-- In a thread whose values are distinct, two associations with the same
    value are the same association. -/
private theorem pair_eq_of_mem_of_snd_eq {l : List (Nat × Nat)}
    (hv : SeenValsNodup l) {x y v : Nat}
    (hx : (x, v) ∈ l) (hy : (y, v) ∈ l) : x = y := by
  unfold SeenValsNodup at hv
  induction l with
  | nil => simp at hx
  | cons p t ih =>
    simp only [List.map_cons, List.nodup_cons] at hv
    obtain ⟨hnotin, hnodup⟩ := hv
    simp only [List.mem_cons] at hx hy
    rcases hx with hxp | hxt
    · rcases hy with hyp | hyt
      · exact congrArg Prod.fst (hxp.trans hyp.symm)
      · exfalso
        have hp2 : p.2 = v := by rw [← hxp]
        have hmem : v ∈ t.map Prod.snd := List.mem_map_of_mem hyt
        rw [← hp2] at hmem
        exact hnotin hmem
    · rcases hy with hyp | hyt
      · exfalso
        have hp2 : p.2 = v := by rw [← hyp]
        have hmem : v ∈ t.map Prod.snd := List.mem_map_of_mem hxt
        rw [← hp2] at hmem
        exact hnotin hmem
      · exact ih hnodup hxt hyt

/-- **The rank is injective** on the labels carried: two labels carried by the
    thread with the same rank are the same label. -/
private theorem threadRank_inj {seen : List (Nat × Nat)} (hv : SeenValsNodup seen)
    {x y vx vy : Nat} (hx : seen.lookup x = some vx) (hy : seen.lookup y = some vy)
    (h : threadRank seen x = threadRank seen y) : x = y := by
  have h2 : vx = vy := by simpa only [threadRank, hx, hy] using h
  have hy' : seen.lookup y = some vx := by rw [h2]; exact hy
  exact pair_eq_of_mem_of_snd_eq hv (mem_of_lookup hx) (mem_of_lookup hy')
end Knots_en.AnyMoves
