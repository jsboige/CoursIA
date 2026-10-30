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
  type". Tranche 12 delivers the missing relation (`AnyEquiv`, section 18) and
  **bounds** the bridge instead of promising it: the route "choose or rename
  the target while keeping the large diagram" is **impossible**, proved by the
  kernel (section 18, `no_verifyR1Fwd_from_witness`). The remaining bridge
  requires either renaming the large diagram as well (the `dropLast` surgery
  then still to be established), or a **relabelling step inside the connected
  relation** — the latter touches `ReidemeisterStep`, hence `Invariant.lean`,
  and belongs to a coordinator arbitration, not to a lane edit;
- the equivalence `canon l = canon l' <-> exists injective renaming`: **closed**.
  The **invariance** half (`canon (mapC σ l) = canon l` for injective `σ`) is
  proved in section 7 (`canon_map_eq`); the **extraction** of the renaming from
  the `canon` equality is proved in section 16 (`canon_extraction`: a renaming
  injective on the labels of the source, which sends `l` onto `l'`); the
  **completeness** is proved in section 17 (`canon_rename_iff`) — the
  extraction, restricted to the labels of the source, is extended outside that
  range by a translation above all the labels of the target, which provides the
  **global** injection required by the "invariance" direction. Tranche 3 also
  fixes the `canonSlots` base (the state now survives the empty list): without
  it, the renumbering restarted at every crossing and `canon` equality accepted
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

/-! ## 13. The sequence of carried ranks (tranche 8)

So far the thread was described by **bounds**: its ranks live between `1` and
the size of the thread (§9). That is necessary, but insufficient for the
extraction: to recover the label of a given rank, the sequence of carried
ranks must be **exactly** `1, 2, …, n` — no gap, and in that order.

This is what this section establishes:

- `ThreadRanks`: the thread carries the sequence `1 … n`;
- `canonLabel_threadRanks`, `canonSlots_threadRanks`, `canonThreaded_threadRanks`: threading
  **preserves** that sequence (a new rank extends it by one);
- `lookup_eq_some_of_mem`: an entry of the thread is indeed the one `lookup`
  returns;
- `rank_covered`: **every** rank of `1 … n` is carried by a label of the
  thread;
- `rank_unique_label`: **a given rank corresponds to exactly one label**
  (existence by the sequence, uniqueness by the injectivity of the rank, §12).

This is the second half of the right definition of `π`: `SeenKeysNodup` (§8)
says a label has a single rank, `ThreadRanks` says a rank has a single label.
-/

/-- The sequence of ranks `1 … n`. -/
private def rankSeq (n : Nat) : List Nat := (List.range n).map (fun k => k + 1)

/-- The sequence `1 … n` extended by `n+1` is the sequence `1 … (n+1)`. -/
private theorem rankSeq_succ (n : Nat) : rankSeq (n + 1) = rankSeq n ++ [n + 1] := by
  unfold rankSeq
  rw [List.range_succ, List.map_append, List.map_singleton]

/-- The thread carries the ranks `1 … n`, in that order. -/
private def ThreadRanks (seen : List (Nat × Nat)) : Prop :=
  seen.map Prod.snd = rankSeq seen.length

/-- The empty thread carries the empty sequence. -/
private theorem threadRanks_nil : ThreadRanks [] := by
  simp [ThreadRanks, rankSeq]

/-- `canonLabel` preserves the sequence of ranks: an already carried rank does
    not move, a new rank extends the sequence by one. -/
private theorem canonLabel_threadRanks {seen : List (Nat × Nat)} {x : Nat}
    (h : ThreadRanks seen) : ThreadRanks (canonLabel seen x).2 := by
  unfold ThreadRanks
  cases hlk : seen.lookup x with
  | some v =>
    have hsame : (canonLabel seen x).2 = seen := by
      unfold canonLabel; rw [hlk]
    rw [hsame]
    exact h
  | none =>
    rw [show (canonLabel seen x).2 = seen ++ [(x, seen.length + 1)] by
      unfold canonLabel; rw [hlk]]
    simp only [List.map_append, List.map_singleton, List.length_append,
      List.length_singleton]
    rw [h, rankSeq_succ]

/-- Threading a sequence of labels preserves the sequence of ranks (induction
    on the sequence, arbitrary initial state). -/
private theorem canonSlots_threadRanks {seen : List (Nat × Nat)} {xs : List Nat}
    (h : ThreadRanks seen) : ThreadRanks (canonSlots seen xs).2 := by
  induction xs generalizing seen with
  | nil =>
    simp only [canonSlots]
    exact h
  | cons y ys ih =>
    cases hlk : seen.lookup y with
    | some v =>
      rw [canonSlots_cons_of_some hlk]
      exact ih h
    | none =>
      have hlab : (canonLabel seen y).2 = seen ++ [(y, seen.length + 1)] := by
        unfold canonLabel; rw [hlk]
      have hk' := canonLabel_threadRanks (seen := seen) (x := y) h
      rw [hlab] at hk'
      rw [canonSlots_cons_of_none hlk]
      exact ih hk'

/-- The final thread of a list of crossings carries the sequence of ranks. -/
private theorem canonThreaded_threadRanks {l : List PDCrossing} {seen : List (Nat × Nat)}
    (h : ThreadRanks seen) : ThreadRanks (canonThreaded l seen).2 := by
  induction l generalizing seen with
  | nil =>
    simp only [canonThreaded]
    exact h
  | cons c cs ih =>
    have hcs := canonSlots_threadRanks (seen := seen)
      (xs := [c.e1, c.e2, c.e3, c.e4]) h
    have hct : (canonThreaded (c :: cs) seen).2 =
        (canonThreaded cs (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2).2 := rfl
    rw [hct]
    exact ih hcs

/-- An entry of the thread is indeed the one `lookup` returns: with distinct
    keys, the query that targets an entry returns its value. -/
private theorem lookup_eq_some_of_mem (l : List (Nat × Nat))
    (hk : SeenKeysNodup l) (p : Nat × Nat) (hp : p ∈ l) :
    l.lookup p.1 = some p.2 := by
  induction l with
  | nil => simp at hp
  | cons q t ih =>
    unfold SeenKeysNodup at hk
    simp only [List.map_cons, List.nodup_cons] at hk
    obtain ⟨hnotin, hnodup⟩ := hk
    simp only [List.mem_cons] at hp
    rcases hp with hpq | hpt
    · subst hpq
      simp only [List.lookup, beq_self_eq_true]
    · have hne : (p.1 == q.1) = false := by
        rw [beq_eq_false_iff_ne]
        intro hqc
        apply hnotin
        rw [← hqc]
        exact List.mem_map.mpr ⟨p, hpt, rfl⟩
      simp only [List.lookup, hne]
      exact ih hnodup hpt

/-- **Every** rank of the thread is carried by a label of the thread: the
    sequence `1 … n` is covered. -/
private theorem rank_covered {seen : List (Nat × Nat)} (h : ThreadRanks seen)
    (hk : SeenKeysNodup seen) {r : Nat} (hr : 1 ≤ r ∧ r ≤ seen.length) :
    ∃ x, seen.lookup x = some r := by
  have hr1 : r - 1 ∈ List.range seen.length := by
    rw [List.mem_range]
    omega
  have hmem : r ∈ seen.map Prod.snd := by
    rw [ThreadRanks] at h
    unfold rankSeq at h
    rw [h, List.mem_map]
    exact ⟨r - 1, hr1, by omega⟩
  obtain ⟨p, hp, hpv⟩ := List.mem_map.mp hmem
  refine ⟨p.1, ?_⟩
  rw [lookup_eq_some_of_mem seen hk p hp]
  exact congrArg some hpv

/-- **A given rank corresponds to exactly one label** of the thread:
    existence comes from the sequence of ranks, uniqueness from the
    injectivity of the rank (§12). -/
private theorem rank_unique_label {seen : List (Nat × Nat)}
    (hv : SeenValsNodup seen) (hk : SeenKeysNodup seen) (hr : ThreadRanks seen)
    {r : Nat} (hb : 1 ≤ r ∧ r ≤ seen.length) :
    (∃ x, seen.lookup x = some r) ∧
      ∀ x y, seen.lookup x = some r → seen.lookup y = some r → x = y := by
  constructor
  · exact rank_covered hr hk hb
  · intro x y hx hy
    exact threadRank_inj hv hx hy (by simp [threadRank, hx, hy])

/-! ## 14. The correspondence of rows (tranche 9)

The equality `canon l = canon l'` concerns **rows**: to every crossing of `l`
corresponds a crossing of `l'`, and the **four slots** correspond positionally.
This is the property that makes the renaming composable: slot `j` of a
crossing of `l` and slot `j` of the corresponding crossing of `l'` carry the
**same rank** in their respective final threads.

The ranks are taken in the final thread of the **current sublist**: the final
thread of a list is the one of its last sublist, threaded from the state it
receives — hence the parallel recursion on the two lists.

- `RowsCorrespond`: the correspondence, stated as a parallel recursion;
- `four_slots_eq`: two rows of four equal slots correspond positionally;
- `rows_correspond`: two lists carrying the same canonical rows correspond
  rank by rank, slot by slot.
-/

/-- Two lists of four slots that are equal correspond positionally: the slot of
    rank `j` on one side is paired with the slot of rank `j` on the other. -/
private theorem four_slots_eq {a b c d a' b' c' d' : Nat} {f g : Nat → Nat}
    (h : [a, b, c, d].map f = [a', b', c', d'].map g) :
    f a = g a' ∧ f b = g b' ∧ f c = g c' ∧ f d = g d' := by
  simp only [List.map] at h
  rcases List.cons.inj h with ⟨h1, h2⟩
  rcases List.cons.inj h2 with ⟨h2', h3⟩
  rcases List.cons.inj h3 with ⟨h3', h4⟩
  rcases List.cons.inj h4 with ⟨h4', _⟩
  exact ⟨h1, h2', h3', h4'⟩

/-- Two lists of crossings correspond when, at every mutually paired crossing,
    the four slots carry the same rank. The ranks are taken in the final
    thread of the current sublist — the final thread of the whole list being
    the one of its last sublist, threaded from the state it receives. -/
private def RowsCorrespond (seen seen' : List (Nat × Nat)) (cs cs' : List PDCrossing) : Prop :=
  match cs, cs' with
  | [], [] => True
  | c :: tl, c' :: tl' =>
      (threadRank (canonThreaded (c :: tl) seen).2 c.e1 =
          threadRank (canonThreaded (c' :: tl') seen').2 c'.e1) ∧
      (threadRank (canonThreaded (c :: tl) seen).2 c.e2 =
          threadRank (canonThreaded (c' :: tl') seen').2 c'.e2) ∧
      (threadRank (canonThreaded (c :: tl) seen).2 c.e3 =
          threadRank (canonThreaded (c' :: tl') seen').2 c'.e3) ∧
      (threadRank (canonThreaded (c :: tl) seen).2 c.e4 =
          threadRank (canonThreaded (c' :: tl') seen').2 c'.e4) ∧
      RowsCorrespond (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2
        (canonSlots seen' [c'.e1, c'.e2, c'.e3, c'.e4]).2 tl tl'
  | _, _ => False

/-- **Two lists carrying the same canonical rows correspond rank by rank, slot
    by slot.** This is the lemma that links the two halves of the bridge: the
    equality `canon l = canon l'` associates to every crossing of `l` a
    crossing of `l'`, and to every slot a slot — by the equality of the ranks. -/
private theorem rows_correspond :
    ∀ (cs : List PDCrossing) (seen seen' : List (Nat × Nat)) (cs' : List PDCrossing),
      (canonThreaded cs seen).1 = (canonThreaded cs' seen').1 →
      RowsCorrespond seen seen' cs cs' := by
  intro cs
  induction cs with
  | nil =>
      intro seen seen' cs' h
      cases cs' with
      | nil => trivial
      | cons c' tl' =>
          have hne : (canonThreaded (c' :: tl') seen').1 ≠ [] := by
            intro hh
            have hct : (canonThreaded (c' :: tl') seen').1 =
                (canonSlots seen' [c'.e1, c'.e2, c'.e3, c'.e4]).1 ::
                  (canonThreaded tl' (canonSlots seen' [c'.e1, c'.e2, c'.e3, c'.e4]).2).1 := rfl
            rw [hct] at hh
            exact (List.cons_ne_nil _ _ hh).elim
          exact absurd (h.symm.trans rfl) hne
  | cons c tl ih =>
      intro seen seen' cs' h
      cases cs' with
      | nil =>
          have hne : (canonThreaded (c :: tl) seen).1 ≠ [] := by
            intro hh
            have hct : (canonThreaded (c :: tl) seen).1 =
                (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).1 ::
                  (canonThreaded tl (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2).1 := rfl
            rw [hct] at hh
            exact (List.cons_ne_nil _ _ hh).elim
          exact absurd h hne
      | cons c' tl' =>
          have hct1 : (canonThreaded (c :: tl) seen).1 =
              (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).1 ::
                (canonThreaded tl (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2).1 := rfl
          have hct2 : (canonThreaded (c' :: tl') seen').1 =
              (canonSlots seen' [c'.e1, c'.e2, c'.e3, c'.e4]).1 ::
                (canonThreaded tl' (canonSlots seen' [c'.e1, c'.e2, c'.e3, c'.e4]).2).1 := rfl
          rw [hct1, hct2] at h
          rcases List.cons.inj h with ⟨hhead, htail⟩
          have hr1 := canonThreaded_row_ranks (c := c) (cs := tl) (seen := seen)
          have hr2 := canonThreaded_row_ranks (c := c') (cs := tl') (seen := seen')
          have hrow1 : ([c.e1, c.e2, c.e3, c.e4].map
                  (fun x => threadRank (canonThreaded (c :: tl) seen).2 x) ::
                (canonThreaded tl (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2).1) =
              ((canonSlots seen [c.e1, c.e2, c.e3, c.e4]).1 ::
                (canonThreaded tl (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2).1) :=
            hr1.symm.trans hct1
          rcases List.cons.inj hrow1 with ⟨hmap, _⟩
          have hrow2 : ([c'.e1, c'.e2, c'.e3, c'.e4].map
                  (fun x => threadRank (canonThreaded (c' :: tl') seen').2 x) ::
                (canonThreaded tl' (canonSlots seen' [c'.e1, c'.e2, c'.e3, c'.e4]).2).1) =
              ((canonSlots seen' [c'.e1, c'.e2, c'.e3, c'.e4]).1 ::
                (canonThreaded tl' (canonSlots seen' [c'.e1, c'.e2, c'.e3, c'.e4]).2).1) :=
            hr2.symm.trans hct2
          rcases List.cons.inj hrow2 with ⟨hmap', _⟩
          have hmap'' : ([c.e1, c.e2, c.e3, c.e4].map
                (fun x => threadRank (canonThreaded (c :: tl) seen).2 x)) =
              ([c'.e1, c'.e2, c'.e3, c'.e4].map
                (fun x => threadRank (canonThreaded (c' :: tl') seen').2 x)) :=
            hmap.trans (hhead.trans hmap'.symm)
          rcases four_slots_eq hmap'' with ⟨h1, h2, h3, h4⟩
          refine ⟨h1, h2, h3, h4, ?_⟩
          exact ih (seen := (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2)
              (seen' := (canonSlots seen' [c'.e1, c'.e2, c'.e3, c'.e4]).2)
              (cs' := tl') htail

/-! ## 15. The label of a rank (tranche 9)

The previous tranches established that a rank carried by a thread is carried by
**one** label (§13) and that a given rank corresponds to **exactly one** label
(§13). What was missing was the **operator** that recovers the label of a given
rank: without it, the renaming `π` cannot be written.

- `pairOfRank`: the first entry of the thread that carries the requested rank;
- `pairOfRank_mem` / `pairOfRank_none`: what it guarantees, and its contrary;
- `labelOfRank`: the label that carries the rank;
- `labelOfRank_spec`: the label returned is indeed the one `lookup` returns;
- `labelOfRank_exists`: every carried rank is carried by the label returned;
- `labelOfRank_inj`: two distinct ranks are never carried by the same label.
-/

/-- The first entry of the thread `t` that carries the rank `r`. -/
private def pairOfRank : List (Nat × Nat) → Nat → Option (Nat × Nat)
  | [], _ => none
  | p :: t, r => if p.2 = r then some p else pairOfRank t r

/-- The entry returned by `pairOfRank` is indeed in the thread, and carries the
    requested rank. -/
private theorem pairOfRank_mem {t : List (Nat × Nat)} {r : Nat} {p : Nat × Nat}
    (h : pairOfRank t r = some p) : p ∈ t ∧ p.2 = r := by
  induction t with
  | nil => simp [pairOfRank] at h
  | cons q t ih =>
      by_cases hq : q.2 = r
      · have hq' : pairOfRank (q :: t) r = some q := by simp [pairOfRank, hq]
        rw [hq'] at h
        have hpq : p = q := (Option.some.inj h).symm
        subst hpq
        exact ⟨List.mem_cons_self, hq⟩
      · have hq' : pairOfRank (q :: t) r = pairOfRank t r := by simp [pairOfRank, hq]
        rw [hq'] at h
        obtain ⟨hm, hv⟩ := ih h
        exact ⟨List.mem_cons_of_mem q hm, hv⟩

/-- No entry of the thread carries the requested rank when `pairOfRank` returns
    nothing. -/
private theorem pairOfRank_none {t : List (Nat × Nat)} {r : Nat}
    (h : pairOfRank t r = none) : ∀ p ∈ t, p.2 ≠ r := by
  induction t with
  | nil => intro p hp; simp at hp
  | cons q t ih =>
      intro p hp
      by_cases hq : q.2 = r
      · have hq' : pairOfRank (q :: t) r = some q := by simp [pairOfRank, hq]
        rw [hq'] at h
        simp at h
      · have hq' : pairOfRank (q :: t) r = pairOfRank t r := by simp [pairOfRank, hq]
        rw [hq'] at h
        rcases List.mem_cons.mp hp with hpq | hpt
        · rw [hpq]
          exact hq
        · exact ih h p hpt

/-- The label that carries the rank `r` in the thread `t`. -/
private def labelOfRank (t : List (Nat × Nat)) (r : Nat) : Option Nat :=
  (pairOfRank t r).map Prod.fst

/-- The label returned by `labelOfRank` is indeed the one `lookup` returns: with
    distinct keys, it carries the requested rank. -/
private theorem labelOfRank_spec {t : List (Nat × Nat)} (hk : SeenKeysNodup t)
    {r y : Nat} (h : labelOfRank t r = some y) : t.lookup y = some r := by
  unfold labelOfRank at h
  cases hp : pairOfRank t r with
  | none => simp [hp] at h
  | some p =>
      have hmem := pairOfRank_mem hp
      have hlookup := lookup_eq_some_of_mem t hk p hmem.1
      have hpy : p.1 = y := by
        simp [hp] at h
        exact h
      calc t.lookup y = t.lookup p.1 := by rw [hpy]
        _ = some p.2 := hlookup
        _ = some r := by rw [hmem.2]

/-- **Every** rank carried by the thread is carried by the label that
    `labelOfRank` returns. Existence comes from the sequence of ranks (§13),
    uniqueness from the injectivity of the values (§12). -/
private theorem labelOfRank_exists {t : List (Nat × Nat)} (hv : SeenValsNodup t)
    (hk : SeenKeysNodup t) (hr : ThreadRanks t) {r : Nat} (hb : 1 ≤ r ∧ r ≤ t.length) :
    ∃ y, labelOfRank t r = some y ∧ t.lookup y = some r := by
  obtain ⟨x, hx⟩ := rank_covered hr hk hb
  have hmem := mem_of_lookup hx
  have hnone : pairOfRank t r ≠ none := by
    intro hn
    exact absurd rfl (pairOfRank_none hn (x, r) hmem)
  cases hp : pairOfRank t r with
  | none => exact absurd hp hnone
  | some p =>
      have hpm := pairOfRank_mem hp
      have hpm' : (p.1, r) ∈ t := by rw [← hpm.2]; exact hpm.1
      have hpx : p.1 = x := pair_eq_of_mem_of_snd_eq hv hpm' hmem
      refine ⟨p.1, ?_, ?_⟩
      · simp [labelOfRank, hp]
      · rw [hpx]
        exact hx

/-- Two distinct ranks are never carried by the same label. -/
private theorem labelOfRank_inj {t : List (Nat × Nat)} (hk : SeenKeysNodup t)
    {r s y z : Nat} (hr : labelOfRank t r = some y) (hs : labelOfRank t s = some z)
    (hne : r ≠ s) : y ≠ z := by
  intro h
  subst h
  have h1 := labelOfRank_spec hk hr
  have h2 := labelOfRank_spec hk hs
  rw [h1] at h2
  exact hne (Option.some.inj h2)


/-! ## 16. The extracted renaming (tranche 10)

The previous tranches established that the equality `canon l = canon l'` pairs
every crossing of `l` with a crossing of `l'`, and every slot with a slot, by
equality of **ranks** (§14), and that a given rank is carried by **exactly one
label** (§13, §15). What was missing was the **composition**: the operator `π`
that renames the labels, and the proof that it is well defined, **injective**,
and that it sends `l` onto `l'`.

- `labelsOf`: the labels carried by a list of crossings;
- `Tfinal`: the final thread of a list of crossings;
- `labelsOf_carried`: a carried label is carried by the final thread;
- `rank_transfer_acc`: the row correspondence **transports the ranks**;
- `piOfT` / `piOf`: the renaming;
- `pi_of_rank`: for a given rank, the renaming returns the label carrying it;
- `pi_transfer`: the rank travels to the target, and the renaming follows;
- `pi_inj`: the renaming is **injective** on the labels of the source;
- `mapC_pi_acc`: the renaming **sends `l` onto `l'`**;
- `canon_extraction`: the extraction, in the shape of the bridge.

The shape of the renaming is the **rank**: the label of `l'` carrying the same
rank as the label of `l`. The sequence of ranks `1 … n` (§13) guarantees that
this label exists and is unique; the injectivity of the rank (§12) guarantees
that the renaming never confuses two distinct labels.
-/

/-- The labels carried by a list of crossings: the four labels of each
    crossing, in order. -/
private def labelsOf (l : List PDCrossing) : List Nat :=
  l.flatMap fun c => [c.e1, c.e2, c.e3, c.e4]

/-- The final thread of a list of crossings: the thread rendered after the
    last crossing, threaded from the empty thread. -/
private def Tfinal (l : List PDCrossing) : List (Nat × Nat) :=
  (canonThreaded l []).2

/-- The renaming: the label of the target carrying the same rank as the label
    of the source. Outside the range of the labels of the source, the renaming
    returns the label itself. -/
private def piOfT (T T' : List (Nat × Nat)) (x : Nat) : Nat :=
  match labelOfRank T' (threadRank T x) with
  | some y => y
  | none => x

/-- The renaming of the labels of `l` into labels of `l'`. -/
private def piOf (l l' : List PDCrossing) (x : Nat) : Nat :=
  piOfT (Tfinal l) (Tfinal l') x

/-- The rank of a carried label is the value the thread carries for it. -/
private theorem threadRank_of_lookup {t : List (Nat × Nat)} {x v : Nat}
    (h : t.lookup x = some v) : threadRank t x = v := by
  simp only [threadRank, h]

/-- The labels of a crossing are those of the list carrying it. -/
private theorem labelsOf_cons (c : PDCrossing) (cs : List PDCrossing) :
    labelsOf (c :: cs) = [c.e1, c.e2, c.e3, c.e4] ++ labelsOf cs := rfl

/-- A label of the current crossing is carried by the list. -/
private theorem mem_labelsOf_head {c : PDCrossing} {cs : List PDCrossing} {x : Nat}
    (hx : x ∈ [c.e1, c.e2, c.e3, c.e4]) : x ∈ labelsOf (c :: cs) := by
  rw [labelsOf_cons]
  exact List.mem_append.mpr (Or.inl hx)

/-- A label carried by the tail is also carried by the whole list. -/
private theorem mem_labelsOf_tail {c : PDCrossing} {cs : List PDCrossing} {x : Nat}
    (hx : x ∈ labelsOf cs) : x ∈ labelsOf (c :: cs) := by
  rw [labelsOf_cons]
  exact List.mem_append.mpr (Or.inr hx)

/-- A label of the list is either one of the current crossing or one of the
    tail. -/
private theorem labelsOf_cons_cases {c : PDCrossing} {cs : List PDCrossing} {x : Nat}
    (hx : x ∈ labelsOf (c :: cs)) : x ∈ [c.e1, c.e2, c.e3, c.e4] ∨ x ∈ labelsOf cs := by
  rw [labelsOf_cons] at hx
  exact List.mem_append.mp hx

/-- **A carried label is carried by the rendered thread**, with a value. -/
private theorem labelsOf_carried :
    ∀ (l : List PDCrossing) (seen : List (Nat × Nat)) (x : Nat),
      x ∈ labelsOf l → ∃ v, (canonThreaded l seen).2.lookup x = some v := by
  intro l
  induction l with
  | nil =>
      intro seen x hx
      have hnil : labelsOf ([] : List PDCrossing) = [] := rfl
      rw [hnil] at hx
      simp at hx
  | cons c cs ih =>
      intro seen x hx
      have hct : (canonThreaded (c :: cs) seen).2 =
          (canonThreaded cs (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2).2 := rfl
      rcases labelsOf_cons_cases hx with hxs | hxs
      · have hx' := canonSlots_lookup_some (seen := seen)
          (xs := [c.e1, c.e2, c.e3, c.e4]) hxs
        obtain ⟨v, hv⟩ := hx'
        have h2 := canonThreaded_ext cs
          (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2 x v hv
        rw [hct]
        exact ⟨v, h2⟩
      · have hx' := ih (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2 x hxs
        obtain ⟨v, hv⟩ := hx'
        rw [hct]
        exact ⟨v, hv⟩

/-- **Two threads carrying the same rank carry the same value.** -/
private theorem rank_pair {S S' : List (Nat × Nat)} {x y : Nat}
    (hr : threadRank S x = threadRank S' y)
    (hx : ∃ v, S.lookup x = some v) (hy : ∃ v, S'.lookup y = some v) :
    ∃ v, S.lookup x = some v ∧ S'.lookup y = some v := by
  obtain ⟨v, hv⟩ := hx
  obtain ⟨v', hv'⟩ := hy
  have h1 : threadRank S x = v := threadRank_of_lookup hv
  have h2 : threadRank S' y = v' := threadRank_of_lookup hv'
  rw [h1] at hr
  rw [h2] at hr
  have hvg : v' = v := hr.symm
  refine ⟨v, hv, ?_⟩
  rw [hvg] at hv'
  exact hv'

/-- The correspondence, decomposed at the "crossing / crossing" case. -/
private theorem rowsCorrespond_cons {c c' : PDCrossing} {cs cs' : List PDCrossing}
    {seen seen' : List (Nat × Nat)} (h : RowsCorrespond seen seen' (c :: cs) (c' :: cs')) :
    (threadRank (canonThreaded (c :: cs) seen).2 c.e1 =
        threadRank (canonThreaded (c' :: cs') seen').2 c'.e1) ∧
    (threadRank (canonThreaded (c :: cs) seen).2 c.e2 =
        threadRank (canonThreaded (c' :: cs') seen').2 c'.e2) ∧
    (threadRank (canonThreaded (c :: cs) seen).2 c.e3 =
        threadRank (canonThreaded (c' :: cs') seen').2 c'.e3) ∧
    (threadRank (canonThreaded (c :: cs) seen).2 c.e4 =
        threadRank (canonThreaded (c' :: cs') seen').2 c'.e4) ∧
    RowsCorrespond (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2
      (canonSlots seen' [c'.e1, c'.e2, c'.e3, c'.e4]).2 cs cs' :=
  h

/-- The correspondence, decomposed at the "empty list on the left" case. -/
private theorem rowsCorrespond_nil_left {c' : PDCrossing} {cs' : List PDCrossing}
    {seen seen' : List (Nat × Nat)} (h : RowsCorrespond seen seen' [] (c' :: cs')) : False :=
  h

/-- The correspondence, decomposed at the "empty list on the right" case. -/
private theorem rowsCorrespond_nil_right {c : PDCrossing} {cs : List PDCrossing}
    {seen seen' : List (Nat × Nat)} (h : RowsCorrespond seen seen' (c :: cs) []) : False :=
  h

/-- **The row correspondence transports the ranks.** Every label of `l` is
    paired with a label of `l'` carrying the same rank in the respective
    threads. -/
private theorem rank_transfer_acc :
    ∀ (l l' : List PDCrossing) (seen seen' : List (Nat × Nat)),
      RowsCorrespond seen seen' l l' →
      ∀ x, x ∈ labelsOf l → ∃ y, y ∈ labelsOf l' ∧
        threadRank (canonThreaded l seen).2 x = threadRank (canonThreaded l' seen').2 y := by
  intro l
  induction l with
  | nil =>
      intro l' seen seen' hrc x hx
      have hnil : labelsOf ([] : List PDCrossing) = [] := rfl
      rw [hnil] at hx
      simp at hx
  | cons c cs ih =>
      intro l' seen seen' hrc x hx
      cases l' with
      | nil =>
          exact (rowsCorrespond_nil_right hrc).elim
      | cons c' cs' =>
          rcases rowsCorrespond_cons hrc with ⟨h1, h2, h3, h4, hrc'⟩
          rcases labelsOf_cons_cases hx with hxs | hxs
          · rcases List.mem_cons.mp hxs with h | h
            · subst h
              refine ⟨c'.e1, mem_labelsOf_head (c := c') (cs := cs') (by
                simp), ?_⟩
              exact h1
            · rcases List.mem_cons.mp h with h | h
              · subst h
                refine ⟨c'.e2, mem_labelsOf_head (c := c') (cs := cs') (by
                  simp), ?_⟩
                exact h2
              · rcases List.mem_cons.mp h with h | h
                · subst h
                  refine ⟨c'.e3, mem_labelsOf_head (c := c') (cs := cs') (by
                    simp), ?_⟩
                  exact h3
                · rcases List.mem_cons.mp h with h | h
                  · subst h
                    refine ⟨c'.e4, mem_labelsOf_head (c := c') (cs := cs') (by
                      simp), ?_⟩
                    exact h4
                  · simp at h
          · obtain ⟨y, hy, hrank⟩ := ih cs'
              (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2
              (canonSlots seen' [c'.e1, c'.e2, c'.e3, c'.e4]).2 hrc' x hxs
            refine ⟨y, mem_labelsOf_tail (c := c') (cs := cs') hy, ?_⟩
            have hct : (canonThreaded (c :: cs) seen).2 =
                (canonThreaded cs (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2).2 := rfl
            have hct' : (canonThreaded (c' :: cs') seen').2 =
                (canonThreaded cs' (canonSlots seen' [c'.e1, c'.e2, c'.e3, c'.e4]).2).2 := rfl
            rw [hct, hct']
            exact hrank

/-- The final thread is faithful when the empty thread is. -/
private theorem Tfinal_faithful (l : List PDCrossing) :
    SeenKeysNodup (Tfinal l) ∧ SeenValsNodup (Tfinal l) ∧ SeenValsBounded (Tfinal l) := by
  have h := canonThreaded_faithful (l := l) (seen := [])
    (hk := by simp [SeenKeysNodup]) (hv := by simp [SeenValsNodup])
    (hb := by simp [SeenValsBounded])
  exact h

/-- The final thread carries the sequence of ranks `1 … n`. -/
private theorem Tfinal_ranks (l : List PDCrossing) : ThreadRanks (Tfinal l) := by
  have h := canonThreaded_threadRanks (l := l) (seen := []) threadRanks_nil
  exact h

/-- **For a given rank, the renaming returns the label carrying it.** -/
private theorem pi_of_rank {T T' : List (Nat × Nat)} (hv : SeenValsNodup T')
    (hk : SeenKeysNodup T') (hr : ThreadRanks T') (hb : SeenValsBounded T')
    {x y r : Nat} (hx : T.lookup x = some r) (hy : T'.lookup y = some r) :
    piOfT T T' x = y := by
  have hmem := mem_of_lookup hy
  have hb' := hb (y, r) hmem
  have hbound : 1 ≤ r ∧ r ≤ T'.length := by
    constructor
    · omega
    · exact hb'.2
  obtain ⟨z, hz, hzl⟩ := labelOfRank_exists hv hk hr hbound
  have h1 : threadRank T' y = r := threadRank_of_lookup hy
  have h2 : threadRank T' z = r := threadRank_of_lookup hzl
  have hyz : y = z := threadRank_inj hv hy hzl (h1.trans h2.symm)
  subst hyz
  have htx : threadRank T x = r := threadRank_of_lookup hx
  simp only [piOfT, htx, hz]

/-- **The rank travels to the target, and the renaming follows.** -/
private theorem pi_transfer {l l' : List PDCrossing} (hrc : RowsCorrespond [] [] l l') :
    ∀ x, x ∈ labelsOf l →
      ∃ y, y ∈ labelsOf l' ∧ piOf l l' x = y ∧
        threadRank (Tfinal l') (piOf l l' x) = threadRank (Tfinal l) x := by
  intro x hx
  obtain ⟨y, hy, hrank⟩ := rank_transfer_acc (l := l) (l' := l') (seen := [])
    (seen' := []) hrc x hx
  have hxv : ∃ v, (Tfinal l).lookup x = some v := labelsOf_carried l [] x hx
  have hxv' : ∃ v, (Tfinal l').lookup y = some v := labelsOf_carried l' [] y hy
  obtain ⟨v, hv⟩ := hxv
  obtain ⟨v', hv'⟩ := hxv'
  have hvg : v' = v := by
    have h1 : threadRank (Tfinal l') y = v' := threadRank_of_lookup hv'
    have h2 : threadRank (Tfinal l') y = threadRank (Tfinal l) x := hrank.symm
    have h3 : threadRank (Tfinal l) x = v := threadRank_of_lookup hv
    rw [h1] at h2
    rw [h3] at h2
    exact h2
  have hf := Tfinal_faithful l'
  have hpi : piOf l l' x = y := pi_of_rank (T := Tfinal l) (T' := Tfinal l')
    hf.2.1 hf.1 (Tfinal_ranks l') hf.2.2 hv (by
      rw [hvg] at hv'
      exact hv')
  refine ⟨y, hy, hpi, ?_⟩
  rw [hpi]
  have h1 : threadRank (Tfinal l') y = v' := threadRank_of_lookup hv'
  rw [h1]
  have h2 : threadRank (Tfinal l) x = v := threadRank_of_lookup hv
  rw [h2]
  exact hvg

/-- **The renaming is injective** on the labels of the source: two distinct
    labels are never confused. -/
private theorem pi_inj {l l' : List PDCrossing} (hrc : RowsCorrespond [] [] l l') :
    ∀ x y, x ∈ labelsOf l → y ∈ labelsOf l → piOf l l' x = piOf l l' y → x = y := by
  intro x y hx hy hxy
  obtain ⟨z, hz, hpi, hrank⟩ := pi_transfer hrc x hx
  obtain ⟨w, hw, hpi', hrank'⟩ := pi_transfer hrc y hy
  have hA : threadRank (Tfinal l') (piOf l l' x) = threadRank (Tfinal l') (piOf l l' y) := by
    rw [hxy]
  have h1 : threadRank (Tfinal l) x = threadRank (Tfinal l) y :=
    hrank.symm.trans (hA.trans hrank')
  have hxv : ∃ v, (Tfinal l).lookup x = some v := labelsOf_carried l [] x hx
  have hxv' : ∃ v, (Tfinal l).lookup y = some v := labelsOf_carried l [] y hy
  obtain ⟨v, hv⟩ := hxv
  obtain ⟨v', hv'⟩ := hxv'
  exact threadRank_inj (Tfinal_faithful l).2.1 hv hv' h1

/-- **A crossing and its image carry the same global rank.** -/
private theorem head_pi {c c' : PDCrossing} {cs cs' : List PDCrossing}
    {seen seen' : List (Nat × Nat)} {T T' : List (Nat × Nat)} {x y : Nat}
    (he : ThreadExt (canonThreaded (c :: cs) seen).2 T)
    (he' : ThreadExt (canonThreaded (c' :: cs') seen').2 T')
    (hr : threadRank (canonThreaded (c :: cs) seen).2 x =
      threadRank (canonThreaded (c' :: cs') seen').2 y)
    (hx : x ∈ labelsOf (c :: cs)) (hy : y ∈ labelsOf (c' :: cs')) :
    ∃ v, T.lookup x = some v ∧ T'.lookup y = some v := by
  have hxv : ∃ v, (canonThreaded (c :: cs) seen).2.lookup x = some v :=
    labelsOf_carried (c :: cs) seen x hx
  have hxv' : ∃ v, (canonThreaded (c' :: cs') seen').2.lookup y = some v :=
    labelsOf_carried (c' :: cs') seen' y hy
  obtain ⟨v, hv, hv'⟩ := rank_pair hr hxv hxv'
  exact ⟨v, he x v hv, he' y v hv'⟩

/-- **The renaming sends the source list onto the target list.** -/
private theorem mapC_pi_acc :
    ∀ (l0 l'0 l l' : List PDCrossing) (seen seen' : List (Nat × Nat)),
      ThreadExt (canonThreaded l seen).2 (Tfinal l0) →
      ThreadExt (canonThreaded l' seen').2 (Tfinal l'0) →
      RowsCorrespond seen seen' l l' →
      mapC (piOfT (Tfinal l0) (Tfinal l'0)) l = l' := by
  intro l0 l'0 l
  induction l with
  | nil =>
      intro l' seen seen' he he' hrc
      cases l' with
      | nil => rfl
      | cons c' cs' => exact (rowsCorrespond_nil_left hrc).elim
  | cons c cs ih =>
      intro l' seen seen' he he' hrc
      cases l' with
      | nil => exact (rowsCorrespond_nil_right hrc).elim
      | cons c' cs' =>
          rcases rowsCorrespond_cons hrc with ⟨h1, h2, h3, h4, hrc'⟩
          have hf := Tfinal_faithful l'0
          have hhead1 : piOfT (Tfinal l0) (Tfinal l'0) c.e1 = c'.e1 := by
            obtain ⟨v, hvx, hvy⟩ := head_pi he he' h1
              (mem_labelsOf_head (c := c) (cs := cs) (by simp))
              (mem_labelsOf_head (c := c') (cs := cs') (by simp))
            exact pi_of_rank (T := Tfinal l0) (T' := Tfinal l'0)
              hf.2.1 hf.1 (Tfinal_ranks l'0) hf.2.2 hvx hvy
          have hhead2 : piOfT (Tfinal l0) (Tfinal l'0) c.e2 = c'.e2 := by
            obtain ⟨v, hvx, hvy⟩ := head_pi he he' h2
              (mem_labelsOf_head (c := c) (cs := cs) (by simp))
              (mem_labelsOf_head (c := c') (cs := cs') (by simp))
            exact pi_of_rank (T := Tfinal l0) (T' := Tfinal l'0)
              hf.2.1 hf.1 (Tfinal_ranks l'0) hf.2.2 hvx hvy
          have hhead3 : piOfT (Tfinal l0) (Tfinal l'0) c.e3 = c'.e3 := by
            obtain ⟨v, hvx, hvy⟩ := head_pi he he' h3
              (mem_labelsOf_head (c := c) (cs := cs) (by simp))
              (mem_labelsOf_head (c := c') (cs := cs') (by simp))
            exact pi_of_rank (T := Tfinal l0) (T' := Tfinal l'0)
              hf.2.1 hf.1 (Tfinal_ranks l'0) hf.2.2 hvx hvy
          have hhead4 : piOfT (Tfinal l0) (Tfinal l'0) c.e4 = c'.e4 := by
            obtain ⟨v, hvx, hvy⟩ := head_pi he he' h4
              (mem_labelsOf_head (c := c) (cs := cs) (by simp))
              (mem_labelsOf_head (c := c') (cs := cs') (by simp))
            exact pi_of_rank (T := Tfinal l0) (T' := Tfinal l'0)
              hf.2.1 hf.1 (Tfinal_ranks l'0) hf.2.2 hvx hvy
          have htail : List.map (fun c => ⟨piOfT (Tfinal l0) (Tfinal l'0) c.e1,
              piOfT (Tfinal l0) (Tfinal l'0) c.e2, piOfT (Tfinal l0) (Tfinal l'0) c.e3,
              piOfT (Tfinal l0) (Tfinal l'0) c.e4⟩) cs = cs' := by
            have hct : (canonThreaded (c :: cs) seen).2 =
                (canonThreaded cs (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2).2 := rfl
            have hct' : (canonThreaded (c' :: cs') seen').2 =
                (canonThreaded cs' (canonSlots seen' [c'.e1, c'.e2, c'.e3, c'.e4]).2).2 := rfl
            have he1 : ThreadExt (canonThreaded cs
                (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2).2 (Tfinal l0) := by
              rw [hct] at he
              exact he
            have he2 : ThreadExt (canonThreaded cs'
                (canonSlots seen' [c'.e1, c'.e2, c'.e3, c'.e4]).2).2 (Tfinal l'0) := by
              rw [hct'] at he'
              exact he'
            have hrec : mapC (piOfT (Tfinal l0) (Tfinal l'0)) cs = cs' := ih cs'
              (canonSlots seen [c.e1, c.e2, c.e3, c.e4]).2
              (canonSlots seen' [c'.e1, c'.e2, c'.e3, c'.e4]).2 he1 he2 hrc'
            rwa [mapC] at hrec
          simp only [mapC, List.map_cons]
          rw [hhead1, hhead2, hhead3, hhead4, htail]

/-- The renaming of the labels commutes with the labelling of a list. -/
private theorem labelsOf_mapC (π : Nat → Nat) (l : List PDCrossing) :
    labelsOf (mapC π l) = (labelsOf l).map π := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    have hmap : mapC π (c :: cs) =
        ⟨π c.e1, π c.e2, π c.e3, π c.e4⟩ :: mapC π cs := rfl
    have hflat : labelsOf (⟨π c.e1, π c.e2, π c.e3, π c.e4⟩ :: mapC π cs) =
        [π c.e1, π c.e2, π c.e3, π c.e4] ++ labelsOf (mapC π cs) := rfl
    have hsrc : labelsOf (c :: cs) = [c.e1, c.e2, c.e3, c.e4] ++ labelsOf cs := rfl
    have hmapapp : ([c.e1, c.e2, c.e3, c.e4] ++ labelsOf cs).map π =
        [π c.e1, π c.e2, π c.e3, π c.e4] ++ (labelsOf cs).map π := by
      simp only [List.map_append, List.map_cons, List.map_nil]
    rw [hmap, hflat, hsrc, ih, hmapapp]

/-- **Extraction.** The equality `canon l = canon l'` produces a renaming `π` of
    the labels which is a **bijection** from `labelsOf l` onto `labelsOf l'`,
    and which sends `l` onto `l'`. This is the "extraction" half of the bridge
    `canon l = canon l' <-> exists label bijection`. -/
private theorem canon_extraction {l l' : List PDCrossing} (h : canon l = canon l') :
    ∃ π : Nat → Nat,
      (∀ x, x ∈ labelsOf l → π x ∈ labelsOf l') ∧
      (∀ x y, x ∈ labelsOf l → y ∈ labelsOf l → π x = π y → x = y) ∧
      (∀ y, y ∈ labelsOf l' → ∃ x, x ∈ labelsOf l ∧ π x = y) ∧
      mapC π l = l' := by
  have hrows : (canonThreaded l []).1 = (canonThreaded l' []).1 := by
    rw [← canon_eq_rows l, ← canon_eq_rows l', h]
  have hrc : RowsCorrespond [] [] l l' := rows_correspond l [] [] l' hrows
  have hmap : mapC (piOf l l') l = l' :=
    mapC_pi_acc l l' l l' [] [] (fun _ _ h => h) (fun _ _ h => h) hrc
  refine ⟨piOf l l', ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hpi, _⟩ := pi_transfer hrc x hx
    rw [hpi]
    exact hy
  · intro x y hx hy hxy
    exact pi_inj hrc x y hx hy hxy
  · intro y hy
    have hy' : y ∈ labelsOf (mapC (piOf l l') l) := by rw [hmap]; exact hy
    rw [labelsOf_mapC] at hy'
    rcases List.mem_map.mp hy' with ⟨x, hx, hxy⟩
    exact ⟨x, hx, hxy⟩
  · exact hmap
/-! ## 17. The canonical form is complete for renaming (tranche 11)

Tranche 16 extracted the renaming from the equality `canon`: there is a
bijection of `labelsOf l` onto `labelsOf l'` that sends `l` onto `l'`. This
tranche closes the loop by showing that the canonical form is a **complete**
invariant of equivalence under renaming:

`canon l = canon l' ↔ ∃ π : Nat → Nat, injective, mapC π l = l'`

The difficulty lies on one side: the extraction (§16) gives an injection
**restricted** to the labels of the source, whereas the other side of the
bridge (`canon_map_eq`, §7) asks for a **global** injection of `Nat` into
`Nat`.

The extension is explicit: the extracted renaming is kept on the labels of the
source, and extended everywhere else by a **translation** above all the labels
of the target. A translation can then meet neither the images of the
extracted renaming (all strictly below the bound) nor itself (it is
injective).

- `natSumC` — the sum of the labels of a list of crossings, an upper bound on
  every label that occurs in it;
- `slot_le_natSumC` — every label of a crossing is below the bound;
- `mem_labelsOf_le_natSumC` — every label of `labelsOf l` is below the bound;
- `slot_mem_labelsOf` — a label of a crossing of `l` belongs to `labelsOf l`
  (the fact that lets the renaming be transported);
- `mapC_congr` — two renamings that agree slot by slot have the same `mapC`;
- `extendRename` — the extension of the renaming outside the label range;
- `canon_rename_iff` — **the completeness theorem**.
-/

/-- Sum of the labels of a list of crossings: an upper bound on every label
    that occurs in it. -/
private def natSumC : List PDCrossing → Nat
  | [] => 0
  | c :: cs => c.e1 + c.e2 + c.e3 + c.e4 + natSumC cs

/-- Every label of a crossing of `l` is bounded by `natSumC l`. -/
private theorem slot_le_natSumC {l : List PDCrossing} {c : PDCrossing} (hc : c ∈ l) :
    c.e1 ≤ natSumC l ∧ c.e2 ≤ natSumC l ∧ c.e3 ≤ natSumC l ∧ c.e4 ≤ natSumC l := by
  induction l with
  | nil => simp at hc
  | cons d ds ih =>
    rw [List.mem_cons] at hc
    rcases hc with rfl | hc
    · simp only [natSumC]
      refine ⟨by omega, ?_⟩
      refine ⟨by omega, ?_⟩
      refine ⟨by omega, by omega⟩
    · have h := ih hc
      simp only [natSumC]
      refine ⟨by omega, ?_⟩
      refine ⟨by omega, ?_⟩
      refine ⟨by omega, by omega⟩

/-- Every label of `labelsOf l` is bounded by `natSumC l`. -/
private theorem mem_labelsOf_le_natSumC {l : List PDCrossing} {y : Nat}
    (hy : y ∈ labelsOf l) : y ≤ natSumC l := by
  simp only [labelsOf, List.mem_flatMap] at hy
  obtain ⟨c, hc, hmem⟩ := hy
  have hmem' : y = c.e1 ∨ y = c.e2 ∨ y = c.e3 ∨ y = c.e4 := by simpa using hmem
  rcases hmem' with rfl | rfl | rfl | rfl
  · exact (slot_le_natSumC hc).1
  · exact (slot_le_natSumC hc).2.1
  · exact (slot_le_natSumC hc).2.2.1
  · exact (slot_le_natSumC hc).2.2.2

/-- A label that occurs in a crossing of `l` belongs to `labelsOf l`: this is
    what lets the extracted renaming be carried from one list to the other. -/
private theorem slot_mem_labelsOf {l : List PDCrossing} {c : PDCrossing} (hc : c ∈ l) :
    c.e1 ∈ labelsOf l ∧ c.e2 ∈ labelsOf l ∧ c.e3 ∈ labelsOf l ∧ c.e4 ∈ labelsOf l := by
  simp only [labelsOf, List.mem_flatMap]
  exact ⟨⟨c, hc, by simp⟩, ⟨c, hc, by simp⟩, ⟨c, hc, by simp⟩, ⟨c, hc, by simp⟩⟩

/-- Two renamings that agree slot by slot produce the same `mapC`. -/
private theorem mapC_congr {π σ : Nat → Nat} {l : List PDCrossing}
    (h : ∀ c ∈ l, π c.e1 = σ c.e1 ∧ π c.e2 = σ c.e2 ∧ π c.e3 = σ c.e3 ∧
      π c.e4 = σ c.e4) : mapC π l = mapC σ l := by
  unfold mapC
  induction l with
  | nil => rfl
  | cons c cs ih =>
    have h1 := h c (by simp)
    obtain ⟨a1, a2, a3, a4⟩ := h1
    have hcs := ih (fun d hd => h d (by simp [hd]))
    simp only [List.map_cons]
    rw [a1, a2, a3, a4, hcs]

/-- **Extension of a renaming outside the label range.** On the labels of
    `A` the renaming is unchanged; everywhere else it translates by `k`. The
    images of the translation are all `≥ k`, hence disjoint from the images of
    the initial renaming as soon as those are `< k`. -/
private def extendRename (π₀ : Nat → Nat) (A : List Nat) (k : Nat) : Nat → Nat :=
  fun x => if x ∈ A then π₀ x else x + k

/-- **Completeness of renaming.** The canonical form is a complete invariant
    of equivalence under renaming: two lists of crossings have the same
    canonical form if and only if one is the renaming of the other by an
    injection of `Nat` into `Nat`.

    - "extraction" direction: §16 gives a bijection of `labelsOf l` onto
      `labelsOf l'`; it is extended outside the labels of the source by a
      translation above all the labels of the target, which gives a **global**
      injection;
    - "invariance" direction: `canon_map_eq` (§7) applied to that injection.
-/
theorem canon_rename_iff {l l' : List PDCrossing} :
    canon l = canon l' ↔ ∃ π : Nat → Nat, Function.Injective π ∧ mapC π l = l' := by
  constructor
  · intro h
    obtain ⟨π₀, hmap₀, hinj₀, hsurj₀, hmapC⟩ := canon_extraction h
    -- the bound: every label of the target is strictly below the bound
    have hbound : ∀ y, y ∈ labelsOf l' → y < natSumC l' + 1 := by
      intro y hy
      have hle : y ≤ natSumC l' := mem_labelsOf_le_natSumC hy
      omega
    -- the extended renaming: π₀ on the labels of the source, a translation
    -- everywhere else
    have hinj : Function.Injective (extendRename π₀ (labelsOf l) (natSumC l' + 1)) := by
      intro x x' hxx'
      by_cases hx : x ∈ labelsOf l
      · by_cases hx' : x' ∈ labelsOf l
        · simp only [extendRename, if_pos hx, if_pos hx'] at hxx'
          exact hinj₀ x x' hx hx' hxx'
        · simp only [extendRename, if_pos hx, if_neg hx'] at hxx'
          have hy : π₀ x ∈ labelsOf l' := hmap₀ x hx
          have hlt : π₀ x < natSumC l' + 1 := hbound _ hy
          omega
      · by_cases hx' : x' ∈ labelsOf l
        · simp only [extendRename, if_neg hx, if_pos hx'] at hxx'
          have hy : π₀ x' ∈ labelsOf l' := hmap₀ x' hx'
          have hlt : π₀ x' < natSumC l' + 1 := hbound _ hy
          omega
        · simp only [extendRename, if_neg hx, if_neg hx'] at hxx'
          omega
    -- the extended renaming agrees with the extracted renaming on the slots
    have hslots : ∀ c ∈ l,
        (extendRename π₀ (labelsOf l) (natSumC l' + 1)) c.e1 = π₀ c.e1 ∧
        (extendRename π₀ (labelsOf l) (natSumC l' + 1)) c.e2 = π₀ c.e2 ∧
        (extendRename π₀ (labelsOf l) (natSumC l' + 1)) c.e3 = π₀ c.e3 ∧
        (extendRename π₀ (labelsOf l) (natSumC l' + 1)) c.e4 = π₀ c.e4 := by
      intro c hc
      obtain ⟨h1, h2, h3, h4⟩ := slot_mem_labelsOf hc
      simp only [extendRename]
      rw [if_pos h1, if_pos h2, if_pos h3, if_pos h4]
      exact ⟨rfl, rfl, rfl, rfl⟩
    refine ⟨extendRename π₀ (labelsOf l) (natSumC l' + 1), hinj, ?_⟩
    rw [mapC_congr hslots]
    exact hmapC
  · rintro ⟨π, hπ, hmap⟩
    have hcanon : canon (mapC π l) = canon l := canon_map_eq hπ l
    rw [hmap] at hcanon
    exact hcanon.symm

/-! ## 18. Equivalence up to renaming, and the bound of the announced bridge (tranche 12)

The residual declared at the head of the module is the **`_any` ->
`ReidemeisterEquiv` soundness**. The route recorded in the grain plan was:
"on canonical forms, `canon` kills the renaming, and the dying labels of the
kink are fresh there". **That premise is false — and it is refuted by the
kernel, not by reading.**

It is measured first: a faithful Python replica of `canon`, of `wf` and of
both `_any` withdrawals (34 withdrawals on canonical, well-formed diagrams)
finds **14 non-fresh** ones. The smallest counter-example fits in two
crossings, and it is the one sealed by this section.

What is delivered here, in this order:

1. `AnyEquiv` — the **missing relation** of the language (two diagrams
   equivalent up to renaming), its equivalence laws, and its characterisation
   `exists injective pi, mapC pi l = l'` (a direct consequence of
   `canon_rename_iff`, section 17);
2. `kinkAnyWitness` / `kinkAnyTarget` — an **authentic** `_any` withdrawal
   whose kink carries `e2 = 1`, that is a **small** label: exactly what the
   connected freshness forbids. The withdrawal is certified by the kernel
   (`verifyKinkDownAny ... = true`);
3. `no_verifyR1Fwd_from_witness` — **no** target satisfies `verifyR1Fwd` on
   this witness. The reason is arithmetic and **independent of the renaming**:
   the connected freshness requires `K.e2 = d.numEdges + 1`, hence
   `d.numEdges = 0` here; the cardinality clause requires
   `D.numEdges = d.numEdges + 2`, hence `D.numEdges = 2` — but it is `4`. The
   two clauses cannot hold at once, whatever `d` is.

**What this changes, and where it is decided.** The bridge cannot be "choose
or rename the target while keeping the large diagram": on this witness, no
target exists. Two closures remain possible, and neither is a lane edit:

- rename the **large** diagram as well, and then establish the `dropLast`
  surgery under the renaming (constructive formulation, high proof cost, no
  change to the connected relation);
- give the connected relation a **relabelling step** — which makes the
  renaming itself a step, and removes the need for a bridge. That choice
  modifies `ReidemeisterStep` and the surface of `Invariant.lean`: it belongs
  to a coordinator arbitration (issue #22359).

Until one of these two choices is arbitrated, the residual stays **open and
now bounded** — it is no longer "probably doable by renaming".
-/

/-- Two diagrams are **equivalent up to renaming** when they have the same
    canonical form. This is the quotient the connected language does not
    provide: its verifiers compare diagrams *literally*, while an `_any`
    withdrawal only preserves the shape.

    The relation deliberately ignores `numEdges`: on a well-formed diagram,
    `numEdges` is determined by the labels present (each of `1` to `numEdges`
    appears exactly twice), so two diagrams with the same canonical form and
    both well-formed have the same `numEdges`. The canonical form is therefore
    the right quotient, and it is weaker than literal equality — that gap is
    precisely what the bridge has to cross. -/
def AnyEquiv (d d' : KnotDiagram) : Prop := canon d.crossings = canon d'.crossings

theorem anyEquiv_refl (d : KnotDiagram) : AnyEquiv d d := rfl

theorem anyEquiv_symm {d d' : KnotDiagram} (h : AnyEquiv d d') : AnyEquiv d' d := h.symm

theorem anyEquiv_trans {d d' d'' : KnotDiagram} (h : AnyEquiv d d') (h' : AnyEquiv d' d'') :
    AnyEquiv d d'' := h.trans h'

/-- `AnyEquiv` is an equivalence relation: the three laws are those of
    equality on the canonical form, transported. -/
theorem anyEquiv_equivalence : Equivalence AnyEquiv :=
  ⟨anyEquiv_refl, anyEquiv_symm, anyEquiv_trans⟩

/-- Characterisation of `AnyEquiv`: two diagrams are equivalent up to renaming
    if and only if an **injective** renaming sends the labels of one onto the
    labels of the other. This is exactly `canon_rename_iff` (section 17), read
    through `AnyEquiv`. -/
theorem anyEquiv_iff_rename {d d' : KnotDiagram} :
    AnyEquiv d d' ↔ ∃ π : Nat → Nat, Function.Injective π ∧ mapC π d.crossings = d'.crossings :=
  canon_rename_iff

/-- Witness: two well-formed crossings (each label from `1` to `4` appears
    exactly twice), the last of them being a kink `⟨3, 1, 4, 4⟩`. Its arc
    `e2 = 1` is **small**: the `_any` withdrawal kills the labels `{1, 3}` by
    fusing `1 -> 3`, whereas the connected freshness would require them to be
    the two largest. -/
def kinkAnyWitness : KnotDiagram := ⟨[⟨1, 2, 3, 2⟩, ⟨3, 1, 4, 4⟩], 4⟩

/-- Target of the withdrawal: the fusion `1 -> 3` rewrites the slot `e1` of
    the first crossing into `⟨3, 2, 3, 2⟩`, whose canonical form is
    `⟨1, 2, 1, 2⟩` — hence the compaction `numEdges = 2` (the dying labels
    `{1, 3}` leave `{2, 4}`, renumbered `{1, 2}`). -/
def kinkAnyTarget : KnotDiagram := ⟨[⟨1, 2, 1, 2⟩], 2⟩

/-- The witness is well-formed: parity checked over the four labels. -/
theorem kinkAnyWitness_wf : kinkAnyWitness.wf = true := by decide

/-- The terminal crossing of the witness is indeed the kink `⟨3, 1, 4, 4⟩`. -/
theorem kinkAnyWitness_kink : kinkAnyWitness.crossings.getLast? = some ⟨3, 1, 4, 4⟩ := by decide

/-- The `_any` withdrawal of the witness is **accepted**: it is an authentic
    R1 move up to renaming, and its target is well-formed. -/
theorem verifyKinkDownAny_witness_kinkAny :
    verifyKinkDownAny kinkAnyWitness kinkAnyTarget = true := by decide

/-- **The bound of the bridge.** On the witness, no target satisfies the
    connected verifier: `verifyR1Fwd d kinkAnyWitness` is false for **every**
    `d`, and not only for the canonical target.

    The proof touches no list: it is purely arithmetic. The kink carries
    `K.e2 = 1`; the connected freshness imposes `K.e2 = d.numEdges + 1`,
    hence `d.numEdges = 0`; the cardinality clause then imposes
    `kinkAnyWitness.numEdges = d.numEdges + 2 = 2`, while it is `4`. The two
    cases on `d.numEdges` close the goal, and **no renaming of `d` can avoid
    them** — which is why this is not a defect of the canonical target, but of
    the bridge itself. -/
theorem no_verifyR1Fwd_from_witness (d : KnotDiagram) :
    verifyR1Fwd d kinkAnyWitness = false := by
  unfold verifyR1Fwd
  rw [kinkAnyWitness_kink]
  cases _h : d.numEdges with
  | zero =>
    -- d.numEdges = 0: the cardinality clause imposes
    -- kinkAnyWitness.numEdges = 0 + 2 = 2, while the witness carries 4.
    simp [kinkAnyWitness]
  | succ n =>
    -- d.numEdges = n + 1: the freshness clause imposes
    -- K.e2 = 1 = (n + 1) + 1, impossible.
    simp [kinkAnyWitness]

/-- **Positive control of the bound**: the connected verifier is not uniformly
    false — it accepts the canonical pair of the witness
    `reidemeister1Connected_satisfiable` (`ReidemeisterMoves` section 7), whose
    kink `⟨1, 5, 6, 6⟩` indeed carries `e2 = 5 = 4 + 1` (the freshness, met).

    The bound of `no_verifyR1Fwd_from_witness` therefore bears on the
    **witness** `kinkAnyWitness` — whose kink carries `e2 = 1` — and not on
    the verifier. -/
theorem verifyR1Fwd_positive_control :
    verifyR1Fwd
      { crossings := [⟨1, 2, 3, 4⟩, ⟨1, 2, 3, 4⟩], numEdges := 4 }
      { crossings := [⟨1, 2, 3, 4⟩, ⟨5, 2, 3, 4⟩, ⟨1, 5, 6, 6⟩], numEdges := 6 }
    = true := by decide

end Knots_en.AnyMoves
