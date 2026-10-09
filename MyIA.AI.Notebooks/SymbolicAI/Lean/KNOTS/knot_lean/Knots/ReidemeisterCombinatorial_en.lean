/-
Knots.ReidemeisterCombinatorial (EN) — Verifiable sequence of Reidemeister moves
=================================================================================

Infrastructure issue (Epic #1453, point 3): the missing organ behind the
remaining `sorry`s of `knot_lean` (Reidemeister.lean:1056, Lidman.lean:81) —
a **kernel-verifiable sequence of Reidemeister moves**.

Why this module is separate from `Knots.Reidemeister`: the RTC machinery
(`ReidemeisterEquiv`) is already in place (inductives `ReidemeisterStep` and
`ReidemeisterEquiv`, lemmas `*.symm`, `reidemeister_equiv_symm`,
`reidemeister_equiv_equivalence`). What is missing is the **algorithmic
backbone**:

  1. an **indexed inductive** `MoveSequence` (`KnotDiagram → KnotDiagram → Type`)
     (the typecarries the structural coherence of sequences — the typer rejects
     any list whose last step does not reach the claimed `d₃`),
  2. a `movesConnects` constructor that seals the RTC into a compact witness,
  3. a **bounded decidable verifier** `verifyMoves` which, for a budget `n`
     of moves allowed, enumerates all R1/R2/R3 sequences and returns `true`
     if any of them connects two diagrams. Bounded to remain decidable;
     full enumeration is `O((crossings+1)^n)`,
  4. the **soundness** of the verifier: if `verifyMoves n d₁ d₂ = true`, then
     `ReidemeisterEquiv d₁ d₂`. This is the target of subsequent prover
     passes.

What this module **does not do**:
- it does not prove the deep Reidemeister theorem (`reidemeister_theorem`,
  Reidemeister.lean:1053) which requires PL-manifolds/S³/ambient isotopy —
  the verifier's soundness only delivers the **combinatorial side**
  (« ⇐ » ReidemeisterEquiv → ambient_isotopic remains out of scope);
- it does not attack the permanent `sorry`s of `Knots.Slice` (Conway,
  Piccirillo, Freedman), explicitly marked as « decades away from formalization »
  by previous sections — these statements live in a 4-manifolds / Khovanov /
  Kirby theory that Mathlib does not have.

Target Lidman:81 — `unknotting_11n102_upper` — **is not made accessible by this
module** (status corrected 2026-10-09, #18611). The planned route was: exhibit a
`MoveSequence` connecting
`(changeCrossingAt c₁ (changeCrossingAt c₂ knot_11n102)).diagram` to
`unknotDiagram`, and seal the implication with `verifyMoves_sound` — **proved
on this module** by the prover passes (#19890/#20000; see the status block
below). Two measurements nonetheless contradict the route: (a) the bounded
search of #18611 (excursions ≤ +2 crossings, diagrams ≤ 13 crossings; 138,623
states explored from the 67 n-changed diagrams) reaches `unknotDiagram` from
none of them, and `min_crossings` stays at 11 for each; (b) the conditioned
floor theorem (`Knots.ReidemeisterMoves` §8) shows that a sequence all of whose
moves preserve `allFourDistinct` cannot decrease the crossing count — a
certificate for 11n102 would therefore have to leave that class along the way.
The organ remains necessary to state the contract; it is not enough to honour
it, and neither side (this module, `Knots.Lidman`) supplies the witness.

Convention i18n (EPIC #4980, user decision 2026-07-04): this file is the **EN
mirror** of `ReidemeisterCombinatorial.lean` (FR canonical), via the sibling
pair pattern ratified 2026-07-04. Theorem statements, Lean tactics, lemma
names and Mathlib references stay in English (Mathlib 4 compat); only module
docstrings and this header block differ between the two files.

Status: the real enumeration of one-move witnesses is in place
(`#19890` — R1/R2 forward and backward, R3 forward), `oneStepWitnesses_sound`
is proved by construction, and `verifyMoves_sound` is total. The concrete
witness `Lidman:81` (`unknotting_11n102_upper`) remains the target of the
following passes, and the inverse of the R3 move is documented future work.
-/

import Knots.Reidemeister
import Knots.Invariant

namespace Knots

/-! ## 1. Sequence of moves — indexed inductive

`MoveSequence` is an **indexed inductive** `KnotDiagram → KnotDiagram → Type`
(not an alias `List ReidemeisterStep`): a reflexive `nil` constructor and a
`cons` constructor chaining a `ReidemeisterStep` with the tail.

The dual-index structure enforces chain coherence by construction: `cons`
requires `step : ReidemeisterStep d₁ d₂` and `tail : MoveSequence d₂ d₃`, so
the typer rejects any list whose last step does not reach the claimed `d₃`.

Convention: application order is « left → right » — `cons step tail` means
« apply `step` first, then `tail` ».
-/

/-- Finite sequence of Reidemeister moves.

Indexed inductive on two `KnotDiagram`: the type carries the guarantee that
the concatenated steps actually connect `d₁` to `d₂`.
-/
inductive MoveSequence : KnotDiagram → KnotDiagram → Type where
  /-- Empty sequence: a diagram connects trivially to itself. -/
  | nil (d : KnotDiagram) : MoveSequence d d
  /-- Chain a `ReidemeisterStep d₁ d₂` with a tail `MoveSequence d₂ d₃`. -/
  | cons {d₁ d₂ d₃ : KnotDiagram}
      (step : ReidemeisterStep d₁ d₂)
      (tail : MoveSequence d₂ d₃) :
      MoveSequence d₁ d₃

/-! ## 2. RTC reconstruction and soundness

`movesConnects` seals a `MoveSequence` into a proof of `ReidemeisterEquiv`: it
is the inverse of the `ReidemeisterEquiv.step` constructor rendered composable.
The structural recursion on the indexed inductive forces the coherence of the
diagrams at the end of the chain.
-/

/-- A sequence of moves connects `d₁` to `d₂` in the sense of `ReidemeisterEquiv`.

Reconstruction by recursion on the `MoveSequence`:
- `nil` (empty sequence) → `ReidemeisterEquiv.refl d₁`,
- `cons step tail` → `ReidemeisterEquiv.trans (ReidemeisterEquiv.step step)
  (movesConnects d₂ d₃ tail)`.

The definition is **non-right-recursive**: `movesConnects d₂ d₃ tail` is
computed before being consumed by `trans`, which keeps evaluation
termination-safe under `decreasing_by wf_tacs`.
-/
def movesConnects {d₁ d₂ : KnotDiagram} :
    MoveSequence d₁ d₂ → ReidemeisterEquiv d₁ d₂
  | .nil d => ReidemeisterEquiv.refl d
  | .cons step tail =>
    ReidemeisterEquiv.trans
      (ReidemeisterEquiv.step step)
      (movesConnects tail)

/-! ## 2.1. Trivial soundness of the RTC

`movesConnects` _constructs_ the RTC, so its soundness is the identity. This
is the stable API for consumers (cf. `Knots.Lidman`).
-/

/-- Trivially sound by construction: `movesConnects` _is_ the RTC. -/
theorem movesConnects_sound {d₁ d₂ : KnotDiagram}
    (ms : MoveSequence d₁ d₂) : ReidemeisterEquiv d₁ d₂ :=
  movesConnects ms

/-! ## 3. Bounded decidable verifier

`verifyMovesAux` enumerates the sequences of length at most `n` and decides
whether any of them connects `d₁` to `d₂`. The decision is **decidable**
(returns a `Bool`) — it is the instrument for prover passes that do not have
access to `decide` orchestration on the space of infinite sequences.

The algorithm is deliberately naive (exhaustive enumeration): for the bounds
useful in practice (n ≤ 4), the branching factor stays dominated by
`(crossings+1) × 3` (R1/R2/R3 × both directions) and the cost stays in
`O((3(numCrossings+1))^n)`. Subsequent prover passes will refine by avoiding
trivial symmetries (`ReidemeisterEquiv.symm`, `trans`).
-/

/-- A view of `ReidemeisterStep` as a pure constructor (without existential
`d₂`). Used by the algorithm to reconstruct the target diagram at each step. -/
def ReidemeisterStep.toWitness (d₁ : KnotDiagram) (d₂ : KnotDiagram)
    (h : (Reidemeister1Connected d₁ d₂ ∨ Reidemeister1Connected d₂ d₁
       ∨ Reidemeister2Connected d₁ d₂ ∨ Reidemeister2Connected d₂ d₁
       ∨ Reidemeister3Connected d₁ d₂ ∨ Reidemeister3Connected d₂ d₁)) :
    ReidemeisterStep d₁ d₂ :=
  -- Distributivity of `∨`: the conjunction is either R1, R2, or R3,
  -- and in each case the direction is forward or backward.
  -- The reconstruction is partial: we accept any witness `h` and
  -- pattern-match to select the right `ReidemeisterStep` constructor.
  -- The `_` is explicit to flag that reconstruction is not always unique
  -- (forward/backward symmetric).
  by
    rcases h with h | h | h | h | h | h
    · exact ReidemeisterStep.r1 (Or.inl h)
    · exact ReidemeisterStep.r1 (Or.inr h)
    · exact ReidemeisterStep.r2 (Or.inl h)
    · exact ReidemeisterStep.r2 (Or.inr h)
    · exact ReidemeisterStep.r3 (Or.inl h)
    · exact ReidemeisterStep.r3 (Or.inr h)

/-! ## 3bis. Real enumeration of one-move witnesses (`#19890`)

The principle: every candidate is built **with its proof** (`StepWitness`), so
that the soundness of the enumeration holds **by construction** — it reduces
to `List.mem_map` in `oneStepWitnesses_sound`, never re-guessed from the
target diagram alone.

Scope of the enumeration:
- **R1**: connected twists FORWARD (adding a kink on a proper arc) and
  BACKWARD (contracting a terminal kink);
- **R2**: bigons FORWARD and BACKWARD (contracting a pair of terminal kinks);
- **R3**: triangular moves FORWARD — the inverse direction is documented
  future work on `Reidemeister3Connected` (the move is not symmetric by
  construction: the back-and-forth at equal Sat is not involutive).

Every candidate is filtered by the exact decidable guards of the relation
(`wf` on both sides, `Nodup` of the R3 labels, kink shape for the
contractions): a malformed candidate is simply not emitted — the list holds
ONLY genuine successors.

The renaming generators (`renameOptsWith` & co.) are themselves
proof-carrying: each slot option is emitted WITH the disjunction that
justifies it in `isRenameOf` / `isDoubleRenameOf`, which avoids any
a-posteriori membership lemma.
-/

/-- A witness of a move: the target diagram and the proof of the
`ReidemeisterStep`, built at the same enumeration site. -/
structure StepWitness (d : KnotDiagram) where
  /-- Diagram reachable from `d` by a single `ReidemeisterStep`. -/
  target : KnotDiagram
  /-- Proof of the step, fabricated at enumeration time. -/
  proof : ReidemeisterStep d target

/-- Canonical embedding `Fin n ↪ Fin (n + m)`: the fresh labels of a surgery
take the rows `n+1, …, n+m` (trivially witnessable ρ, always constructible). -/
def finEmbed (n m : Nat) : Fin n ↪ Fin (n + m) where
  toFun j := ⟨j.val, by omega⟩
  inj' x y h := by injection h with hv; exact Fin.ext hv

/-- Rewriting a slot to its current value does not change the list. -/
theorem list_set_current {l : List PDCrossing} {i : Nat}
    (h : i < l.length) : l.set i (l.get ⟨i, h⟩) = l := by
  induction l generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    match i with
    | 0 => rfl
    | i + 1 =>
      exact congrArg (List.cons x) (ih (by simp only [List.length_cons] at h; omega))

/-- Generalized form: rewriting slot `i` to a value equal to the current one
does not change the list. -/
theorem list_set_eq {l : List PDCrossing} {i : Nat} {x : PDCrossing}
    (h : i < l.length) (hx : l.get ⟨i, h⟩ = x) : l.set i x = l := by
  rw [← hx]; exact list_set_current h

/-- Reading slot `i` right after writing it yields the written value. -/
theorem list_get_set_self {l : List PDCrossing} {i : Nat} (a : PDCrossing)
    (h : i < (l.set i a).length) : (l.set i a).get ⟨i, h⟩ = a := by
  rw [List.get_eq_getElem, List.getElem_set_self]

/-- Options of a slot for `isRenameOf c a b` (R1 forward): a slot equal to
`a` may be preserved or become `b`; any other slot is preserved. Each option
is emitted with its proof. -/
def renameOptsWith (x a b : Nat) : List { y : Nat // y = x ∨ (y = b ∧ x = a) } :=
  if hx : x = a then
    [⟨x, Or.inl rfl⟩, ⟨b, Or.inr ⟨rfl, hx⟩⟩]
  else
    [⟨x, Or.inl rfl⟩]

/-- Options of a slot for `isDoubleRenameOf c a o₁ o₂` (R2 forward): a slot
equal to `a` may be preserved, become `o₁` or become `o₂`. -/
def rename2OptsWith (x a o₁ o₂ : Nat) :
    List { y : Nat // y = x ∨ (y = o₁ ∧ x = a) ∨ (y = o₂ ∧ x = a) } :=
  if hx : x = a then
    [⟨x, Or.inl rfl⟩, ⟨o₁, Or.inr (Or.inl ⟨rfl, hx⟩)⟩, ⟨o₂, Or.inr (Or.inr ⟨rfl, hx⟩)⟩]
  else
    [⟨x, Or.inl rfl⟩]

/-- Inverse options of a slot (R1 contraction): for a known `Y'`, the source
values `x` such that the renamed slot equals `y`. -/
def unRenameOptsWith (y b a : Nat) : List { x : Nat // y = x ∨ (y = b ∧ x = a) } :=
  if hy : y = b then
    [⟨y, Or.inl rfl⟩, ⟨a, Or.inr ⟨hy, rfl⟩⟩]
  else
    [⟨y, Or.inl rfl⟩]

/-- Double inverse options of a slot (R2 contraction). -/
def unRename2Opts (y o₁ o₂ a : Nat) :
    List { x : Nat // y = x ∨ (y = o₁ ∧ x = a) ∨ (y = o₂ ∧ x = a) } :=
  if hy : y = o₁ then
    [⟨y, Or.inl rfl⟩, ⟨a, Or.inr (Or.inl ⟨hy, rfl⟩)⟩]
  else if hy2 : y = o₂ then
    [⟨y, Or.inl rfl⟩, ⟨a, Or.inr (Or.inr ⟨hy2, rfl⟩)⟩]
  else
    [⟨y, Or.inl rfl⟩]

/-- All R1 renames of `c`, with the `isRenameOf` proof attached. -/
def PDCrossing.allRenamesWith (c : PDCrossing) (a b : Nat) :
    List { Y : PDCrossing // Y.isRenameOf c a b } :=
  (renameOptsWith c.e1 a b).flatMap fun e1 =>
    (renameOptsWith c.e2 a b).flatMap fun e2 =>
      (renameOptsWith c.e3 a b).flatMap fun e3 =>
        (renameOptsWith c.e4 a b).map fun e4 =>
          ⟨⟨e1.1, e2.1, e3.1, e4.1⟩, ⟨e1.2, e2.2, e3.2, e4.2⟩⟩

/-- All R2 double-renames of `c`, with the proof attached. -/
def PDCrossing.allDoubleRenamesWith (c : PDCrossing) (a o₁ o₂ : Nat) :
    List { Y : PDCrossing // Y.isDoubleRenameOf c a o₁ o₂ } :=
  (rename2OptsWith c.e1 a o₁ o₂).flatMap fun e1 =>
    (rename2OptsWith c.e2 a o₁ o₂).flatMap fun e2 =>
      (rename2OptsWith c.e3 a o₁ o₂).flatMap fun e3 =>
        (rename2OptsWith c.e4 a o₁ o₂).map fun e4 =>
          ⟨⟨e1.1, e2.1, e3.1, e4.1⟩, ⟨e1.2, e2.2, e3.2, e4.2⟩⟩

/-- All sources `Y` whose R1 rename is `Y'` (contraction), with the proof
attached. -/
def PDCrossing.allUnRenamesWith (Y' : PDCrossing) (a b : Nat) :
    List { Y : PDCrossing // Y'.isRenameOf Y a b } :=
  (unRenameOptsWith Y'.e1 b a).flatMap fun e1 =>
    (unRenameOptsWith Y'.e2 b a).flatMap fun e2 =>
      (unRenameOptsWith Y'.e3 b a).flatMap fun e3 =>
        (unRenameOptsWith Y'.e4 b a).map fun e4 =>
          ⟨⟨e1.1, e2.1, e3.1, e4.1⟩, ⟨e1.2, e2.2, e3.2, e4.2⟩⟩

/-- All sources `Y` whose R2 double-rename is `Y'` (contraction). -/
def PDCrossing.allUnDoubleRenamesWith (Y' : PDCrossing) (a o₁ o₂ : Nat) :
    List { Y : PDCrossing // Y'.isDoubleRenameOf Y a o₁ o₂ } :=
  (unRename2Opts Y'.e1 o₁ o₂ a).flatMap fun e1 =>
    (unRename2Opts Y'.e2 o₁ o₂ a).flatMap fun e2 =>
      (unRename2Opts Y'.e3 o₁ o₂ a).flatMap fun e3 =>
        (unRename2Opts Y'.e4 o₁ o₂ a).map fun e4 =>
          ⟨⟨e1.1, e2.1, e3.1, e4.1⟩, ⟨e1.2, e2.2, e3.2, e4.2⟩⟩

/-- Candidate arcs of `d` (bounds and membership proved). -/
def arcCandidatesWith (d : KnotDiagram) :
    List { a : Nat // 1 ≤ a ∧ a ≤ d.numEdges ∧ a ∈ d.edges } :=
  d.edges.attach.flatMap fun a =>
    if h : 1 ≤ a.1 ∧ a.1 ≤ d.numEdges then [⟨a.1, h.1, h.2, a.2⟩] else []

/-- Proper-arc witnesses: indices `j ≠ i` whose crossing carries arc `a`
(anti-monogon guard of `Reidemeister1Connected`). -/
def properArcWitnesses (d : KnotDiagram) (i : Fin d.crossings.length) (a : Nat) :
    List { j : Fin d.crossings.length // j ≠ i ∧ (d.crossings.get j).hasEdge a } :=
  (List.finRange d.crossings.length).filterMap fun j =>
    if hij : j = i then none
    else if hhas : (d.crossings.get j).e1 = a ∨ (d.crossings.get j).e2 = a
                ∨ (d.crossings.get j).e3 = a ∨ (d.crossings.get j).e4 = a
    then some ⟨j, hij, hhas⟩
    else none

/-- R1 FORWARD: connected twist on every proper arc of every crossing. -/
def r1ForwardWitnesses (d : KnotDiagram) : List (StepWitness d) :=
  (List.finRange d.crossings.length).flatMap fun i =>
    (arcCandidatesWith d).flatMap fun a =>
      (properArcWitnesses d i a.1).flatMap fun _j =>
        ((d.crossings.get i).allRenamesWith a.1 (d.numEdges + 1)).flatMap fun Y' =>
          let d₂ : KnotDiagram :=
            { crossings := d.crossings.set i.val Y'.1 ++
                [⟨a.1, d.numEdges + 1, d.numEdges + 2, d.numEdges + 2⟩]
            , numEdges := d.numEdges + 2 }
          if hwf : d.wf = true ∧ d₂.wf = true then
            [{ target := d₂
             , proof := ReidemeisterStep.r1 (Or.inl
                 ⟨hwf.1, hwf.2, i, a.1, Y'.1, finEmbed d.numEdges 2,
                   a.2.1, a.2.2.1, a.2.2.2, ⟨_j.1, _j.2.1, _j.2.2⟩,
                   Y'.2, rfl, rfl⟩) }]
          else []

/-- R1 BACKWARD: contraction of a terminal kink `⟨a, n-1, n, n⟩` (n =
`d.numEdges`) — enumerates the sources `Y₀` whose modified crossing `Y'` of
`d` is the rename. -/
def r1BackwardWitnesses (d : KnotDiagram) : List (StepWitness d) :=
  match hlast : d.crossings.getLast? with
  | some kink =>
    if hk : kink.e2 = d.numEdges - 1 ∧ kink.e3 = d.numEdges ∧ kink.e4 = d.numEdges
        ∧ 2 ≤ d.numEdges then
      (List.finRange d.crossings.length).flatMap fun (i : Fin d.crossings.length) =>
        if hilt : i.val < d.crossings.length - 1 then
          have hdl : i.val < d.crossings.dropLast.length := by
            simp only [List.length_dropLast]; omega
          let Y' := d.crossings.dropLast.get ⟨i.val, hdl⟩
          (Y'.allUnRenamesWith kink.e1 (d.numEdges - 1)).flatMap fun Y₀ =>
            let d' : KnotDiagram :=
              { crossings := d.crossings.dropLast.set i.val Y₀.1
              , numEdges := d.numEdges - 2 }
            have hdlen : i.val < d'.crossings.length := by
              change i.val < (d.crossings.dropLast.set i.val Y₀.1).length
              rw [List.length_set]; exact hdl
            if ha : 1 ≤ kink.e1 ∧ kink.e1 ≤ d.numEdges - 2 ∧ kink.e1 ∈ d'.edges then
              (properArcWitnesses d' ⟨i.val, hdlen⟩ kink.e1).flatMap fun _j =>
                if hwf : d'.wf = true ∧ d.wf = true then
                  [{ target := d'
                   , proof := by
                       have hY'get : d'.crossings.get ⟨i.val, hdlen⟩ = Y₀.1 := by
                         change (d.crossings.dropLast.set i.val Y₀.1).get ⟨i.val, hdlen⟩
                           = Y₀.1
                         rw [List.get_eq_getElem, List.getElem_set_self]
                       have hkink : kink = ⟨kink.e1, d.numEdges - 1, d.numEdges, d.numEdges⟩ := by
                         rw [show kink = ⟨kink.e1, kink.e2, kink.e3, kink.e4⟩ from rfl,
                             hk.1, hk.2.1, hk.2.2.1]
                       refine ReidemeisterStep.r1 (Or.inr
                         ⟨hwf.1, hwf.2, ⟨i.val, hdlen⟩, kink.e1, Y', finEmbed _ 2,
                           ha.1, ha.2.1, ha.2.2, ⟨_j.1, _j.2.1, _j.2.2⟩, ?_, ?_, ?_⟩)
                       · rw [hY'get,
                           show d'.numEdges + 1 = d.numEdges - 1 by
                             show d.numEdges - 2 + 1 = d.numEdges - 1; omega]
                         exact Y₀.2
                       · show d.crossings =
                           d'.crossings.set i.val Y' ++
                             [⟨kink.e1, d'.numEdges + 1, d'.numEdges + 2, d'.numEdges + 2⟩]
                         rw [show d'.crossings = d.crossings.dropLast.set i.val Y₀.1 from rfl,
                           List.set_set Y₀.1,
                           list_set_eq (x := Y') hdl (by rfl),
                           show d'.numEdges + 1 = d.numEdges - 1 by
                             show d.numEdges - 2 + 1 = d.numEdges - 1; omega,
                           show d'.numEdges + 2 = d.numEdges by
                             show d.numEdges - 2 + 2 = d.numEdges; omega,
                           ← hkink]
                         have hmem : kink ∈ d.crossings.getLast? := by
                           rw [hlast]; exact Option.mem_some.mpr rfl
                         exact (List.dropLast_append_getLast? kink hmem).symm
                       · show d.numEdges = d'.numEdges + 2
                         show d.numEdges = d.numEdges - 2 + 2
                         omega }]
                else []
            else []
        else []
    else []
  | none => []

/-- R2 FORWARD: connected bigon on every double arc of every crossing. -/
def r2ForwardWitnesses (d : KnotDiagram) : List (StepWitness d) :=
  (List.finRange d.crossings.length).flatMap fun i =>
    (arcCandidatesWith d).flatMap fun a =>
      ((d.crossings.get i).allDoubleRenamesWith a.1 (d.numEdges + 2) (d.numEdges + 4)).flatMap fun Y' =>
        let d₂ : KnotDiagram :=
          { crossings := d.crossings.set i.val Y'.1 ++
              [⟨a.1, d.numEdges + 1, d.numEdges + 1, d.numEdges + 2⟩,
               ⟨a.1, d.numEdges + 3, d.numEdges + 3, d.numEdges + 4⟩]
          , numEdges := d.numEdges + 4 }
        if hwf : d.wf = true ∧ d₂.wf = true then
          [{ target := d₂
           , proof := ReidemeisterStep.r2 (Or.inl
               ⟨hwf.1, hwf.2, i, a.1, Y'.1, finEmbed d.numEdges 4,
                 a.2.1, a.2.2.1, a.2.2.2, Y'.2, rfl, rfl⟩) }]
        else []

/-- R2 BACKWARD: contraction of a pair of terminal kinks
`⟨a, n-3, n-3, n-2⟩`, `⟨a, n-1, n-1, n⟩` (n = `d.numEdges`). -/
def r2BackwardWitnesses (d : KnotDiagram) : List (StepWitness d) :=
  match h2 : d.crossings.getLast? with
  | some k2 =>
    match h1 : d.crossings.dropLast.getLast? with
    | some k1 =>
      if hk : k1.e2 = d.numEdges - 3 ∧ k1.e3 = d.numEdges - 3 ∧ k1.e4 = d.numEdges - 2
          ∧ k2.e1 = k1.e1 ∧ k2.e2 = d.numEdges - 1 ∧ k2.e3 = d.numEdges - 1
          ∧ k2.e4 = d.numEdges ∧ 4 ≤ d.numEdges then
        (List.finRange d.crossings.length).flatMap fun (i : Fin d.crossings.length) =>
          if hilt : i.val < d.crossings.length - 2 then
            have hdl : i.val < d.crossings.dropLast.dropLast.length := by
              simp only [List.length_dropLast]; omega
            let Y' := d.crossings.dropLast.dropLast.get ⟨i.val, hdl⟩
            (Y'.allUnDoubleRenamesWith k1.e1 (d.numEdges - 2) d.numEdges).flatMap fun Y₀ =>
              let d' : KnotDiagram :=
                { crossings := d.crossings.dropLast.dropLast.set i.val Y₀.1
                , numEdges := d.numEdges - 4 }
              have hdlen : i.val < d'.crossings.length := by
                change i.val < (d.crossings.dropLast.dropLast.set i.val Y₀.1).length
                rw [List.length_set]; exact hdl
              if ha : 1 ≤ k1.e1 ∧ k1.e1 ≤ d.numEdges - 4 ∧ k1.e1 ∈ d'.edges then
                if hwf : d'.wf = true ∧ d.wf = true then
                  [{ target := d'
                   , proof := by
                       have hY'get : d'.crossings.get ⟨i.val, hdlen⟩ = Y₀.1 := by
                         change (d.crossings.dropLast.dropLast.set i.val Y₀.1).get
                           ⟨i.val, hdlen⟩ = Y₀.1
                         rw [List.get_eq_getElem, List.getElem_set_self]
                       have hk1 : k1 =
                           ⟨k1.e1, d.numEdges - 3, d.numEdges - 3, d.numEdges - 2⟩ := by
                         rw [show k1 = ⟨k1.e1, k1.e2, k1.e3, k1.e4⟩ from rfl,
                             hk.1, hk.2.1, hk.2.2.1]
                       have hk2 : k2 =
                           ⟨k1.e1, d.numEdges - 1, d.numEdges - 1, d.numEdges⟩ := by
                         rw [show k2 = ⟨k2.e1, k2.e2, k2.e3, k2.e4⟩ from rfl,
                             hk.2.2.2.1, hk.2.2.2.2.1, hk.2.2.2.2.2.1, hk.2.2.2.2.2.2.1]
                       refine ReidemeisterStep.r2 (Or.inr
                         ⟨hwf.1, hwf.2, ⟨i.val, hdlen⟩, k1.e1, Y', finEmbed _ 4,
                           ha.1, ha.2.1, ha.2.2, ?_, ?_, ?_⟩)
                       · rw [hY'get,
                           show d'.numEdges + 2 = d.numEdges - 2 by
                             show d.numEdges - 4 + 2 = d.numEdges - 2; omega,
                           show d'.numEdges + 4 = d.numEdges by
                             show d.numEdges - 4 + 4 = d.numEdges; omega]
                         exact Y₀.2
                       · show d.crossings =
                           d'.crossings.set i.val Y' ++
                             [⟨k1.e1, d'.numEdges + 1, d'.numEdges + 1, d'.numEdges + 2⟩,
                              ⟨k1.e1, d'.numEdges + 3, d'.numEdges + 3, d'.numEdges + 4⟩]
                         rw [show d'.crossings = d.crossings.dropLast.dropLast.set i.val Y₀.1
                             from rfl,
                           List.set_set Y₀.1,
                           list_set_eq (x := Y') hdl (by rfl),
                           show d'.numEdges + 1 = d.numEdges - 3 by
                             show d.numEdges - 4 + 1 = d.numEdges - 3; omega,
                           show d'.numEdges + 2 = d.numEdges - 2 by
                             show d.numEdges - 4 + 2 = d.numEdges - 2; omega,
                           show d'.numEdges + 3 = d.numEdges - 1 by
                             show d.numEdges - 4 + 3 = d.numEdges - 1; omega,
                           show d'.numEdges + 4 = d.numEdges by
                             show d.numEdges - 4 + 4 = d.numEdges; omega,
                           ← hk1, ← hk2]
                         have hmem2 : k2 ∈ d.crossings.getLast? := by
                           rw [h2]; exact Option.mem_some.mpr rfl
                         have hmem1 : k1 ∈ d.crossings.dropLast.getLast? := by
                           rw [h1]; exact Option.mem_some.mpr rfl
                         have e2 : d.crossings = d.crossings.dropLast ++ [k2] :=
                           (List.dropLast_append_getLast? k2 hmem2).symm
                         have e1 : d.crossings.dropLast =
                             d.crossings.dropLast.dropLast ++ [k1] :=
                           (List.dropLast_append_getLast? k1 hmem1).symm
                         exact e2.trans ((congrArg (fun x => x ++ [k2]) e1).trans
                           (by simp [List.append_assoc]))
                       · show d.numEdges = d'.numEdges + 4
                         show d.numEdges = d.numEdges - 4 + 4
                         omega }]
                else []
              else []
          else []
      else []
    | none => []
  | none => []

/-- R3 FORWARD: triangular move — deterministic by window of 3 consecutive
crossings, zero fresh labels (redistribution of the 9 existing labels). -/
def r3ForwardWitnesses (d : KnotDiagram) : List (StepWitness d) :=
  (List.range (d.crossings.length)).flatMap fun i =>
      if hi : i + 2 < d.crossings.length then
      let X₁ := d.crossings.get ⟨i, by omega⟩
      let X₂ := d.crossings.get ⟨i + 1, by omega⟩
      let X₃ := d.crossings.get ⟨i + 2, by omega⟩
      -- layout of the triangle X: X₁ = ⟨a₂,a₁,g₁,g₂⟩, X₂ = ⟨a₃,g₁,g₃,b₃⟩,
      -- X₃ = ⟨g₃,g₂,b₂,b₁⟩ — the overlap equalities make the three
      -- `get` definitional after rewriting.
      if hlay : X₂.e2 = X₁.e3 ∧ X₃.e1 = X₂.e3 ∧ X₃.e2 = X₁.e4 then
        -- Nodup order of the def: [a₂, a₁, a₃, b₃, b₂, b₁, g₁, g₂, g₃]
        if hnd : List.Nodup
            [X₁.e1, X₁.e2, X₂.e1, X₂.e4, X₃.e3, X₃.e4, X₁.e3, X₁.e4, X₂.e3] then
          let d₂ : KnotDiagram :=
            { crossings := ((d.crossings.set i ⟨X₂.e1, X₂.e4, X₂.e3, X₁.e3⟩).set (i + 1)
                ⟨X₂.e3, X₁.e2, X₃.e3, X₁.e4⟩).set (i + 2) ⟨X₁.e3, X₁.e4, X₁.e1, X₃.e4⟩
            , numEdges := d.numEdges }
          if hwf : d.wf = true ∧ d₂.wf = true then
            if hlen : d.crossings.length = d₂.crossings.length then
              [{ target := d₂
               , proof := ReidemeisterStep.r3 (Or.inl
                   ⟨hwf.1, hwf.2, hlen, rfl, i, hi,
                     X₁.e2, X₁.e1, X₂.e1, X₃.e4, X₃.e3, X₂.e4, X₁.e3, X₁.e4, X₂.e3,
                     hnd,
                     by show X₁ = ⟨X₁.e1, X₁.e2, X₁.e3, X₁.e4⟩; rfl,
                     by show X₂ = ⟨X₂.e1, X₁.e3, X₂.e3, X₂.e4⟩; rw [← hlay.1],
                     by show X₃ = ⟨X₂.e3, X₁.e4, X₃.e3, X₃.e4⟩; rw [← hlay.2.1, ← hlay.2.2],
                     rfl⟩) }]
            else []
          else []
        else []
      else []
    else []

/-- The full enumeration of one-move witnesses, proofs attached. -/
def oneStepWitnessesWithProof (d : KnotDiagram) : List (StepWitness d) :=
  r1ForwardWitnesses d ++ r1BackwardWitnesses d
  ++ r2ForwardWitnesses d ++ r2BackwardWitnesses d ++ r3ForwardWitnesses d

/-- Raw witness of an applicable move: a `KnotDiagram` reachable from `d₁`
by a single `ReidemeisterStep` (without a witness of the relation). This is
the public API consumed by `verifyMovesAux`.
-/
def oneStepWitnesses (d₁ : KnotDiagram) : List KnotDiagram :=
  (oneStepWitnessesWithProof d₁).map StepWitness.target

/-- Bounded recursive verifier.

`verifyMovesAux k d₁ d₂` returns `true` iff there is a sequence of at most
`k` `ReidemeisterStep`s connecting `d₁` to `d₂`. Base cases:
- `k = 0` → `d₁ = d₂` (RTC reflexive);
- `k ≥ 1` → there is a 1-step successor `d'` of `d₁` such that
  `verifyMovesAux (k-1) d' d₂` is `true`.

**Status**: the real enumeration is wired in (`#19890`). `oneStepWitnesses d`
returns the list of genuine one-move successors (R1/R2 in both directions,
R3 forward), filtered by the decidable guards of each relation — the `false`
return stays conservative (sound:
`verifyMovesAux = true → ReidemeisterEquiv`, proved by `verifyMoves_sound`
below).
-/
def verifyMovesAux : Nat → KnotDiagram → KnotDiagram → Bool
  | 0, d, d' => decide (d = d')
  | k+1, d, d' =>
    -- Skeleton: we decide equality `d = d'` (reflexive closure at 0 moves,
    -- via the derived `DecidableEq` — no `LawfulBEq` required) and each
    -- 1-step successor of `d`. The `false` return is conservative
    -- (sound: `verifyMovesAux = true → ReidemeisterEquiv`, the converse
    -- is not required).
    decide (d = d') ||
    (oneStepWitnesses d).any fun d_next => verifyMovesAux k d_next d'

/-- Public interface of the bounded verifier. -/
def verifyMoves (n : Nat) (d₁ d₂ : KnotDiagram) : Bool :=
  verifyMovesAux n d₁ d₂

/-! ## 4. Soundness

Soundness: « if `verifyMoves n d₁ d₂ = true`, then
`ReidemeisterEquiv d₁ d₂ ». The converse (completeness) is out of scope —
the algorithm is deliberately bounded and loses witnesses beyond the budget.

**Proof** (the PR2+ « targeted » outline, now held): induction on `n`.
- `n = 0`: `verifyMovesAux 0 d₁ d₂ = decide (d₁ = d₂) = true` → `d₁ = d₂`
  (via `of_decide_eq_true`, through the derived `DecidableEq`) →
  `ReidemeisterEquiv.refl d₁`.
- `n = k+1`: `verifyMovesAux (k+1) d₁ d₂ = true` →
  (`decide (d₁ = d₂) = true` ∧ reflexivity) ∨ (∃ d_next, `verifyMovesAux k d_next d₂ = true`
  ∧ `ReidemeisterStep d₁ d_next`). Case by case, the first reduces to
  `n = 0`, the second uses the induction hypothesis to obtain
  `ReidemeisterEquiv d_next d₂`, then `ReidemeisterEquiv.step` + `trans`
  close the diagram.

The concrete instrumentation (`Bool.or_eq_true_iff` then extraction of the
witness `d_next` from `(oneStepWitnesses d).any` via `List.any_eq_true`) is
in place; the former PR2+ wall — the real enumeration of witnesses — is now
cleared by the bridge lemma `oneStepWitnesses_sound` below.
-/
/-- Bridge lemma (`named-hard-wall` pattern, now held): every witness returned
by `oneStepWitnesses d` is a one-`ReidemeisterStep` successor of `d`.

Since the real enumeration (`#19890`), the proof is **by construction**: each
element of `oneStepWitnessesWithProof d` carries its proof
(`StepWitness.proof`), and `oneStepWitnesses` is only the `map` of the
targets — the membership is lifted back by `List.mem_map`. No soundness is
re-guessed from the target diagram. -/
theorem oneStepWitnesses_sound (d d' : KnotDiagram)
    (h : d' ∈ oneStepWitnesses d) : ReidemeisterStep d d' := by
  obtain ⟨w, _hw, heq⟩ := List.mem_map.mp h
  subst heq
  exact w.proof

/-- Acceptance `#19890` (3), R1 witness: the concrete pair of
`reidemeister1Connected_satisfiable` is indeed connected by the verifier at
budget 1 — the R1 FORWARD enumeration emits `d₂` as a successor of `d₁`. -/
theorem verifyMoves_one_r1_witness :
    verifyMoves 1
      { crossings := [⟨1,2,3,4⟩, ⟨1,2,3,4⟩], numEdges := 4 }
      { crossings := [⟨1,2,3,4⟩, ⟨5,2,3,4⟩, ⟨1,5,6,6⟩], numEdges := 6 } = true := by
  decide

/-- Acceptance `#19890` (3), R3 witness: the concrete pair of
`reidemeister3Connected_satisfiable` is indeed connected at budget 1 — the
triangular move is deterministic by window, the enumeration finds it. -/
theorem verifyMoves_one_r3_witness :
    verifyMoves 1
      { crossings := [⟨1,2,7,8⟩, ⟨3,7,9,4⟩, ⟨9,8,5,6⟩,
                       ⟨1,2,10,10⟩, ⟨3,4,5,6⟩], numEdges := 10 }
      { crossings := [⟨3,4,9,7⟩, ⟨9,2,5,8⟩, ⟨7,8,1,6⟩,
                       ⟨1,2,10,10⟩, ⟨3,4,5,6⟩], numEdges := 10 } = true := by
  decide

theorem verifyMoves_sound :
    ∀ (n : Nat) (d₁ d₂ : KnotDiagram),
      verifyMoves n d₁ d₂ = true → ReidemeisterEquiv d₁ d₂ := by
  intro n
  induction n with
  | zero =>
    intro d₁ d₂ h
    simp only [verifyMoves, verifyMovesAux] at h
    have hd : d₁ = d₂ := of_decide_eq_true h
    subst hd
    exact ReidemeisterEquiv.refl d₁
  | succ k ih =>
    intro d₁ d₂ h
    simp only [verifyMoves, verifyMovesAux] at h
    rcases Bool.or_eq_true_iff.mp h with heq | hany
    · have hd : d₁ = d₂ := of_decide_eq_true heq
      subst hd
      exact ReidemeisterEquiv.refl d₁
    · obtain ⟨d_next, hmem, hver⟩ := List.any_eq_true.mp hany
      exact ReidemeisterEquiv.trans
        (ReidemeisterEquiv.step (oneStepWitnesses_sound d₁ d_next hmem))
        (ih d_next d₂ hver)

/-! ## 5. Helpers for `Lidman.lean` (indirect target)

`foldChangeCrossingsAt` sequentially applies a list of crossing changes to
a knot (fold left). This is the « `indices` witness » of
`Knot.UnknottableIn` (Invariant.lean:2292) rendered operational.

`unknottingWitness` seals the typical usage: « for a knot to have unknotting
number ≤ n, exhibit a length-n crossing-change sequence and a
ReidemeisterEquiv sequence between its image and `unknotDiagram` ». This is
the contract that `unknotting_11n102_upper` (Lidman:81) is meant to honour — the
structure exists, no instance is supplied: #18611 measured that a bounded search
(diagrams ≤ 13 crossings, 138,623 states) does not reach `unknotDiagram` from the
11n102 class, and this module does not supply the witness.
-/

/-- Sequentially applies a list of crossing changes. -/
def foldChangeCrossingsAt (k : Knot) (indices : List Nat) : Knot :=
  indices.foldl Knot.changeCrossingAt k

/-- Unknotting witness: a list of crossing changes + a ReidemeisterEquiv
sequence between its image and `unknotDiagram`. -/
structure UnknottingWitness (k : Knot) (n : Nat) where
  indices : List Nat
  length_eq : indices.length = n
  equiv :
    MoveSequence
      (foldChangeCrossingsAt k indices).diagram
      unknotDiagram

/-! ## 6. Future compatibility

The module only depends on `Knots.Reidemeister` and `Knots.Invariant` — not
on `Knots.ReidemeisterInvariance` (which would import `Knots.Conway` and
spin the lake needlessly for passes that only attack the combinatorial side).

The lake does **not** import this module yet: `Knots.lean` (root aggregator)
lists `Knots.ReidemeisterMoves` but not `Knots.ReidemeisterCombinatorial`
(checked 2026-10-09). Wiring it in first requires resolving the API collision
with `Knots.ReidemeisterMoves`, which already defines `movesConnects`,
`verifyMoves` and `verifyMoves_sound` (ReidemeisterMoves.lean:303/295/501) —
two `movesConnects` with different signatures in the same `Knots` namespace
cannot be imported together.
-/

end Knots
