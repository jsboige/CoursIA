/-
Knots.ReidemeisterMoves_en — kernel-verifiable sequences of moves (EN sibling)
===============================================================================

English sibling of `ReidemeisterMoves.lean` (FR canonical). Convention EPIC
#4980 (decision ratified 2026-07-04, cf `code-style.md` §Lean i18n): distinct
FR + EN sibling files — no inline bilingual block in a single file (Option B
rejected). The module docstring and the theorem docstrings below differ from
the FR version; the body signatures, proofs and tactics remain byte-identical
between the two files (`namespace Knots_en` to avoid name clashes).

The missing organ named by the 30/09 arbitration (issue #18611, Epic #1453,
point 3): a **kernel-verifiable sequence of Reidemeister moves**, on the
combinatorial side. Until now, `ReidemeisterStep` has been a `Prop` — a
proof, impossible to execute or to certify from an external certificate.
This module introduces the **data** layer:

* an inductive `ReidemeisterMove` (R1 loop creation/removal, R2 pair
  addition/removal, R3 triangle) carrying both diagrams;
* verifiers `verifyR1Fwd` / `verifyR2Fwd` / `verifyR3Fwd : Bool` that
  **decide** the relations `Reidemeister1Connected` /
  `Reidemeister2Connected` / `Reidemeister3Connected` by witness extraction
  (no enumeration beyond the surgery index: the kink is read at the end of
  the list, the rewritten crossing at its index);
* a chain verifier `verifyMoves : List ReidemeisterMove → … → Bool` and the
  connector `movesConnects d₁ d₂` (certified list + well-formedness);
* the **soundness** theorem `movesConnects_sound`: a Bool certificate that
  passes the verifier compiles to a proof of `ReidemeisterEquiv`. This is
  what gives the 14 remaining `sorry`s of the lake (Reidemeister:1053,
  Lidman:80/100, Slice:42/55/82/118, and their `_en` twins) a language in
  which to *state and verify* their witnesses.

Why soundness suffices (and why completeness is deferred): the verifier
extracts witnesses exactly in the shape of the surgery of the definitions
(kink in last position, `List.set` at the rewritten crossing), so
`Reidemeister1Connected d d' → verifyR1Fwd d d' = true` should also hold;
the formal proof of that direction (completeness) is left as documented
future work, the immediate value being the certificate → proof direction.

Verifier design note: crossings are read through `crossingAt`
(`Option.getD`, neutral default out of bounds) rather than by `match` on
`l[i]?` — an inner `match` would make the soundness inversion dependent
(eliminating a scrutinee that occurs in a hypothesis under a `match`
fails). Out-of-bounds reads are rejected anyway by the surgery equations,
and the neutral default can never forge a false positive: every tested
clause is reinjected as-is into the witness of the target definition.

Witness theorems on arc partitions (point 1 of #18611, mirror of the
`reidemeister3Connected_*`): bare `SameRel` is **false** under R1/R2 — the
fresh labels `n+1…` are covered on one side only, and renaming an `e2`/`e4`
slot destroys an old Wirtinger link (the arc class refines, the arc
subdivides). This module introduces `SameRelOn n` (restriction to common
labels ≤ n) and `RefinesOn n` (refinement), proved by `decide` on the three
satisfiable witnesses of the lake.
-/

import Knots.Conway_en
import Knots.ReidemeisterInvariance_en

namespace Knots_en

/-! ## 1. `SameRelOn` and `RefinesOn` — partition invariance bounded to common labels

`SameRel` (ReidemeisterInvariance) requires the same class relation for
ALL labels. Under R1/R2, the fresh labels `d₁.numEdges + k` are covered
only by the enlarged diagram: bare `SameRel` mechanically fails. The
right reading of invariance is **bounded to the common labels** — the
form under which the R3 witness of section 5 of
`ReidemeisterInvariance_en.lean` generalises to the moves that change
`numEdges`.
-/

/-- Two partitions carry the same class relation on the labels `≤ n`
    (labels common to both diagrams of an R1/R2 surgery). Weakening of
    `SameRel`: the restriction to the old labels. -/
def SameRelOn (n : Nat) (P Q : List (List Nat)) : Prop :=
  ∀ ⦃x y : Nat⦄, x ≤ n → y ≤ n → (SameClass P x y ↔ SameClass Q x y)

/-- The partition `fine` refines the partition `coarse` on the labels
    `≤ n`: every common class of `fine` lives in a class of `coarse`.
    This is the correct form of the R1/R2 effect on arc partitions —
    renaming an `e2`/`e4` slot may destroy an old Wirtinger link
    (refinement), never create one. -/
def RefinesOn (n : Nat) (fine coarse : List (List Nat)) : Prop :=
  ∀ ⦃x y : Nat⦄, x ≤ n → y ≤ n → (SameClass fine x y → SameClass coarse x y)

/-- `SameRel` implies its bounded restriction: the bridge from the
    general R3 theorem (`Reidemeister3Connected.arcPartition_sameRel`)
    to the witness theorems of this module. -/
lemma SameRel.sameRelOn {P Q : List (List Nat)} (h : SameRel P Q) (n : Nat) :
    SameRelOn n P Q := fun _ _ _ _ => h _ _

/-- `SameClass` is decidable: the definition is a bounded existence in a
    literal list, `Nat`s have decidable equality. This is the vehicle of
    the witness theorems proved by `decide` (section 6). -/
instance decidableSameClass {P : List (List Nat)} {x y : Nat} :
    Decidable (SameClass P x y) := by
  unfold SameClass
  infer_instance

/-- Reduction of a bounded quantifier `∀ x ≤ n` to a finite enumeration:
    the vehicle of the witness theorems proved by `decide` (the partition
    domain is literal, only the quantifier is infinite). -/
lemma forall_le_iff_all_range {n : Nat} {p : Nat → Prop} [DecidablePred p] :
    (∀ x, x ≤ n → p x) ↔ (List.range (n + 1)).all (fun x => decide (p x)) = true := by
  constructor
  · intro h
    exact List.all_eq_true.mpr fun x hx =>
      decide_eq_true (h x (Nat.lt_succ_iff.mp (List.mem_range.mp hx)))
  · intro h x hx
    exact of_decide_eq_true
      (List.all_eq_true.mp h x (List.mem_range.mpr (Nat.lt_succ_iff.mpr hx)))

/-! ## 2. The inductive `ReidemeisterMove` — the move as data

`ReidemeisterStep` is a `Prop`: it lives in `Prop`, eliminated only by
proofs. The organ requested by #18611 is the **data** version of the
step — constructible, serialisable, checkable by a `Bool` function. Each
constructor carries the two diagrams; the nature of the move (R1 kink,
R2 pair, R3 triangle) is the constructor itself.
-/

/-- A Reidemeister move as **data**: the nature of the move (R1 kink,
    R2 pair, R3 triangle) and the source/target diagrams.
    Well-formedness is NOT a field — it is checked (`verifyMove`) and
    certified (`movesConnects_sound`), mirroring the design choice of
    `KnotDiagram.wf` (Basic_en.lean, issue #8604). -/
inductive ReidemeisterMove : Type where
  /-- Creation/removal of a kink (loop). -/
  | r1 (source target : KnotDiagram) : ReidemeisterMove
  /-- Insertion/removal of a pair of crossings (bigon). -/
  | r2 (source target : KnotDiagram) : ReidemeisterMove
  /-- Triangular slide. -/
  | r3 (source target : KnotDiagram) : ReidemeisterMove
  deriving Repr

/-- Source diagram of the move (projection not generated automatically:
    a three-constructor inductive has no common projectable fields, the
    projection is defined by pattern matching). -/
def ReidemeisterMove.source : ReidemeisterMove → KnotDiagram
  | .r1 s _ => s
  | .r2 s _ => s
  | .r3 s _ => s

/-- Target diagram of the move. -/
def ReidemeisterMove.target : ReidemeisterMove → KnotDiagram
  | .r1 _ t => t
  | .r2 _ t => t
  | .r3 _ t => t

/-! ## 3. The per-move verifiers

Extraction principle (no enumeration): the surgery of the connected
definitions places the kink in **last** position of `d₂.crossings` and
rewrites the endpoint crossing **at its index** via `List.set`. The
verifier thus reads the kink by `getLast?`, the rewritten crossing by
`crossingAt`, and enumerates only the index `i` — polynomial per step,
suited to the small diagrams targeted by #18611.

The relations `isRenameOf` / `isDoubleRenameOf` / `hasEdge` are `Prop`s
defined by conjunctions/disjunctions of `Nat` equalities: without a
declared `Decidable` instance, `decide` cannot see them (the instance
does not cross the delta-reduction of a `def`). The three instances
below expose them — same remedy as the `unfold … ; decide` of the
witnesses of `Reidemeister_en.lean`, in reusable form.
-/

/-- Safe crossing read by index: the crossing at index `i` if it exists,
    else a neutral default. Avoids inner `match`es in the verifiers
    (non-dependent soundness inversion); an out-of-bounds read cannot
    produce a false positive because every tested clause is reinjected
    as-is into the witness of the target definition. -/
def crossingAt (l : List PDCrossing) (i : Nat) : PDCrossing :=
  l[i]?.getD ⟨0, 0, 0, 0⟩

/-- `PDCrossing.isRenameOf` is decidable (conjunctions/disjunctions of
    `Nat` equalities after delta-reduction). -/
instance decidableIsRenameOf (Y' c : PDCrossing) (a b : Nat) :
    Decidable (Y'.isRenameOf c a b) := by
  unfold PDCrossing.isRenameOf
  infer_instance

/-- `PDCrossing.isDoubleRenameOf` is decidable. -/
instance decidableIsDoubleRenameOf (Y' c : PDCrossing) (a o₁ o₂ : Nat) :
    Decidable (Y'.isDoubleRenameOf c a o₁ o₂) := by
  unfold PDCrossing.isDoubleRenameOf
  infer_instance

/-- `PDCrossing.hasEdge` is decidable. -/
instance decidableHasEdge (c : PDCrossing) (z : Nat) :
    Decidable (c.hasEdge z) := by
  unfold PDCrossing.hasEdge
  infer_instance

/-- Bool verifier of `Reidemeister1Connected d d'` (forward direction
    only: `d'` is the kink-enlarged diagram). Extracts `a` from the
    terminal kink `⟨a, n+1, n+2, n+2⟩`, `Y'` from the crossing at the
    enumerated index, then re-tests every clause of the definition:
    `wf` on both sides, `numEdges + 2`, bounds and membership of `a`,
    proper arc (`∃ j ≠ i`), `isRenameOf`, and the surgery equation via
    `dropLast`. -/
def verifyR1Fwd (d d' : KnotDiagram) : Bool :=
  d.wf && d'.wf && decide (d'.numEdges = d.numEdges + 2) &&
  match d'.crossings.getLast? with
  | none => false
  | some K =>
    decide (K.e2 = d.numEdges + 1 ∧ K.e3 = d.numEdges + 2 ∧ K.e4 = d.numEdges + 2 ∧
      1 ≤ K.e1 ∧ K.e1 ≤ d.numEdges ∧ K.e1 ∈ d.edges) &&
    (List.range d.crossings.length).any fun i =>
      decide (d'.crossings.dropLast = d.crossings.set i (crossingAt d'.crossings.dropLast i)) &&
      decide ((crossingAt d'.crossings.dropLast i).isRenameOf
        (crossingAt d.crossings i) K.e1 (d.numEdges + 1)) &&
      (List.range d.crossings.length).any fun j =>
        decide (j ≠ i ∧ (crossingAt d.crossings j).hasEdge K.e1)

/-- Bool verifier of `Reidemeister2Connected d d'` (forward direction).
    Extracts `a` from the two terminal bigons `⟨a, n+1, n+1, n+2⟩` and
    `⟨a, n+3, n+3, n+4⟩`, `Y'` from the crossing at the enumerated
    index, then re-tests every clause: `wf`, `numEdges + 4`, bounds and
    membership of `a`, `isDoubleRenameOf`, surgery via double
    `dropLast`. -/
def verifyR2Fwd (d d' : KnotDiagram) : Bool :=
  d.wf && d'.wf && decide (d'.numEdges = d.numEdges + 4) &&
  match d'.crossings.getLast? with
  | none => false
  | some K₂ =>
    decide (K₂.e2 = d.numEdges + 3 ∧ K₂.e3 = d.numEdges + 3 ∧ K₂.e4 = d.numEdges + 4 ∧
      1 ≤ K₂.e1 ∧ K₂.e1 ≤ d.numEdges ∧ K₂.e1 ∈ d.edges) &&
    match d'.crossings.dropLast.getLast? with
    | none => false
    | some K₁ =>
      decide (K₁.e1 = K₂.e1 ∧ K₁.e2 = d.numEdges + 1 ∧ K₁.e3 = d.numEdges + 1 ∧
        K₁.e4 = d.numEdges + 2) &&
      (List.range d.crossings.length).any fun i =>
        decide (d'.crossings.dropLast.dropLast =
          d.crossings.set i (crossingAt d'.crossings.dropLast.dropLast i)) &&
        decide ((crossingAt d'.crossings.dropLast.dropLast i).isDoubleRenameOf
          (crossingAt d.crossings i) K₂.e1 (d.numEdges + 2) (d.numEdges + 4))

/-- Bool verifier of `Reidemeister3Connected d d'` (forward direction).
    Enumerates the triangle apex index `i`, reads the three consecutive
    crossings of `d` (X layout `⟨a₂,a₁,g₁,g₂⟩`, `⟨a₃,g₁,g₃,b₃⟩`,
    `⟨g₃,g₂,b₂,b₁⟩`), checks the sharing of internal labels between the
    three vertices (field equalities), the `Nodup` of the nine labels,
    and the surgery equation of the triple `List.set`. -/
def verifyR3Fwd (d d' : KnotDiagram) : Bool :=
  d.wf && d'.wf && decide (d.crossings.length = d'.crossings.length) &&
  decide (d.numEdges = d'.numEdges) &&
  (List.range d.crossings.length).any fun i =>
    decide (i + 2 < d.crossings.length ∧
      (crossingAt d.crossings (i + 1)).e2 = (crossingAt d.crossings i).e3 ∧
      (crossingAt d.crossings (i + 2)).e1 = (crossingAt d.crossings (i + 1)).e3 ∧
      (crossingAt d.crossings (i + 2)).e2 = (crossingAt d.crossings i).e4 ∧
      List.Nodup [(crossingAt d.crossings i).e1, (crossingAt d.crossings i).e2,
        (crossingAt d.crossings (i + 1)).e1, (crossingAt d.crossings (i + 1)).e4,
        (crossingAt d.crossings (i + 2)).e3, (crossingAt d.crossings (i + 2)).e4,
        (crossingAt d.crossings i).e3, (crossingAt d.crossings i).e4,
        (crossingAt d.crossings (i + 1)).e3] ∧
      d'.crossings = ((d.crossings.set i
          ⟨(crossingAt d.crossings (i + 1)).e1, (crossingAt d.crossings (i + 1)).e4,
            (crossingAt d.crossings (i + 1)).e3, (crossingAt d.crossings i).e3⟩).set (i + 1)
        ⟨(crossingAt d.crossings (i + 1)).e3, (crossingAt d.crossings i).e2,
          (crossingAt d.crossings (i + 2)).e3, (crossingAt d.crossings i).e4⟩).set (i + 2)
        ⟨(crossingAt d.crossings i).e3, (crossingAt d.crossings i).e4,
          (crossingAt d.crossings i).e1, (crossingAt d.crossings (i + 2)).e4⟩)

/-- Bool verifier of one elementary step, direction-neutral: the
    `Reidemeister1Connected` relation is bipolar (the move and its
    inverse), the step accepts either orientation — exact mirror of the
    disjunction of the constructors of `ReidemeisterStep`. -/
def verifyR1 (d d' : KnotDiagram) : Bool := verifyR1Fwd d d' || verifyR1Fwd d' d

/-- R2 counterpart of `verifyR1`. -/
def verifyR2 (d d' : KnotDiagram) : Bool := verifyR2Fwd d d' || verifyR2Fwd d' d

/-- Bool verifier of the triangular move. The inverse direction
    (`Reidemeister3ConnectedInv`) rewrites the Y triangle into X —
    accepted by testing both orientations of the X layout. -/
def verifyR3 (d d' : KnotDiagram) : Bool := verifyR3Fwd d d' || verifyR3Fwd d' d

/-- Bool verifier of a move: `true` iff the move is a well-formed
    **connected** Reidemeister step in either direction. -/
def verifyMove (m : ReidemeisterMove) : Bool :=
  match m with
  | .r1 src tgt => verifyR1 src tgt
  | .r2 src tgt => verifyR2 src tgt
  | .r3 src tgt => verifyR3 src tgt

/-! ## 4. The verified chain — `verifyMoves` and `movesConnects`

A sequence of moves connects `d₁` to `d₂` if it forms a continuous chain
whose every link passes `verifyMove`. Well-formedness is not data of the
list: it **is** the `= true` of the verifier.
-/

/-- Checks that a sequence of moves forms a continuous chain from `start`
    to `end` whose every link is a well-formed connected Reidemeister
    step. Base case: the empty list requires `start = end`
    (reflexivity). -/
def verifyMoves : List ReidemeisterMove → KnotDiagram → KnotDiagram → Bool
  | [], start, end_ => decide (start = end_)
  | m :: ms, start, end_ =>
    decide (m.source = start) && verifyMove m && verifyMoves ms m.target end_

/-- The connector of #18611: `movesConnects d₁ d₂` is the proposition
    "the list `ms` is a well-formedness certificate linking `d₁` to `d₂`"
    — a certified list of moves, checkable by the kernel. -/
def movesConnects (ms : List ReidemeisterMove) (d₁ d₂ : KnotDiagram) : Prop :=
  verifyMoves ms d₁ d₂ = true

/-! ## 5. Soundness — a Bool certificate compiles to a proof

The central theorem of the organ: `verifyMoves ms d₁ d₂ = true` implies
`ReidemeisterEquiv d₁ d₂`. The proof recomposes the chain link by link;
each link rebuilds the existential witness of the connected definition
from the data extracted by the verifier. Two inversion bricks: the split
of the kink `getLast?` happens BEFORE unfolding the verifier (the
scrutinee is then in no hypothesis, the elimination is free), and the
indexed reads are converted by
`List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩` (no `cases` on a scrutinee
present in a hypothesis). The "rewritten prefix ++ kink(s)"
reconstruction leans on `List.getLast?_eq_some_iff`
(`l.getLast? = some K ↔ ∃ M, l = M ++ [K]`).
-/

/-- Soundness of the R1 verifier (forward direction): if the verifier
    accepts `(d, d')`, then `Reidemeister1Connected d d'` holds — the
    existential witness of the definition (index, arc `a`, rewritten
    crossing `Y'`, renaming `ρ`, proper arc `j`) is rebuilt from the
    data the verifier extracted. -/
theorem verifyR1Fwd_sound {d d' : KnotDiagram} (h : verifyR1Fwd d d' = true) :
    Reidemeister1Connected d d' := by
  cases hK : d'.crossings.getLast? with
  | none => simp [verifyR1Fwd, hK] at h
  | some K =>
    simp only [verifyR1Fwd, hK, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hwf1, hwf2⟩, hn⟩, hform, hanyi⟩ := h
    obtain ⟨hb, hc, hc', ha1, han, hmem⟩ := of_decide_eq_true hform
    rw [List.any_eq_true] at hanyi
    obtain ⟨i, hi_mem, hbody⟩ := hanyi
    have hi : i < d.crossings.length := List.mem_range.mp hi_mem
    have hY2 : d.crossings[i]? = some d.crossings[i] :=
      List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩
    simp only [Bool.and_eq_true, crossingAt, hY2, Option.getD_some] at hbody
    obtain ⟨⟨hsurg, hrename⟩, hanyj⟩ := hbody
    rw [List.any_eq_true] at hanyj
    obtain ⟨j, hj_mem, hj_body⟩ := hanyj
    have hj : j < d.crossings.length := List.mem_range.mp hj_mem
    have hcj : d.crossings[j]? = some d.crossings[j] :=
      List.getElem?_eq_some_iff.mpr ⟨hj, rfl⟩
    simp only [crossingAt, hcj, Option.getD_some] at hj_body
    obtain ⟨hjne, hhas⟩ := of_decide_eq_true hj_body
    -- the rebuilt kink shape (structural eta then fields)
    have heta : K = ⟨K.e1, K.e2, K.e3, K.e4⟩ := rfl
    have hKform : K = ⟨K.e1, d.numEdges + 1, d.numEdges + 2, d.numEdges + 2⟩ :=
      heta.trans (by simp [hb, hc, hc'])
    -- surgery reconstruction: rewritten prefix ++ kink
    obtain ⟨M, hM⟩ := List.getLast?_eq_some_iff.mp hK
    set Y' := crossingAt d'.crossings.dropLast i with hY'def
    have hsurg' : d'.crossings.dropLast = d.crossings.set i Y' :=
      of_decide_eq_true hsurg
    have hMeq : M = d.crossings.set i Y' := by
      have h2 : (M ++ [K]).dropLast = d.crossings.set i Y' := by
        rw [← hM]; exact hsurg'
      simp at h2
      exact h2
    have hchirurgie : d'.crossings =
        d.crossings.set i Y' ++
        [⟨K.e1, d.numEdges + 1, d.numEdges + 2, d.numEdges + 2⟩] := by
      rw [hM, hMeq, hKform]
    have hρ : Fin d.numEdges ↪ Fin (d.numEdges + 2) :=
      ⟨fun k => ⟨k.val, by omega⟩, fun x y hxy => by
        injection hxy with hv; exact Fin.ext hv⟩
    exact ⟨hwf1, hwf2, ⟨⟨i, hi⟩, K.e1, Y', hρ,
      ha1, han, hmem,
      ⟨⟨j, hj⟩, Fin.ne_of_val_ne hjne, hhas⟩,
      of_decide_eq_true hrename, hchirurgie,
      of_decide_eq_true hn⟩⟩

/-- Soundness of the R2 verifier (forward direction): same mechanics as
    R1 with the two terminal bigons and the double `dropLast`. -/
theorem verifyR2Fwd_sound {d d' : KnotDiagram} (h : verifyR2Fwd d d' = true) :
    Reidemeister2Connected d d' := by
  cases hK₂ : d'.crossings.getLast? with
  | none => simp [verifyR2Fwd, hK₂] at h
  | some K₂ =>
    cases hK₁ : d'.crossings.dropLast.getLast? with
    | none => simp [verifyR2Fwd, hK₂, hK₁] at h
    | some K₁ =>
      simp only [verifyR2Fwd, hK₂, hK₁, Bool.and_eq_true] at h
      obtain ⟨⟨⟨hwf1, hwf2⟩, hn⟩, hform₂, hform₁, hanyi⟩ := h
      obtain ⟨hb₂, hc₂, hd₂, ha1, han, hmem⟩ := of_decide_eq_true hform₂
      obtain ⟨ha_eq, hb₁, hc₁, hd₁⟩ := of_decide_eq_true hform₁
      rw [List.any_eq_true] at hanyi
      obtain ⟨i, hi_mem, hbody⟩ := hanyi
      have hi : i < d.crossings.length := List.mem_range.mp hi_mem
      have hY2 : d.crossings[i]? = some d.crossings[i] :=
        List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩
      simp only [Bool.and_eq_true, crossingAt, hY2, Option.getD_some] at hbody
      obtain ⟨hsurg, hrename⟩ := hbody
      -- the two rebuilt kink shapes (structural eta then fields)
      have heta₁ : K₁ = ⟨K₁.e1, K₁.e2, K₁.e3, K₁.e4⟩ := rfl
      have hK₁form : K₁ = ⟨K₂.e1, d.numEdges + 1, d.numEdges + 1, d.numEdges + 2⟩ :=
        heta₁.trans (by simp [ha_eq, hb₁, hc₁, hd₁])
      have heta₂ : K₂ = ⟨K₂.e1, K₂.e2, K₂.e3, K₂.e4⟩ := rfl
      have hK₂form : K₂ = ⟨K₂.e1, d.numEdges + 3, d.numEdges + 3, d.numEdges + 4⟩ :=
        heta₂.trans (by simp [hb₂, hc₂, hd₂])
      -- the two reconstruction levels
      set Y' := crossingAt d'.crossings.dropLast.dropLast i with hY'def
      obtain ⟨M₂, hM₂⟩ := List.getLast?_eq_some_iff.mp hK₂
      have hdrop₂ : d'.crossings.dropLast = M₂ := by rw [hM₂]; simp
      obtain ⟨M₁, hM₁⟩ := List.getLast?_eq_some_iff.mp hK₁
      have hM₁eq : M₁ = d.crossings.set i Y' := by
        have h2 : (M₁ ++ [K₁]).dropLast = d.crossings.set i Y' := by
          rw [← hM₁]; exact of_decide_eq_true hsurg
        simp at h2
        exact h2
      have hM₂eq : M₂ = d.crossings.set i Y' ++
          [⟨K₂.e1, d.numEdges + 1, d.numEdges + 1, d.numEdges + 2⟩] := by
        rw [← hdrop₂, hM₁, hM₁eq, hK₁form]
      have hchirurgie : d'.crossings =
          d.crossings.set i Y' ++
          [⟨K₂.e1, d.numEdges + 1, d.numEdges + 1, d.numEdges + 2⟩,
           ⟨K₂.e1, d.numEdges + 3, d.numEdges + 3, d.numEdges + 4⟩] := by
        rw [hM₂, hM₂eq, hK₂form, List.append_assoc]
        rfl
      have hρ : Fin d.numEdges ↪ Fin (d.numEdges + 4) :=
        ⟨fun k => ⟨k.val, by omega⟩, fun x y hxy => by
          injection hxy with hv; exact Fin.ext hv⟩
      exact ⟨hwf1, hwf2, ⟨⟨i, hi⟩, K₂.e1, Y', hρ,
        ha1, han, hmem, of_decide_eq_true hrename, hchirurgie,
        of_decide_eq_true hn⟩⟩

/-- Soundness of the R3 verifier (forward direction): the three indexed
    reads provide the nine labels of the triangle, the internal label
    sharing equalities and the `Nodup` are decided, and the triple
    `List.set` equation is the very surgery of the definition. -/
theorem verifyR3Fwd_sound {d d' : KnotDiagram} (h : verifyR3Fwd d d' = true) :
    Reidemeister3Connected d d' := by
  simp only [verifyR3Fwd, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hwf1, hwf2⟩, hlen⟩, hedges⟩, hany⟩ := h
  rw [List.any_eq_true] at hany
  obtain ⟨i, hi_mem, hbody⟩ := hany
  have hi : i < d.crossings.length := List.mem_range.mp hi_mem
  obtain ⟨hi2, he₁, he₂, he₃, hnodup, hchirurgie⟩ := of_decide_eq_true hbody
  have hilt : i + 1 < d.crossings.length := by omega
  have h₁ : d.crossings[i]? = some d.crossings[i] :=
    List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩
  have h₂ : d.crossings[i + 1]? = some d.crossings[i + 1] :=
    List.getElem?_eq_some_iff.mpr ⟨hilt, rfl⟩
  have h₃ : d.crossings[i + 2]? = some d.crossings[i + 2] :=
    List.getElem?_eq_some_iff.mpr ⟨hi2, rfl⟩
  -- reduction of the indexed reads to direct accesses
  have hval₁ : crossingAt d.crossings i = d.crossings[i] := by
    simp only [crossingAt, h₁, Option.getD_some]
  have hval₂ : crossingAt d.crossings (i + 1) = d.crossings[i + 1] := by
    simp only [crossingAt, h₂, Option.getD_some]
  have hval₃ : crossingAt d.crossings (i + 2) = d.crossings[i + 2] := by
    simp only [crossingAt, h₃, Option.getD_some]
  simp only [hval₁, hval₂, hval₃] at he₁ he₂ he₃ hnodup hchirurgie
  -- the nine labels are the fields of the three crossings; the read
  -- equations close by structural eta, the sharing of the internal
  -- labels (he₁ he₂ he₃) rewrites the relevant slots
  have hget₁ : d.crossings[i] =
      ⟨(d.crossings[i]).e1, (d.crossings[i]).e2, (d.crossings[i]).e3,
        (d.crossings[i]).e4⟩ := rfl
  have hget₂ : d.crossings[i + 1] =
      ⟨(d.crossings[i + 1]).e1, (d.crossings[i]).e3, (d.crossings[i + 1]).e3,
        (d.crossings[i + 1]).e4⟩ := by rw [← he₁]
  have hget₃ : d.crossings[i + 2] =
      ⟨(d.crossings[i + 1]).e3, (d.crossings[i]).e4, (d.crossings[i + 2]).e3,
        (d.crossings[i + 2]).e4⟩ := by rw [← he₂, ← he₃]
  exact ⟨hwf1, hwf2, of_decide_eq_true hlen, of_decide_eq_true hedges, i, hi2,
    (d.crossings[i]).e2, (d.crossings[i]).e1, (d.crossings[i + 1]).e1,
    (d.crossings[i + 2]).e4, (d.crossings[i + 2]).e3, (d.crossings[i + 1]).e4,
    (d.crossings[i]).e3, (d.crossings[i]).e4, (d.crossings[i + 1]).e3,
    hnodup, hget₁, hget₂, hget₃, hchirurgie⟩

/-- Soundness of the step verifier: an accepted move is a
    `ReidemeisterStep` (in either direction, like the corresponding
    constructor). -/
theorem verifyMove_sound {m : ReidemeisterMove} (h : verifyMove m = true) :
    ReidemeisterStep m.source m.target := by
  cases m with
  | r1 d d' =>
    simp only [ReidemeisterMove.source, ReidemeisterMove.target, verifyMove,
      verifyR1] at h ⊢
    rcases Bool.or_eq_true_iff.mp h with h' | h'
    · exact ReidemeisterStep.r1 (Or.inl (verifyR1Fwd_sound h'))
    · exact ReidemeisterStep.r1 (Or.inr (verifyR1Fwd_sound h'))
  | r2 d d' =>
    simp only [ReidemeisterMove.source, ReidemeisterMove.target, verifyMove,
      verifyR2] at h ⊢
    rcases Bool.or_eq_true_iff.mp h with h' | h'
    · exact ReidemeisterStep.r2 (Or.inl (verifyR2Fwd_sound h'))
    · exact ReidemeisterStep.r2 (Or.inr (verifyR2Fwd_sound h'))
  | r3 d d' =>
    simp only [ReidemeisterMove.source, ReidemeisterMove.target, verifyMove,
      verifyR3] at h ⊢
    rcases Bool.or_eq_true_iff.mp h with h' | h'
    · exact ReidemeisterStep.r3 (Or.inl (verifyR3Fwd_sound h'))
    · exact ReidemeisterStep.r3 (Or.inr (verifyR3Fwd_sound h'))

/-- Soundness of the chain verifier: an accepted sequence is a proof of
    `ReidemeisterEquiv` — the complete organ of #18611, point 2. -/
theorem verifyMoves_sound {ms : List ReidemeisterMove} {d₁ d₂ : KnotDiagram}
    (h : verifyMoves ms d₁ d₂ = true) : ReidemeisterEquiv d₁ d₂ := by
  induction ms generalizing d₁ with
  | nil =>
    have := of_decide_eq_true h
    subst this
    exact ReidemeisterEquiv.refl _
  | cons m ms ih =>
    simp only [verifyMoves, Bool.and_eq_true] at h
    obtain ⟨⟨hsrc, hmove⟩, hrest⟩ := h
    have hsrc' := of_decide_eq_true hsrc
    rw [← hsrc']
    exact ReidemeisterEquiv.trans
      (ReidemeisterEquiv.step (verifyMove_sound hmove)) (ih hrest)

/-- **The organ theorem**: a `List ReidemeisterMove` certificate that
    passes the verifier compiles to a proof of Reidemeister equivalence.
    The combinatorial half (⇐) of `reidemeister_theorem` restated:
    without PL manifolds or ambient isotopy, a Bool-certified path
    suffices to establish `KnotEquiv`. -/
theorem movesConnects_sound {ms : List ReidemeisterMove} {d₁ d₂ : KnotDiagram}
    (h : movesConnects ms d₁ d₂) : ReidemeisterEquiv d₁ d₂ :=
  verifyMoves_sound h

/-! ## 6. Witness theorems on arc partitions (point 1 of #18611)

Mirror of the `reidemeister3Connected_*` for R1 then R2, proved by
`decide` on the satisfiable witnesses of the lake. Why witnesses rather
than general theorems: renaming an `e2`/`e4` slot destroys an old
Wirtinger link (the arc class refines), so the equality of relation
(`SameRelOn`) holds only when the renaming bears on `e1`/`e3` — which is
the case of the R1 witness; the R2 witness illustrates the general
refinement (`RefinesOn`), which is the correct form of the effect of
subdivision moves on arc partitions.
-/

/-- R1 witness: on the `reidemeister1Connected_satisfiable` pair, the
    arc class relation is preserved on the common labels (the renaming
    of the witness bears on `e1`, which does not count in the
    `arcPartition` collapse). -/
theorem reidemeister1Connected_arcPartition_sameRelOn_witness :
    SameRelOn 4
      (arcPartition { crossings := [⟨1,2,3,4⟩, ⟨1,2,3,4⟩], numEdges := 4 })
      (arcPartition { crossings := [⟨1,2,3,4⟩, ⟨5,2,3,4⟩, ⟨1,5,6,6⟩],
                      numEdges := 6 }) := by
  intro x y hx hy
  have hall : ((List.range 5).all fun x =>
    (List.range 5).all fun y =>
      decide (SameClass (arcPartition
          { crossings := [⟨1,2,3,4⟩, ⟨1,2,3,4⟩], numEdges := 4 }) x y ↔
        SameClass (arcPartition
          { crossings := [⟨1,2,3,4⟩, ⟨5,2,3,4⟩, ⟨1,5,6,6⟩], numEdges := 6 }) x y)) = true := by
    decide
  have hx5 := List.all_eq_true.mp hall x (List.mem_range.mpr (by omega))
  exact of_decide_eq_true (List.all_eq_true.mp hx5 y (List.mem_range.mpr (by omega)))

/-- R2 witness: the arc partition of the enlarged diagram **refines**
    that of the source diagram on the common labels — the renaming of
    the `e2` slot (pair `(1,3)` become `(8,3)`) detaches arc `1` from
    the class `{1,3,4}`; no old class is merged. This is the correct
    general form of the R1/R2 effect on arc partitions. -/
theorem reidemeister2Connected_arcPartition_refinesOn_witness :
    RefinesOn 4
      (arcPartition { crossings := [⟨6,8,2,3⟩, ⟨2,3,4,4⟩, ⟨1,5,5,6⟩, ⟨1,7,7,8⟩],
                      numEdges := 8 })
      (arcPartition { crossings := [⟨1,1,2,3⟩, ⟨2,3,4,4⟩], numEdges := 4 }) := by
  intro x y hx hy hxy
  have hall : ((List.range 5).all fun x =>
    (List.range 5).all fun y =>
      decide (¬ SameClass (arcPartition
          { crossings := [⟨6,8,2,3⟩, ⟨2,3,4,4⟩, ⟨1,5,5,6⟩, ⟨1,7,7,8⟩],
            numEdges := 8 }) x y ∨
        SameClass (arcPartition
          { crossings := [⟨1,1,2,3⟩, ⟨2,3,4,4⟩], numEdges := 4 }) x y)) = true := by
    decide
  have hx5 := List.all_eq_true.mp hall x (List.mem_range.mpr (by omega))
  rcases of_decide_eq_true (List.all_eq_true.mp hx5 y (List.mem_range.mpr (by omega))) with h' | h'
  · exact absurd hxy h'
  · exact h'

/-- R3 witness: bounded instance of the general theorem
    `Reidemeister3Connected.arcPartition_sameRel` (the triangular move
    preserves `numEdges`, so bare `SameRel` restricts trivially). -/
theorem reidemeister3Connected_arcPartition_sameRelOn_witness :
    SameRelOn 10
      (arcPartition { crossings := [⟨1,2,7,8⟩, ⟨3,7,9,4⟩, ⟨9,8,5,6⟩,
                       ⟨1,2,10,10⟩, ⟨3,4,5,6⟩], numEdges := 10 })
      (arcPartition { crossings := [⟨3,4,9,7⟩, ⟨9,2,5,8⟩, ⟨7,8,1,6⟩,
                       ⟨1,2,10,10⟩, ⟨3,4,5,6⟩], numEdges := 10 }) :=
  (reidemeister3Connected_satisfiable.arcPartition_sameRel).sameRelOn 10

/-- End-to-end demonstration of the organ on the R3 witness: the unary
    certificate `[r3 X Y]` passes the verifier (kernel `decide`: reading
    of the three crossings, `Nodup`, triple `List.set` on literals), and
    `movesConnects_sound` compiles it into `ReidemeisterEquiv X Y`. -/
theorem reidemeister3Connected_witness_movesConnects :
    movesConnects
      [ReidemeisterMove.r3
        { crossings := [⟨1,2,7,8⟩, ⟨3,7,9,4⟩, ⟨9,8,5,6⟩,
                         ⟨1,2,10,10⟩, ⟨3,4,5,6⟩], numEdges := 10 }
        { crossings := [⟨3,4,9,7⟩, ⟨9,2,5,8⟩, ⟨7,8,1,6⟩,
                         ⟨1,2,10,10⟩, ⟨3,4,5,6⟩], numEdges := 10 }]
      { crossings := [⟨1,2,7,8⟩, ⟨3,7,9,4⟩, ⟨9,8,5,6⟩,
                       ⟨1,2,10,10⟩, ⟨3,4,5,6⟩], numEdges := 10 }
      { crossings := [⟨3,4,9,7⟩, ⟨9,2,5,8⟩, ⟨7,8,1,6⟩,
                       ⟨1,2,10,10⟩, ⟨3,4,5,6⟩], numEdges := 10 } := by
  unfold movesConnects
  decide

/-! ## 7. Completeness (⇐) — the canonical witness decides

The header documents completeness (`Reidemeister1Connected d d' →
verifyR1Fwd d d' = true`) as future work, backed by a plausibility
argument: the verifier extracts witnesses exactly in the shape of the
surgery of the definitions. The two bounded examples below **measure**
that alignment on the decisive case raised by the 03/10 forensic
(#18611): the NON-final kink. Measured verdict: both languages speak the
same surgery — per-move completeness is a **lemma to prove** (induction
on the existential of the definition), not a statement to weaken. -/

/-- Completeness direction held on the canonical witness: the pair (d₁, d₂)
    whose `reidemeister1Connected_satisfiable` (Reidemeister.lean) proves it
    satisfies the Prop passes the Bool verifier. On the Prop side the kink
    is appended by `++ [C]` (hence always last in the list), on the Bool
    side it is read by `getLast?` — same shape, kernel `decide` returns
    true. -/
example : verifyR1Fwd
    { crossings := [⟨1,2,3,4⟩, ⟨1,2,3,4⟩], numEdges := 4 }
    { crossings := [⟨1,2,3,4⟩, ⟨5,2,3,4⟩, ⟨1,5,6,6⟩], numEdges := 6 }
    = true := by decide

/-- The NON-final kink is not a completeness gap: the Prop rules it out
    from the start (the surgery is `set i Y' ++ [C]`, the kink is ALWAYS
    appended last) and the verifier refuses it just the same. Here the
    crossings are exactly those of the witness above, only the order
    differs: the kink `⟨1,5,6,6⟩` sits at index 1, before the rewritten
    crossing `⟨5,2,3,4⟩`. `verifyR1` (both orientations) returns false:
    a "middle" kink is expressible in NEITHER language — the crossing
    order is invariant under the three moves (R1/R2 append and remove at
    the end, R3 rewrites in place), so no chain connects the pair.
    Prop/Bool consistency, not an organ defect. -/
example : verifyR1
    { crossings := [⟨1,2,3,4⟩, ⟨1,2,3,4⟩], numEdges := 4 }
    { crossings := [⟨1,2,3,4⟩, ⟨1,5,6,6⟩, ⟨5,2,3,4⟩], numEdges := 6 }
    = false := by decide

end Knots_en
