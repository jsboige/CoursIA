/-
  Knots.ConwayKTMutation_en — English mirror of Knots.ConwayKTMutation
  ===================================================================

  English sibling (Pattern A, EPIC #4980): identical statements, proofs and
  tactics byte-for-byte; only module docstrings and comments differ. The
  French file `Knots/ConwayKTMutation.lean` is the canonical source.

  Slice 1 of the "Conway and Kinoshita-Terasaka construction via mutation"
  item of EPIC #2874. The full programme — proving
  `AreMutants conwayKnot kinoshitaTerasakaKnot` — requires an intermediate
  diagram (see the NOTE in `Knots.Mutation`, §Controls); this module
  consolidates the measurable foundation of that programme:

  1. The three combinatorial mutants of the Conway knot on the window 5-11
     (crossings 6 to 11, the part of the PD code where 11n34 and 11n42
     diverge), with `wf` proved and `AreMutantDiagrams` by construction.
  2. Window-normalisation lemmas (`mutateWindow_empty_window`,
     `mutateWindow_take`, `mutateWindow_ge_length_right`), reusable for any
     future negative proof `¬ AreWindowMutantDiagrams`.
  3. The one-shot impossibility theorem
     `not_areWindowMutantDiagrams_conway_kt`: NO window and NO Klein rotation
     sends the designated PD code of Conway onto that of Kinoshita-Terasaka,
     in the bare-window sense (`AreWindowMutantDiagrams`) — the informal NOTE
     of `Knots.Mutation` becomes a kernel-checked exhaustive enumeration
     proof. The version with boundary relabeling σ (`AreMutantDiagrams`,
     the sigma amendment of `Knots.Mutation`) remains open: kernel
     enumeration does not cover involutions `Nat → Nat`; that is a later
     sub-grain of the programme.

  Assumed limitation of the model (inherited from `Knots.Mutation`): the
  "window" is combinatorial (a range of indices in the crossing list), not a
  geometric Conway sphere — the geometric definition remains a TODO of the
  lake (`ConwaySphere`). The mutants below are mutants of the combinatorial
  model, to be examined as such.
-/

import Knots.Basic_en
import Knots.Mutation_en
import Knots.ConwayPD_en

namespace Knots_en

/-! ## 1. Window normalisation

Three structural facts about `mutateWindow`, used by the one-shot
impossibility theorem of §3. They bound the space of useful windows: an
empty window (`j ≤ i`) is the identity, positions before `i` are unchanged,
and a right bound past the list clamps to its length. -/

/-- Empty window (`j ≤ i`): the mutation is the identity. -/
theorem mutateWindow_empty_window (cs : List PDCrossing) (i j : Nat)
    (ρ : KleinRot) (hij : j ≤ i) : mutateWindow cs i j ρ = cs := by
  induction cs generalizing i j with
  | nil => rfl
  | cons c cs' ih =>
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j' => omega
    | succ i' =>
      cases j with
      | zero => rfl
      | succ j' => simp [mutateWindow, ih i' j' (by omega)]

/-- Positions strictly before the window are unchanged (for a non-empty
window `i ≤ j`). -/
theorem mutateWindow_take (cs : List PDCrossing) (i j : Nat) (ρ : KleinRot)
    (hij : i ≤ j) : (mutateWindow cs i j ρ).take i = cs.take i := by
  induction cs generalizing i j with
  | nil => rfl
  | cons c cs' ih =>
    cases i with
    | zero => rfl
    | succ i' =>
      cases j with
      | zero => rfl
      | succ j' => simp [mutateWindow, ih i' j' (by omega)]

/-- Right bound past the list: mutating with `j ≥ length cs` amounts to
mutating up to the end of the list. -/
theorem mutateWindow_ge_length_right (cs : List PDCrossing) (i j : Nat)
    (ρ : KleinRot) (hj : cs.length ≤ j) :
    mutateWindow cs i j ρ = mutateWindow cs i cs.length ρ := by
  induction cs generalizing i j with
  | nil => rfl
  | cons c cs' ih =>
    simp only [List.length_cons] at hj ⊢
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j' => simp [mutateWindow, ih 0 j' (by omega)]
    | succ i' =>
      cases j with
      | zero => omega
      | succ j' => simp [mutateWindow, ih i' j' (by omega)]

/-! ## 2. The combinatorial mutants of the Conway knot

Crossings 6 to 11 (indices 5 to 10) are the part of the PD code where 11n34
and 11n42 diverge — the first five crossings are common. The window 5-11 is
therefore the natural mutation window of the model. The three non-trivial
Klein group rotations yield the three combinatorial mutants. -/

/-- The Conway mutant by `r12` on the window 5-11 (crossings 6 to 11). -/
def conwayMutantR12Diagram : KnotDiagram where
  crossings := mutateWindow conwayKnotDiagram.crossings 5 11 KleinRot.r12
  numEdges := 22

/-- The Conway mutant by `r13` on the window 5-11. -/
def conwayMutantR13Diagram : KnotDiagram where
  crossings := mutateWindow conwayKnotDiagram.crossings 5 11 KleinRot.r13
  numEdges := 22

/-- The Conway mutant by `r14` on the window 5-11. -/
def conwayMutantR14Diagram : KnotDiagram where
  crossings := mutateWindow conwayKnotDiagram.crossings 5 11 KleinRot.r14
  numEdges := 22

/-- `wf` of the r12 mutant: `KleinRot.apply` permutes labels inside each
crossing, the global multiset of the 22 edges is unchanged — the `wf` parity
passes (kernel check, in the style of `conway_wf`). -/
theorem conwayMutantR12_wf : conwayMutantR12Diagram.wf = true := by decide

/-- `wf` of the r13 mutant. -/
theorem conwayMutantR13_wf : conwayMutantR13Diagram.wf = true := by decide

/-- `wf` of the r14 mutant. -/
theorem conwayMutantR14_wf : conwayMutantR14Diagram.wf = true := by decide

/-- Each mutant is a mutant of Conway by construction (window 5-11,
designated rotation, trivial relabeling `σ = id`) — the witness is the very
definition: `reattachWindow_id` reduces `sphereMutate` to `mutateWindow`. -/
theorem areMutantDiagrams_conway_conwayMutantR12 :
    AreMutantDiagrams conwayKnotDiagram conwayMutantR12Diagram :=
  ⟨5, 11, .r12, id, fun _ => rfl, by
    simp only [sphereMutate, reattachWindow_id]
    rfl⟩

theorem areMutantDiagrams_conway_conwayMutantR13 :
    AreMutantDiagrams conwayKnotDiagram conwayMutantR13Diagram :=
  ⟨5, 11, .r13, id, fun _ => rfl, by
    simp only [sphereMutate, reattachWindow_id]
    rfl⟩

theorem areMutantDiagrams_conway_conwayMutantR14 :
    AreMutantDiagrams conwayKnotDiagram conwayMutantR14Diagram :=
  ⟨5, 11, .r14, id, fun _ => rfl, by
    simp only [sphereMutate, reattachWindow_id]
    rfl⟩

/-- The three mutants as knots (designated diagram = the mutant). -/
def conwayMutantR12 : Knot where diagram := conwayMutantR12Diagram
def conwayMutantR13 : Knot where diagram := conwayMutantR13Diagram
def conwayMutantR14 : Knot where diagram := conwayMutantR14Diagram

/-- Mutation relation at the knot level, designated witnesses. -/
theorem areMutants_conway_conwayMutantR12 :
    AreMutants conwayKnot conwayMutantR12 :=
  ⟨conwayKnotDiagram, conwayMutantR12Diagram, ReidemeisterEquiv.refl _,
    ReidemeisterEquiv.refl _, areMutantDiagrams_conway_conwayMutantR12⟩

theorem areMutants_conway_conwayMutantR13 :
    AreMutants conwayKnot conwayMutantR13 :=
  ⟨conwayKnotDiagram, conwayMutantR13Diagram, ReidemeisterEquiv.refl _,
    ReidemeisterEquiv.refl _, areMutantDiagrams_conway_conwayMutantR13⟩

theorem areMutants_conway_conwayMutantR14 :
    AreMutants conwayKnot conwayMutantR14 :=
  ⟨conwayKnotDiagram, conwayMutantR14Diagram, ReidemeisterEquiv.refl _,
    ReidemeisterEquiv.refl _, areMutantDiagrams_conway_conwayMutantR14⟩

/-! ## 3. One-shot impossibility: the designated codes are not mutants

The NOTE in `Knots.Mutation` (§Controls) observes that no one-shot map
superposes the designated PD codes of 11n34 and 11n42. The theorem below
proves it: for EVERY window and EVERY Klein rotation,
`mutateWindow conwayKnotDiagram.crossings i j ρ ≠ kinoshitaTerasakaDiagram.crossings`.

The proof bounds the space with the lemmas of §1 (empty window = identity;
positions before `i` unchanged; right bound clamped), then enumerates the
remaining cases — each branch is closed by the kernel (`decide` on literal
lists). The bound `i ≤ 5` comes from crossing 6: the codes diverge at index
5 already (`⟨16, 9, 15, 8⟩` against `⟨17, 9, 18, 8⟩`), so any window
starting later leaves the first six positions unchanged.

Scope: the impossibility targets the bare window
(`AreWindowMutantDiagrams`); the version with boundary relabeling σ
(`AreMutantDiagrams`) remains open — kernel enumeration does not cover
involutions `Nat → Nat`. Consequence for the programme, in the bare-window
sense: the junction `AreMutants conwayKnot kinoshitaTerasakaKnot`
necessarily goes through an intermediate diagram in the Reidemeister class
of either knot — that is the later sub-grain. -/

/-- The designated PD codes of Conway and Kinoshita-Terasaka differ (kernel
check). -/
theorem conway_designated_ne_kt :
    conwayKnotDiagram.crossings ≠ kinoshitaTerasakaDiagram.crossings := by
  decide

/-- They already differ on the first six crossings. -/
theorem conway_designated_take6_ne_kt :
    conwayKnotDiagram.crossings.take 6 ≠
      kinoshitaTerasakaDiagram.crossings.take 6 := by
  decide

/-- **One-shot impossibility** (bare window): no window and no Klein
rotation sends the designated PD code of the Conway knot onto that of
Kinoshita-Terasaka. The version with boundary relabeling σ
(`AreMutantDiagrams`) remains open. -/
theorem not_areWindowMutantDiagrams_conway_kt :
    ¬ AreWindowMutantDiagrams conwayKnotDiagram kinoshitaTerasakaDiagram := by
  rintro ⟨i, j, ρ, h⟩
  by_cases hij : j ≤ i
  · rw [mutateWindow_empty_window _ i j ρ hij] at h
    exact conway_designated_ne_kt h
  · by_cases hi6 : 6 ≤ i
    · have h6 := congrArg (List.take 6) h
      have htake := mutateWindow_take conwayKnotDiagram.crossings i j ρ
        (by omega)
      have hmin : min 6 i = 6 := Nat.min_eq_left (by omega)
      have hstep : (mutateWindow conwayKnotDiagram.crossings i j ρ).take 6
          = ((mutateWindow conwayKnotDiagram.crossings i j ρ).take i).take 6 := by
        rw [List.take_take, hmin]
      rw [hstep, htake, List.take_take, hmin] at h6
      exact conway_designated_take6_ne_kt h6
    · have hlen : conwayKnotDiagram.crossings.length = 11 := by decide
      have hi5 : i ≤ 5 := by omega
      by_cases hj11 : 11 ≤ j
      · rw [mutateWindow_ge_length_right _ i j ρ (by rw [hlen]; omega)] at h
        interval_cases i <;> cases ρ <;> exact absurd h (by decide)
      · have hj10 : j ≤ 10 := by omega
        interval_cases i <;> interval_cases j <;> cases ρ <;>
          exact absurd h (by decide)

end Knots_en
