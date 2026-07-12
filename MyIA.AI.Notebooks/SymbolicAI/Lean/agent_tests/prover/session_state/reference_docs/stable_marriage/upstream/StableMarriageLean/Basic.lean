import Mathlib.Data.Fintype.Basic

namespace StableMarriageLean

-- Base preferences over partners on an acceptable list.
structure Preferences (Agent Partner : Type*) where
  acceptable : Agent → Partner → Prop
  prefers : Agent → Partner → Partner → Prop
  prefers_irrefl : ∀ a o, ¬ prefers a o o
  prefers_trans : ∀ a o1 o2 o3, prefers a o1 o2 → prefers a o2 o3 → prefers a o1 o3
  prefers_total : ∀ a o1 o2, acceptable a o1 → acceptable a o2 → o1 ≠ o2 →
    prefers a o1 o2 ∨ prefers a o2 o1
  prefers_acceptable_left : ∀ a o1 o2, prefers a o1 o2 → acceptable a o1
  prefers_acceptable_right : ∀ a o1 o2, prefers a o1 o2 → acceptable a o2

-- A stable marriage instance with finite sets of men and women and their preferences.
structure Problem where
  Men : Type*
  Women : Type*
  [menFintype : Fintype Men]
  [womenFintype : Fintype Women]
  menPrefs : Preferences Men Women
  womenPrefs : Preferences Women Men

-- A matching as two partial maps
structure Matching (P : Problem) where
  menMatches : P.Men → Option P.Women
  womenMatches : P.Women → Option P.Men

-- Men/Women maps agree on who is matched to whom.
def consistent (P : Problem) (μ : Matching P) : Prop :=
  ∀ m w, μ.menMatches m = some w ↔ μ.womenMatches w = some m

noncomputable section
open Classical

-- Extend preferences to include the unmatched option (none).
def prefersOpt (p : Preferences Agent Partner) (a : Agent) :
    Option Partner → Option Partner → Prop
  | some o1, some o2 =>
      if p.acceptable a o1 then
        if p.acceptable a o2 then p.prefers a o1 o2 else True
      else
        False
  | some o, none => p.acceptable a o
  | none, some o => ¬ p.acceptable a o
  | none, none => False

-- Mutual acceptability of a pair of agents.
def Problem.acceptablePair (P : Problem) (m : P.Men) (w : P.Women) : Prop :=
  P.menPrefs.acceptable m w ∧ P.womenPrefs.acceptable w m

-- No agent is matched to an unacceptable partner.
def individuallyRational (P : Problem) (μ : Matching P) : Prop :=
  (∀ m w, μ.menMatches m = some w → P.menPrefs.acceptable m w) ∧
    (∀ w m, μ.womenMatches w = some m → P.womenPrefs.acceptable w m)

-- A pair (m, w) that both prefer over their current matches.
def blockingPair (P : Problem) (μ : Matching P) (m : P.Men) (w : P.Women) : Prop :=
  P.acceptablePair m w ∧
    prefersOpt P.menPrefs m (some w) (μ.menMatches m) ∧
    prefersOpt P.womenPrefs w (some m) (μ.womenMatches w)

-- A matching with no blocking pairs and no unacceptable matches.
def stable (P : Problem) (μ : Matching P) : Prop :=
  consistent P μ ∧
    individuallyRational P μ ∧
    (∀ m w, ¬ blockingPair P μ m w)

-- Being unmatched is better than being matched to an unacceptable partner.
theorem prefersOpt_none_over_unacceptable
    (p : Preferences Agent Partner) (a : Agent) (o : Partner) :
    ¬ p.acceptable a o → prefersOpt p a none (some o) := by
  intro hacc
  simp [prefersOpt, hacc]

-- Any acceptable partner is better than being unmatched.
theorem prefersOpt_acceptable_over_none
    (p : Preferences Agent Partner) (a : Agent) (o : Partner) :
    p.acceptable a o → prefersOpt p a (some o) none := by
  intro hacc
  simp [prefersOpt, hacc]

-- Any acceptable partner is better than any unacceptable one.
theorem prefersOpt_acceptable_over_unacceptable
    (p : Preferences Agent Partner) (a : Agent) (o1 o2 : Partner) :
    p.acceptable a o1 → ¬ p.acceptable a o2 → prefersOpt p a (some o1) (some o2) := by
  intro hacc1 hacc2
  simp [prefersOpt, hacc1, hacc2]

-- Within the acceptable list, use the original preference relation.
theorem prefersOpt_within_list
    (p : Preferences Agent Partner) (a : Agent) (o1 o2 : Partner) :
    p.acceptable a o1 → p.acceptable a o2 → p.prefers a o1 o2 →
      prefersOpt p a (some o1) (some o2) := by
  intro hacc1 hacc2 hpref
  simp [prefersOpt, hacc1, hacc2, hpref]

end

end StableMarriageLean
