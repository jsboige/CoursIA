/-
  Stable Marriage - Lattice Structure on Stable Matchings
  ========================================================

  Knuth (1976) showed that the set of stable matchings forms a lattice
  under the "common preferences" ordering. Wu & Roth (2018) generalized
  this to many-to-one; we specialize to the one-to-one case.

  Key results:
  - Stable matchings are partially ordered by man-preference
  - The join (supremum) of two stable matchings is stable
  - The meet (infimum) of two stable matchings is stable
  - The set of stable matchings forms a distributive lattice
  - The GS man-proposing output is the top (man-optimal) element

  Reference: Knuth (1976), "Marriages Stables"
  Reference: Wu & Roth (2018), "Lattice Structures in Stable Matching"
  Reference: Stanley (2011), "Enumerative Combinatorics" Vol 1 (finite lattice lemma)

  Strategy:
  - We define μ ≤ ν iff every man prefers μ to ν (or is indifferent)
  - join μ ν: each man gets his preferred partner between μ and ν
  - meet μ ν: each man gets his less-preferred partner between μ and ν
  - Wu-Roth Lemma 3.2 (one-to-one): join and meet of stable matchings are stable
  - Stanley lemma: finite join-semilattice with min = lattice
-/

import Mathlib.Order.Lattice
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Common
import StableMarriage.Definitions
import StableMarriage.Lemmas
import StableMarriage.Lattice

/-
  Stable Marriage - Lattice Structure on Stable Matchings (EN sibling)
  ====================================================================

  English mirror of `StableMarriage/Lattice.lean` (FR-first canonical).
  Convention i18n Lean ratifiée par ai-01 (2026-07-04, #4980 comment-4881909354) :
  fichiers `.lean` distincts FR + EN siblings dans le même lake, les deux compilent.
  Drift-CI detectable : contenu non-docstring byte-identique entre siblings.
  Namespace sibling : `StableMarriage_en` (le FR canonique reste `StableMarriage`).
  Pas une traduction destructive : le fichier source EN historique est préservé ici
  verbatim depuis `aaaf0c52ae` (post-merge #5321 GSState i18n) ; seule la ligne
  `namespace` diffère pour éviter la collision de declaration.

  See #4980. Part of #4208 (axe E).
-/

namespace StableMarriage_en

open Function Finset Classical
open StableMarriage

variable {n : Nat} [NeZero n] (prof : PrefProfile n)

/-! ## Partial Order on Stable Matchings via Man-Preference -/

/--
Man-preference ordering on matchings: μ ≤ ν iff every man prefers
his partner in μ at least as much as in ν (i.e., menPref m (μ m) ≤ menPref m (ν m)).
Lower rank = more preferred, so μ ≤ ν means μ is man-preferred over ν.
-/
def ManLE (μ ν : Matching n) : Prop :=
  ∀ m : Fin n, prof.menPref m (μ.spouse m) ≤ prof.menPref m (ν.spouse m)

namespace ManLE

variable {prof} {μ ν σ : Matching n}

@[refl] lemma refl : ManLE prof μ μ := fun m => Nat.le_refl _

@[trans] lemma trans (h1 : ManLE prof μ ν) (h2 : ManLE prof ν σ) :
    ManLE prof μ σ := fun m => Nat.le_trans (h1 m) (h2 m)

lemma antisymm (h1 : ManLE prof μ ν) (h2 : ManLE prof ν μ) :
    μ = ν := by
  have hsp : μ.spouse = ν.spouse := by
    funext m
    have hle : (prof.menPref m (μ.spouse m) : Nat) ≤ prof.menPref m (ν.spouse m) := h1 m
    have hge : (prof.menPref m (ν.spouse m) : Nat) ≤ prof.menPref m (μ.spouse m) := h2 m
    have heq : (prof.menPref m (μ.spouse m) : Nat) = prof.menPref m (ν.spouse m) :=
      Nat.le_antisymm hle hge
    have hfeq : prof.menPref m (μ.spouse m) = prof.menPref m (ν.spouse m) := Fin.ext heq
    exact (prof.menPref_bijective m).injective hfeq
  have hsp_eq : μ.spouse = ν.spouse := hsp
  cases μ; cases ν
  congr 1

end ManLE

/-! ## Inverse Helpers (needed for join/meet bijectivity) -/

/--
Key fact: μ.inverse w is the unique m such that μ.spouse m = w.
-/
lemma inverse_eq_of_spouse_eq (μ : Matching n) (m w : Fin n)
    (h : μ.spouse m = w) : μ.inverse w = m := by
  unfold Matching.inverse
  have := Equiv.ofBijective_symm_apply_apply μ.spouse μ.bijective m
  rw [h] at this
  exact this

/--
Key fact: μ.spouse (μ.inverse w) = w.
-/
lemma spouse_inverse (μ : Matching n) (w : Fin n) :
    μ.spouse (μ.inverse w) = w := by
  unfold Matching.inverse
  exact Equiv.ofBijective_apply_symm_apply μ.spouse μ.bijective w

/-! ## Anti-crossing Lemma (Knuth decomposition) -/

/--
A sound anti-crossing fragment: if the shared woman `w` is chosen by both men
against their partners in the other stable matching, then the two men coincide.
This is the cross-case needed for injectivity of `joinSpouse`.
-/
lemma no_cross_if_both_choose_cross (μ ν : Matching n)
    (hμ : IsStable prof μ) (hν : IsStable prof ν)
    {m₁ m₂ w : Fin n}
    (h1 : μ.spouse m₁ = w) (h2 : ν.spouse m₂ = w)
    (hm₁ : prof.ManPrefers m₁ w (ν.spouse m₁))
    (hm₂ : prof.ManPrefers m₂ w (μ.spouse m₂)) :
    m₁ = m₂ := by
  by_contra hne
  have hμinv_w : μ.inverse w = m₁ := inverse_eq_of_spouse_eq μ m₁ _ h1
  have hνinv_w : ν.inverse w = m₂ := inverse_eq_of_spouse_eq ν m₂ _ h2
  have hnot₁ : ¬prof.WomanPrefers w m₁ m₂ := by
    intro hw
    have hbp : IsBlockingPair prof ν m₁ w := by
      unfold IsBlockingPair
      rw [hνinv_w]
      exact ⟨hm₁, hw⟩
    exact hν m₁ w hbp
  have hnot₂ : ¬prof.WomanPrefers w m₂ m₁ := by
    intro hw
    have hbp : IsBlockingPair prof μ m₂ w := by
      unfold IsBlockingPair
      rw [hμinv_w]
      exact ⟨hm₂, hw⟩
    exact hμ m₂ w hbp
  unfold PrefProfile.WomanPrefers at hnot₁ hnot₂
  simp only [not_lt] at hnot₁ hnot₂
  have heq : (prof.womenPref w m₁ : Nat) = prof.womenPref w m₂ :=
    Nat.le_antisymm (mod_cast hnot₂) (mod_cast hnot₁)
  exact hne ((prof.womenPref_bijective w).injective (Fin.ext heq))

/-! ## Refutation of the anti-crossing conjecture (`no_cross_match`)

Earlier versions of this file stated the following "anti-crossing lemma",
attributed to Knuth's decomposition argument, and left its Cases A2/B as
`sorry` after many unsuccessful proof attempts:

  `no_cross_match : IsStable prof μ → IsStable prof ν →`
  `    μ.spouse m₁ = w → ν.spouse m₂ = w → μ.spouse m₂ = ν.spouse m₁`

This statement is FALSE.  It would force the symmetric difference of any two
stable matchings to decompose into 2-cycles (swaps), but rotations of length
≥ 3 between stable matchings exist.  The kernel-checked counterexample below
(`NoCrossCounterexample.no_cross_match_is_false`) uses the classic 3×3
latin-square instance (Knuth 1976): the identity matching and its cyclic
shift are both stable, yet the claimed cross-partner equality fails.  This
explains why all proof attempts on the `sorry` branches stalled: the goals
were unprovable.

Knuth's lattice theorem does not need any anti-crossing statement: the
weaker facts proved in this file (`no_cross_if_both_choose_cross`,
`joinSpouse_injective`, and the counting argument in `meetSpouse_eq_of_eq`)
suffice to show that join and meet of two stable matchings are matchings.

The statements `man_optimality_key_step` and `doctor_optimal_eq_top` that
previously closed this file were false for the same reason (they implied
that all stable matchings are pairwise ManLE-comparable in both directions,
hence equal); they are refuted at the end of this file and replaced by the
honest theorem `exists_isManOptimal`.
-/

/--
Stability from a fully computable check: it suffices to verify, for every
man `m`, woman `w` and candidate husband `m'` with `μ.spouse m' = w`, that
`(m, w)` is not a blocking pair.  This formulation avoids the noncomputable
`Matching.inverse`, so on concrete instances the hypothesis can be
discharged by `decide`.
-/
lemma isStable_of_check (μ : Matching n)
    (h : ∀ m w m' : Fin n, μ.spouse m' = w →
      ¬(prof.menPref m w < prof.menPref m (μ.spouse m) ∧
        prof.womenPref w m < prof.womenPref w m')) :
    IsStable prof μ := by
  intro m w hbp
  obtain ⟨h1, h2⟩ := hbp
  exact h m w (μ.inverse w) (spouse_inverse μ w) ⟨h1, h2⟩

namespace NoCrossCounterexample

/-- Men's rankings of the 3×3 latin-square instance (Knuth 1976).
`menPref3 m w` is the rank man `m` assigns to woman `w` (lower = preferred):
m₁ : w₁ > w₂ > w₃, m₂ : w₂ > w₃ > w₁, m₃ : w₃ > w₁ > w₂. -/
def menPref3 : Fin 3 → Fin 3 → Fin 3 := ![![0, 1, 2], ![2, 0, 1], ![1, 2, 0]]

/-- Women's rankings, cyclically shifted against the men's:
w₁ : m₂ > m₃ > m₁, w₂ : m₃ > m₁ > m₂, w₃ : m₁ > m₂ > m₃. -/
def womenPref3 : Fin 3 → Fin 3 → Fin 3 := ![![2, 0, 1], ![1, 2, 0], ![0, 1, 2]]

/-- The 3×3 latin-square preference profile. -/
def prof3 : PrefProfile 3 where
  menPref := menPref3
  womenPref := womenPref3
  menPref_bijective := by decide
  womenPref_bijective := by decide

/-- The identity matching mᵢ ↦ wᵢ. -/
def M0 : Matching 3 where
  spouse := id
  bijective := Function.bijective_id

/-- The cyclic-shift matching mᵢ ↦ wᵢ₊₁. -/
def M1 : Matching 3 where
  spouse := ![1, 2, 0]
  bijective := by decide

lemma M0_stable : IsStable prof3 M0 :=
  isStable_of_check prof3 M0 (by decide)

lemma M1_stable : IsStable prof3 M1 :=
  isStable_of_check prof3 M1 (by decide)

/--
**Refutation** of the former `no_cross_match` lemma (its full universally
quantified statement).  Instantiation: μ = M0 (identity), ν = M1 (shift),
w = w₁, m₁ = m₁ (married to w₁ in M0), m₂ = m₃ (married to w₁ in M1).
The conclusion would force `M0.spouse m₃ = M1.spouse m₁`, i.e. w₃ = w₂.
-/
theorem no_cross_match_is_false :
    ¬ ∀ (n : Nat) [NeZero n] (prof : PrefProfile n) (μ ν : Matching n),
        IsStable prof μ → IsStable prof ν →
        ∀ m₁ m₂ w : Fin n, μ.spouse m₁ = w → ν.spouse m₂ = w →
          μ.spouse m₂ = ν.spouse m₁ := by
  intro h
  have hcontra := h 3 prof3 M0 M1 M0_stable M1_stable 0 2 0 (by decide) (by decide)
  exact absurd hcontra (by decide)

end NoCrossCounterexample

/-! ## Join and Meet Operations -/

-- The join spouse function: each man gets his preferred partner between μ and ν.
-- Defined as a bare function so that bijectivity can be proved separately with
-- stability hypotheses. The join is NOT bijective for arbitrary matchings;
-- it requires both μ and ν to be stable (anti-complementarity).
-- (EN sibling: definition imported from FR canonical `StableMarriage.Lattice`
-- via `import StableMarriage.Lattice`. Redefining it here would shadow the
-- FR canonical and break `simp`/`unfold` resolution across namespaces.)

-- The meet spouse function: each man gets his less-preferred partner between μ and ν.
-- (EN sibling: imported from FR canonical, see joinSpouse note above.)

/--
Injectivity of join: if joinSpouse μ ν m₁ = joinSpouse μ ν m₂, then m₁ = m₂.
Key insight: the cross-cases (one man picks μ-spouse, other picks ν-spouse,
both equal same woman w) lead to a blocking-pair contradiction via stability.
The easy cases (both men pick same matching) follow from that matching's injectivity.
-/
private lemma joinSpouse_injective (μ ν : Matching n)
    (hμ : IsStable prof μ) (hν : IsStable prof ν) :
    Injective (fun m => μ.joinSpouse prof ν m) := by
  intro m₁ m₂ heq
  by_cases c₁ : prof.menPref m₁ (μ.spouse m₁) ≤ prof.menPref m₁ (ν.spouse m₁)
  · simp only [Matching.joinSpouse, c₁, if_true] at heq
    by_cases c₂ : prof.menPref m₂ (μ.spouse m₂) ≤ prof.menPref m₂ (ν.spouse m₂)
    · simp only [Matching.joinSpouse, c₂, if_true] at heq
      exact μ.bijective.1 heq
    · simp only [Matching.joinSpouse, c₂, if_false] at heq
      -- Cross-case: μ.spouse m₁ = ν.spouse m₂ = w, m₁ picks μ, m₂ picks ν
      have hm₂pref : prof.ManPrefers m₂ (ν.spouse m₂) (μ.spouse m₂) := by
        unfold PrefProfile.ManPrefers
        have : ¬(prof.menPref m₂ (μ.spouse m₂) ≤ prof.menPref m₂ (ν.spouse m₂)) := c₂
        have hle : (prof.menPref m₂ (μ.spouse m₂) : Nat) ≤ prof.menPref m₂ (ν.spouse m₂) → False := by
          intro hle; exact this (mod_cast hle)
        exact mod_cast Nat.lt_of_not_le hle
      by_contra hne
      -- ν stability applied to (m₁, ν.spouse m₂):
      -- need ManPrefers m₁ (ν.spouse m₂) (ν.spouse m₁)
      by_cases hm₁str : prof.ManPrefers m₁ (μ.spouse m₁) (ν.spouse m₁)
      · -- Case: m₁ strictly prefers μ.spouse m₁ to ν.spouse m₁
        -- ν stability: ¬IsBlockingPair ν m₁ (ν.spouse m₂)
        have hmp : prof.ManPrefers m₁ (ν.spouse m₂) (ν.spouse m₁) := by
          rw [← heq]; exact hm₁str
        have hm₂inv : ν.inverse (ν.spouse m₂) = m₂ := inverse_eq_of_spouse_eq ν m₂ _ rfl
        have hwp' : ¬prof.WomanPrefers (ν.spouse m₂) m₁ m₂ := by
          intro hw'
          exact hν m₁ (ν.spouse m₂) ⟨hmp, by rwa [hm₂inv]⟩
        -- μ stability: ¬IsBlockingPair μ m₂ (ν.spouse m₂)
        have hm₁inv : μ.inverse (μ.spouse m₁) = m₁ := inverse_eq_of_spouse_eq μ m₁ _ rfl
        have hwp₂ : ¬prof.WomanPrefers (ν.spouse m₂) m₂ m₁ := by
          intro hw'
          have hw'' : prof.WomanPrefers (ν.spouse m₂) m₂ (μ.inverse (ν.spouse m₂)) := by
            have h1 : μ.inverse (ν.spouse m₂) = m₁ := by
              rw [← heq]; exact hm₁inv
            rw [h1]; exact hw'
          exact hμ m₂ (ν.spouse m₂) ⟨hm₂pref, hw''⟩
        -- Both ¬WomanPrefers gives womenPref equality, contradicting injectivity
        unfold PrefProfile.WomanPrefers at hwp' hwp₂
        simp only [not_lt] at hwp' hwp₂
        have heq' : (prof.womenPref (ν.spouse m₂) m₂ : Nat) = prof.womenPref (ν.spouse m₂) m₁ :=
          Nat.le_antisymm (mod_cast hwp') (mod_cast hwp₂)
        exact hne ((prof.womenPref_bijective (ν.spouse m₂)).injective (Fin.ext heq'.symm))
      · -- Case: m₁ does NOT strictly prefer μ.spouse m₁ to ν.spouse m₁
        -- c₁ + ¬hm₁str gives menPref m₁ (μ.spouse m₁) = menPref m₁ (ν.spouse m₁)
        -- By injectivity: μ.spouse m₁ = ν.spouse m₁
        -- But ν.spouse is injective and ν.spouse m₁ ≠ ν.spouse m₂ = μ.spouse m₁
        unfold PrefProfile.ManPrefers at hm₁str
        simp only [not_lt] at hm₁str
        have heq' : (prof.menPref m₁ (μ.spouse m₁) : Nat) = prof.menPref m₁ (ν.spouse m₁) :=
          Nat.le_antisymm (mod_cast c₁) (mod_cast hm₁str)
        have hsp_eq : μ.spouse m₁ = ν.spouse m₁ :=
          (prof.menPref_bijective m₁).injective (Fin.ext heq')
        -- ν.spouse m₁ = μ.spouse m₁ = ν.spouse m₂ (by heq), contradicting injectivity
        rw [heq] at hsp_eq
        exact hne (ν.bijective.1 hsp_eq.symm)
  · simp only [Matching.joinSpouse, c₁, if_false] at heq
    by_cases c₂ : prof.menPref m₂ (μ.spouse m₂) ≤ prof.menPref m₂ (ν.spouse m₂)
    · simp only [Matching.joinSpouse, c₂, if_true] at heq
      -- Cross-case: ν.spouse m₁ = μ.spouse m₂, m₁ picks ν, m₂ picks μ
      -- heq : ν.spouse m₁ = μ.spouse m₂
      have hm₁pref : prof.ManPrefers m₁ (ν.spouse m₁) (μ.spouse m₁) := by
        unfold PrefProfile.ManPrefers
        have hle : (prof.menPref m₁ (μ.spouse m₁) : Nat) ≤ prof.menPref m₁ (ν.spouse m₁) → False := by
          intro hle; exact c₁ (mod_cast hle)
        exact mod_cast Nat.lt_of_not_le hle
      by_contra hne
      by_cases hm₂str : prof.ManPrefers m₂ (μ.spouse m₂) (ν.spouse m₂)
      · -- m₂ strictly prefers μ.spouse m₂ to ν.spouse m₂
        -- Key: w = ν.spouse m₁ = μ.spouse m₂ (by heq)
        -- ν stability on (m₂, w): ManPrefers m₂ w (ν.spouse m₂) holds (via heq + hm₂str)
        --   → ¬WomanPrefers w m₂ (ν⁻¹(w)) = ¬WomanPrefers w m₂ m₁
        have hm₁νinv : ν.inverse (ν.spouse m₁) = m₁ := inverse_eq_of_spouse_eq ν m₁ _ rfl
        have hwp₂ : ¬prof.WomanPrefers (ν.spouse m₁) m₂ m₁ := by
          intro hw'
          have hman : prof.ManPrefers m₂ (ν.spouse m₁) (ν.spouse m₂) := by rw [heq]; exact hm₂str
          exact hν m₂ (ν.spouse m₁) ⟨hman, by rw [hm₁νinv]; exact hw'⟩
        -- μ stability on (m₁, w): ManPrefers m₁ w (μ.spouse m₁) holds (via heq + hm₁pref)
        --   → ¬WomanPrefers w m₁ (μ⁻¹(w)) = ¬WomanPrefers w m₁ m₂
        have hm₂μinv : μ.inverse (μ.spouse m₂) = m₂ := inverse_eq_of_spouse_eq μ m₂ _ rfl
        have hwp₁ : ¬prof.WomanPrefers (ν.spouse m₁) m₁ m₂ := by
          intro hw'
          have hman : prof.ManPrefers m₁ (ν.spouse m₁) (μ.spouse m₁) := hm₁pref
          have hinv_eq : μ.inverse (ν.spouse m₁) = m₂ := by rw [heq, hm₂μinv]
          have hw'' : prof.WomanPrefers (ν.spouse m₁) m₁ (μ.inverse (ν.spouse m₁)) := by
            rw [hinv_eq]; exact hw'
          exact hμ m₁ (ν.spouse m₁) ⟨hman, hw''⟩
        -- Combine: both directions give womenPref equality → injectivity → m₁ = m₂
        unfold PrefProfile.WomanPrefers at hwp₁ hwp₂
        simp only [not_lt] at hwp₁ hwp₂
        have heq' : (prof.womenPref (ν.spouse m₁) m₂ : Nat) = prof.womenPref (ν.spouse m₁) m₁ :=
          Nat.le_antisymm (mod_cast hwp₁) (mod_cast hwp₂)
        exact hne ((prof.womenPref_bijective (ν.spouse m₁)).injective (Fin.ext heq'.symm))
      · -- m₂ does NOT strictly prefer μ.spouse m₂ to ν.spouse m₂
        -- c₂ + ¬hm₂str gives menPref equality → μ.spouse m₂ = ν.spouse m₂
        -- Combined with heq: ν.spouse m₁ = ν.spouse m₂ → m₁ = m₂
        unfold PrefProfile.ManPrefers at hm₂str
        simp only [not_lt] at hm₂str
        have heq' : (prof.menPref m₂ (μ.spouse m₂) : Nat) = prof.menPref m₂ (ν.spouse m₂) :=
          Nat.le_antisymm (mod_cast c₂) (mod_cast hm₂str)
        have hsp_eq : μ.spouse m₂ = ν.spouse m₂ :=
          (prof.menPref_bijective m₂).injective (Fin.ext heq')
        rw [← heq] at hsp_eq
        exact hne (ν.bijective.1 hsp_eq)
    · simp only [Matching.joinSpouse, c₂, if_false] at heq
      exact ν.bijective.1 heq

-- The join of two STABLE matchings: each man gets his preferred partner.
-- Bijectivity follows from anti-complementarity: on the woman side, the join
-- acts as the meet, so no two men map to the same woman.
-- (EN sibling: definition imported from FR canonical, see joinSpouse note.)

/--
Each man's join/meet pair is exactly his pair of partners in `{μ, ν}`:
either the join picks his μ-partner and the meet his ν-partner, or the
other way around.  Purely definitional if-split; no stability needed.
-/
private lemma joinSpouse_meetSpouse_cases (μ ν : Matching n) (m : Fin n) :
    (μ.joinSpouse prof ν m = μ.spouse m ∧ μ.meetSpouse prof ν m = ν.spouse m) ∨
    (μ.joinSpouse prof ν m = ν.spouse m ∧ μ.meetSpouse prof ν m = μ.spouse m) := by
  by_cases hc : prof.menPref m (μ.spouse m) ≤ prof.menPref m (ν.spouse m)
  · exact Or.inl ⟨by simp [Matching.joinSpouse, hc], by simp [Matching.meetSpouse, hc]⟩
  · exact Or.inr ⟨by simp [Matching.joinSpouse, hc], by simp [Matching.meetSpouse, hc]⟩

/--
Core of meet-injectivity, by counting — no anti-crossing lemma needed
(the anti-crossing statement is in fact false, see
`NoCrossCounterexample.no_cross_match_is_false`).

If two men m₁, m₂ both have meet-partner `w`, then each of them is
`μ.inverse w` or `ν.inverse w` (a man's meet-partner is one of his own
partners).  The join is surjective (`joinSpouse_injective` + finiteness),
so some m₀ has join-partner `w`, and m₀ also lies in
`{μ.inverse w, ν.inverse w}`.  In the mixed case (m₁, m₂ occupying the two
distinct slots), m₀ coincides with one of them; but a man whose join- AND
meet-partner are both `w` has both his μ- and ν-partner equal to `w`,
which collapses both inverses onto him — and then m₁ and m₂ both equal him.
-/
private lemma meetSpouse_eq_of_eq (μ ν : Matching n)
    (hμ : IsStable prof μ) (hν : IsStable prof ν) (w m₁ m₂ : Fin n)
    (h₁ : μ.meetSpouse prof ν m₁ = w) (h₂ : μ.meetSpouse prof ν m₂ = w) :
    m₁ = m₂ := by
  -- any man who meets to w is μ.inverse w or ν.inverse w
  have hmeet_mem : ∀ m : Fin n, μ.meetSpouse prof ν m = w →
      m = μ.inverse w ∨ m = ν.inverse w := by
    intro m hm
    rcases joinSpouse_meetSpouse_cases prof μ ν m with ⟨_, hmm⟩ | ⟨_, hmm⟩
    · exact Or.inr (inverse_eq_of_spouse_eq ν m w (hmm.symm.trans hm)).symm
    · exact Or.inl (inverse_eq_of_spouse_eq μ m w (hmm.symm.trans hm)).symm
  -- the join is surjective, so some m₀ has join-partner w
  have hbij : Function.Bijective (fun m => μ.joinSpouse prof ν m) :=
    Finite.injective_iff_bijective.mp (joinSpouse_injective prof μ ν hμ hν)
  obtain ⟨m₀, hm₀⟩ := hbij.2 w
  have hm₀' : μ.joinSpouse prof ν m₀ = w := hm₀
  have hm₀_mem : m₀ = μ.inverse w ∨ m₀ = ν.inverse w := by
    rcases joinSpouse_meetSpouse_cases prof μ ν m₀ with ⟨hjj, _⟩ | ⟨hjj, _⟩
    · exact Or.inl (inverse_eq_of_spouse_eq μ m₀ w (hjj.symm.trans hm₀')).symm
    · exact Or.inr (inverse_eq_of_spouse_eq ν m₀ w (hjj.symm.trans hm₀')).symm
  -- a man who both joins and meets to w pins down BOTH inverses
  have hboth : ∀ m : Fin n, μ.joinSpouse prof ν m = w → μ.meetSpouse prof ν m = w →
      μ.inverse w = m ∧ ν.inverse w = m := by
    intro m hj hm
    rcases joinSpouse_meetSpouse_cases prof μ ν m with ⟨hjj, hmm⟩ | ⟨hjj, hmm⟩
    · exact ⟨inverse_eq_of_spouse_eq μ m w (hjj.symm.trans hj),
             inverse_eq_of_spouse_eq ν m w (hmm.symm.trans hm)⟩
    · exact ⟨inverse_eq_of_spouse_eq μ m w (hmm.symm.trans hm),
             inverse_eq_of_spouse_eq ν m w (hjj.symm.trans hj)⟩
  -- mixed-slot case: the join witness collapses the two inverses
  have key : ∀ ma mb : Fin n, ma = μ.inverse w → mb = ν.inverse w →
      μ.meetSpouse prof ν ma = w → μ.meetSpouse prof ν mb = w → ma = mb := by
    intro ma mb ea eb hma hmb
    rcases hm₀_mem with e₀ | e₀
    · -- m₀ = μ.inverse w = ma, so ma joins AND meets to w
      have hja : μ.joinSpouse prof ν ma = w := by rw [ea, ← e₀]; exact hm₀'
      obtain ⟨_, hbν⟩ := hboth ma hja hma
      rw [eb, hbν]
    · -- m₀ = ν.inverse w = mb, so mb joins AND meets to w
      have hjb : μ.joinSpouse prof ν mb = w := by rw [eb, ← e₀]; exact hm₀'
      obtain ⟨hbμ, _⟩ := hboth mb hjb hmb
      rw [ea, hbμ]
  rcases hmeet_mem m₁ h₁ with e₁ | e₁ <;> rcases hmeet_mem m₂ h₂ with e₂ | e₂
  · exact e₁.trans e₂.symm
  · exact key m₁ m₂ e₁ e₂ h₁ h₂
  · exact (key m₂ m₁ e₂ e₁ h₂ h₁).symm
  · exact e₁.trans e₂.symm

/--
Injectivity of meet, via the counting argument in `meetSpouse_eq_of_eq`.
-/
private lemma meetSpouse_injective (μ ν : Matching n)
    (hμ : IsStable prof μ) (hν : IsStable prof ν) :
    Injective (fun m => μ.meetSpouse prof ν m) := by
  intro m₁ m₂ heq
  exact meetSpouse_eq_of_eq prof μ ν hμ hν (μ.meetSpouse prof ν m₂) m₁ m₂ heq rfl

-- The meet of two STABLE matchings: each man gets his less-preferred partner.
-- (EN sibling: imported from FR canonical, see joinSpouse note.)

/-! ## Stability of Join and Meet (Wu-Roth Lemma 3.2, one-to-one case) -/

open PrefProfile

/--
Helper: if m prefers w to his join-spouse, then m prefers w to both
his partner in μ and his partner in ν.
The join picks the lower-ranked (more preferred) of the two partners.
Uses joinSpouse (no stability needed).
-/
lemma join_pref_both (μ ν : Matching n) (m w : Fin n)
    (h : prof.ManPrefers m w (μ.joinSpouse prof ν m)) :
    prof.ManPrefers m w (μ.spouse m) ∧ prof.ManPrefers m w (ν.spouse m) := by
  unfold ManPrefers at h ⊢
  simp only [Matching.joinSpouse] at h
  split_ifs at h
  · -- menPref m (μ.spouse m) ≤ menPref m (ν.spouse m), h : menPref m w < menPref m (μ.spouse m)
    refine ⟨h, ?_⟩
    have : (prof.menPref m w : Nat) < prof.menPref m (μ.spouse m) := mod_cast h
    have : (prof.menPref m (μ.spouse m) : Nat) ≤ prof.menPref m (ν.spouse m) := mod_cast ‹_›
    exact mod_cast Nat.lt_of_lt_of_le ‹_› ‹_›
  · -- ¬(menPref m (μ.spouse m) ≤ menPref m (ν.spouse m)), h : menPref m w < menPref m (ν.spouse m)
    refine ⟨?_, h⟩
    have hνμ : (prof.menPref m (ν.spouse m) : Nat) < prof.menPref m (μ.spouse m) := by
      have : ¬ (prof.menPref m (μ.spouse m) ≤ prof.menPref m (ν.spouse m)) := ‹_›
      have : (prof.menPref m (μ.spouse m) : Nat) ≤ prof.menPref m (ν.spouse m) → False := by
        intro hle; exact this (mod_cast hle : prof.menPref m (μ.spouse m) ≤ prof.menPref m (ν.spouse m))
      omega
    have : (prof.menPref m w : Nat) < prof.menPref m (ν.spouse m) := mod_cast h
    exact mod_cast Nat.lt_trans ‹_› hνμ

/--
Helper: if m prefers w to his meet-spouse, then m prefers w to at least one
of his partners in μ or ν (the less-preferred one).
Uses meetSpouse (no stability needed).
-/
lemma meet_pref_one (μ ν : Matching n) (m w : Fin n)
    (h : prof.ManPrefers m w (μ.meetSpouse prof ν m)) :
    prof.ManPrefers m w (μ.spouse m) ∨ prof.ManPrefers m w (ν.spouse m) := by
  unfold ManPrefers at h ⊢
  simp only [Matching.meetSpouse] at h
  split_ifs at h
  · -- meet picked ν.spouse m: h : menPref m w < menPref m (ν.spouse m)
    right; exact h
  · -- meet picked μ.spouse m: h : menPref m w < menPref m (μ.spouse m)
    left; exact h

/--
Anti-complementarity of the join:
(μ ⊔ ν).inverse w equals either μ⁻¹(w) or ν⁻¹(w).

Proof: let m = (μ ⊔ ν).inverse w. The join gives m his preferred partner,
which equals w. So either μ.spouse m = w (making m = μ⁻¹(w))
or ν.spouse m = w (making m = ν⁻¹(w)).
-/
lemma join_inverse_anti (μ ν : Matching n) (hμ : IsStable prof μ) (hν : IsStable prof ν)
    (w : Fin n) :
    (μ.join prof hμ hν).inverse w = μ.inverse w ∨
    (μ.join prof hμ hν).inverse w = ν.inverse w := by
  have hspw : (μ.join prof hμ hν).spouse ((μ.join prof hμ hν).inverse w) = w :=
    spouse_inverse (μ.join prof hμ hν) w
  simp only [Matching.join, Matching.joinSpouse] at hspw
  split_ifs at hspw
  · left; exact (inverse_eq_of_spouse_eq μ _ w hspw).symm
  · right; exact (inverse_eq_of_spouse_eq ν _ w hspw).symm

/--
Anti-complementarity of the meet (woman side):
If meet.inverse w = μ⁻¹(w), then w prefers μ⁻¹(w) to ν⁻¹(w).
The meet on the man side acts as the join on the woman side: w gets her
more-preferred man. If meet picked μ⁻¹(w), then ν⁻¹(w) must be less preferred.
Requires stability of μ and ν.
-/
lemma meet_inverse_anti_pref (μ ν : Matching n)
    (hμ : IsStable prof μ) (hν : IsStable prof ν) (w : Fin n)
    (h : (μ.meet prof hμ hν).inverse w = μ.inverse w) :
    prof.womenPref w (μ.inverse w) ≤ prof.womenPref w (ν.inverse w) := by
  have hmsp : μ.spouse (μ.inverse w) = w := spouse_inverse μ w
  have hmMeet : (μ.meet prof hμ hν).spouse (μ.inverse w) = w := by
    rw [← h, spouse_inverse]
  simp only [Matching.meet, Matching.meetSpouse] at hmMeet
  by_cases hle : prof.menPref (μ.inverse w) (μ.spouse (μ.inverse w)) ≤
      prof.menPref (μ.inverse w) (ν.spouse (μ.inverse w))
  · -- meetSpouse = ν.spouse, so ν.spouse (μ⁻¹w) = w = μ.spouse (μ⁻¹w)
    simp only [hle, if_true] at hmMeet
    have hνinv : ν.inverse w = μ.inverse w :=
      inverse_eq_of_spouse_eq ν _ _ hmMeet
    rw [hνinv]
  · -- μ⁻¹w strictly prefers ν.spouse(μ⁻¹w) over μ.spouse(μ⁻¹w) = w
    push Not at hle
    -- Need: womenPref w (μ⁻¹w) ≤ womenPref w (ν⁻¹w)
    -- By contraposition: if womenPref w (ν⁻¹w) < womenPref w (μ⁻¹w),
    -- then w prefers ν⁻¹w over μ⁻¹w.
    -- Combined with man μ⁻¹w preferring ν.spouse(μ⁻¹w) over w,
    -- if ν.spouse(μ⁻¹w) = w then ν⁻¹(w) = μ⁻¹w, contradicted by injectivity of menPref.
    by_cases hw : ν.spouse (μ.inverse w) = w
    · -- ν also matches μ⁻¹w to w, so ν⁻¹w = μ⁻¹w
      have hνinv_eq : ν.inverse w = μ.inverse w :=
        inverse_eq_of_spouse_eq ν _ _ hw
      rw [hνinv_eq]
    · -- ν.spouse(μ⁻¹w) ≠ w
      set m' := ν.inverse w with hm'def
      have hνm' : ν.spouse m' = w := spouse_inverse ν w
      by_cases hle' : prof.menPref m' (μ.spouse m') ≤ prof.menPref m' (ν.spouse m')
      · -- meet picks ν.spouse m' = w for man m'
        -- meet.spouse m' = ν.spouse m' = w, so meet.inverse w = m' = ν⁻¹w
        have hmeetm' : (μ.meet prof hμ hν).spouse m' = ν.spouse m' := by
          show (μ.meet prof hμ hν).spouse m' = ν.spouse m'
          simp only [Matching.meet, Matching.meetSpouse, hle', if_true]
        have hmeetm'w : (μ.meet prof hμ hν).spouse m' = w := hmeetm' ▸ hνm'
        have hinv' : (μ.meet prof hμ hν).inverse w = m' :=
          inverse_eq_of_spouse_eq (μ.meet prof hμ hν) m' w hmeetm'w
        -- But h says meet.inverse w = μ⁻¹w, so m' = μ⁻¹w
        have hm'eq : m' = μ.inverse w := hinv' ▸ h
        -- Then ν.spouse(μ⁻¹w) = ν.spouse m' = w, contradicting hw
        have : ν.spouse (μ.inverse w) = w := hm'eq ▸ hνm'
        exact absurd this hw
      · -- meet picks μ.spouse m' for man m'
        -- menPref m' (ν.spouse m') < menPref m' (μ.spouse m'), i.e. m' prefers w over μ.sp m'
        have hm'pref : prof.ManPrefers m' w (μ.spouse m') := by
          unfold ManPrefers
          have hνsp : prof.menPref m' (ν.spouse m') = prof.menPref m' w := by rw [hνm']
          have := hle'
          simp only [not_le] at this
          rw [hνsp] at this
          exact mod_cast this
        -- Use stability of μ: ¬IsBlockingPair μ m' w
        -- ManPrefers m' w (μ.spouse m') holds, so woman side must fail
        have hblock : ¬IsBlockingPair prof μ m' w := hμ m' w
        have : ¬prof.WomanPrefers w m' (μ.inverse w) := by
          intro hw'
          exact hblock ⟨hm'pref, hw'⟩
        unfold WomanPrefers at this
        simp only [not_lt] at this
        exact this

/--
Anti-complementarity of the meet (woman side, ν branch):
If meet.inverse w = ν⁻¹(w), then w prefers ν⁻¹(w) to μ⁻¹(w).
Requires stability of μ and ν.
-/
lemma meet_inverse_anti_pref' (μ ν : Matching n)
    (hμ : IsStable prof μ) (hν : IsStable prof ν) (w : Fin n)
    (h : (μ.meet prof hμ hν).inverse w = ν.inverse w) :
    prof.womenPref w (ν.inverse w) ≤ prof.womenPref w (μ.inverse w) := by
  have hνsp : ν.spouse (ν.inverse w) = w := spouse_inverse ν w
  have hmMeet : (μ.meet prof hμ hν).spouse (ν.inverse w) = w := by
    rw [← h, spouse_inverse]
  simp only [Matching.meet, Matching.meetSpouse] at hmMeet
  by_cases hle : prof.menPref (ν.inverse w) (μ.spouse (ν.inverse w)) ≤
      prof.menPref (ν.inverse w) (ν.spouse (ν.inverse w))
  · -- meet picks ν.spouse(ν⁻¹w) = w
    simp only [hle, if_true] at hmMeet
    by_cases hw : μ.spouse (ν.inverse w) = w
    · rw [inverse_eq_of_spouse_eq μ _ _ hw]
    · -- μ⁻¹w ≠ ν⁻¹w, and ν⁻¹w weakly prefers μ.sp(ν⁻¹w) to w.
      -- Use the μ-stability on (ν⁻¹w, w): ν⁻¹w is matched to μ.sp(ν⁻¹w) ≠ w in μ.
      -- hle says ν⁻¹w prefers μ.sp(ν⁻¹w) to w, i.e., man prefers w less.
      -- So man side of blocking pair (ν⁻¹w, w) in μ FAILS (man doesn't prefer w).
      -- This doesn't give us the womenPref inequality.
      -- Instead use the anti-complementarity of the proved meet_inverse_anti_pref lemma:
      -- meet chose ν⁻¹w for w, and by anti_pref, womenPref w (μ⁻¹w) ≤ womenPref w (ν⁻¹w).
      -- We need the opposite: womenPref w (ν⁻¹w) ≤ womenPref w (μ⁻¹w).
      -- This requires the ' version which is what we're trying to prove!
      -- Fall back to: ν-stability on (μ⁻¹w, w) if man prefers w.
      have hmμ : μ.spouse (μ.inverse w) = w := spouse_inverse μ w
      by_cases hνpref : prof.menPref (μ.inverse w) w <
          prof.menPref (μ.inverse w) (ν.spouse (μ.inverse w))
      · -- μ⁻¹w prefers w to ν.sp(μ⁻¹w): (μ⁻¹w, w) would block ν
        -- unless w doesn't prefer μ⁻¹w to ν⁻¹w
        have hblock : ¬IsBlockingPair prof ν (μ.inverse w) w := hν (μ.inverse w) w
        have hm'pref : prof.ManPrefers (μ.inverse w) w (ν.spouse (μ.inverse w)) := by
          unfold ManPrefers; exact mod_cast hνpref
        have : ¬prof.WomanPrefers w (μ.inverse w) (ν.inverse w) := by
          intro hw'; exact hblock ⟨hm'pref, hw'⟩
        unfold WomanPrefers at this
        simp only [not_lt] at this
        exact this
      · -- ¬hνpref: menPref(μ⁻¹w)(ν.sp(μ⁻¹w)) ≤ menPref(μ⁻¹w)(w) = menPref(μ⁻¹w)(μ.sp(μ⁻¹w))
        -- Either meet picks μ.sp(μ⁻¹w)=w, or equality forces ν.sp(μ⁻¹w)=w by injectivity.
        -- In both cases meet⁻¹w = μ⁻¹w, and combined with h, μ⁻¹w = ν⁻¹w.
        have hnle : ¬prof.menPref (μ.inverse w) (μ.spouse (μ.inverse w)) ≤
            prof.menPref (μ.inverse w) (ν.spouse (μ.inverse w)) := by
          intro hle'
          simp only [not_lt] at hνpref
          rw [hmμ] at hle'
          have hnat₁ : (prof.menPref (μ.inverse w) w : Nat) ≤
              prof.menPref (μ.inverse w) (ν.spouse (μ.inverse w)) := mod_cast hle'
          have hnat₂ : (prof.menPref (μ.inverse w) (ν.spouse (μ.inverse w)) : Nat) ≤
              prof.menPref (μ.inverse w) w := mod_cast hνpref
          have hnat_eq : prof.menPref (μ.inverse w) w =
              prof.menPref (μ.inverse w) (ν.spouse (μ.inverse w)) :=
            Fin.ext (Nat.le_antisymm hnat₁ hnat₂)
          have hνspμ : ν.spouse (μ.inverse w) = w :=
            (prof.menPref_bijective (μ.inverse w)).injective hnat_eq.symm
          have hνeq : ν.inverse w = μ.inverse w :=
            (inverse_eq_of_spouse_eq ν _ _ hνspμ).trans
              (inverse_eq_of_spouse_eq μ _ _ hmμ).symm
          rw [hνeq] at hw
          exact hw hmμ
        have hmMeet' : (μ.meet prof hμ hν).spouse (μ.inverse w) =
            μ.spouse (μ.inverse w) := by
          simp only [Matching.meet, Matching.meetSpouse, hnle, if_false]
        have hmMeetw : (μ.meet prof hμ hν).spouse (μ.inverse w) = w := by
          rw [hmMeet', hmμ]
        have hinvEq : (μ.meet prof hμ hν).inverse w = μ.inverse w :=
          inverse_eq_of_spouse_eq (μ.meet prof hμ hν) _ _ hmMeetw
        rw [← h, hinvEq]
  · -- meet picks μ.spouse(ν⁻¹w), so μ.spouse(ν⁻¹w) = w, hence μ⁻¹w = ν⁻¹w
    push Not at hle
    split_ifs at hmMeet with hle'
    · -- pos branch contradicts ¬hle: hle' says a≤b but hle says b<a
      exfalso; omega
    · -- neg branch: μ.spouse(ν⁻¹w) = w, so μ⁻¹w = ν⁻¹w
      rw [inverse_eq_of_spouse_eq μ _ _ hmMeet]

/--
Anti-complementarity of the meet: (μ ⊓ ν).inverse w equals either μ⁻¹(w) or ν⁻¹(w).
Same argument as join_inverse_anti: the meet spouse of (meet.inverse w) equals w,
and the meet picks one of the two partners.
-/
lemma meet_inverse_anti (μ ν : Matching n) (hμ : IsStable prof μ) (hν : IsStable prof ν)
    (w : Fin n) :
    (μ.meet prof hμ hν).inverse w = μ.inverse w ∨
    (μ.meet prof hμ hν).inverse w = ν.inverse w := by
  have hspw : (μ.meet prof hμ hν).spouse ((μ.meet prof hμ hν).inverse w) = w :=
    spouse_inverse (μ.meet prof hμ hν) w
  simp only [Matching.meet, Matching.meetSpouse] at hspw
  split_ifs at hspw
  · right; exact (inverse_eq_of_spouse_eq ν _ w hspw).symm
  · left; exact (inverse_eq_of_spouse_eq μ _ w hspw).symm

/--
Wu-Roth Lemma 3.2 (one-to-one specialization):
The join of two stable matchings is stable.

Proof: suppose (m, w) blocks μ ⊔ ν.
Man side: m prefers w to join-partner ⟹ m prefers w to both μ(m) and ν(m).
Woman side: (μ ⊔ ν).inverse w is either μ⁻¹(w) or ν⁻¹(w).
  Case μ⁻¹(w): w prefers m to μ⁻¹(w), so (m,w) blocks μ. Contradiction.
  Case ν⁻¹(w): w prefers m to ν⁻¹(w), so (m,w) blocks ν. Contradiction.
-/
theorem join_isStable (μ ν : Matching n)
    (hμ : IsStable prof μ) (hν : IsStable prof ν) :
    IsStable prof (μ.join prof hμ hν) := by
  intro m w hblock
  obtain ⟨hmpref, hwpref⟩ := hblock
  simp only [Matching.join, Matching.joinSpouse] at hmpref
  have hboth := join_pref_both prof μ ν m w hmpref
  rcases join_inverse_anti prof μ ν hμ hν w with hinvμ | hinvν
  · rw [hinvμ] at hwpref
    exact hμ m w ⟨hboth.1, hwpref⟩
  · rw [hinvν] at hwpref
    exact hν m w ⟨hboth.2, hwpref⟩

/--
The meet of two stable matchings is stable.

Proof: suppose (m, w) blocks μ ⊓ ν.
Man side: m prefers w to meet-partner ⟹ m prefers w to at least one of μ(m) or ν(m).
Woman side: (μ ⊓ ν).inverse w is either μ⁻¹(w) or ν⁻¹(w).
  Combined, at least one of the cases gives a blocking pair for μ or ν.
-/
theorem meet_isStable (μ ν : Matching n)
    (hμ : IsStable prof μ) (hν : IsStable prof ν) :
    IsStable prof (μ.meet prof hμ hν) := by
  intro m w hblock
  obtain ⟨hmpref, hwpref⟩ := hblock
  simp only [Matching.meet, Matching.meetSpouse] at hmpref
  have hone := meet_pref_one prof μ ν m w hmpref
  rcases meet_inverse_anti prof μ ν hμ hν w with hinvμ | hinvν
  · -- (μ ⊓ ν).inverse w = μ.inverse w, so w prefers m to μ⁻¹(w)
    rw [hinvμ] at hwpref
    rcases hone with hmμ | hmν
    · -- m prefers w to μ(m) AND w prefers m to μ⁻¹(w) → blocks μ
      exact hμ m w ⟨hmμ, hwpref⟩
    · -- m prefers w to ν(m), w prefers m to μ⁻¹(w)
      -- Anti-complementarity: meet.inverse w = μ⁻¹(w) ⟹ w prefers μ⁻¹(w) to ν⁻¹(w)
      -- Transitively: w prefers m to ν⁻¹(w). Combined with hmν, (m,w) blocks ν.
      have hwν := meet_inverse_anti_pref prof μ ν hμ hν w hinvμ
      have h1 : (prof.womenPref w m : Nat) < prof.womenPref w (μ.inverse w) := mod_cast hwpref
      have h2 : (prof.womenPref w (μ.inverse w) : Nat) ≤ prof.womenPref w (ν.inverse w) := mod_cast hwν
      have hwν' : prof.WomanPrefers w m (ν.inverse w) := mod_cast Nat.lt_of_lt_of_le h1 h2
      exact hν m w ⟨hmν, hwν'⟩
  · -- (μ ⊓ ν).inverse w = ν.inverse w, so w prefers m to ν⁻¹(w)
    rw [hinvν] at hwpref
    rcases hone with hmμ | hmν
    · -- m prefers w to μ(m), w prefers m to ν⁻¹(w)
      -- Anti-complementarity: meet.inverse w = ν⁻¹(w) ⟹ w prefers ν⁻¹(w) to μ⁻¹(w)
      -- Transitively: w prefers m to μ⁻¹(w). Combined with hmμ, (m,w) blocks μ.
      have hwμ := meet_inverse_anti_pref' prof μ ν hμ hν w hinvν
      have h1 : (prof.womenPref w m : Nat) < prof.womenPref w (ν.inverse w) := mod_cast hwpref
      have h2 : (prof.womenPref w (ν.inverse w) : Nat) ≤ prof.womenPref w (μ.inverse w) := mod_cast hwμ
      have hwμ' : prof.WomanPrefers w m (μ.inverse w) := mod_cast Nat.lt_of_lt_of_le h1 h2
      exact hμ m w ⟨hmμ, hwμ'⟩
    · -- m prefers w to ν(m) AND w prefers m to ν⁻¹(w) → blocks ν
      exact hν m w ⟨hmν, hwpref⟩

/-! ## Lattice Instance -/

-- TODO: Instance requires proving all lattice axioms on the subtype.
-- This needs join_isStable + meet_isStable fully proved first.
-- Will instantiate after proofs are complete.

/-! ## Man-Optimality (honest version)

The two statements that previously closed this file —

  `man_optimality_key_step : menPref m' (ν.spouse m') < menPref m' (μ.spouse m') → False`
  `doctor_optimal_eq_top   : IsStable prof μ_gs → IsStable prof μ' → ManLE prof μ_gs μ'`

— were FALSE as stated (their `sorry`s were unprovable): neither statement
mentioned the Gale-Shapley algorithm, so together they claimed that ANY two
stable matchings are ManLE-comparable in both directions, i.e. that the
stable matching is unique.  The 3×3 latin-square instance refutes both
(`NoCrossCounterexample.man_optimality_key_step_is_false`,
`NoCrossCounterexample.doctor_optimal_eq_top_is_false`).

The honest replacement is the EXISTENCE of a man-optimal stable matching,
`exists_isManOptimal`, proved by a minimal-weight argument on the join
semilattice (`join_isStable`).  `gale_shapley_man_optimal` in
GaleShapley.lean consumes it, seeded by `gale_shapley_stable`.
-/

namespace NoCrossCounterexample

/--
**Refutation** of the former `man_optimality_key_step` lemma: m₁ strictly
prefers his M0-partner w₁ (rank 0) to his M1-partner w₂ (rank 1), and both
matchings are stable, so no `False` can follow.
-/
theorem man_optimality_key_step_is_false :
    ¬ ∀ (n : Nat) [NeZero n] (prof : PrefProfile n) (μ ν : Matching n),
        IsStable prof μ → IsStable prof ν →
        ∀ m' : Fin n,
          prof.menPref m' (ν.spouse m') < prof.menPref m' (μ.spouse m') → False := by
  intro h
  exact h 3 prof3 M1 M0 M1_stable M0_stable 0 (by decide)

/--
**Refutation** of the former `doctor_optimal_eq_top` theorem: with
μ_gs := M1 and μ' := M0 (both stable), ManLE would require
`menPref m₁ w₂ ≤ menPref m₁ w₁`, i.e. `1 ≤ 0`.
-/
theorem doctor_optimal_eq_top_is_false :
    ¬ ∀ (n : Nat) [NeZero n] (prof : PrefProfile n) (μ_gs : Matching n),
        IsStable prof μ_gs →
        ∀ μ' : Matching n, IsStable prof μ' → ManLE prof μ_gs μ' := by
  intro h
  have hle := h 3 prof3 M1 M1_stable M0 M0_stable
  have h0 := hle 0
  exact absurd h0 (by decide)

end NoCrossCounterexample

/--
A man-optimal stable matching exists as soon as a stable matching exists.

Minimal-weight argument: let `W μ = Σ_m rank_m (μ.spouse m)` and pick (via
`Nat.find`) a stable matching `μ₀` whose weight is minimal among stable
matchings.  If some stable `ν` gave some man `m` a strictly better partner,
the join `μ₀ ⊔ ν` would be stable (`join_isStable`), pointwise weakly
man-better than `μ₀` (the join hands each man his preferred partner of the
two) and strictly better for `m`, hence of strictly smaller weight —
contradicting minimality.  So `μ₀` is man-optimal.

The hypothesis is discharged by `gale_shapley_stable` in GaleShapley.lean
(kept as a hypothesis here to avoid an import cycle).
-/
theorem exists_isManOptimal (hex : ∃ μ : Matching n, IsStable prof μ) :
    ∃ μ : Matching n, IsManOptimal prof μ := by
  classical
  let W : Matching n → Nat := fun μ => ∑ m : Fin n, (prof.menPref m (μ.spouse m) : Nat)
  let P : Nat → Prop := fun k => ∃ μ : Matching n, IsStable prof μ ∧ W μ = k
  have hP : ∃ k, P k := by
    obtain ⟨μ, hμ⟩ := hex
    exact ⟨W μ, μ, hμ, rfl⟩
  obtain ⟨μ₀, hμ₀, hW₀⟩ := Nat.find_spec hP
  refine ⟨μ₀, hμ₀, ?_⟩
  intro ν hν m
  by_contra hgt
  push Not at hgt
  -- hgt : m strictly prefers his ν-partner; consider the join μ₀ ⊔ ν
  have hle : ∀ m' : Fin n,
      (prof.menPref m' ((μ₀.join prof hμ₀ hν).spouse m') : Nat) ≤
        (prof.menPref m' (μ₀.spouse m') : Nat) := by
    intro m'
    show (prof.menPref m' (μ₀.joinSpouse prof ν m') : Nat) ≤ _
    unfold Matching.joinSpouse
    split_ifs with hc
    · exact le_refl _
    · have hnle : ¬((prof.menPref m' (μ₀.spouse m') : Nat) ≤
          (prof.menPref m' (ν.spouse m') : Nat)) := fun hh => hc (mod_cast hh)
      omega
  have hlt : (prof.menPref m ((μ₀.join prof hμ₀ hν).spouse m) : Nat) <
      (prof.menPref m (μ₀.spouse m) : Nat) := by
    show (prof.menPref m (μ₀.joinSpouse prof ν m) : Nat) < _
    unfold Matching.joinSpouse
    split_ifs with hc
    · exfalso
      have h1 : (prof.menPref m (μ₀.spouse m) : Nat) ≤
          (prof.menPref m (ν.spouse m) : Nat) := mod_cast hc
      have h2 : (prof.menPref m (ν.spouse m) : Nat) <
          (prof.menPref m (μ₀.spouse m) : Nat) := mod_cast hgt
      omega
    · exact mod_cast hgt
  have hWlt : W (μ₀.join prof hμ₀ hν) < W μ₀ :=
    Finset.sum_lt_sum (fun i _ => hle i) ⟨m, Finset.mem_univ m, hlt⟩
  have hPlt : P (W (μ₀.join prof hμ₀ hν)) :=
    ⟨μ₀.join prof hμ₀ hν, join_isStable prof μ₀ ν hμ₀ hν, rfl⟩
  exact Nat.find_min hP (lt_of_lt_of_le hWlt (le_of_eq hW₀)) hPlt


end StableMarriage_en
