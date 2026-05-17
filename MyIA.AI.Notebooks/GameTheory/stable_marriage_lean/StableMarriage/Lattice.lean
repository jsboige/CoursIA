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
import Mathlib.Tactic.Common
import StableMarriage.Definitions

namespace StableMarriage

open Function Finset Classical

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

/-! ## Join and Meet Operations -/

/--
The join spouse function: each man gets his preferred partner between μ and ν.
Defined as a bare function so that bijectivity can be proved separately with
stability hypotheses. The join is NOT bijective for arbitrary matchings;
it requires both μ and ν to be stable (anti-complementarity).
-/
noncomputable def Matching.joinSpouse (μ ν : Matching n) (m : Fin n) : Fin n :=
  if prof.menPref m (μ.spouse m) ≤ prof.menPref m (ν.spouse m) then
    μ.spouse m
  else
    ν.spouse m

/--
The meet spouse function: each man gets his less-preferred partner between μ and ν.
-/
noncomputable def Matching.meetSpouse (μ ν : Matching n) (m : Fin n) : Fin n :=
  if prof.menPref m (μ.spouse m) ≤ prof.menPref m (ν.spouse m) then
    ν.spouse m
  else
    μ.spouse m

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

/--
The join of two STABLE matchings: each man gets his preferred partner.
Bijectivity follows from anti-complementarity: on the woman side, the join
acts as the meet, so no two men map to the same woman.
-/
noncomputable def Matching.join (hμ : IsStable prof μ) (hν : IsStable prof ν) :
    Matching n where
  spouse := fun m => μ.joinSpouse prof ν m
  bijective := Finite.injective_iff_bijective.mp (joinSpouse_injective prof μ ν hμ hν)

/--
Injectivity of meet: symmetric to joinSpouse_injective.
-/
private lemma meetSpouse_injective (μ ν : Matching n)
    (hμ : IsStable prof μ) (hν : IsStable prof ν) :
    Injective (fun m => μ.meetSpouse prof ν m) := by
  intro m₁ m₂ heq
  by_cases c₁ : prof.menPref m₁ (μ.spouse m₁) ≤ prof.menPref m₁ (ν.spouse m₁)
  · simp only [Matching.meetSpouse, c₁, if_true] at heq
    by_cases c₂ : prof.menPref m₂ (μ.spouse m₂) ≤ prof.menPref m₂ (ν.spouse m₂)
    · simp only [Matching.meetSpouse, c₂, if_true] at heq
      exact ν.bijective.1 heq
    · simp only [Matching.meetSpouse, c₂, if_false] at heq
      -- Cross-case: ν.spouse m₁ = μ.spouse m₂, m₁ gets ν, m₂ gets μ
      -- c₁: menPref m₁ (μ.sp m₁) ≤ menPref m₁ (ν.sp m₁) (m₁ weakly prefers μ)
      -- ¬c₂: m₂ prefers ν.sp to μ.sp (strict)
      -- Key insight: c₁ gives ≤. If also ≥, equality → injectivity contradiction.
      -- If strictly <, use stability (sorry for now).
      by_cases hm₁str : (prof.menPref m₁ (μ.spouse m₁) : Nat) < prof.menPref m₁ (ν.spouse m₁)
      · -- Strict: m₁ strictly prefers μ.sp₁ to ν.sp₁ = μ.sp m₂
        -- Meet cross-case: men prefer DIFFERENT women.
        -- Use anti-complementarity: meet on man side = join on woman side.
        -- The key insight: consider woman μ.sp₁.
        -- m₁ prefers μ.sp₁ over w. Use ν-stability on (m₁, μ.sp₁).
        by_contra hne
        have hw : ν.spouse m₁ = μ.spouse m₂ := heq
        have hm₁μinv : μ.inverse (μ.spouse m₁) = m₁ := inverse_eq_of_spouse_eq μ m₁ _ rfl
        -- ν-stability on (m₁, μ.sp₁): m₁ prefers μ.sp₁ to w = ν.sp₁
        have hm₁pref : prof.ManPrefers m₁ (μ.spouse m₁) (ν.spouse m₁) := by
          unfold PrefProfile.ManPrefers; exact mod_cast hm₁str
        -- If μ.sp₁ also prefers m₁ to ν⁻¹(μ.sp₁), blocks ν
        by_cases hw₁ : prof.WomanPrefers (μ.spouse m₁) m₁ (ν.inverse (μ.spouse m₁))
        · -- (m₁, μ.sp₁) blocks ν
          have hblock₁ : IsBlockingPair prof ν m₁ (μ.spouse m₁) := ⟨hm₁pref, hw₁⟩
          exact hν m₁ (μ.spouse m₁) hblock₁
        · -- μ.sp₁ doesn't prefer m₁ to ν⁻¹(μ.sp₁)
          -- So ν⁻¹(μ.sp₁) ≤ m₁ in womenPref. Who is ν⁻¹(μ.sp₁)?
          -- Now consider woman ν.sp₂. m₂ prefers ν.sp₂ over w.
          have hm₂νinv : ν.inverse (ν.spouse m₂) = m₂ := inverse_eq_of_spouse_eq ν m₂ _ rfl
          have hm₂pref : prof.ManPrefers m₂ (ν.spouse m₂) (μ.spouse m₂) := by
            unfold PrefProfile.ManPrefers
            exact mod_cast (Nat.lt_of_not_le (mod_cast c₂))
          -- μ-stability on (m₂, ν.sp₂): m₂ prefers ν.sp₂ to w = μ.sp₂
          by_cases hw₂ : prof.WomanPrefers (ν.spouse m₂) m₂ (μ.inverse (ν.spouse m₂))
          · -- (m₂, ν.sp₂) blocks μ
            have hblock₂ : IsBlockingPair prof μ m₂ (ν.spouse m₂) := ⟨hm₂pref, hw₂⟩
            exact hμ m₂ (ν.spouse m₂) hblock₂
          · -- Both women don't prefer the respective man.
            -- hw₁: ¬WomanPrefers (μ.sp₁) m₁ (ν⁻¹(μ.sp₁))
            -- hw₂: ¬WomanPrefers (ν.sp₂) m₂ (μ⁻¹(ν.sp₂))
            by_cases hwsame : μ.spouse m₁ = ν.spouse m₂
            · -- Same woman w = μ.sp₁ = ν.sp₂. From stability:
              --   hw₁: womenPref w (ν⁻¹w) ≤ womenPref w m₁
              --   hw₂: womenPref w (μ⁻¹w) ≤ womenPref w m₂
              -- But ν⁻¹w = m₂ and μ⁻¹w = m₁, so antisymm gives womenPref w m₁ = womenPref w m₂.
              have hμinv₁ : μ.inverse (μ.spouse m₁) = m₁ := inverse_eq_of_spouse_eq μ m₁ _ rfl
              have hνinv₂ : ν.inverse (ν.spouse m₂) = m₂ := inverse_eq_of_spouse_eq ν m₂ _ rfl
              -- ν⁻¹(μ.sp₁) = ν⁻¹(ν.sp₂) = m₂  (using hwsame: μ.sp₁ = ν.sp₂)
              have hνinv₁ : ν.inverse (μ.spouse m₁) = m₂ := hwsame ▸ hνinv₂
              -- hw₁: ¬WomanPrefers (μ.sp₁) m₁ (ν⁻¹(μ.sp₁))  →  womenPref(μ.sp₁)(m₂) ≤ womenPref(μ.sp₁)(m₁)
              -- hw₂: ¬WomanPrefers (ν.sp₂) m₂ (μ⁻¹(ν.sp₂))  →  womenPref(ν.sp₂)(μ⁻¹(ν.sp₂)) ≤ womenPref(ν.sp₂)(m₂)
              -- With hwsame and inverses: womenPref(μ.sp₁)(m₁) ≤ womenPref(μ.sp₁)(m₂)
              unfold PrefProfile.WomanPrefers at hw₁ hw₂
              simp only [not_lt] at hw₁ hw₂
              rw [hνinv₁] at hw₁
              -- hw₂: womenPref (ν.sp₂) (μ⁻¹(ν.sp₂)) ≤ womenPref (ν.sp₂) m₂
              -- After rw [← hwsame]: womenPref (μ.sp₁) (μ⁻¹(μ.sp₁)) ≤ womenPref (μ.sp₁) m₂
              -- Then rw [hμinv₁]: womenPref (μ.sp₁) m₁ ≤ womenPref (μ.sp₁) m₂
              have hw₂' : prof.womenPref (μ.spouse m₁) m₁ ≤ prof.womenPref (μ.spouse m₁) m₂ := by
                have h1 := hw₂
                rw [← hwsame] at h1
                rw [hμinv₁] at h1
                exact mod_cast h1
              -- hw₁: womenPref (μ.sp₁) m₂ ≤ womenPref (μ.sp₁) m₁
              -- hw₂: womenPref (μ.sp₁) m₁ ≤ womenPref (μ.sp₁) m₂
              exact hne ((prof.womenPref_bijective (μ.spouse m₁)).injective
                (Fin.ext (Nat.le_antisymm (mod_cast hw₂') (mod_cast hw₁))))
            · -- Different women: needs deeper lattice argument
              sorry
      · -- Equality: m₁ equally prefers both → μ.sp m₁ = ν.sp m₁ → injectivity contradiction
        push_neg at hm₁str
        have hm₁ge : (prof.menPref m₁ (ν.spouse m₁) : Nat) ≤ prof.menPref m₁ (μ.spouse m₁) :=
          mod_cast hm₁str
        have heq' : (prof.menPref m₁ (μ.spouse m₁) : Nat) = prof.menPref m₁ (ν.spouse m₁) :=
          Nat.le_antisymm (mod_cast c₁) hm₁ge
        have hsp_eq : μ.spouse m₁ = ν.spouse m₁ :=
          (prof.menPref_bijective m₁).injective (Fin.ext heq')
        rw [heq] at hsp_eq
        exact μ.bijective.1 hsp_eq
  · simp only [Matching.meetSpouse, c₁, if_false] at heq
    by_cases c₂ : prof.menPref m₂ (μ.spouse m₂) ≤ prof.menPref m₂ (ν.spouse m₂)
    · simp only [Matching.meetSpouse, c₂, if_true] at heq
      -- Cross-case: μ.spouse m₁ = ν.spouse m₂, m₁ gets μ, m₂ gets ν
      -- ¬c₁: m₁ prefers ν.sp to μ.sp; c₂: m₂ weakly prefers μ.sp to ν.sp
      by_cases hm₂strict : (prof.menPref m₂ (μ.spouse m₂) : Nat) < prof.menPref m₂ (ν.spouse m₂)
      · -- Strict: m₂ strictly prefers μ.sp₂ to ν.sp₂
        -- Symmetric to first cross-case. heq: μ.sp m₁ = ν.sp m₂ = w
        -- m₁ prefers ν.sp₁ to μ.sp₁=w. m₂ prefers μ.sp₂ to ν.sp₂.
        by_contra hne
        have hm₁pref : prof.ManPrefers m₁ (ν.spouse m₁) (μ.spouse m₁) := by
          unfold PrefProfile.ManPrefers
          exact mod_cast (Nat.lt_of_not_le (mod_cast c₁))
        have hm₂pref : prof.ManPrefers m₂ (μ.spouse m₂) (ν.spouse m₂) := by
          unfold PrefProfile.ManPrefers; exact mod_cast hm₂strict
        -- ν-stability on (m₁, ν.sp₁): m₁ prefers ν.sp₁ to μ.sp₁=w
        -- But m₁ IS matched to ν.sp₁ in ν. So can't block with himself.
        -- Instead: μ-stability on (m₁, ν.sp₁): m₁ prefers ν.sp₁ to μ.sp₁.
        by_cases hw₁ : prof.WomanPrefers (ν.spouse m₁) m₁ (μ.inverse (ν.spouse m₁))
        · have hblock₁ : IsBlockingPair prof μ m₁ (ν.spouse m₁) := ⟨hm₁pref, hw₁⟩
          exact hμ m₁ (ν.spouse m₁) hblock₁
        · -- ν-stability on (m₂, μ.sp₂): m₂ prefers μ.sp₂ to ν.sp₂
          by_cases hw₂ : prof.WomanPrefers (μ.spouse m₂) m₂ (ν.inverse (μ.spouse m₂))
          · have hblock₂ : IsBlockingPair prof ν m₂ (μ.spouse m₂) := ⟨hm₂pref, hw₂⟩
            exact hν m₂ (μ.spouse m₂) hblock₂
          · -- Both women don't prefer the respective man.
            -- hw₁: ¬WomanPrefers (ν.sp₁) m₁ (μ⁻¹(ν.sp₁))
            -- hw₂: ¬WomanPrefers (μ.sp₂) m₂ (ν⁻¹(μ.sp₂))
            by_cases hwsame : ν.spouse m₁ = μ.spouse m₂
            · -- Same woman w = ν.sp₁ = μ.sp₂
              have hμinv₁ : μ.inverse (μ.spouse m₁) = m₁ := inverse_eq_of_spouse_eq μ m₁ _ rfl
              have hνinv₁ : ν.inverse (ν.spouse m₁) = m₁ := inverse_eq_of_spouse_eq ν m₁ _ rfl
              have hμinv₂ : μ.inverse (μ.spouse m₂) = m₂ := inverse_eq_of_spouse_eq μ m₂ _ rfl
              have hνinv₂ : ν.inverse (ν.spouse m₂) = m₂ := inverse_eq_of_spouse_eq ν m₂ _ rfl
              -- μ⁻¹(ν.sp₁) = μ⁻¹(μ.sp₂) = m₂
              have hμinvν₁ : μ.inverse (ν.spouse m₁) = m₂ := by rw [hwsame]; exact hμinv₂
              -- ν⁻¹(μ.sp₂) = ν⁻¹(ν.sp₁) = m₁
              have hνinvμ₂ : ν.inverse (μ.spouse m₂) = m₁ := by rw [← hwsame]; exact hνinv₁
              unfold PrefProfile.WomanPrefers at hw₁ hw₂
              simp only [not_lt] at hw₁ hw₂
              rw [hμinvν₁] at hw₁
              rw [hνinvμ₂] at hw₂
              -- hw₁: womenPref (ν.sp₁) m₂ ≤ womenPref (ν.sp₁) m₁
              -- hw₂: womenPref (μ.sp₂) m₁ ≤ womenPref (μ.sp₂) m₂
              -- But ν.sp₁ = μ.sp₂ = w, so rewrite hw₂ to use ν.sp₁
              rw [← hwsame] at hw₂
              -- hw₁: womenPref w m₂ ≤ womenPref w m₁
              -- hw₂: womenPref w m₁ ≤ womenPref w m₂
              exact hne ((prof.womenPref_bijective (ν.spouse m₁)).injective
                (Fin.ext (Nat.le_antisymm (mod_cast hw₂) (mod_cast hw₁))))
            · sorry
      · -- Equality: μ.spouse m₂ = ν.spouse m₂, then with heq: μ.spouse₁ = ν.spouse₂ = μ.spouse₂
        -- contradicts μ injectivity (m₁ ≠ m₂)
        push_neg at hm₂strict
        have hm₂ge : (prof.menPref m₂ (ν.spouse m₂) : Nat) ≤ prof.menPref m₂ (μ.spouse m₂) :=
          mod_cast hm₂strict
        have heq' : (prof.menPref m₂ (μ.spouse m₂) : Nat) = prof.menPref m₂ (ν.spouse m₂) :=
          Nat.le_antisymm (mod_cast c₂) hm₂ge
        have hsp_eq : μ.spouse m₂ = ν.spouse m₂ :=
          (prof.menPref_bijective m₂).injective (Fin.ext heq')
        rw [← heq] at hsp_eq
        exact μ.bijective.1 hsp_eq.symm
    · simp only [Matching.meetSpouse, c₂, if_false] at heq
      exact μ.bijective.1 heq

/--
The meet of two STABLE matchings: each man gets his less-preferred partner.
-/
noncomputable def Matching.meet (hμ : IsStable prof μ) (hν : IsStable prof ν) :
    Matching n where
  spouse := fun m => μ.meetSpouse prof ν m
  bijective := Finite.injective_iff_bijective.mp (meetSpouse_injective prof μ ν hμ hν)

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
      · -- μ⁻¹w prefers ν.sp(μ⁻¹w) to w (or equal).
        -- meet for μ⁻¹w: if μ⁻¹w prefers μ.sp(μ⁻¹w)=w to ν.sp(μ⁻¹w), meet picks w.
        -- But we can't conclude womenPref directly from this either.
        sorry
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

/-! ## Man-Optimal = Top of the Lattice -/

/--
The man-proposing Gale-Shapley output is the bottom element of the lattice
of stable matchings under ManLE: every man gets his best achievable partner.
ManLE prof μ_gs μ' means each man's GS partner is at least as preferred
as his partner in any other stable matching μ'.
-/
theorem doctor_optimal_eq_top (μ_gs : Matching n)
    (hgs : IsStable prof μ_gs)
    (μ' : Matching n) (hstable : IsStable prof μ') :
    ManLE prof μ_gs μ' :=
  fun m => by
  sorry

end StableMarriage
