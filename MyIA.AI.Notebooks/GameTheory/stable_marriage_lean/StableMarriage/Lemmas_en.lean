/-
  Stable Marriage - Key Lemmas for Gale-Shapley Algorithm Correctness
  ===================================================================

  English mirror of `StableMarriage/Lemmas.lean` (FR-first canonical).
  Convention i18n Lean ratifiée par ai-01 (2026-07-04, #4980 comment-4881909354) :
  fichiers `.lean` distincts FR + EN siblings dans le même lake, les deux compilent.
  Drift-CI detectable : contenu non-docstring byte-identique entre siblings.
  Namespace sibling : `StableMarriage_en` (le FR canonique reste `StableMarriage`).
  Convention observée : imports intra-lake restent sur fichiers FR canoniques.
  Pas une traduction destructive : manual translation FR-first-from-origin
  (pas d'historique EN pré-Option A pour ce fichier) ; code tactique Lean
  byte-identique préservé verbatim, prose traduite. Pattern identique
  c.238.2/#5362 (RepeatedGames), c.238.3/#5363 (Minimax), c.238.4/#5419 (Shapley).

  Adapté de / Adapted from: https://github.com/mmaaz-git/stable-marriage-lean (v4.25.0)

  See #4980. Part of #4208 (axe E).
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Common
import StableMarriage.Definitions
import StableMarriage.GSState

namespace StableMarriage_en


open Function Finset Classical

variable {n : Nat} [NeZero n]

/-! ## Consistent partial matching -/

/-- Un couplage partiel est cohérent : chaque appariement est mutuel.
    Si l'homme `m` est apparié à la femme `w`, alors la femme `w` est appariée
    à l'homme `m`, et réciproquement. -/
def GSConsistent (μ : GSMatching n) : Prop :=
  ∀ m w, μ.menMatch m = some w ↔ μ.womenMatch w = some m

namespace GSConsistent

variable {μ : GSMatching n}

lemma men_iff_women (h : GSConsistent μ) (m : Fin n) (w : Fin n) :
    μ.menMatch m = some w ↔ μ.womenMatch w = some m := h m w

lemma women_iff_men (h : GSConsistent μ) (w : Fin n) (m : Fin n) :
    μ.womenMatch w = some m ↔ μ.menMatch m = some w := (h m w).symm

/-- The initial matching is consistent (all matches are `none`). -/
lemma initial : GSConsistent (GSMatching.initial (n := n)) := by
  intro m w
  simp [GSMatching.initial]

/-- Matching a free man with a free woman preserves consistency. -/
lemma matchFree (h : GSConsistent μ) (m : Fin n) (w : Fin n)
    (hm : μ.menMatch m = none) (hw : μ.womenMatch w = none) :
    GSConsistent (μ.matchFree m w) := by
  intro m' w'
  simp only [GSMatching.matchFree, Function.update_apply]
  split_ifs
  · simp_all
  · have : μ.womenMatch w' ≠ some m := by
      intro heq; have := (h m w').mpr heq; simp_all
    simp_all [ne_comm]
  · have : μ.menMatch m' ≠ some w := by
      intro heq; have := (h m' w).mp heq; simp_all
    simp_all [ne_comm]
  · exact h m' w'

end GSConsistent

/-! ## Tracking the proposal set -/

/-- The set of proposed pairs, seen as a `Finset`. -/
noncomputable def proposedSet (prof : PrefProfile n) (σ : GSState prof) :
    Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun mw => σ.proposed mw.1 mw.2)

/-- Number of proposed pairs. -/
noncomputable def proposedCount (prof : PrefProfile n) (σ : GSState prof) : Nat :=
  (proposedSet prof σ).card

namespace proposedSet

variable (prof : PrefProfile n) {σ : GSState prof}

lemma mem_iff (mw : Fin n × Fin n) :
    mw ∈ proposedSet prof σ ↔ σ.proposed mw.1 mw.2 := by
  simp [proposedSet]

/-- `gsStepWith` inserts exactly one new pair in the proposal set. -/
lemma stepWith_insert (σ : GSState prof) (m w : Fin n) :
    proposedSet prof (gsStepWith prof σ m w) =
      insert (m, w) (proposedSet prof σ) := by
  classical
  ext ⟨m', w'⟩
  simp only [mem_iff, mem_insert, Prod.mk.injEq]
  unfold gsStepWith
  split
  · simp; tauto
  · split <;> simp <;> tauto

end proposedSet

namespace proposedCount

variable (prof : PrefProfile n) {σ : GSState prof}

/-- The initial state has zero proposals. -/
lemma initial : proposedCount prof (gsInitial prof) = 0 := by
  classical
  simp [proposedCount, proposedSet, gsInitial]

/-- `StepWith` increases the counter by one for any new proposal. -/
lemma stepWith (σ : GSState prof) (m w : Fin n) (hnew : ¬ σ.proposed m w) :
    proposedCount prof (gsStepWith prof σ m w) = proposedCount prof σ + 1 := by
  classical
  have hmem : (m, w) ∉ proposedSet prof σ := by
    simp [proposedSet]
    exact hnew
  simp only [proposedCount, proposedSet.stepWith_insert]
  exact card_insert_of_notMem hmem

end proposedCount

/-! ## Invariant - men propose in decreasing order of preference -/

/-- Dans l'algorithme de Gale-Shapley, les hommes proposent par ordre décroissant
    de préférence. Après `k` étapes, toutes les propositions de l'homme `m` vont à
    ses `k` candidates les plus préférées. Comme les préférences sont des bijections
    totales, chaque femme est une candidate valide. -/
def menProposedDownward (prof : PrefProfile n) (σ : GSState prof) : Prop :=
  ∀ m w w', σ.proposed m w → prof.menPref m w' < prof.menPref m w →
    σ.proposed m w'

/-! ## Invariant - best match for each woman -/

/-- Le partenaire actuel de chaque femme est la meilleure proposition qu'elle ait reçue. -/
def womenBestState (prof : PrefProfile n) (σ : GSState prof) : Prop :=
  ∀ w m m', σ.matching.womenMatch w = some m → σ.proposed m' w →
    prof.womenPref w m ≤ prof.womenPref w m'

namespace womenBestState

variable (prof : PrefProfile n) {σ : GSState prof}

/-- The initial state trivially satisfies `womenBest` (no matching). -/
lemma initial : womenBestState prof (gsInitial prof) := by
  unfold womenBestState
  intro w m m' hmatch _
  unfold gsInitial GSMatching.initial at hmatch
  simp at hmatch

end womenBestState

/-! ## Invariant - every matched man has proposed -/

/-- Tout homme apparié a bien proposé à sa partenaire actuelle. -/
def menMatchedProposed (prof : PrefProfile n) (σ : GSState prof) : Prop :=
  ∀ m w, σ.matching.menMatch m = some w → σ.proposed m w

namespace menMatchedProposed

variable (prof : PrefProfile n) {σ : GSState prof}

/-- The initial state trivially satisfies this invariant (no matching). -/
lemma initial : menMatchedProposed prof (gsInitial prof) := by
  unfold menMatchedProposed
  intro m w hmatch
  unfold gsInitial at hmatch
  unfold GSMatching.initial at hmatch
  simp at hmatch

end menMatchedProposed

/-! ## Consistency preservation by GS steps -/

namespace GSConsistent

variable (prof : PrefProfile n) {σ : GSState prof}

/-- `swapMatch` préserve la cohérence lorsque la femme `w` préfère `m` à `mOld`.
    Le schéma suit la preuve de `matchFree` : `split_ifs` + `have` pour les enchaînements
    de cohérence. -/
lemma swapMatch (h : GSConsistent σ.matching) (m mOld w : Fin n)
    (hm : σ.matching.menMatch m = none)
    (hw : σ.matching.womenMatch w = some mOld)
    (hmOld : σ.matching.menMatch mOld = some w) :
    GSConsistent (σ.matching.swapMatch m mOld w) := by
  have hne : m ≠ mOld := by intro heq; subst heq; simp_all
  intro m' w'
  simp only [GSMatching.swapMatch, Function.update_apply]
  -- `if` extérieur : `m' = mOld` (depuis la mise à jour extérieure)
  -- puis `if` intérieur : `m' = m` (depuis la mise à jour intérieure)
  -- `if` côté droit : `w' = w`
  split_ifs with h_mOld h_ww h_m h_nw h_nm
  · -- `m' = mOld`, `w' = w` : les deux côtés sont `False` par `hne`
    simp_all
  · -- `m' = mOld`, `w' ≠ w` : on a besoin de `μ.womenMatch w' ≠ some mOld`
    have : σ.matching.womenMatch w' ≠ some mOld := by
      intro heq; have := (h mOld w').mpr heq; simp_all
    simp_all
  · -- `m' ≠ mOld`, `m' = m`, `w' = w` : les deux côtés sont `True`
    simp_all
  · -- `m' ≠ mOld`, `m' = m`, `w' ≠ w` : on a besoin de `μ.womenMatch w' ≠ some m`
    have hnw' : w ≠ w' := ne_comm.mp ‹¬w' = w›
    have : σ.matching.womenMatch w' ≠ some m := by
      intro heq; have := (h m w').mpr heq; simp_all
    simp_all
  · -- `m' ≠ mOld`, `m' ≠ m`, `w' = w` : on a besoin de `μ.menMatch m' ≠ some w`
    have hnm' : m ≠ m' := ne_comm.mp ‹¬m' = m›
    have : σ.matching.menMatch m' ≠ some w := by
      intro heq; have := (h m' w).mp heq; simp_all
    simp_all
  · -- `m' ≠ mOld`, `m' ≠ m`, `w' ≠ w` : cohérence directe
    exact h m' w'

/-- `gsStepWith` preserves the consistency of the matching. -/
lemma stepWith (h : GSConsistent σ.matching) (m w : Fin n)
    (hm : σ.matching.menMatch m = none)
    (_hproposed : ¬ σ.proposed m w) :
    GSConsistent (gsStepWith prof σ m w).matching := by
  unfold gsStepWith
  split
  · -- `womenMatch w = none` : cas `matchFree`
    exact matchFree h m w hm ‹_›
  · -- `womenMatch w = some mOld`
    split
    · -- La femme préfère `m` à `mOld` : cas `swapMatch`
      next mOld hwm hwlt =>
        have hmOld : σ.matching.menMatch mOld = some w := (h mOld w).mpr hwm
        exact swapMatch prof h m mOld w hm hwm hmOld
    · -- La femme ne préfère PAS `m` : couplage inchangé
      exact h

/-- `gsStep` preserves the consistency of the matching. -/
lemma step (h : GSConsistent σ.matching) (hfree : ∃ m, gsIsFree prof σ m) :
    GSConsistent (gsStep prof σ).matching := by
  unfold gsStep
  rw [dif_pos hfree]
  let m := Classical.choose hfree
  have hm : gsIsFree prof σ m := Classical.choose_spec hfree
  let w := gsChooseMax prof σ m hm.2
  have hw : ¬ σ.proposed m w := by
    have := gsChooseMax_mem prof σ m hm.2
    simp [gsCandidates] at this
    exact this
  exact stepWith prof h m w hm.1 hw

/-- `gsRunSteps` preserves the consistency of the matching. -/
lemma runSteps (k : Nat) :
    GSConsistent (gsRunSteps prof k).matching := by
  induction k with
  | zero => exact initial
  | succ k' ih =>
    simp only [gsRunSteps]
    by_cases h : ∃ m, gsIsFree prof (gsRunSteps prof k') m
    · exact step prof ih h
    · have hid : gsStep prof (gsRunSteps prof k') = gsRunSteps prof k' := by
        unfold gsStep; simp [h]
      rw [hid]; exact ih

end GSConsistent

/-! ## Termination: bound on the number of proposals -/

namespace proposedCount

variable (prof : PrefProfile n) {σ : GSState prof}

/-- A step for a free man increases the proposal counter. -/
lemma step_of_free (σ : GSState prof) (m : Fin n)
    (hf : gsIsFree prof σ m) :
    proposedCount prof (gsStep prof σ) = proposedCount prof σ + 1 := by
  unfold gsStep
  rw [dif_pos ⟨m, hf⟩]
  let m' := Classical.choose ⟨m, hf⟩
  have hm' : gsIsFree prof σ m' := Classical.choose_spec ⟨m, hf⟩
  let w := gsChooseMax prof σ m' hm'.2
  have hw : ¬ σ.proposed m' w := by
    have := gsChooseMax_mem prof σ m' hm'.2
    simp [gsCandidates] at this
    exact this
  exact stepWith prof σ m' w hw

/-- The number of proposals never exceeds `n²` for any state. -/
lemma le_bound (σ : GSState prof) :
    proposedCount prof σ ≤ gsProposalBound n := by
  classical
  unfold proposedCount proposedSet gsProposalBound
  calc (Finset.univ.filter fun mw => σ.proposed mw.1 mw.2).card
      ≤ (Finset.univ : Finset (Fin n × Fin n)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = n * n := by
        simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]

/-- At step `k`, the number of proposals never exceeds the bound. -/
lemma runSteps_le_bound (k : Nat) :
    proposedCount prof (gsRunSteps prof k) ≤ gsProposalBound n :=
  le_bound prof _

/-- If there is a free man, an additional step keeps the counter under the bound. -/
lemma step_preserves_le_bound {_σ : GSState prof}
    (_h : proposedCount prof _σ ≤ gsProposalBound n) :
    proposedCount prof (gsStep prof _σ) ≤ gsProposalBound n :=
    le_bound prof _

/-- If the algorithm has not terminated after `k` steps, the counter is `k`. -/
lemma runSteps_eq_of_not_terminated (k : Nat)
    (hterm : ¬ gsTerminated prof (gsRunSteps prof k)) :
    proposedCount prof (gsRunSteps prof k) = k := by
  induction k with
  | zero =>
    simp only [gsRunSteps]
    exact initial prof
  | succ k' ih =>
    simp only [gsRunSteps]
    have hnk : ¬ gsTerminated prof (gsRunSteps prof k') := by
      intro hk_term
      unfold gsTerminated at hk_term hterm
      simp only [gsRunSteps] at hterm
      unfold gsStep at hterm
      rw [dif_neg hk_term] at hterm
      exact hterm hk_term
    have ihk := ih hnk
    have hf : ∃ m, gsIsFree prof (gsRunSteps prof k') m := not_not.mp hnk
    rw [step_of_free prof (gsRunSteps prof k') (Classical.choose hf)
        (Classical.choose_spec hf), ihk]

end proposedCount

/-! ## Step identity when the algorithm has terminated -/

/-- If the current state is terminal, `gsStep` is the identity. -/
lemma gsStep_eq_of_terminated (prof : PrefProfile n) (σ : GSState prof)
    (h : gsTerminated prof σ) :
    gsStep prof σ = σ := by
  unfold gsStep gsTerminated at *
  split
  · contradiction
  · rfl

/-- If the algorithm has terminated at step `k`, all subsequent steps are the identity. -/
lemma gsRunSteps_eq_of_terminated (prof : PrefProfile n) (k j : Nat) (hkj : k ≤ j)
    (h : gsTerminated prof (gsRunSteps prof k)) :
    gsRunSteps prof j = gsRunSteps prof k := by
  induction j generalizing k with
  | zero =>
    have : k = 0 := Nat.eq_zero_of_le_zero hkj
    subst this; rfl
  | succ j' ih =>
    simp only [gsRunSteps]
    cases eq_or_lt_of_le hkj with
    | inl heq => subst heq; rfl
    | inr hlt =>
      rw [ih k (Nat.le_of_lt_succ hlt) h]
      exact gsStep_eq_of_terminated prof _ h

/-! ## Invariant - men propose in decreasing order of preference (step preservation) -/

namespace menProposedDownward

variable (prof : PrefProfile n) {σ : GSState prof}

/-- `gsStep` preserves the `menProposedDownward` invariant. -/
lemma step (h : menProposedDownward prof σ)
    (hfree : ∃ m, gsIsFree prof σ m) :
    menProposedDownward prof (gsStep prof σ) := by
  unfold gsStep
  rw [dif_pos hfree]
  let m₀ := Classical.choose hfree
  have hm₀ : gsIsFree prof σ m₀ := Classical.choose_spec hfree
  let w₀ := gsChooseMax prof σ m₀ hm₀.2
  have hw₀ : ¬ σ.proposed m₀ w₀ := by
    intro h
    have := gsChooseMax_mem prof σ m₀ hm₀.2
    simp [gsCandidates] at this
    exact this h
  -- Maximalité : `gsChooseMax` renvoie la candidate la plus préférée ; aucune candidate n'est davantage préférée
  have hmax : ∀ w', w' ∈ gsCandidates prof σ m₀ →
      gsMenPrefLE prof m₀ w₀ w' → w₀ = w' := by
    intro w' hw'in hle
    have hmax' := gsChooseMax_maximal prof σ m₀ hm₀.2 w' hw'in
    cases hle with
    | inl h => exact h
    | inr hlt =>
      cases hmax' with
      | inl h => exact h.symm
      | inr hgt => exact absurd hgt (lt_asymm hlt)
  intro m w w' hprop hlt
  have goal_from (hab : σ.proposed m w') :
      (gsStepWith prof σ m₀ w₀).proposed m w' :=
    (@proposedSet.mem_iff n _ prof (gsStepWith prof σ m₀ w₀) (m, w')).mp
      (by rw [proposedSet.stepWith_insert prof σ m₀ w₀]
          simp only [Finset.mem_insert, Prod.mk.injEq, proposedSet.mem_iff]
          right; exact hab)
  have hsrc : σ.proposed m w ∨ (m = m₀ ∧ w = w₀) := by
    have hmem := (@proposedSet.mem_iff n _ prof (gsStepWith prof σ m₀ w₀) (m, w)).mpr hprop
    rw [proposedSet.stepWith_insert prof σ m₀ w₀] at hmem
    simp only [Finset.mem_insert, Prod.mk.injEq, proposedSet.mem_iff] at hmem
    cases hmem with | inl h => right; exact h | inr h => left; exact h
  rcases hsrc with (hw | ⟨rfl, rfl⟩)
  · exact goal_from (h m w w' hw hlt)
  · have hw' : σ.proposed m₀ w' := by
      by_contra hn
      have hw'in : w' ∈ gsCandidates prof σ m₀ := by simp [gsCandidates]; exact hn
      have : w₀ = w' := hmax w' hw'in (Or.inr hlt)
      subst this; exact lt_irrefl _ hlt
    exact goal_from hw'

/-- `gsRunSteps` preserves the `menProposedDownward` invariant. -/
lemma runSteps (k : Nat) :
    menProposedDownward prof (gsRunSteps prof k) := by
  induction k with
  | zero =>
    simp only [gsRunSteps]
    intro m w w' hw hlt
    unfold gsInitial GSMatching.initial at hw
    simp at hw
  | succ k' ih =>
    simp only [gsRunSteps]
    by_cases h : ∃ m, gsIsFree prof (gsRunSteps prof k') m
    · exact step prof ih h
    · have hid : gsStep prof (gsRunSteps prof k') = gsRunSteps prof k' := by
        unfold gsStep; simp [h]
      rw [hid]; exact ih

end menProposedDownward

/-! ## Invariant - every matched man has proposed (step preservation) -/

namespace menMatchedProposed

variable (prof : PrefProfile n) {σ : GSState prof}

/-- `gsStepWith` preserves `menMatchedProposed`. -/
lemma stepWith (h : menMatchedProposed prof σ) (m w : Fin n) :
    menMatchedProposed prof (gsStepWith prof σ m w) := by
  intro m' w' hmatch
  simp only [gsStepWith] at hmatch ⊢
  split at *
  · -- Cas `none` : `matchFree m w`
    dsimp [GSMatching.matchFree] at hmatch ⊢
    rw [Function.update_apply] at hmatch
    split_ifs at hmatch
    · injection hmatch with hw; right; exact ⟨‹m' = m›, hw.symm⟩
    · left; exact h m' w' hmatch
  · -- Cas `some mOld`
    rename_i mOld
    split_ifs at *
    · -- La femme préfère `m` : `swapMatch m mOld w`
      dsimp [GSMatching.swapMatch] at hmatch ⊢
      rw [Function.update_apply, Function.update_apply] at hmatch
      split_ifs at hmatch
      · injection hmatch with hw; right; exact ⟨‹m' = m›, hw.symm⟩
      · left; exact h m' w' hmatch
    · -- Pas de préférence : couplage inchangé
      dsimp at hmatch ⊢
      left; exact h m' w' hmatch

/-- `gsStep` preserves `menMatchedProposed`. -/
lemma step (h : menMatchedProposed prof σ)
    (hfree : ∃ m, gsIsFree prof σ m) :
    menMatchedProposed prof (gsStep prof σ) := by
  unfold gsStep
  rw [dif_pos hfree]
  let m := Classical.choose hfree
  have hm : gsIsFree prof σ m := Classical.choose_spec hfree
  let w := gsChooseMax prof σ m hm.2
  exact stepWith prof h m w

/-- `gsRunSteps` preserves `menMatchedProposed`. -/
lemma runSteps (k : Nat) :
    menMatchedProposed prof (gsRunSteps prof k) := by
  induction k with
  | zero =>
    simp only [gsRunSteps]
    exact initial prof
  | succ k' ih =>
    simp only [gsRunSteps]
    by_cases h : ∃ m, gsIsFree prof (gsRunSteps prof k') m
    · exact step prof ih h
    · have hid : gsStep prof (gsRunSteps prof k') = gsRunSteps prof k' := by
        unfold gsStep; simp [h]
      rw [hid]; exact ih

end menMatchedProposed

/-! ## Invariant - every proposed woman is matched -/

/-- Si un homme a proposé à une femme, alors elle doit être appariée. -/
def womenProposedImpliesMatched (prof : PrefProfile n) (σ : GSState prof) : Prop :=
  ∀ w m, σ.proposed m w → σ.matching.womenMatch w ≠ none

namespace womenProposedImpliesMatched

variable (prof : PrefProfile n) {σ : GSState prof}

lemma initial : womenProposedImpliesMatched prof (gsInitial prof) := by
  intro w m hprop; unfold gsInitial at hprop; simp at hprop

lemma stepWith (h : womenProposedImpliesMatched prof σ) (m₀ w₀ : Fin n)
    (hnew : ¬ σ.proposed m₀ w₀) :
    womenProposedImpliesMatched prof (gsStepWith prof σ m₀ w₀) := by
  intro w m' hprop
  have hmem := (@proposedSet.mem_iff n _ prof (gsStepWith prof σ m₀ w₀) (m', w)).mpr hprop
  rw [proposedSet.stepWith_insert prof σ m₀ w₀] at hmem
  simp only [Finset.mem_insert, Prod.mk.injEq] at hmem
  simp only [gsStepWith]
  split
  · dsimp [GSMatching.matchFree]
    rw [Function.update_apply]
    by_cases hw : w = w₀
    · rw [if_pos hw]; simp
    · rw [if_neg hw]
      rcases hmem with ⟨⟨rfl, rfl⟩⟩ | hold
      · exact absurd rfl hw
      · exact h w m' ((@proposedSet.mem_iff n _ prof σ (m', w)).mp hold)
  · split
    · next mOld hmold hpref =>
      dsimp [GSMatching.swapMatch]
      rw [Function.update_apply]
      by_cases hw : w = w₀
      · rw [if_pos hw]; simp
      · rw [if_neg hw]
        rcases hmem with ⟨⟨rfl, rfl⟩⟩ | hold
        · exact absurd rfl hw
        · exact h w m' ((@proposedSet.mem_iff n _ prof σ (m', w)).mp hold)
    · next mOld hmold hpref =>
      rcases hmem with ⟨⟨rfl, rfl⟩⟩ | hold
      · simp [hmold]
      · exact h w m' ((@proposedSet.mem_iff n _ prof σ (m', w)).mp hold)

lemma step (h : womenProposedImpliesMatched prof σ)
    (hfree : ∃ m, gsIsFree prof σ m) :
    womenProposedImpliesMatched prof (gsStep prof σ) := by
  unfold gsStep; rw [dif_pos hfree]
  let m := Classical.choose hfree
  have hm : gsIsFree prof σ m := Classical.choose_spec hfree
  let w := gsChooseMax prof σ m hm.2
  have hw : ¬ σ.proposed m w := by
    have := gsChooseMax_mem prof σ m hm.2; simp [gsCandidates] at this; exact this
  exact stepWith prof h m w hw

lemma runSteps (k : Nat) :
    womenProposedImpliesMatched prof (gsRunSteps prof k) := by
  induction k with
  | zero => simp only [gsRunSteps]; exact initial prof
  | succ k' ih =>
    simp only [gsRunSteps]
    by_cases h : ∃ m, gsIsFree prof (gsRunSteps prof k') m
    · exact step prof ih h
    · have hid : gsStep prof (gsRunSteps prof k') = gsRunSteps prof k' := by
        unfold gsStep; simp [h]
      rw [hid]; exact ih

end womenProposedImpliesMatched

/-! ## Invariant - best match for each woman (step preservation) -/

/-- Si une femme est libre et que `womenProposedImpliesMatched` est vrai,
    alors aucun homme ne lui a encore proposé (contraposée). -/
lemma womenUnproposed (prof : PrefProfile n) (σ : GSState prof)
    (h : womenBestState prof σ)
    (hwp : womenProposedImpliesMatched prof σ)
    (hfree : ∃ m, gsIsFree prof σ m) :
    ∀ w, σ.matching.womenMatch w = none → ∀ m', ¬σ.proposed m' w := by
  intro w hw m' hprop
  exact (hwp w m' hprop) hw

namespace womenBestState

variable (prof : PrefProfile n) {σ : GSState prof}

/-- `gsStep` preserves `womenBestState`. -/
lemma step (h : womenBestState prof σ)
    (hwp : womenProposedImpliesMatched prof σ)
    (hfree : ∃ m, gsIsFree prof σ m) :
    womenBestState prof (gsStep prof σ) := by
  unfold gsStep; rw [dif_pos hfree]
  set m₀ := Classical.choose hfree
  have hm₀ : gsIsFree prof σ m₀ := Classical.choose_spec hfree
  set w₀ := gsChooseMax prof σ m₀ hm₀.2
  unfold womenBestState
  intro w m m' hmatch hprop
  have hsrc : σ.proposed m' w ∨ (m' = m₀ ∧ w = w₀) := by
    have hmem := (@proposedSet.mem_iff n _ prof (gsStepWith prof σ m₀ w₀) (m', w)).mpr hprop
    rw [proposedSet.stepWith_insert prof σ m₀ w₀] at hmem
    simp only [Finset.mem_insert, Prod.mk.injEq, proposedSet.mem_iff] at hmem
    cases hmem with | inl h => right; exact h | inr h => left; exact h
  -- Réduire le couplage de `gsStepWith` et découper sur le discriminant
  change (gsStepWith prof σ m₀ w₀).matching.womenMatch w = some m at hmatch
  simp only [gsStepWith] at hmatch
  split at hmatch
  · -- Cas `none` : `matchFree`
    dsimp [GSMatching.matchFree] at hmatch
    rw [Function.update_apply] at hmatch
    by_cases hw : w = w₀
    · rw [if_pos hw] at hmatch
      injection hmatch with hmi; subst hmi
      rcases hsrc with (hw' | ⟨rfl, rfl⟩)
      · exfalso
        have hn := ‹σ.matching.womenMatch w₀ = none›
        exact womenUnproposed prof σ h hwp hfree w₀ hn m' (hw ▸ hw')
      · exact le_rfl
    · rw [if_neg hw] at hmatch
      rcases hsrc with (hw' | ⟨rfl, rfl⟩)
      · exact h w m m' hmatch hw'
      · exfalso; exact hw rfl
  · -- Cas `some mOld`
    next mOld hmold =>
    by_cases hpref : prof.womenPref w₀ m₀ < prof.womenPref w₀ mOld
    · rw [if_pos hpref] at hmatch
      dsimp [GSMatching.swapMatch] at hmatch
      rw [Function.update_apply] at hmatch
      by_cases hw : w = w₀
      · rw [if_pos hw] at hmatch
        injection hmatch with hmi; subst hmi
        rcases hsrc with (hw' | ⟨rfl, rfl⟩)
        · subst hw
          have hold := h w₀ mOld m' hmold hw'
          exact le_trans (le_of_lt hpref) hold
        · exact le_rfl
      · rw [if_neg hw] at hmatch
        rcases hsrc with (hw' | ⟨rfl, rfl⟩)
        · exact h w m m' hmatch hw'
        · exfalso; exact hw rfl
    · rw [if_neg hpref] at hmatch
      rcases hsrc with (hw' | ⟨rfl, rfl⟩)
      · by_cases hw : w = w₀
        · subst hw; exact h w₀ m m' hmatch hw'
        · exact h w m m' hmatch hw'
      · rw [hmatch] at hmold
        injection hmold with heq; subst heq
        exact by omega

/-- `gsRunSteps` preserves `womenBestState`. -/
lemma runSteps (k : Nat) :
    womenBestState prof (gsRunSteps prof k) := by
  induction k with
  | zero =>
    simp only [gsRunSteps]
    exact initial prof
  | succ k' ih =>
    simp only [gsRunSteps]
    by_cases h : ∃ m, gsIsFree prof (gsRunSteps prof k') m
    · exact step prof ih (womenProposedImpliesMatched.runSteps prof k') h
    · have hid : gsStep prof (gsRunSteps prof k') = gsRunSteps prof k' := by
        unfold gsStep; simp [h]
      rw [hid]; exact ih

end womenBestState

/-! ## Termination: the algorithm terminates in at most n^2 steps -/

lemma gsTerminated_runSteps_bound (prof : PrefProfile n) :
    gsTerminated prof (gsRunSteps prof (gsProposalBound n)) := by
  classical
  by_contra hnot
  have ⟨m, hm⟩ : ∃ m, gsIsFree prof (gsRunSteps prof (gsProposalBound n)) m := by
    simpa [gsTerminated] using hnot
  set σ := gsRunSteps prof (gsProposalBound n)
  have hmcand : (gsCandidates prof σ m).Nonempty := hm.2
  set w := gsChooseMax prof σ m hmcand
  have hw : ¬ σ.proposed m w := by
    have := gsChooseMax_mem prof σ m hmcand
    simp [gsCandidates] at this; exact this
  have hcount : proposedCount prof σ = gsProposalBound n :=
    proposedCount.runSteps_eq_of_not_terminated prof (gsProposalBound n) hnot
  have hss : proposedSet prof σ ⊆ (Finset.univ : Finset (Fin n × Fin n)) :=
    Finset.filter_subset _ _
  have huniv : (Finset.univ : Finset (Fin n × Fin n)).card = n * n := by
    simp [Fintype.card_prod, Fintype.card_fin]
  have hcount_card : (proposedSet prof σ).card = n * n := by
    unfold proposedCount at hcount; simp [gsProposalBound] at hcount; exact hcount
  have heq : proposedSet prof σ = Finset.univ :=
    Finset.eq_of_subset_of_card_le hss (by rw [huniv]; exact hcount_card.ge)
  exact hw ((proposedSet.mem_iff prof (m, w)).1 (heq ▸ Finset.mem_univ _))

/-- Lorsque GS a terminé, chaque homme est apparié (`menMatch m ≠ none`).
    Si un homme était libre, `gsCandidates` devrait être vide (sans quoi il serait
    libre lui aussi), donc il aurait proposé à toutes les femmes. Par
    `womenProposedImpliesMatched`, toutes les femmes seraient alors appariées via
    d'autres hommes. Mais cohérence + `n` femmes appariées par `n-1` autres hommes
    est impossible sur `Fin n`. -/
lemma gsTerminated_allMenMatched (prof : PrefProfile n) {σ : GSState prof}
    (hterm : gsTerminated prof σ)
    (hwp : womenProposedImpliesMatched prof σ)
    (hcon : GSConsistent σ.matching)
    (m : Fin n) :
    σ.matching.menMatch m ≠ none := by
  intro hnone
  have hcand_empty : (gsCandidates prof σ m).Nonempty → False := by
    intro hne; exact hterm ⟨m, ⟨hnone, hne⟩⟩
  have hpropAll : ∀ w, σ.proposed m w := by
    intro w
    by_contra hnot
    exact hcand_empty ⟨w, by simp [gsCandidates, hnot]⟩
  have hwMatched : ∀ w, σ.matching.womenMatch w ≠ none :=
    fun w => hwp w m (hpropAll w)
  have hex (w : Fin n) : ∃ m', σ.matching.womenMatch w = some m' ∧ σ.matching.menMatch m' = some w := by
    obtain ⟨m', hm'⟩ := Option.ne_none_iff_exists.mp (hwMatched w)
    have hwf : σ.matching.womenMatch w = some m' := hm'.symm
    exact ⟨m', hwf, (hcon m' w).mpr hwf⟩
  -- Construire une injection `f : Fin n → {m' : Fin n // m' ≠ m}`, puis déduire la contradiction
  have hSpec (w : Fin n) :
      σ.matching.womenMatch w = some (Classical.choose (hex w)) ∧
      σ.matching.menMatch (Classical.choose (hex w)) = some w :=
    Classical.choose_spec (hex w)
  have fne (w : Fin n) : Classical.choose (hex w) ≠ m := by
    intro heq
    have h := (hSpec w).2
    rw [heq, hnone] at h
    cases h
  let f (w : Fin n) : { m' : Fin n // m' ≠ m } :=
    ⟨Classical.choose (hex w), fne w⟩
  have hf : Function.Injective f := by
    intro w₁ w₂ heq
    have h1 := (hSpec w₁).2
    have h2 := (hSpec w₂).2
    have hval : Classical.choose (hex w₁) = Classical.choose (hex w₂) :=
      congrArg Subtype.val heq
    congr 1
    have := congrArg (σ.matching.menMatch ·) hval
    simp only [h1, h2, Option.some.injEq] at this
    exact this
  -- `|{m' ≠ m}| < |Fin n|` contredit l'injection `Fin n → {m' ≠ m}`
  have hle := Fintype.card_le_of_injective f hf
  have hcard_fin : Fintype.card (Fin n) = n := Fintype.card_fin n
  -- Contradiction : `Fin n` s'injecte dans `{m' ≠ m}` mais `{m' ≠ m} ⊂ Fin n`
  have hcontra : Fintype.card (Fin n) ≤ Fintype.card { m' : Fin n // m' ≠ m } :=
    Fintype.card_le_of_injective f hf
  have hlt : Fintype.card { m' : Fin n // m' ≠ m } < Fintype.card (Fin n) :=
    @Fintype.card_lt_of_injective_of_notMem _ _ _ _
      (Subtype.val : {m' : Fin n // m' ≠ m} → Fin n)
      Subtype.coe_injective m
      (by simp)
  omega

/-! ## Conversion of the final GS matching -/

/-- Extraire l'épouse d'un `GSMatching` via `Classical.choose` (évite les problèmes de typage de `Option.get`). -/
noncomputable def gsSpouse (μ : GSMatching n)
    (hall : ∀ m, μ.menMatch m ≠ none) (m : Fin n) : Fin n :=
  Classical.choose (Option.ne_none_iff_exists.mp (hall m))

lemma gsSpouse_spec (μ : GSMatching n)
    (hall : ∀ m, μ.menMatch m ≠ none) (m : Fin n) :
    μ.menMatch m = some (gsSpouse μ hall m) :=
  (Classical.choose_spec (Option.ne_none_iff_exists.mp (hall m))).symm

/-- Toutes les femmes sont appariées dès que tous les hommes sont appariés et que le couplage est cohérent. -/
lemma gsAllWomenMatched {μ : GSMatching n}
    (hall : ∀ m, μ.menMatch m ≠ none)
    (hcon : GSConsistent μ) (w : Fin n) :
    μ.womenMatch w ≠ none := by
  by_contra hnone
  have hNoMan : ∀ m, μ.menMatch m ≠ some w := by
    intro m hmw; have := hcon m w |>.mp hmw; rw [hnone] at this; simp at this
  -- Chaque homme est associé à un certain `w' ≠ w`, injectivement → contradiction par pigeonhole
  have hMap (m : Fin n) : ∃ w', μ.menMatch m = some w' ∧ w' ≠ w := by
    obtain ⟨w', hw'⟩ := Option.ne_none_iff_exists.mp (hall m)
    exact ⟨w', hw'.symm, fun heq => hNoMan m (heq ▸ hw'.symm)⟩
  let f (m : Fin n) : {w' : Fin n // w' ≠ w} :=
    ⟨Classical.choose (hMap m), (Classical.choose_spec (hMap m)).2⟩
  have hf : Injective f := by
    intro m₁ m₂ heq
    simp only [f, Subtype.mk.injEq] at heq
    have h₁ := (Classical.choose_spec (hMap m₁)).1
    have h₂ := (Classical.choose_spec (hMap m₂)).1
    rw [heq] at h₁
    -- h₁ : μ.menMatch m₁ = some c  (où `c = Classical.choose (hMap m₂)`)
    -- h₂ : μ.menMatch m₂ = some c
    have hw₁ := hcon m₁ (Classical.choose (hMap m₂)) |>.mp h₁
    have hw₂ := hcon m₂ (Classical.choose (hMap m₂)) |>.mp h₂
    -- hw₁ : μ.womenMatch c = some m₁
    -- hw₂ : μ.womenMatch c = some m₂
    exact Option.some.inj (hw₁.symm.trans hw₂)
  have hle : Fintype.card (Fin n) ≤ Fintype.card {w' : Fin n // w' ≠ w} :=
    Fintype.card_le_of_injective f hf
  have hlt : Fintype.card {w' : Fin n // w' ≠ w} < Fintype.card (Fin n) :=
    @Fintype.card_lt_of_injective_of_notMem _ _ _ _
      (Subtype.val : {w' : Fin n // w' ≠ w} → Fin n) Subtype.coe_injective w (by simp)
  omega

/-- Construire un `Matching` total à partir d'un `GSMatching` terminé. -/
noncomputable def gsFinalMatching (prof : PrefProfile n)
    (σ : GSState prof)
    (hall : ∀ m, σ.matching.menMatch m ≠ none)
    (hcon : GSConsistent σ.matching) : Matching n where
  spouse := gsSpouse σ.matching hall
  bijective := by
    constructor
    · -- injectif : `spouse m₁ = spouse m₂` → `m₁ = m₂`
      intro m₁ m₂ heq
      have h₁ := gsSpouse_spec σ.matching hall m₁
      have h₂ := gsSpouse_spec σ.matching hall m₂
      rw [heq] at h₁
      -- h₁ : σ.matching.menMatch m₁ = some (gsSpouse σ.matching hall m₂)
      -- h₂ : σ.matching.menMatch m₂ = some (gsSpouse σ.matching hall m₂)
      have hw₁ := hcon m₁ (gsSpouse σ.matching hall m₂) |>.mp h₁
      have hw₂ := hcon m₂ (gsSpouse σ.matching hall m₂) |>.mp h₂
      -- hw₁ : σ.matching.womenMatch _ = some m₁
      -- hw₂ : σ.matching.womenMatch _ = some m₂
      exact Option.some.inj (hw₁.symm.trans hw₂)
    · -- surjectif : pour chaque `w`, trouver `m` avec `spouse m = w`
      intro w
      have hwn := gsAllWomenMatched hall hcon w
      obtain ⟨m, hm⟩ := Option.ne_none_iff_exists.mp hwn
      have hmw : σ.matching.menMatch m = some w := (hcon m w).mpr hm.symm
      exact ⟨m, by
        have hspec := gsSpouse_spec σ.matching hall m
        -- hspec : σ.matching.menMatch m = some (gsSpouse σ.matching hall m)
        rw [hmw] at hspec
        -- hspec : some w = some (gsSpouse σ.matching hall m)
        exact Option.some.inj hspec.symm⟩

/-- Lemme clé : `gsFinalMatching.spouse m` extrait directement la valeur de l'`Option`. -/
lemma gsFinalMatching_spouse_get (prof : PrefProfile n) (σ : GSState prof)
    (hall : ∀ m, σ.matching.menMatch m ≠ none)
    (hcon : GSConsistent σ.matching) (m : Fin n) :
    (gsFinalMatching prof σ hall hcon).spouse m =
      Classical.choose (Option.ne_none_iff_exists.mp (hall m)) := rfl

/-! ## Absence of blocking pairs (adapted from `Properties.lean` upstream L48-120) -/

/-- L'état final de GS ne comporte aucune paire bloquante.

    Structure de la preuve (adaptée de `Properties.lean galeShapley_noBlockingPairs` du dépôt mmaaz-git) :
    1. Supposer une paire bloquante `(m, w)` : `m` préfère `w` à son épouse, `w` préfère `m` à son époux
    2. Montrer que `m` a proposé à `w` (`menProposedDownward` + `menMatchedProposed`)
    3. `w` est appariée à `mW` (`womenProposedImpliesMatched`)
    4. `womenBestState` donne : `womenPref w mW ≤ womenPref w m`
    5. La condition de blocage donne : `womenPref w m < womenPref w mW`
    6. Contradiction (`≤` et `<` sont incompatibles)

    Simplification par rapport à l'upstream : pas de branche « `w` est libre » (préférences totales).
-/
lemma gsNoBlockingPairs (prof : PrefProfile n)
    (hterm : gsTerminated prof (gsRunSteps prof (gsProposalBound n)))
    (hcon : GSConsistent (gsRunSteps prof (gsProposalBound n)).matching)
    (hwp : womenProposedImpliesMatched prof (gsRunSteps prof (gsProposalBound n)))
    (hdown : menProposedDownward prof (gsRunSteps prof (gsProposalBound n)))
    (hmatch_prop : menMatchedProposed prof (gsRunSteps prof (gsProposalBound n)))
    (hbest : womenBestState prof (gsRunSteps prof (gsProposalBound n)))
    (m w : Fin n) :
    ¬ IsBlockingPair prof (gsFinalMatching prof (gsRunSteps prof (gsProposalBound n))
      (fun m => gsTerminated_allMenMatched prof hterm hwp hcon m) hcon) m w := by
  intro hblock
  obtain ⟨hmpref, hwpref⟩ := hblock
  set σ := gsRunSteps prof (gsProposalBound n)
  set hall : ∀ m, σ.matching.menMatch m ≠ none :=
    fun m => gsTerminated_allMenMatched prof hterm hwp hcon m
  set μ := gsFinalMatching prof σ hall hcon
  -- Étape 1 : `m` est apparié, extraire sa partenaire `wMatch`
  have hwMatch' : σ.matching.menMatch m = some (μ.spouse m) :=
    gsSpouse_spec σ.matching hall m
  -- Étape 2 : `m` a proposé à sa partenaire (`μ.spouse m`)
  have hpropMatch : σ.proposed m (μ.spouse m) :=
    hmatch_prop m (μ.spouse m) hwMatch'
  -- Étape 3 : `m` a proposé à `w` (clôture décroissante)
  -- Le blocage dit que `menPref m w < menPref m (μ.spouse m)`, donc `w` est préférée
  have hpropw : σ.proposed m w :=
    hdown m (μ.spouse m) w hpropMatch hmpref
  -- Étape 4 : `w` est appariée (`womenProposedImpliesMatched`)
  have hwomMatch : σ.matching.womenMatch w ≠ none := hwp w m hpropw
  obtain ⟨mW, hmW⟩ := Option.ne_none_iff_exists.mp hwomMatch
  have hmW' : σ.matching.womenMatch w = some mW := hmW.symm
  -- Étape 5 : `womenBestState` donne `womenPref w mW ≤ womenPref w m`
  have hbest' : prof.womenPref w mW ≤ prof.womenPref w m :=
    hbest w mW m hmW' hpropw
  -- Étape 6 : `μ.inverse w = mW`
  -- Par cohérence : `menMatch mW = some w`, donc `spouse mW = w`
  have hmw' : σ.matching.menMatch mW = some w := (hcon mW w).mpr hmW'
  have hspouse_mW : μ.spouse mW = w := by
    have h₁ := gsSpouse_spec σ.matching hall mW
    -- h₁ : `menMatch mW = some (gsSpouse ...)` et `hmw'` : `menMatch mW = some w`
    exact Option.some.inj (h₁.symm.trans hmw')
  -- `inverse w = mW` car `spouse mW = w`
  have hwinv : μ.inverse w = mW := by
    unfold Matching.inverse
    rw [← hspouse_mW]
    exact Equiv.ofBijective_symm_apply_apply (gsSpouse σ.matching hall) _ mW
  rw [hwinv] at hwpref
  -- `hwpref` : `womenPref w m < womenPref w mW`
  -- `hbest'` : `womenPref w mW ≤ womenPref w m`
  -- Contradiction : `hbest'` dit `womenPref w mW ≤ womenPref w m`
  -- mais `hwpref` dit `womenPref w m < womenPref w mW`
  -- c'est-à-dire : `a ≤ b` et `b < a` est impossible
  have : (prof.womenPref w mW : Nat) ≤ (prof.womenPref w m : Nat) := by
    exact mod_cast hbest'
  have : (prof.womenPref w m : Nat) < (prof.womenPref w mW : Nat) := by
    exact mod_cast hwpref
  omega

end StableMarriage_en
