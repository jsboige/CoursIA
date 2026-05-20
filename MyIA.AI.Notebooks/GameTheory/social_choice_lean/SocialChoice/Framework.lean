/-
  Social Choice Framework — Shared Abstractions
  ==============================================

  Common definitions for social choice theory: preference profiles,
  social welfare functions, Arrow's axioms, and preference manipulation
  helpers. Extracted from Arrow.lean so that Sen.lean and Voting.lean
  can import these without depending on Arrow's proof machinery.

  Reference: Amartya Sen, "Collective Choice and Social Welfare" (1970)
  Reference: John Geanakoplos, "Three Brief Proofs of Arrow's Impossibility Theorem" (2005)
-/

import SocialChoice.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

variable {ι : Type*} {σ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq σ]

/-! ## Preference Profiles and Social Welfare Functions -/

/-- A preference profile assigns a preference order to each individual -/
def Profile (ι σ : Type*) := ι → PrefOrder σ

/-- A social welfare function maps profiles to social preferences -/
def SWF (ι σ : Type*) := Profile ι σ → PrefOrder σ

/-! ## Arrow's Axioms -/

/-- Weak Pareto: If everyone strictly prefers x to y, so does society -/
def weak_pareto (f : SWF ι σ) (X : Finset σ) : Prop :=
  ∀ prof : Profile ι σ, ∀ x y : σ, x ∈ X → y ∈ X →
    (∀ i : ι, P (prof i).rel x y) → P (f prof).rel x y

/-- Independence of Irrelevant Alternatives (IIA) -/
def ind_of_irr_alts (f : SWF ι σ) (X : Finset σ) : Prop :=
  ∀ prof prof' : Profile ι σ, ∀ x y : σ, x ∈ X → y ∈ X →
    (∀ i : ι, same_order' (prof i).rel (prof' i).rel x y x y) →
    same_order' (f prof).rel (f prof').rel x y x y

/-- Individual d is a dictator over pair (x, y) -/
def is_dictator_on (f : SWF ι σ) (d : ι) (x y : σ) : Prop :=
  ∀ prof : Profile ι σ, P (prof d).rel x y → P (f prof).rel x y

/-- Individual d is a dictator over all pairs in X -/
def is_dictatorship (f : SWF ι σ) (X : Finset σ) : Prop :=
  ∃ d : ι, ∀ x y : σ, x ∈ X → y ∈ X → x ≠ y → is_dictator_on f d x y

/-! ## Preference Profile Manipulation

Inspired by ChihChengLiang/arrow's `prefer_ifs` technique:
extract `rel` into named functions so `unfold` + `split_ifs` works in proofs.
-/

/-- Rel helper for maketop: b at top, original ordering preserved elsewhere -/
def maketop_rel (R : σ → σ → Prop) (b : σ) (x y : σ) : Prop :=
  if x = b then True else if y = b then False else R x y

/-- Rel helper for makebot: b at bottom, original ordering preserved elsewhere -/
def makebot_rel (R : σ → σ → Prop) (b : σ) (x y : σ) : Prop :=
  if y = b then True else if x = b then False else R x y

/-- Rel helper for makeabove: places b directly above a, preserving order elsewhere.
    Port of asouther4's makeabove — transitive for all PrefOrders.
    Logic: b is placed just above a (if r a y then b > y, if r a x then x > b).
    Uses [DecidableEq σ] for the outer ifs and Classical.dec for R comparisons. -/
def makeabove_rel (R : σ → σ → Prop) (a b : σ) (x y : σ) : Prop :=
  if x = b then (if y = b then True else @ite _ _ (Classical.dec (R a y)) True False)
  else if y = b then @ite _ _ (Classical.dec (R a x)) False True
  else R x y

/-- PrefOrder reverse: if ¬R x y then R y x (from totality) -/
lemma PrefOrder.rel_rev {r : PrefOrder σ} {x y : σ} (h : ¬r.rel x y) : r.rel y x :=
  (r.total x y).resolve_left h

/-- Make b the top-ranked alternative for individual i -/
noncomputable def maketop (prof : Profile ι σ) (i : ι) (b : σ) (X : Finset σ)
    (hb : b ∈ X) : Profile ι σ :=
  fun j => if j = i then
    { rel := maketop_rel (prof i).rel b
      refl := by
        intro x; simp only [maketop_rel]; split_ifs
        all_goals first | trivial | contradiction | exact (prof i).refl x
      total := by
        intro x y; simp only [maketop_rel]; split_ifs
        all_goals first | left; trivial | right; trivial | contradiction
                         | exact (prof i).total x y
      trans := by
        intro x y z hxy hyz; simp only [maketop_rel] at hxy hyz ⊢; split_ifs at hxy hyz ⊢
        all_goals first | trivial | contradiction | exact (prof i).trans hxy hyz
    }
  else prof j

/-- Make b the bottom-ranked alternative for individual i -/
noncomputable def makebot (prof : Profile ι σ) (i : ι) (b : σ) (X : Finset σ)
    (hb : b ∈ X) : Profile ι σ :=
  fun j => if j = i then
    { rel := makebot_rel (prof i).rel b
      refl := by
        intro x; simp only [makebot_rel]; split_ifs
        all_goals first | trivial | contradiction | exact (prof i).refl x
      total := by
        intro x y; simp only [makebot_rel]; split_ifs
        all_goals first | left; trivial | right; trivial | contradiction
                         | exact (prof i).total x y
      trans := by
        intro x y z hxy hyz; simp only [makebot_rel] at hxy hyz ⊢; split_ifs at hxy hyz ⊢
        all_goals first | trivial | contradiction | exact (prof i).trans hxy hyz
    }
  else prof j

/-- Make b directly above a for individual i (port of asouther4's makeabove) -/
noncomputable def makeabove (prof : Profile ι σ) (i : ι) (a b : σ) : Profile ι σ :=
  fun j => if j = i then
    { rel := makeabove_rel (prof i).rel a b
      refl := by
        intro x; simp only [makeabove_rel]; split_ifs
        all_goals first | trivial | contradiction | exact (prof i).refl x
      total := by
        intro x y; simp only [makeabove_rel]; split_ifs <;> (
          first | left; trivial | right; trivial | contradiction
                  | exact (prof i).total x y
                  | left; exact (prof i).rel_rev (id (by assumption : ¬(prof i).rel a y))
                  | right; exact (prof i).rel_rev (id (by assumption : ¬(prof i).rel a x))
        )
      trans := by
        intro x y z hxy hyz; simp only [makeabove_rel] at hxy hyz ⊢
        split_ifs at hxy hyz ⊢ <;> (
          first | trivial
                 | contradiction
                 | exact (prof i).trans hxy hyz
                 | exact absurd hxy (by assumption)
                 | exact absurd hyz (by assumption)
                 | exact absurd (by assumption : (prof i).rel a y) (by assumption)
                 | exact (prof i).trans (by assumption : (prof i).rel a y) hyz
                 | exact (prof i).trans hxy (by assumption : (prof i).rel a z)
                 | exact (prof i).trans (by assumption : (prof i).rel a y)
                     (by assumption : (prof i).rel a z)
                 | exact (prof i).trans (PrefOrder.rel_rev (by assumption))
                     (by assumption : (prof i).rel a z)
                 | exact (prof i).trans (by assumption : (prof i).rel a y)
                     (PrefOrder.rel_rev (by assumption))
                 | exact absurd ((prof i).trans (by assumption : (prof i).rel a y) hyz)
                     (by assumption : ¬(prof i).rel a z)
                 | exact absurd ((prof i).trans (by assumption : (prof i).rel a x) hxy)
                     (by assumption : ¬(prof i).rel a y)
                 | contradiction
        )
    }
  else prof j

/-- Makeabove parameterized by a PrefOrder (instead of a profile + individual).
    Used to construct makeabove_all where ALL individuals are modified. -/
noncomputable def makeabove_pref (r : PrefOrder σ) (a b : σ) : PrefOrder σ :=
  { rel := makeabove_rel r.rel a b
    refl := by
      intro x; simp only [makeabove_rel]; split_ifs
      all_goals first | trivial | contradiction | exact r.refl x
    total := by
      intro x y; simp only [makeabove_rel]; split_ifs <;> (
        first | left; trivial | right; trivial | contradiction
                | exact r.total x y
                | left; exact r.rel_rev (id (by assumption : ¬r.rel a y))
                | right; exact r.rel_rev (id (by assumption : ¬r.rel a x))
      )
    trans := by
      intro x y z hxy hyz; simp only [makeabove_rel] at hxy hyz ⊢
      split_ifs at hxy hyz ⊢ <;> (
        first | trivial
               | contradiction
               | exact r.trans hxy hyz
               | exact absurd hxy (by assumption)
               | exact absurd hyz (by assumption)
               | exact absurd (by assumption : r.rel a y) (by assumption)
               | exact r.trans (by assumption : r.rel a y) hyz
               | exact r.trans hxy (by assumption : r.rel a z)
               | exact r.trans (by assumption : r.rel a y) (by assumption : r.rel a z)
               | exact r.trans (r.rel_rev (by assumption)) (by assumption : r.rel a z)
               | exact r.trans (by assumption : r.rel a y) (r.rel_rev (by assumption))
               | exact absurd (r.trans (by assumption : r.rel a y) hyz)
                   (by assumption : ¬r.rel a z)
               | exact absurd (r.trans (by assumption : r.rel a x) hxy)
                   (by assumption : ¬r.rel a y)
               | contradiction
      )
  }

/-- Maketop parameterized by a PrefOrder. -/
noncomputable def maketop_pref (r : PrefOrder σ) (b : σ) : PrefOrder σ :=
  { rel := maketop_rel r.rel b
    refl := by
      intro x; simp only [maketop_rel]; split_ifs
      all_goals first | trivial | contradiction | exact r.refl x
    total := by
      intro x y; simp only [maketop_rel]; split_ifs
      all_goals first | left; trivial | right; trivial | contradiction | exact r.total x y
    trans := by
      intro x y z hxy hyz; simp only [maketop_rel] at hxy hyz ⊢; split_ifs at hxy hyz ⊢
      all_goals first | trivial | contradiction | exact r.trans hxy hyz
  }

/-- Makebot parameterized by a PrefOrder. -/
noncomputable def makebot_pref (r : PrefOrder σ) (b : σ) : PrefOrder σ :=
  { rel := makebot_rel r.rel b
    refl := by
      intro x; simp only [makebot_rel]; split_ifs
      all_goals first | trivial | contradiction | exact r.refl x
    total := by
      intro x y; simp only [makebot_rel]; split_ifs
      all_goals first | left; trivial | right; trivial | contradiction | exact r.total x y
    trans := by
      intro x y z hxy hyz; simp only [makebot_rel] at hxy hyz ⊢; split_ifs at hxy hyz ⊢
      all_goals first | trivial | contradiction | exact r.trans hxy hyz
  }

/-- Profile where ALL individuals place b directly above a (makeabove for everyone) -/
noncomputable def makeabove_all (prof : Profile ι σ) (a b : σ) : Profile ι σ :=
  fun j => makeabove_pref (prof j) a b

/-! ## Preservation Lemmas for Profile Manipulation

When maketop/makebot/makeabove modify an individual's ranking, pairs not involving b
are preserved. These lemmas are essential for IIA arguments.
-/

lemma maketop_rel_noteq {R : σ → σ → Prop} {a b c : σ}
    (hab : a ≠ b) (hcb : c ≠ b) :
    (maketop_rel R b a c ↔ R a c) ∧ (maketop_rel R b c a ↔ R c a) := by
  unfold maketop_rel; simp [hab, hcb]

lemma makebot_rel_noteq {R : σ → σ → Prop} {a b c : σ}
    (hab : a ≠ b) (hcb : c ≠ b) :
    (makebot_rel R b a c ↔ R a c) ∧ (makebot_rel R b c a ↔ R c a) := by
  unfold makebot_rel; simp [hab, hcb]

lemma makeabove_rel_noteq (R : σ → σ → Prop) (a : σ) {b c d : σ}
    (hcb : c ≠ b) (hdb : d ≠ b) :
    (makeabove_rel R a b c d ↔ R c d) ∧ (makeabove_rel R a b d c ↔ R d c) := by
  unfold makeabove_rel; simp [hcb, hdb]


/-- PrefOrder: if R a x then ¬(¬R a x) -/
lemma PrefOrder.rel_of_not_not {r : PrefOrder σ} {x y : σ} (h : r.rel x y) : ¬¬r.rel x y :=
  fun hn => hn h

/-- Extract _noteq' variants that give P equivalences -/
lemma maketop_rel_noteq_P (R : σ → σ → Prop) {a b c : σ}
    (hab : a ≠ b) (hcb : c ≠ b) :
    (P (maketop_rel R b) a c ↔ P R a c) ∧ (P (maketop_rel R b) c a ↔ P R c a) := by
  have h := maketop_rel_noteq (R := R) hab hcb
  have h2 := maketop_rel_noteq (R := R) hcb hab
  simp only [P, h.1, h.2, h2.1, h2.2, true_and]

lemma makebot_rel_noteq_P (R : σ → σ → Prop) {a b c : σ}
    (hab : a ≠ b) (hcb : c ≠ b) :
    (P (makebot_rel R b) a c ↔ P R a c) ∧ (P (makebot_rel R b) c a ↔ P R c a) := by
  have h := makebot_rel_noteq (R := R) hab hcb
  have h2 := makebot_rel_noteq (R := R) hcb hab
  simp only [P, h.1, h.2, h2.1, h2.2, true_and]

lemma makeabove_rel_noteq_P (R : σ → σ → Prop) (a : σ) {b c d : σ}
    (hcb : c ≠ b) (hdb : d ≠ b) :
    (P (makeabove_rel R a b) c d ↔ P R c d) ∧ (P (makeabove_rel R a b) d c ↔ P R d c) := by
  have h := makeabove_rel_noteq R a hcb hdb
  have h2 := makeabove_rel_noteq R a hdb hcb
  simp only [P, h.1, h.2, h2.1, h2.2, true_and]
