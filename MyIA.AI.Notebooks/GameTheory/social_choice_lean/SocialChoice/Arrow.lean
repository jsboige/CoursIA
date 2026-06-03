/-
  Arrow's Impossibility Theorem
  =============================

  Port of asouther4/lean-social-choice to Lean 4
  Original: https://github.com/asouther4/lean-social-choice

  This file proves Arrow's Impossibility Theorem following
  Geanakoplos's (2005) elegant proof approach.

  Main result: Any social welfare function with at least 3 alternatives
  that satisfies Weak Pareto and Independence of Irrelevant Alternatives
  must be a dictatorship.

  Proof structure:
  1. Extremal Lemma: If all place b extremally, society does too
  2. Pivot existence: Every alternative has a pivotal individual
  3. Dictatorial extension: Pivots become dictators over pairs
  4. Complete dictatorship: Partial dictator becomes full dictator
-/

import SocialChoice.Framework

variable {ι : Type*} {σ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq σ]

/-! ## Extremal Positions -/

/-- b is strictly best in individual i's ordering over X -/
def is_strictly_best (R : σ → σ → Prop) (b : σ) (X : Finset σ) : Prop :=
  b ∈ X ∧ ∀ a ∈ X, a ≠ b → P R b a

/-- b is strictly worst in individual i's ordering over X -/
def is_strictly_worst (R : σ → σ → Prop) (b : σ) (X : Finset σ) : Prop :=
  b ∈ X ∧ ∀ a ∈ X, a ≠ b → P R a b

/-- b is in an extremal position (best or worst) -/
def is_extremal (R : σ → σ → Prop) (b : σ) (X : Finset σ) : Prop :=
  is_strictly_best R b X ∨ is_strictly_worst R b X

lemma not_strictly_worst {R : σ → σ → Prop} {b : σ} {X : Finset σ} (hb : b ∈ X) :
    ¬is_strictly_worst R b X ↔ ∃ a ∈ X, a ≠ b ∧ ¬P R a b := by
  constructor
  · intro h; unfold is_strictly_worst at h; push_neg at h; exact h hb
  · intro ⟨a, ha, hab, hPa⟩ ⟨hbX, hAll⟩; exact hPa (hAll a ha hab)

lemma not_strictly_best {R : σ → σ → Prop} {b : σ} {X : Finset σ} (hb : b ∈ X) :
    ¬is_strictly_best R b X ↔ ∃ a ∈ X, a ≠ b ∧ ¬P R b a := by
  constructor
  · intro h; unfold is_strictly_best at h; push_neg at h; exact h hb
  · intro ⟨a, ha, hab, hPa⟩ ⟨hbX, hAll⟩; exact hPa (hAll a ha hab)

lemma not_extremal {R : σ → σ → Prop} {b : σ} {X : Finset σ} (hR : Total R)
    (hX : 3 ≤ X.card) (hb : b ∈ X) :
    ¬is_extremal R b X → ∃ a ∈ X, ∃ c ∈ X, a ≠ b ∧ c ≠ b ∧ a ≠ c ∧ R a b ∧ R b c := by
  intro h
  simp only [is_extremal, not_or] at h
  obtain ⟨hnBest, hnWorst⟩ := h
  obtain ⟨a, ha, hab, hPba⟩ := not_strictly_best hb |>.mp hnBest
  obtain ⟨c, hc, hcb, hPcb⟩ := not_strictly_worst hb |>.mp hnWorst
  have Rab : R a b := R_of_nP_total hR hPba
  have Rbc : R b c := R_of_nP_total hR hPcb
  by_cases hac : a = c
  · subst hac
    obtain ⟨d, hd, hda, hdb⟩ := exists_third_distinct_mem (by omega : 2 < X.card) ha hb hab
    have : R d b ∨ R b d := hR d b
    cases this with
    | inl hdb' => exact ⟨d, hd, a, ha, hdb, hab, hda, hdb', Rbc⟩
    | inr hrbd => exact ⟨a, ha, d, hd, hab, hdb, hda.symm, Rab, hrbd⟩
  · exact ⟨a, ha, c, hc, hab, hcb, hac, Rab, Rbc⟩

lemma is_strictly_best.not_strictly_worst {R : σ → σ → Prop} {b : σ} {X : Finset σ}
    (htop : is_strictly_best R b X) (hX : 2 ≤ X.card) (hb : b ∈ X) :
    ¬is_strictly_worst R b X := by
  obtain ⟨a, ha, hab⟩ := exists_second_distinct_mem hX hb
  exact fun h => (nP_of_reverseP (htop.2 a ha hab)) (h.2 a ha hab)

lemma is_strictly_worst.not_strictly_best {R : σ → σ → Prop} {b : σ} {X : Finset σ}
    (hbot : is_strictly_worst R b X) (hX : 2 ≤ X.card) (hb : b ∈ X) :
    ¬is_strictly_best R b X := by
  obtain ⟨a, ha, hab⟩ := exists_second_distinct_mem hX hb
  exact fun h => (nP_of_reverseP (hbot.2 a ha hab)) (h.2 a ha hab)

lemma is_extremal.is_strictly_best {R : σ → σ → Prop} {b : σ} {X : Finset σ}
    (hextr : is_extremal R b X) (h : ¬is_strictly_worst R b X) :
    is_strictly_best R b X :=
  match hextr with
  | Or.inl hbest => hbest
  | Or.inr hworst => absurd hworst h

lemma is_extremal.is_strictly_worst {R : σ → σ → Prop} {b : σ} {X : Finset σ}
    (hextr : is_extremal R b X) (h : ¬_root_.is_strictly_best R b X) :
    _root_.is_strictly_worst R b X :=
  match hextr with
  | Or.inl hbest => absurd hbest h
  | Or.inr hworst => hworst

lemma is_strictly_best.is_extremal {R : σ → σ → Prop} {b : σ} {X : Finset σ}
    (h : is_strictly_best R b X) : is_extremal R b X := Or.inl h

lemma is_strictly_worst.is_extremal {R : σ → σ → Prop} {b : σ} {X : Finset σ}
    (h : is_strictly_worst R b X) : is_extremal R b X := Or.inr h

/-! ## Helper Lemmas for Extremal / Pivot Proofs

These are adapted from asouther4's original Lean 3 proofs.
-/

/-- maketop_rel makes b strictly best -/
lemma is_strictly_best_maketop_rel {R : σ → σ → Prop} {b : σ} {X : Finset σ}
    (hb : b ∈ X) (hR : Reflexive R) :
    is_strictly_best (maketop_rel R b) b X := by
  refine ⟨hb, fun a ha hab => ?_⟩
  simp [P, maketop_rel, hab]

/-- makebot_rel makes b strictly worst -/
lemma is_strictly_worst_makebot_rel {R : σ → σ → Prop} {b : σ} {X : Finset σ}
    (hb : b ∈ X) (hR : Reflexive R) :
    is_strictly_worst (makebot_rel R b) b X := by
  refine ⟨hb, fun a ha hab => ?_⟩
  simp [P, makebot_rel, hab]

/-- makeabove_above: In makeabove r a b, b is strictly above a -/
lemma makeabove_above {r : PrefOrder σ} {a b : σ} (hab : a ≠ b) :
    P (makeabove_rel r.rel a b) b a := by
  unfold makeabove_rel P; simp [hab, r.refl a]

/-- makeabove_above': If r a c then in makeabove r a b, b is strictly above c -/
lemma makeabove_above' {r : PrefOrder σ} {a b c : σ} (hcb : c ≠ b) (hr : r.rel a c) :
    P (makeabove_rel r.rel a b) b c := by
  unfold makeabove_rel P; simp [hcb, hr]

/-- makeabove_below: If ¬r a c then in makeabove r a b, c is strictly above b -/
lemma makeabove_below {r : PrefOrder σ} {a b c : σ} (hcb : c ≠ b) (hr : ¬r.rel a c) :
    P (makeabove_rel r.rel a b) c b := by
  unfold makeabove_rel P; simp [hcb, hr]

/-- If everyone places b strictly best, society places b strictly best (Weak Pareto) -/
theorem is_strictly_best_of_forall_is_strictly_best {f : SWF ι σ} {X : Finset σ} {b : σ}
    (hb : b ∈ X) (hwp : weak_pareto f X) {prof : Profile ι σ}
    (htop : ∀ i, is_strictly_best (prof i).rel b X) :
    is_strictly_best (f prof).rel b X :=
  ⟨hb, fun a ha hab => hwp prof b a hb ha (fun i => (htop i).2 a ha hab)⟩

/-- If everyone places b strictly worst, society places b strictly worst (Weak Pareto) -/
theorem is_strictly_worst_of_forall_is_strictly_worst {f : SWF ι σ} {X : Finset σ} {b : σ}
    (hb : b ∈ X) (hwp : weak_pareto f X) {prof : Profile ι σ}
    (hbot : ∀ i, is_strictly_worst (prof i).rel b X) :
    is_strictly_worst (f prof).rel b X :=
  ⟨hb, fun a ha hab => hwp prof a b ha hb (fun i => (hbot i).2 a ha hab)⟩

/-! ## Pivotality -/

/-- Witness data for pivotality. Type-valued so that field projections
    (e.g. .hothers) produce proper functions. -/
structure PivotalData (f : SWF ι σ) (X : Finset σ) (n : ι) (b : σ) : Type _ where
  prof : Profile ι σ
  prof' : Profile ι σ
  /-- Others' preferences identical between prof and prof' -/
  hothers : ∀ j : ι, j ≠ n → prof' j = prof j
  /-- Everyone places b extremally in prof -/
  hall : ∀ i : ι, is_extremal (prof i).rel b X
  /-- Everyone places b extremally in prof' -/
  hall' : ∀ i : ι, is_extremal (prof' i).rel b X
  /-- n has b worst in prof -/
  hworst : is_strictly_worst (prof n).rel b X
  /-- n has b best in prof' -/
  hbest : is_strictly_best (prof' n).rel b X
  /-- society ranks b worst -/
  hsoc_worst : is_strictly_worst (f prof).rel b X
  /-- society ranks b best -/
  hsoc_best : is_strictly_best (f prof').rel b X

/-- Individual n is pivotal for alternative b. -/
def is_pivotal (f : SWF ι σ) (X : Finset σ) (n : ι) (b : σ) : Prop :=
  Nonempty (PivotalData f X n b)

/-- Derive pairwise agreement from profile equality for others. -/
def apply_hothers {ι σ : Type*} {n : ι}
    {prof prof' : Profile ι σ}
    (h : ∀ j : ι, j ≠ n → prof' j = prof j)
    (j : ι) (hj : j ≠ n) (x y : σ) :
    (prof j).rel x y ↔ (prof' j).rel x y := by
  rw [h j hj]

/-! ## Key Lemmas -/

/-- Extremal Lemma: If all individuals place b extremally, so does society.
    PROOF SKETCH (Geanakoplos 2005):
    Suppose for contradiction that society ranks b neither best nor worst.
    Then ∃ a, c ∈ X with a ≠ b, c ≠ b, a ≠ c such that
    P(f prof) a b (society prefers a to b) and P(f prof) b c (society prefers b to c).
    Since all individuals rank b extremally, each ranks b either above both
    a and c, or below both a and c.
    By IIA, society's ranking of (a,b) depends only on individual rankings of (a,b).
    Similarly for (b,c). Since every individual has the same relative ranking
    of (a,b) as (a,c) (both above or both below b), Pareto on the pairs
    where everyone agrees gives a contradiction: society cannot rank a > b > c
    if everyone places b at an extreme. -/
theorem extremal_lemma (f : SWF ι σ) (X : Finset σ)
    (hwp : weak_pareto f X) (hind : ind_of_irr_alts f X)
    (hX : 3 ≤ X.card) (b : σ) (hb : b ∈ X)
    (prof : Profile ι σ)
    (hall : ∀ i : ι, is_extremal (prof i).rel b X) :
    is_extremal (f prof).rel b X := by
  by_contra hnot
  obtain ⟨a, ha, c, hc, hab, hcb, hac, hfab, hfbc⟩ := not_extremal (f prof).total hX hb hnot
  let prof' : Profile ι σ := makeabove_all prof a c
  -- H1: if b not worst for j (→ b best), then ¬(prof j).rel a b,
  --     so makeabove_below gives P(prof' j) b c (b above c in prof')
  have H1 (j : ι) (h : ¬is_strictly_worst (prof j).rel b X) :
      P (prof' j).rel b c :=
    have hbest := hall j |>.is_strictly_best h
    makeabove_below hcb.symm (hbest.2 a ha hab).2
  -- H2: if b not best for j (→ b worst), then (prof j).rel a b,
  --     so makeabove_above' gives P(prof' j) c b (c above b in prof')
  have H2 (j : ι) (h : ¬is_strictly_best (prof j).rel b X) :
      P (prof' j).rel c b :=
    have hworst := hall j |>.is_strictly_worst h
    makeabove_above' hcb.symm (hworst.2 a ha hab).1
  -- IIA for (a,b): pair (a,b) doesn't involve c, so makeabove preserves P
  have hIIA_ab : same_order (f prof).rel (f prof').rel a b a b :=
    (same_order_iff_same_order' (f prof).total (f prof').total).2 <|
      hind prof prof' a b ha hb fun j => by
        have h := makeabove_rel_noteq_P (prof j).rel a hac hcb.symm
        simp only [makeabove_all, makeabove_pref] at h ⊢
        exact ⟨h.1.symm, h.2.symm⟩
  -- IIA for (b,c): pair involves c (raised element), case-split via extremality
  have hIIA_bc : same_order (f prof).rel (f prof').rel b c b c :=
    (same_order_iff_same_order' (f prof).total (f prof').total).2 <|
      hind prof prof' b c hb hc fun j => by
        show same_order' (prof j).rel (makeabove_rel (prof j).rel a c) b c b c
        -- is_extremal = is_strictly_best ∨ is_strictly_worst
        rcases hall j with hbest | hworst
        · -- b best: ∀ a' ∈ X, a' ≠ b → P (prof j) b a'
          obtain ⟨hbB, hPba⟩ := hbest
          have hRba : (prof j).rel b a := (hPba a ha hab).1
          have hnRab : ¬(prof j).rel a b := (hPba a ha hab).2
          have hRbc : (prof j).rel b c := (hPba c hc hcb).1
          have hnRcb : ¬(prof j).rel c b := (hPba c hc hcb).2
          -- makeabove: since ¬R a b, makeabove_below gives P(prof') b c
          have hPbc' : P (makeabove_rel (prof j).rel a c) b c :=
            makeabove_below hcb.symm hnRab
          have hnPcb' : ¬P (makeabove_rel (prof j).rel a c) c b :=
            nP_of_reverseP hPbc'
          -- Best case: P(prof j) b c = ⟨hRbc, hnRcb⟩, P(prof j) c b impossible (hnRcb)
          -- In prof': P(prof' j) b c = hPbc', P(prof' j) c b impossible (hnPcb')
          exact ⟨⟨fun _ => hPbc', fun _ => ⟨hRbc, hnRcb⟩⟩,
                 ⟨fun h => absurd h.1 hnRcb, fun h => False.elim (hnPcb' h)⟩⟩
        · -- b worst: ∀ a' ∈ X, a' ≠ b → P (prof j) a' b
          obtain ⟨hbW, hPab⟩ := hworst
          have hRab : (prof j).rel a b := (hPab a ha hab).1
          have hRcb : (prof j).rel c b := (hPab c hc hcb).1
          have hnRbc : ¬(prof j).rel b c := (hPab c hc hcb).2
          -- makeabove: since R a b, makeabove_above' gives P(prof') c b
          have hPcb' : P (makeabove_rel (prof j).rel a c) c b :=
            makeabove_above' hcb.symm hRab
          have hnPbc' : ¬P (makeabove_rel (prof j).rel a c) b c :=
            fun h => hPcb'.2 h.1
          -- Worst case: P(prof j) b c impossible (hnRbc), P(prof j) c b = ⟨hRcb, hnRbc⟩
          -- In prof': P(prof' j) b c impossible (hnPbc'), P(prof' j) c b = hPcb'
          exact ⟨⟨fun h => absurd h.1 hnRbc, fun h => False.elim (hnPbc' h)⟩,
                 ⟨fun _ => hPcb', fun _ => ⟨hRcb, hnRbc⟩⟩⟩
  -- Transfer weak relations via same_order
  have Rab' : (f prof').rel a b := hIIA_ab.1.1.1 hfab
  have Rbc' : (f prof').rel b c := hIIA_bc.1.1.1 hfbc
  have Rac' : (f prof').rel a c := (f prof').trans Rab' Rbc'
  exact (hwp prof' c a hc ha fun j => makeabove_above hac).2 Rac'

/-- Existence of pivot: For any alternative, there exists a pivotal individual.
    PROOF SKETCH (Geanakoplos 2005):
    Enumerate individuals as i₁, ..., iₘ. Construct profiles:
    - prof⁰: everyone places b at bottom → society ranks b worst (by Pareto)
    - profᵏ: i₁,...,iₖ place b at top, rest at bottom
    - profᵐ: everyone places b at top → society ranks b best (by Pareto)
    By the extremal lemma, for each profᵏ, society ranks b extremally.
    Since prof⁰ has b worst and profᵐ has b best, there must be some k where
    society flips from worst to best. Then iₖ is pivotal.
    NOTE: Requires finite enumeration of individuals (Fintype ι). -/
theorem pivot_exists (f : SWF ι σ) (X : Finset σ)
    (hwp : weak_pareto f X) (hind : ind_of_irr_alts f X)
    (hX : 3 ≤ X.card) (b : σ) (hb : b ∈ X) :
    ∃ n : ι, is_pivotal f X n b := by
  -- Use well-founded induction on D.card (set of individuals ranking b at bottom).
  -- For each D.card value k, given any profile where exactly D individuals rank b worst
  -- and the rest rank b best, with society ranking b worst, find a pivot.
  -- If D is empty → contradiction (Pareto forces society best ≠ worst).
  -- If D is nonempty → pick i ∈ D, flip to top. Either society flips (pivot found)
  -- or recurse with D \ {i} (smaller cardinality).
  suffices h : ∀ (D : Finset ι) (prof : Profile ι σ),
      (∀ i ∈ D, is_strictly_worst (prof i).rel b X) →
      (∀ i ∉ D, is_strictly_best (prof i).rel b X) →
      (∀ i, is_extremal (prof i).rel b X) →
      is_strictly_worst (f prof).rel b X →
      ∃ n : ι, is_pivotal f X n b by
    -- Construct initial profile: everyone places b at bottom.
    -- Define a PrefOrder where b is strictly worst and everything else is indifferent.
    -- rel x y = (x ≠ b) ∨ (x = b ∧ y = b), i.e., x = b → y = b.
    let botRel : σ → σ → Prop := fun x y => x = b → y = b
    let all_bot : Profile ι σ := fun _ =>
      { rel := botRel
        refl := fun x => by simp [botRel]
        total := fun x y => by
          by_cases hx : x = b <;> by_cases hy : y = b
          · left; intro _; exact hy
          · right; intro _; exact hx
          · left; intro hxb; exact (hx hxb).elim
          · left; intro hxb; exact (hx hxb).elim
        trans := fun x y z hxy hyz => by
          simp only [botRel] at hxy hyz ⊢
          intro hxz
          exact hxy hxz |> hyz }
    have hbot : ∀ i, is_strictly_worst (all_bot i).rel b X := by
      intro i; refine ⟨hb, fun a ha hab => ?_⟩
      dsimp [botRel, P]
      exact ⟨fun _ => rfl, fun h => hab (h rfl)⟩
    have hsoc_bot : is_strictly_worst (f all_bot).rel b X :=
      is_strictly_worst_of_forall_is_strictly_worst hb hwp hbot
    have hall : ∀ i, is_extremal (all_bot i).rel b X :=
      fun i => (hbot i).is_extremal
    exact h Finset.univ all_bot (fun i _ => hbot i)
      (fun i hi => (hi (Finset.mem_univ i)).elim) hall hsoc_bot
  -- Well-founded induction on the cardinality of D
  intro D prof hD_worst hDcomp_best hext hsoc_worst
  -- We do strong induction on D.card, with D and prof as extra parameters
  have hinduction : ∀ (k : Nat) (D' : Finset ι) (prof' : Profile ι σ),
      D'.card = k →
      (∀ i ∈ D', is_strictly_worst (prof' i).rel b X) →
      (∀ i ∉ D', is_strictly_best (prof' i).rel b X) →
      (∀ i, is_extremal (prof' i).rel b X) →
      is_strictly_worst (f prof').rel b X →
      ∃ n : ι, is_pivotal f X n b := by
    intro k
    induction k using Nat.strongRecOn with
    | ind m IH =>
      intro D' prof' hDcard hD'worst hD'comp_best hD'ext hsoc'worst
      by_cases hDne : D'.Nonempty
      · -- D' nonempty: pick i ∈ D', flip to top
        obtain ⟨i, hiD⟩ := hDne
        let prof'' := maketop prof' i b X hb
        have hi''_best : is_strictly_best (prof'' i).rel b X := by
          show is_strictly_best ((maketop prof' i b X hb) i).rel b X
          simp only [maketop]
          exact is_strictly_best_maketop_rel hb (prof' i).refl
        have hother (j : ι) (hj : j ≠ i) : prof'' j = prof' j := by
          show (maketop prof' i b X hb) j = prof' j
          simp only [maketop]
          exact if_neg hj
        have hD''ext : ∀ j, is_extremal (prof'' j).rel b X := by
          intro j
          by_cases hj : j = i
          · subst hj; exact hi''_best.is_extremal
          · have := hother j hj; rw [this]; exact hD'ext j
        have hsoc''_ext : is_extremal (f prof'').rel b X :=
          extremal_lemma f X hwp hind hX b hb prof'' hD''ext
        rcases hsoc''_ext with hsoc''_best | hsoc''_worst
        · -- Society flipped: i is pivotal!
          -- prof'' is maketop prof' i b X hb. For j ≠ i, prof'' j = prof' j.
          -- We construct the others-agree proof by unfolding maketop.
          have hagree := hother
          exact ⟨i, ⟨prof', prof'', hagree, hD'ext, hD''ext,
            hD'worst i hiD, hi''_best, hsoc'worst, hsoc''_best⟩⟩
        · -- Society still worst: recurse on D' \ {i}
          let D'' := D'.erase i
          have hD''card_lt : D''.card < D'.card := by
            show (D'.erase i).card < D'.card
            rw [Finset.card_erase_of_mem hiD]
            exact Nat.sub_lt (Finset.card_pos.mpr ⟨i, hiD⟩) (by norm_num)
          have hD''worst : ∀ j ∈ D'', is_strictly_worst (prof'' j).rel b X := by
            intro j hj
            have ⟨hji, hjD⟩ := Finset.mem_erase.mp hj
            have : prof'' j = prof' j := hother j hji
            rw [this]
            exact hD'worst j hjD
          have hD''comp_best : ∀ j ∉ D'', is_strictly_best (prof'' j).rel b X := by
            intro j hj
            by_cases hji : j = i
            · subst hji; exact hi''_best
            · have hjnD : j ∉ D' := by
                intro hjD
                apply hj
                exact Finset.mem_erase.mpr ⟨hji, hjD⟩
              have : prof'' j = prof' j := hother j hji
              rw [this]
              exact hD'comp_best j hjnD
          have hD''lt_m : D''.card < m := by
            show (D'.erase i).card < m
            have := Finset.card_erase_of_mem hiD
            omega
          exact IH D''.card hD''lt_m D'' prof'' (Eq.refl D''.card)
            hD''worst hD''comp_best hD''ext hsoc''_worst
      · -- D' empty: contradiction (Pareto forces best ≠ worst)
        have hempty : D' = ∅ := Finset.not_nonempty_iff_eq_empty.mp hDne
        have hbest : ∀ i, is_strictly_best (prof' i).rel b X := by
          intro i; rw [hempty] at hD'comp_best; exact hD'comp_best i (by simp)
        have hsoc_best := is_strictly_best_of_forall_is_strictly_best hb hwp hbest
        exact absurd hsoc_best (is_strictly_worst.not_strictly_best hsoc'worst (Nat.le_of_lt (Nat.lt_of_lt_of_le (by norm_num) hX)) hb)
  exact hinduction D.card D prof (Eq.refl D.card) hD_worst hDcomp_best hext hsoc_worst

/-- A pivotal individual is a dictator over pairs not involving b.
    Port of asouther4's third_step.
    Given n pivotal for b, show n dictates over (c,a) where c,a ≠ b.
    PROOF: Construct Q' where n uses makeabove (b above a), others use
    makebot/maketop based on pivotality profile prof₀. Then:
    P(f prof) c a ← IIA(prof,Q') ← P(f Q') c a
    P(f Q') c a ← trans ← P(f Q') c b ∧ P(f Q') b a
    P(f Q') c b ← IIA(prof₀,Q') ← P(f prof₀) c b (society b-worst)
    P(f Q') b a ← IIA(prof₁,Q') ← P(f prof₁) b a (society b-best) -/
theorem pivot_is_dictator_except_b (f : SWF ι σ) (X : Finset σ)
    (hind : ind_of_irr_alts f X)
    (b : σ) (hb : b ∈ X)
    (n : ι) (hn : is_pivotal f X n b)
    (a c : σ) (ha : a ∈ X) (hc : c ∈ X) (hab : a ≠ b) (hcb : c ≠ b) (hac : a ≠ c) :
    is_dictator_on f n c a := by
  intro prof hPca
  -- h is ¬(prof n).rel a c, the second component of P (prof n).rel c a
  have h : ¬(prof n).rel a c := hPca.2
  obtain ⟨w⟩ := hn
  obtain ⟨prof₀, prof₁, hothers, hall₀, hall₁, hn_worst₀, hn_best₁, hsoc_worst, hsoc_best⟩ := w
  -- Build Q': n uses makeabove (b above a), others use makebot/maketop based on prof₀
  let Q' : Profile ι σ :=
    fun j => if j = n then makeabove_pref (prof j) a b
             else @ite (PrefOrder σ) (is_strictly_worst (prof₀ j).rel b X)
                   (Classical.dec (is_strictly_worst (prof₀ j).rel b X))
                   (makebot_pref (prof j) b)
                   (maketop_pref (prof j) b)
  have hQ'n : Q' n = makeabove_pref (prof n) a b := by
    unfold Q'; simp
  have hQ'bot (j : ι) (hj : j ≠ n) (hbot : is_strictly_worst (prof₀ j).rel b X) :
      Q' j = makebot_pref (prof j) b := by
    unfold Q'; simp [hj, hbot]
  have hQ'top (j : ι) (hj : j ≠ n) (htop : ¬is_strictly_worst (prof₀ j).rel b X) :
      Q' j = maketop_pref (prof j) b := by
    unfold Q'; simp [hj, htop]
  -- IIA prof ↔ Q' on (c,a): all manipulations preserve pairs not involving b
  have hIIA_ca : same_order' (f prof).rel (f Q').rel c a c a := by
    apply hind prof Q' c a hc ha
    intro j
    suffices h : ∀ d ≠ b, ∀ e ≠ b, same_order' (prof j).rel (Q' j).rel e d e d by
      exact h a hab c hcb
    intro d hdb e heb
    by_cases hjn : j = n
    · rw [hjn, hQ'n]
      show same_order' (prof n).rel (makeabove_rel (prof n).rel a b) e d e d
      have h := makeabove_rel_noteq_P (prof n).rel a heb hdb
      exact ⟨h.1.symm, h.2.symm⟩
    · by_cases hbot : is_strictly_worst (prof₀ j).rel b X
      · have := hQ'bot j hjn hbot; rw [this]
        show same_order' (prof j).rel (makebot_rel (prof j).rel b) e d e d
        have h := makebot_rel_noteq_P (prof j).rel heb hdb
        exact ⟨h.1.symm, h.2.symm⟩
      · have := hQ'top j hjn hbot; rw [this]
        show same_order' (prof j).rel (maketop_rel (prof j).rel b) e d e d
        have h := maketop_rel_noteq_P (prof j).rel heb hdb
        exact ⟨h.1.symm, h.2.symm⟩
  -- IIA prof₀ ↔ Q' on (c,b): transfer P(f prof₀) c b → P(f Q') c b
  have hIIA_cb : same_order' (f prof₀).rel (f Q').rel c b c b := by
    apply hind prof₀ Q' c b hc hb
    intro j
    by_cases hjn : j = n
    · -- j = n: prof₀ n has b worst (from is_pivotal guarantee)
      rw [hjn]
      have hworst₀ : is_strictly_worst (prof₀ n).rel b X := hn_worst₀
      have hPcb₀ : P (prof₀ n).rel c b := hworst₀.2 c hc hcb
      have hPcb_ma : P (Q' n).rel c b := by
        rw [hQ'n]; exact makeabove_below hcb h
      have hnPbc_ma : ¬P (Q' n).rel b c := nP_of_reverseP hPcb_ma
      have hnPbc₀ : ¬P (prof₀ n).rel b c := nP_of_reverseP hPcb₀
      exact ⟨Iff.intro (fun _ => hPcb_ma) (fun _ => hPcb₀),
             Iff.intro (fun h => False.elim (hnPbc₀ h)) (fun h => False.elim (hnPbc_ma h))⟩
    · -- j ≠ n: show same_order' (prof₀ j) (Q' j) c b c b
      -- Q' j is either makebot or maketop based on prof₀ j's extremality on b
      simp only [same_order']
      by_cases hbot : is_strictly_worst (prof₀ j).rel b X
      · -- prof₀ j has b worst → Q' j = makebot
        have hPcb₀ : P (prof₀ j).rel c b := hbot.2 c hc hcb
        have this : Q' j = makebot_pref (prof j) b := hQ'bot j hjn hbot
        rw [this]
        have hPcb_mb : P (makebot_rel (prof j).rel b) c b := by
          simp [P, makebot_rel, hcb]
        have hnPbc_mb : ¬P (makebot_rel (prof j).rel b) b c := by
          simp [P, makebot_rel, hcb]
        exact ⟨Iff.intro (fun _ => hPcb_mb) (fun _ => hPcb₀),
               Iff.intro (fun h => False.elim (nP_of_reverseP hPcb₀ h))
                        (fun h => False.elim (hnPbc_mb h))⟩
      · -- prof₀ j has b best (since extremal + not worst) → Q' j = maketop
        have htop : is_strictly_best (prof₀ j).rel b X :=
          (hall₀ j).is_strictly_best hbot
        have hPbc₀ : P (prof₀ j).rel b c := htop.2 c hc hcb
        have hnPcb₀ : ¬P (prof₀ j).rel c b := nP_of_reverseP hPbc₀
        have this : Q' j = maketop_pref (prof j) b := hQ'top j hjn hbot
        rw [this]
        have hPbc_mt : P (maketop_rel (prof j).rel b) b c := by
          simp [P, maketop_rel, hcb]
        have hnPcb_mt : ¬P (maketop_rel (prof j).rel b) c b := by
          simp [P, maketop_rel, hcb]
        exact ⟨Iff.intro (fun h => False.elim (hnPcb₀ h))
                         (fun h => False.elim (hnPcb_mt h)),
               Iff.intro (fun _ => hPbc_mt) (fun _ => hPbc₀)⟩
  -- IIA prof₁ ↔ Q' on (b,a): transfer P(f prof₁) b a → P(f Q') b a
  have hIIA_ba : same_order' (f prof₁).rel (f Q').rel b a b a := by
    apply hind prof₁ Q' b a hb ha
    intro j
    show same_order' (prof₁ j).rel (Q' j).rel b a b a
    by_cases hjn : j = n
    · -- n: prof₁ n has b best (from is_pivotal guarantee)
      rw [hjn]
      have hbest₁ : is_strictly_best (prof₁ n).rel b X := hn_best₁
      have hPba₁' : P (prof₁ n).rel b a := hbest₁.2 a ha hab
      have hnPab₁ : ¬P (prof₁ n).rel a b := nP_of_reverseP hPba₁'
      have hPba_ma : P (Q' n).rel b a := by
        rw [hQ'n]; exact makeabove_above hab
      have hnPab_ma : ¬P (Q' n).rel a b := nP_of_reverseP hPba_ma
      exact ⟨Iff.intro (fun _ => hPba_ma) (fun _ => hPba₁'),
             Iff.intro (fun h => False.elim (hnPab₁ h)) (fun h => False.elim (hnPab_ma h))⟩
    · -- j ≠ n: show same_order' (prof₁ j) (Q' j) b a b a
      -- hothers: prof₀ j ↔ prof₁ j on X pairs. So extremality transfers.
      simp only [same_order']
      by_cases hbot₀ : is_strictly_worst (prof₀ j).rel b X
      · -- prof₀ j has b worst → prof₁ j also b worst (via hothers on (a,b) pair)
        have hPab₀ : P (prof₀ j).rel a b := hbot₀.2 a ha hab
        have hRab₀ : (prof₀ j).rel a b := hPab₀.1
        have hnRba₀ : ¬(prof₀ j).rel b a := hPab₀.2
        have habIff : (prof₀ j).rel a b ↔ (prof₁ j).rel a b :=
          apply_hothers hothers j hjn a b
        have hbaIff : (prof₀ j).rel b a ↔ (prof₁ j).rel b a :=
          apply_hothers hothers j hjn b a
        have hRab₁ : (prof₁ j).rel a b := habIff.mp hRab₀
        have hnRba₁ : ¬(prof₁ j).rel b a :=
          fun h => hnRba₀ (hbaIff.mpr h)
        have hPab₁ : P (prof₁ j).rel a b := ⟨hRab₁, hnRba₁⟩
        have hnPba₁ : ¬P (prof₁ j).rel b a := nP_of_reverseP hPab₁
        have this' : Q' j = makebot_pref (prof j) b := hQ'bot j hjn hbot₀
        rw [this']
        have hPab_mb : P (makebot_rel (prof j).rel b) a b := by
          simp [P, makebot_rel, hab]
        have hnPba_mb : ¬P (makebot_rel (prof j).rel b) b a := by
          simp [P, makebot_rel, hab]
        exact ⟨Iff.intro (fun h => False.elim (hnPba₁ h))
                         (fun h => False.elim (hnPba_mb h)),
               Iff.intro (fun _ => hPab_mb) (fun _ => hPab₁)⟩
      · -- prof₀ j has b best → prof₁ j also b best → Q' j = maketop
        have htop₀ : is_strictly_best (prof₀ j).rel b X :=
          (hall₀ j).is_strictly_best hbot₀
        have hPba₀ : P (prof₀ j).rel b a := htop₀.2 a ha hab
        have hRba₀ : (prof₀ j).rel b a := hPba₀.1
        have hnRab₀ : ¬(prof₀ j).rel a b := hPba₀.2
        have hbaIff : (prof₀ j).rel b a ↔ (prof₁ j).rel b a :=
          apply_hothers hothers j hjn b a
        have habIff : (prof₀ j).rel a b ↔ (prof₁ j).rel a b := by
          have hRba₁ : (prof₁ j).rel b a := hbaIff.mp hRba₀
          have hnWorst₁ : ¬is_strictly_worst (prof₁ j).rel b X := by
            intro h
            have hPab₁ : P (prof₁ j).rel a b := h.2 a ha hab
            exact hPab₁.2 hRba₁
          have htop₁ : is_strictly_best (prof₁ j).rel b X :=
            (hall₁ j).is_strictly_best hnWorst₁
          have hnRab₁ : ¬(prof₁ j).rel a b :=
            (htop₁.2 a ha hab).2
          constructor
          · intro h; exact absurd h hnRab₀
          · intro h; exact absurd h hnRab₁
        have hRba₁ : (prof₁ j).rel b a := hbaIff.mp hRba₀
        have hnRab₁ : ¬(prof₁ j).rel a b :=
          fun h => habIff.mpr h |> hnRab₀
        have hPba₁ : P (prof₁ j).rel b a := ⟨hRba₁, hnRab₁⟩
        have this' : Q' j = maketop_pref (prof j) b := hQ'top j hjn hbot₀
        rw [this']
        have hPba_mt : P (maketop_rel (prof j).rel b) b a := by
          simp [P, maketop_rel, hab]
        have hnPab_mt : ¬P (maketop_rel (prof j).rel b) a b := by
          simp [P, maketop_rel, hab]
        have hnPab₁ : ¬P (prof₁ j).rel a b :=
          fun h => hnRab₁ h.1
        exact ⟨Iff.intro (fun _ => hPba_mt) (fun _ => hPba₁),
               Iff.intro (fun h => False.elim (hnPab₁ h))
                        (fun h => False.elim (hnPab_mt h))⟩
  -- Chain: P(f prof) c a ← IIA ← P(f Q') c a ← trans ← P(f Q') c b ∧ P(f Q') b a
  have hPfQ'cb : P (f Q').rel c b :=
    hIIA_cb.1.mp (hsoc_worst.2 c hc hcb)
  have hPfQ'ba : P (f Q').rel b a :=
    hIIA_ba.1.mp (hsoc_best.2 a ha hab)
  have hPfQ'ca : P (f Q').rel c a :=
    P_trans (f Q').trans hPfQ'cb hPfQ'ba
  exact hIIA_ca.1.mpr hPfQ'ca

/-- A dictator over all pairs except those involving b is actually a full dictator.
    Proof via pivot uniqueness (asouther4's fourth_step):
    For any c ∈ X, ∃ j pivotal for c. If j ≠ n, derive contradiction using
    n's pivotal profiles and j's dictatorship on pairs not involving c.
    Therefore j = n, so n is pivotal for c, hence dictator on (b,y) via pivot_is_dictator_except_b.
    -/
theorem partial_dictator_is_full_dictator (f : SWF ι σ) (X : Finset σ)
    (hind : ind_of_irr_alts f X)
    (hwp : weak_pareto f X)
    (hX : 3 ≤ X.card) (b : σ) (hb : b ∈ X)
    (n : ι) (hn_piv : is_pivotal f X n b)
    (hn : ∀ a c : σ, a ∈ X → c ∈ X → a ≠ b → c ≠ b → a ≠ c → is_dictator_on f n a c) :
    ∀ x y : σ, x ∈ X → y ∈ X → x ≠ y → is_dictator_on f n x y := by
  intro x y hx hy hxy
  by_cases hxb : x = b
  · -- x = b, y ≠ b
    have hyb : y ≠ b := fun h => hxy (hxb.trans h.symm)
    have ⟨c, hc, hcb, hcy⟩ := exists_third_distinct_mem (by omega : 2 < X.card) hb hy (Ne.symm hyb)
    obtain ⟨j, hj_piv⟩ := pivot_exists f X hwp hind hX c hc
    by_cases hjn : j = n
    · -- j = n: n is pivotal for c, hence dictator on (b,y)
      have h := pivot_is_dictator_except_b f X hind c hc j hj_piv y b hy hb
        (Ne.symm hcy) (Ne.symm hcb) hyb
      rw [hjn] at h
      exact hxb ▸ h
    · -- j ≠ n: derive contradiction via n's pivotal profiles
      obtain ⟨w⟩ := hn_piv
      obtain ⟨prof₀, prof₁, hothers, hall₀, hall₁, hworst₀, hbest₁, hsoc_worst, hsoc_best⟩ := w
      have hj_yb : is_dictator_on f j y b :=
        pivot_is_dictator_except_b f X hind c hc j hj_piv b y hb hy
          (Ne.symm hcb) (Ne.symm hcy) (Ne.symm hyb)
      have hj_by : is_dictator_on f j b y :=
        pivot_is_dictator_except_b f X hind c hc j hj_piv y b hy hb
          (Ne.symm hcy) (Ne.symm hcb) hyb
      have hnPyb₁ : ¬P (f prof₁).rel y b := nP_of_reverseP (hsoc_best.2 y hy hyb)
      have hnPby₀ : ¬P (f prof₀).rel b y := nP_of_reverseP (hsoc_worst.2 y hy hyb)
      have hby_iff : (prof₀ j).rel b y ↔ (prof₁ j).rel b y :=
        apply_hothers hothers j hjn b y
      have hyb_iff : (prof₀ j).rel y b ↔ (prof₁ j).rel y b :=
        apply_hothers hothers j hjn y b
      rcases hall₁ j with hbest_j | hworst_j
      · -- j places b best in prof₁: transfer to prof₀, contradict society worst
        have hP₁ : P (prof₁ j).rel b y := hbest_j.2 y hy hyb
        have hP₀ : P (prof₀ j).rel b y :=
          ⟨hby_iff.mpr hP₁.1, fun h => hP₁.2 (hyb_iff.mp h)⟩
        exact absurd (hj_by prof₀ hP₀) hnPby₀
      · -- j places b worst in prof₁: contradict society best
        have hP₁ : P (prof₁ j).rel y b := hworst_j.2 y hy hyb
        exact absurd (hj_yb prof₁ hP₁) hnPyb₁
  · by_cases hyb : y = b
    · -- x ≠ b, y = b: symmetric argument
      have ⟨c, hc, hcx, hcb⟩ := exists_third_distinct_mem (by omega : 2 < X.card) hx hb hxb
      obtain ⟨j, hj_piv⟩ := pivot_exists f X hwp hind hX c hc
      by_cases hjn : j = n
      · -- j = n: n is pivotal for c, hence dictator on (x,b)
        have h := pivot_is_dictator_except_b f X hind c hc j hj_piv b x hb hx
          (Ne.symm hcb) (Ne.symm hcx) (Ne.symm hxb)
        rw [hjn] at h
        exact hyb ▸ h
      · -- j ≠ n: derive contradiction
        obtain ⟨w⟩ := hn_piv
        obtain ⟨prof₀, prof₁, hothers, hall₀, hall₁, hworst₀, hbest₁, hsoc_worst, hsoc_best⟩ := w
        have hj_bx : is_dictator_on f j b x :=
          pivot_is_dictator_except_b f X hind c hc j hj_piv x b hx hb
            (Ne.symm hcx) (Ne.symm hcb) hxb
        have hj_xb : is_dictator_on f j x b :=
          pivot_is_dictator_except_b f X hind c hc j hj_piv b x hb hx
            (Ne.symm hcb) (Ne.symm hcx) (Ne.symm hxb)
        have hnPxb₁ : ¬P (f prof₁).rel x b := nP_of_reverseP (hsoc_best.2 x hx hxb)
        have hnPbx₀ : ¬P (f prof₀).rel b x := nP_of_reverseP (hsoc_worst.2 x hx hxb)
        have hbx_iff : (prof₀ j).rel b x ↔ (prof₁ j).rel b x :=
          apply_hothers hothers j hjn b x
        have hxb_iff : (prof₀ j).rel x b ↔ (prof₁ j).rel x b :=
          apply_hothers hothers j hjn x b
        rcases hall₁ j with hbest_j | hworst_j
        · -- j places b best in prof₁: transfer to prof₀, contradict society worst
          have hP₁ : P (prof₁ j).rel b x := hbest_j.2 x hx hxb
          have hP₀ : P (prof₀ j).rel b x :=
            ⟨hbx_iff.mpr hP₁.1, fun h => hP₁.2 (hxb_iff.mp h)⟩
          exact absurd (hj_bx prof₀ hP₀) hnPbx₀
        · -- j places b worst in prof₁: contradict society best
          have hP₁ : P (prof₁ j).rel x b := hworst_j.2 x hx hxb
          exact absurd (hj_xb prof₁ hP₁) hnPxb₁
    · -- x ≠ b, y ≠ b: direct from hn
      exact hn x y hx hy hxb hyb hxy

/-! ## Main Theorem -/

/--
Arrow's Impossibility Theorem:
Any social welfare function over at least 3 alternatives that satisfies
Weak Pareto and Independence of Irrelevant Alternatives must be a dictatorship.
-/
theorem arrow (f : SWF ι σ) (X : Finset σ)
    (hwp : weak_pareto f X) (hind : ind_of_irr_alts f X) (hX : 3 ≤ X.card) :
    is_dictatorship f X := by
  have hne : X.Nonempty := Finset.card_pos.mp (Nat.lt_of_lt_of_le (by norm_num : 0 < 3) hX)
  obtain ⟨b, hb⟩ := hne
  obtain ⟨n, hn⟩ := pivot_exists f X hwp hind hX b hb
  have h3 : ∀ a c, a ∈ X → c ∈ X → a ≠ b → c ≠ b → a ≠ c → is_dictator_on f n a c :=
    fun a c ha hc hab hcb hac => pivot_is_dictator_except_b f X hind b hb n hn c a hc ha hcb hab (Ne.symm hac)
  have h4 := partial_dictator_is_full_dictator f X hind hwp hX b hb n hn h3
  exact ⟨n, h4⟩

/-! ## Consequences -/

/-- Non-dictatorship: No single individual determines everything -/
def non_dictatorial (f : SWF ι σ) (X : Finset σ) : Prop :=
  ¬is_dictatorship f X

/-- Arrow's theorem in negative form: No SWF satisfies all three desirable properties -/
theorem no_perfect_swf (f : SWF ι σ) (X : Finset σ)
    (hwp : weak_pareto f X) (hind : ind_of_irr_alts f X) (hX : 3 ≤ X.card) :
    ¬non_dictatorial f X := by
  intro hnd
  exact hnd (arrow f X hwp hind hX)
