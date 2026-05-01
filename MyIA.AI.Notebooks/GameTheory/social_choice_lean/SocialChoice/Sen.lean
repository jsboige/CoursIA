/-
  Sen's Liberal Paradox
  =====================

  Port of asouther4/lean-social-choice to Lean 4

  Sen's impossibility theorem shows that no social decision procedure
  can simultaneously satisfy:
  1. Weak Pareto criterion
  2. Minimal liberalism (some individuals are decisive over some pairs)
  3. Unrestricted domain

  This is a fundamental result showing tension between efficiency and liberty.
-/

import SocialChoice.Framework
import Mathlib.Tactic

variable {ι : Type*} {σ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq σ]

/-! ## Minimal Liberalism -/

/-- Individual i is decisive over the pair (x, y):
    Society follows i's strict preference in both directions.
    Conforms to Sen 1970 and Holliday/Norman/Pacuit 2021 (bidirectional). -/
def is_decisive_over (f : SWF ι σ) (i : ι) (x y : σ) : Prop :=
  (∀ prof : Profile ι σ, P (prof i).rel x y → P (f prof).rel x y) ∧
  (∀ prof : Profile ι σ, P (prof i).rel y x → P (f prof).rel y x)

/-- Minimal liberalism: At least two individuals each have at least one
    pair over which they are decisive -/
def minimal_liberal (f : SWF ι σ) (X : Finset σ) : Prop :=
  ∃ i j : ι, i ≠ j ∧
    (∃ x y : σ, x ∈ X ∧ y ∈ X ∧ x ≠ y ∧ is_decisive_over f i x y) ∧
    (∃ x y : σ, x ∈ X ∧ y ∈ X ∧ x ≠ y ∧ is_decisive_over f j x y)

-- Unrestricted domain: The SWF accepts any profile
-- (This is implicit in our definition of SWF)

/-! ## Sen's Paradox Construction -/

-- A preference profile that demonstrates the paradox:
-- Prude prefers (not-read, not-read) > (read-by-other, not-read) > (read, read-by-other)
-- Lewd prefers (read-by-other, read) > (read, not-read) > (not-read, not-read)

/-! ## Sen's Impossibility Theorem -/

/--
Sen's Liberal Paradox:
There exists no social welfare function that satisfies both
Weak Pareto and Minimal Liberalism for all preference profiles.
PROOF SKETCH:
From minimal_liberal, get two individuals i, j with decisive pairs:
  i is decisive over (x, y), j is decisive over (z, w).
These pairs may overlap. The standard construction uses:
  i decisive over (a, b), j decisive over (b, c) (or disjoint pairs).
Case 1 (overlapping): i decisive over (a,b), j decisive over (b,c).
  Construct prof where i prefers a > b (exercises right → society: a > b)
  and j prefers b > c (exercises right → society: b > c)
  and everyone prefers c > a (Pareto → society: c > a).
  Cycle: a > b > c > a. No best element exists.
Case 2 (disjoint): i decisive over (a,b), j decisive over (c,d).
  Similar cycle construction using the four alternatives.
  Requires |X| >= 4 in this case (guaranteed by hX : 3 ≤ |X| only
  gives 3, so the proof uses the overlapping case). -/
theorem sen_impossibility (f : SWF ι σ) (X : Finset σ)
    (hne : (2 : ℕ) ≤ Fintype.card ι)
    (hX : 3 ≤ X.card)
    (hwp : weak_pareto f X)
    (hml : minimal_liberal f X) :
    ∃ prof : Profile ι σ, ¬∃ best : σ, is_best_element best X (f prof).rel := by
  obtain ⟨i, j, hij, ⟨a, b, ha, hb, hab, hi_dec⟩, ⟨c, d, hc, hd, hcd, hj_dec⟩⟩ := hml
  by_cases hbc : b = c
  · -- Overlapping: i decisive on (a,b), j decisive on (b,d) since b=c
    subst hbc
    -- Sub-case: a = d means both decisive on pairs sharing b, with a=d
    by_cases had : a = d
    · -- a=d: i on (a,b), j on (b,a). Build profile: i prefers a>b, j prefers b>a
      -- Society gets P a b and P b a → contradiction
      subst had
      let base : PrefOrder σ := ⟨fun _ _ => True, fun _ => trivial,
        fun _ _ => Or.inl trivial, fun _ _ _ _ _ => trivial⟩
      let prof : Profile ι σ := fun k =>
        if k = i then maketop_pref base a
        else if k = j then maketop_pref base b
        else maketop_pref base a
      use prof
      intro ⟨best, hbest⟩
      have hPa_b : P (f prof).rel a b := hi_dec.1 prof (by
        unfold prof; simp only [hij]
        show maketop_rel (fun _ _ ↦ True) a a b ∧ ¬maketop_rel (fun _ _ ↦ True) a b a
        simp [maketop_rel, hab, hab.symm])
      have hPb_a : P (f prof).rel b a := hj_dec.1 prof (by
        unfold prof; simp only [hij.symm]
        show maketop_rel (fun _ _ ↦ True) b b a ∧ ¬maketop_rel (fun _ _ ↦ True) b a b
        simp [maketop_rel, hab])
      exact hPa_b.2 hPb_a.1
    · -- a≠d, b≠d: overlapping with i on (a,b), j on (b,d)
      -- Cycle: P a b (i decisive), P b d (j decisive), P d a (Pareto)
      have hbd : b ≠ d := hcd
      let base : PrefOrder σ := ⟨fun _ _ => True, fun _ => trivial,
        fun _ _ => Or.inl trivial, fun _ _ _ _ _ => trivial⟩
      let prof : Profile ι σ := fun k =>
        if k = i then maketop_pref (makebot_pref base b) d
        else if k = j then maketop_pref (makebot_pref base a) b
        else maketop_pref (makebot_pref base a) d
      use prof
      intro ⟨best, hbest⟩
      have hPa_b : P (f prof).rel a b := hi_dec.1 prof (by
        unfold prof; simp only [hij]
        simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel, hab, had, hbd])
      have hPb_d : P (f prof).rel b d := hj_dec.1 prof (by
        unfold prof
        simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel, hab, hbd.symm, hij.symm])
      have hAll_d_a : ∀ k, P (prof k).rel d a := by
        intro k; unfold prof; split_ifs with hki hkj
        · simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel, hab, had, hbd]
        · show P (maketop_rel (makebot_rel (fun _ _ ↦ True) a) b) d a
          simp [P, maketop_rel, makebot_rel, hab, hbd.symm]
          exact fun h => had h.symm
        · simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel, hab, had, hbd]
      have hPd_a : P (f prof).rel d a := hwp prof d a hd ha hAll_d_a
      have hPad := P_trans (f prof).trans hPa_b hPb_d
      exact hPad.2 hPd_a.1
  · -- b≠c: i on (a,b), j on (c,d) with b≠c
    have hcb : c ≠ b := fun h => hbc h.symm
    by_cases had : a = d
    · -- a=d: i on (a,b), j on (c,a) — chain-compatible overlap (a shared in
      -- different positions: 1st in i's pair, 2nd in j's). Cycle: a>b (i), b>c (Pareto), c>a (j)
      subst had
      have hca : c ≠ a := hcd
      let base : PrefOrder σ := ⟨fun _ _ => True, fun _ => trivial,
        fun _ _ => Or.inl trivial, fun _ _ _ _ _ => trivial⟩
      let prof : Profile ι σ := fun k =>
        if k = i then maketop_pref (makebot_pref base c) a
        else maketop_pref (makebot_pref base a) b
      use prof
      intro ⟨best, hbest⟩
      have hPa_b : P (f prof).rel a b := hi_dec.1 prof (by
        unfold prof; simp only [hij]
        simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel, hab, hab.symm, hca, hca.symm])
      have hPc_a : P (f prof).rel c a := hj_dec.1 prof (by
        unfold prof; simp only [hij.symm]
        simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel, hca, hca.symm, hab, hab.symm, hcb])
      have hcb_local : ¬c = b := fun h => hbc h.symm
      have hAll_b_c : ∀ k, P (prof k).rel b c := by
        intro k; unfold prof; split_ifs with hki
        · simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel,
            hab, hab.symm, hca, hca.symm, hbc]
        · simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel,
            hab, hab.symm, hca, hca.symm, hcb_local]
      have hPb_c : P (f prof).rel b c := hwp prof b c hb hc hAll_b_c
      exact (P_trans (f prof).trans hPa_b hPb_c).2 hPc_a.1
    · -- a≠d, b≠c: bidirectional decisiveness lets us handle fork cases
      by_cases hac : a = c
      · -- a=c (fork): i on (a,b), j on (a,d) with bidirectional j on (d,a).
        subst hac
        by_cases hbd_check : b = d
        · -- b=d means both decisive on (a,b): same pair contradiction
          subst hbd_check
          let base : PrefOrder σ := ⟨fun _ _ => True, fun _ => trivial,
            fun _ _ => Or.inl trivial, fun _ _ _ _ _ => trivial⟩
          let prof : Profile ι σ := fun k =>
            if k = i then maketop_pref base a
            else maketop_pref base b
          use prof
          intro ⟨best, hbest⟩
          have hPa_b : P (f prof).rel a b := hi_dec.1 prof (by
            unfold prof; simp only [hij]
            show maketop_rel (fun _ _ ↦ True) a a b ∧ ¬maketop_rel (fun _ _ ↦ True) a b a
            simp [maketop_rel, hab, hab.symm])
          have hPb_a : P (f prof).rel b a := hj_dec.2 prof (by
            unfold prof; simp only [hij.symm]
            show maketop_rel (fun _ _ ↦ True) b b a ∧ ¬maketop_rel (fun _ _ ↦ True) b a b
            simp [maketop_rel, hab, hab.symm])
          exact hPa_b.2 hPb_a.1
        · -- b≠d: Cycle a>b (i.1), b>d (Pareto), d>a (j.2)
          have hbd_ne : b ≠ d := fun h => hbd_check h
          let base : PrefOrder σ := ⟨fun _ _ => True, fun _ => trivial,
            fun _ _ => Or.inl trivial, fun _ _ _ _ _ => trivial⟩
          let prof : Profile ι σ := fun k =>
            if k = i then maketop_pref (makebot_pref base d) a
            else maketop_pref (makebot_pref base a) b
          use prof
          intro ⟨best, hbest⟩
          have hPa_b : P (f prof).rel a b := hi_dec.1 prof (by
            unfold prof; simp only [hij]
            show maketop_rel (makebot_rel (fun _ _ ↦ True) d) a a b ∧
              ¬maketop_rel (makebot_rel (fun _ _ ↦ True) d) a b a
            simp [maketop_rel, makebot_rel, hab, hab.symm, hbd_ne, hcd, hcd.symm])
          have hPd_a : P (f prof).rel d a := hj_dec.2 prof (by
            unfold prof; simp only [hij.symm]
            show maketop_rel (makebot_rel (fun _ _ ↦ True) a) b d a ∧
              ¬maketop_rel (makebot_rel (fun _ _ ↦ True) a) b a d
            simp [maketop_rel, makebot_rel, hab, hab.symm, hbd_ne, hcd, hcd.symm])
          have hAll_b_d : ∀ k, P (prof k).rel b d := by
            intro k; unfold prof; split_ifs with hki
            · simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel,
                hab, hab.symm, hbd_ne, hcd, hcd.symm]
            · simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel,
                hab, hab.symm, hbd_ne, hcd, hcd.symm]; exact fun h => hbd_ne h.symm
          have hPb_d : P (f prof).rel b d := hwp prof b d hb hd hAll_b_d
          exact (P_trans (f prof).trans hPa_b hPb_d).2 hPd_a.1
      · -- a≠c, b≠c, a≠d: check b=d fork
        by_cases hbd2 : b = d
        · -- b=d (fork): after subst, d→b. i on (a,b), j on (c,b) bidirectional.
          -- Cycle: c>b (j.1), b>a (i.2), a>c (Pareto)
          subst hbd2
          have hac' : ¬a = c := hac
          let base : PrefOrder σ := ⟨fun _ _ => True, fun _ => trivial,
            fun _ _ => Or.inl trivial, fun _ _ _ _ _ => trivial⟩
          let prof : Profile ι σ := fun k =>
            if k = i then maketop_pref (maketop_pref (makebot_pref base c) a) b
            else if k = j then maketop_pref (maketop_pref (makebot_pref base b) c) a
            else maketop_pref (makebot_pref base c) a
          use prof
          intro ⟨best, hbest⟩
          have hPc_b : P (f prof).rel c b := hj_dec.1 prof (by
            unfold prof; simp only [hij.symm]
            simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel,
                hac', hab, hab.symm, hcd, hcd.symm])
          have hPb_a : P (f prof).rel b a := hi_dec.2 prof (by
            unfold prof; simp only [hij]
            simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel,
                hac', hab, hab.symm, hcd, hcd.symm])
          have hca : c ≠ a := fun h => hac' h.symm
          have hAll_a_c : ∀ k, P (prof k).rel a c := by
            intro k; unfold prof; split_ifs with hki hkj
            · simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel,
                hac', hca, hab, hab.symm, hcd, hcd.symm]
            · simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel,
                hac', hca, hab, hab.symm, hcd, hcd.symm]
            · simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel,
                hac', hca, hab, hcd]
          have hPa_c : P (f prof).rel a c := hwp prof a c ha hc hAll_a_c
          exact (P_trans (f prof).trans hPc_b hPb_a).2 hPa_c.1
        · -- All distinct: 4-cycle a>b>c>d>a using 4 alternatives
          -- i on (a,b) bidirectional, j on (c,d) bidirectional
          -- Cycle: a>b (i.1), b>c (Pareto), c>d (j.1), d>a (Pareto)
          let base : PrefOrder σ := ⟨fun _ _ => True, fun _ => trivial,
            fun _ _ => Or.inl trivial, fun _ _ _ _ _ => trivial⟩
          let prof : Profile ι σ := fun k =>
            if k = i then maketop_pref (maketop_pref (maketop_pref (makebot_pref base c) b) a) d
            else if k = j then maketop_pref (maketop_pref (maketop_pref (makebot_pref base a) d) c) b
            else maketop_pref (maketop_pref (makebot_pref base c) b) d
          use prof
          intro ⟨best, hbest⟩
          have hdb : ¬d = b := fun h => hbd2 h.symm
          have hda : ¬d = a := fun h => had h.symm
          have hca : ¬c = a := fun h => hac h.symm
          have hPa_b : P (f prof).rel a b := hi_dec.1 prof (by
            unfold prof; simp only [hij]
            simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel,
                hab, hab.symm, hac, hca, had, hda, hbc, hcb, hbd2, hdb, hcd])
          have hPc_d : P (f prof).rel c d := hj_dec.1 prof (by
            unfold prof; simp only [hij.symm]
            simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel,
                hab, hab.symm, hac, hca, had, hda, hbc, hcb, hbd2, hdb, hcd, hcd.symm])
          have hAll_b_c : ∀ k, P (prof k).rel b c := by
            intro k; unfold prof; split_ifs with hki hkj
            · simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel,
                hab, hab.symm, hac, hca, had, hda, hbc, hcb, hbd2, hdb, hcd, hcd.symm]
            · simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel,
                hab, hab.symm, hac, hca, had, hda, hbc, hcb, hbd2, hdb, hcd, hcd.symm]
            · simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel,
                hab, hab.symm, hac, hca, had, hda, hbc, hcb, hbd2, hdb, hcd, hcd.symm]
          have hAll_d_a : ∀ k, P (prof k).rel d a := by
            intro k; unfold prof; split_ifs with hki hkj
            · simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel,
                hab, hab.symm, hac, hca, had, hda, hbc, hcb, hbd2, hdb, hcd, hcd.symm]
            · simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel,
                hab, hab.symm, hac, hca, had, hda, hbc, hcb, hbd2, hdb, hcd, hcd.symm]
            · simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel,
                hab, hab.symm, hac, hca, had, hda, hbc, hcb, hbd2, hdb, hcd, hcd.symm]
          have hPb_c : P (f prof).rel b c := hwp prof b c hb hc hAll_b_c
          have hPd_a : P (f prof).rel d a := hwp prof d a hd ha hAll_d_a
          exact (P_trans (f prof).trans hPa_b hPb_c).2
            (P_trans (f prof).trans hPc_d hPd_a).1

/-! ## Example: The Book Reading Paradox -/

/-- Classic example with Prude (p) and Lewd (l) choosing who reads a book
    Alternatives: np (no one reads), pr (prude reads), lr (lewd reads) -/

-- The paradox arises because:
-- 1. Prude is decisive over (pr, lr): prefers not to read if Lewd reads
-- 2. Lewd is decisive over (np, lr): prefers to read rather than no one
-- 3. Both agree (Pareto): (np, pr) - better if Prude reads than no one
--
-- This creates a cycle: np > pr (Pareto), pr > lr (Prude), lr > np (Lewd)
-- No social choice function can break this cycle

theorem book_paradox_demonstrates_sen
    (prude lewd : ι) (hne : prude ≠ lewd)
    (np pr lr : σ) (hdist : np ≠ pr ∧ pr ≠ lr ∧ np ≠ lr)
    (f : SWF ι σ) (X : Finset σ)
    (hX : X = {np, pr, lr})
    (hwp : weak_pareto f X)
    (hprude : is_decisive_over f prude pr lr)
    (hlewd : is_decisive_over f lewd lr np) :
    ∃ prof : Profile ι σ,
      P (f prof).rel np pr ∧ P (f prof).rel pr lr ∧ P (f prof).rel lr np := by
  -- Construct a base PrefOrder (using Classical.choice)
  have ⟨hnppr, hprlr, hnp_lr⟩ := hdist
  let base : PrefOrder σ := ⟨fun _ _ => True, fun _ => trivial,
    fun _ _ => Or.inl trivial, fun _ _ _ _ _ => trivial⟩
  -- Profile construction:
  --   Prude: np top, lr bottom → P np pr, P pr lr
  --   Lewd: lr top, pr bottom → P lr np, P np pr
  --   Others: np top → P np pr
  let prof : Profile ι σ := fun i =>
    if i = prude then
      maketop_pref (makebot_pref base lr) np
    else if i = lewd then
      maketop_pref (makebot_pref base pr) lr
    else
      maketop_pref base np
  use prof
  -- Step 1: Everyone prefers np > pr (Weak Pareto)
  have hpr_np : pr ≠ np := fun h => hnppr h.symm
  have hlr_np : lr ≠ np := fun h => hnp_lr h.symm
  have hpr_lr : pr ≠ lr := hprlr
  have hAllNpPr : ∀ i : ι, P (prof i).rel np pr := by
    intro i
    unfold prof
    split_ifs with hi_p hi_l
    · -- Prude: maketop(makebot(base, lr), np) → np is top → P np pr
      simp [P, maketop_pref, maketop_rel, hpr_np, hlr_np]
    · -- Lewd: maketop(makebot(base, pr), lr) → np, pr ≠ lr
      simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel, hnppr, hnp_lr, hpr_lr]
    · -- Others: maketop(base, np) → np is top → P np pr
      simp [P, maketop_pref, maketop_rel, hpr_np]
  have hPnpPr : P (f prof).rel np pr := hwp prof np pr
    (by rw [hX]; simp) (by rw [hX]; simp) hAllNpPr
  -- Step 2: Prude prefers pr > lr (decisive)
  have hPrudePrLr : P (prof prude).rel pr lr := by
    unfold prof; simp only [hne]
    simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel, hpr_np, hlr_np, hpr_lr]
  have hPprLr : P (f prof).rel pr lr :=
    hprude.1 prof hPrudePrLr
  -- Step 3: Lewd prefers lr > np (decisive)
  have hLewdLrNp : P (prof lewd).rel lr np := by
    unfold prof; simp only [hne.symm]
    simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel, hnp_lr]
  have hPlrNp : P (f prof).rel lr np :=
    hlewd.1 prof hLewdLrNp
  exact ⟨hPnpPr, hPprLr, hPlrNp⟩

/-! ## Resolution Approaches -/

-- Sen's paradox has led to various resolution approaches:
-- 1. Restricting the domain (not all profiles allowed)
-- 2. Weakening Pareto (conditional Pareto)
-- 3. Weakening liberalism (conditional liberalism)
-- 4. Procedural approaches (rights as game forms)

-- The paradox remains philosophically important as it shows
-- a fundamental tension between efficiency and individual rights.
