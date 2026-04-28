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

import SocialChoice.Basic
import SocialChoice.Arrow
import Mathlib.Tactic

variable {ι : Type*} {σ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq σ]

/-! ## Minimal Liberalism -/

/-- Individual i is decisive over the pair (x, y):
    If i strictly prefers x to y, society does too -/
def is_decisive_over (f : SWF ι σ) (i : ι) (x y : σ) : Prop :=
  ∀ prof : Profile ι σ, P (prof i).rel x y → P (f prof).rel x y

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
      have hPa_b : P (f prof).rel a b := hi_dec prof (by
        unfold prof; simp only [hij]
        show maketop_rel (fun _ _ ↦ True) a a b ∧ ¬maketop_rel (fun _ _ ↦ True) a b a
        simp [maketop_rel, hab, hab.symm])
      have hPb_a : P (f prof).rel b a := hj_dec prof (by
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
      have hPa_b : P (f prof).rel a b := hi_dec prof (by
        unfold prof; simp only [hij]
        simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel, hab, had, hbd])
      have hPb_d : P (f prof).rel b d := hj_dec prof (by
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
      have hPa_b : P (f prof).rel a b := hi_dec prof (by
        unfold prof; simp only [hij]
        simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel, hab, hab.symm, hca, hca.symm])
      have hPc_a : P (f prof).rel c a := hj_dec prof (by
        unfold prof; simp only [hij.symm]
        simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel, hca.symm, hab, hab.symm, hca])
      have hcb : ¬c = b := fun h => hbc h.symm
      have hAll_b_c : ∀ k, P (prof k).rel b c := by
        intro k; unfold prof; split_ifs with hki
        · simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel,
            hab, hab.symm, hca, hca.symm, hbc]
        · simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel,
            hab, hab.symm, hca, hca.symm, hcb]
      have hPb_c : P (f prof).rel b c := hwp prof b c hb hc hAll_b_c
      exact (P_trans (f prof).trans hPa_b hPb_c).2 hPc_a.1
    · -- a≠d: with b≠c, a≠d, the remaining cases (a=c, b=d, all-distinct)
      -- require chain-compatible overlap or bidirectional decisiveness.
      -- With one-directional is_decisive_over, the fork cases (a=c, b=d)
      -- and all-distinct case cannot form a cycle from our profile constructions.
      -- These cases need either bidirectional decisiveness or more expressive profiles.
      sorry

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
    hprude prof hPrudePrLr
  -- Step 3: Lewd prefers lr > np (decisive)
  have hLewdLrNp : P (prof lewd).rel lr np := by
    unfold prof; simp only [hne.symm]
    simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel, hnp_lr]
  have hPlrNp : P (f prof).rel lr np :=
    hlewd prof hLewdLrNp
  exact ⟨hPnpPr, hPprLr, hPlrNp⟩

/-! ## Resolution Approaches -/

-- Sen's paradox has led to various resolution approaches:
-- 1. Restricting the domain (not all profiles allowed)
-- 2. Weakening Pareto (conditional Pareto)
-- 3. Weakening liberalism (conditional liberalism)
-- 4. Procedural approaches (rights as game forms)

-- The paradox remains philosophically important as it shows
-- a fundamental tension between efficiency and individual rights.
