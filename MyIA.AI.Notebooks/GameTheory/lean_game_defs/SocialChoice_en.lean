/-
  Social Choice Theory in Lean 4
  ==============================

  Formalizes key concepts from social choice theory:
  - Preferences and orderings
  - Social welfare functions
  - Arrow's axioms (Pareto, IIA, Non-dictatorship)
  - Arrow's Impossibility Theorem (statement)

  Based on GameTheory-19-Lean-SocialChoice.ipynb
  Inspired by asouther4/lean-social-choice (Lean 3)

  ---
  i18n sibling: this module is the EN mirror of the FR canonical
  `SocialChoice.lean` (sibling-pair Pattern A, ratified by user on 2026-07-04,
  EPIC #4980). The FR canonical lives in `SocialChoice.lean` (top-level
  declarations, no namespace). Unlike `Nash_en.lean` (which `import Basic`
  because `Nash.lean` depends on the shared `Game2x2` base), `SocialChoice.lean`
  is self-contained (no imports, Lean core only), so this EN mirror is likewise
  self-contained and re-declares its types (`Preference`, `SocialWelfareFunction`,
  ...) inside `namespace SocialChoiceEn` to avoid name collisions with the FR
  `SocialChoice` module when both live in the same lake. The body of
  definitions, signatures, tactics and the `arrow_impossibility` proof is
  byte-identical between the two files; only the docstrings `/-! ... -/`
  (section headings) and `/-- ... -/` (declaration docstrings) differ — EN in
  this file, FR in `SocialChoice.lean`.
-/

namespace SocialChoiceEn

/-!
## Preferences
-/

/-- A preference relation is a binary relation on alternatives. -/
structure Preference (A : Type) where
  /-- R x y means "x is at least as good as y" -/
  R : A → A → Prop
  /-- Completeness: for any x, y, either R x y or R y x -/
  complete : ∀ x y, R x y ∨ R y x
  /-- Transitivity -/
  trans : ∀ x y z, R x y → R y z → R x z

/-- Strict preference: x is strictly preferred to y -/
def StrictPref {A : Type} (p : Preference A) (x y : A) : Prop :=
  p.R x y ∧ ¬p.R y x

/-- Indifference: x and y are equally good -/
def Indifferent {A : Type} (p : Preference A) (x y : A) : Prop :=
  p.R x y ∧ p.R y x

/-!
## Social Welfare Functions
-/

/-- A social welfare function aggregates individual preferences into a social preference -/
structure SocialWelfareFunction (I A : Type) where
  /-- The aggregation function -/
  aggregate : (I → Preference A) → Preference A

/-!
## Arrow's Axioms
-/

/-- Weak Pareto: If everyone strictly prefers x to y, society prefers x to y -/
def WeakPareto {I A : Type} (swf : SocialWelfareFunction I A) : Prop :=
  ∀ prefs : I → Preference A, ∀ x y,
    (∀ i, StrictPref (prefs i) x y) → StrictPref (swf.aggregate prefs) x y

/-- Independence of Irrelevant Alternatives (IIA) -/
def IIA {I A : Type} (swf : SocialWelfareFunction I A) : Prop :=
  ∀ prefs prefs' : I → Preference A, ∀ x y,
    -- If preferences x vs y are identical in both profiles
    (∀ i, (prefs i).R x y ↔ (prefs' i).R x y) →
    (∀ i, (prefs i).R y x ↔ (prefs' i).R y x) →
    -- Then the social preference on x, y is identical
    ((swf.aggregate prefs).R x y ↔ (swf.aggregate prefs').R x y)

/-- Non-dictatorship: No single individual determines the social preference -/
def NonDictatorial {I A : Type} (swf : SocialWelfareFunction I A) : Prop :=
  ¬∃ d : I, ∀ prefs : I → Preference A, ∀ x y,
    StrictPref (prefs d) x y → StrictPref (swf.aggregate prefs) x y

/-!
## Arrow's Impossibility Theorem
-/

/-!
**Statement.** There is no social welfare function over at least three
alternatives that simultaneously satisfies:

1. Weak Pareto;
2. Independence of Irrelevant Alternatives (IIA);
3. non-dictatorship.

Stated with explicit `Fin n` types instead of a generic `Fintype` to avoid the
Mathlib dependency: the mathematical content of the theorem is identical.

The proof is given at the end of the file (the "Stage 4b" section); the
`axiom arrow_impossibility` declaration that stated it without proof has been
removed (#23022).
-/

/-!
## Examples
-/

/-- Dictatorship SWF: Individual d's preference becomes social preference -/
def dictatorship {I A : Type} (d : I) : SocialWelfareFunction I A := {
  aggregate := fun prefs => prefs d
}

/-- Theorem: A dictatorship satisfies Pareto and IIA -/
theorem dictatorship_satisfies_pareto {I A : Type} (d : I) :
    WeakPareto (dictatorship (I := I) (A := A) d) := by
  intro prefs x y h_all
  exact h_all d

theorem dictatorship_satisfies_iia {I A : Type} (d : I) :
    IIA (dictatorship (I := I) (A := A) d) := by
  intro prefs prefs' x y h1 h2
  exact h1 d

/-!
## Sen's Impossibility
-/

/-- Minimal Liberalism: Some individual is decisive over some pair -/
def MinimalLiberalism {I A : Type} (swf : SocialWelfareFunction I A) : Prop :=
  ∃ i : I, ∃ x y : A,
    ∀ prefs : I → Preference A,
      StrictPref (prefs i) x y → StrictPref (swf.aggregate prefs) x y

/- Sen's Impossibility Theorem:
   this definition is not enough to state it. The proof is at the end of the
   file (section "Sen's Impossibility: the proof"): it bears on a stronger
   condition, `SenLiberalism` (two distinct individuals, two crossing pairs).
   `dictatorship_minimally_liberal` shows why: a dictatorship satisfies
   `MinimalLiberalism`, so Pareto and minimal liberalism are compatible under
   that definition. -/

/-!
## Utility Representations
-/

/-- A utility function represents a preference if u(x) ≥ u(y) iff R x y -/
def represents {A : Type} (u : A → Int) (p : Preference A) : Prop :=
  ∀ x y, p.R x y ↔ u x >= u y

/-- Create a preference from a utility function -/
def prefFromUtility {A : Type} (u : A → Int)
    (h_finite : ∀ x y, u x >= u y ∨ u y >= u x := by decide) : Preference A := {
  R := fun x y => u x >= u y
  complete := h_finite
  trans := fun x y z hxy hyz => by omega
}

/-!
## Decisive coalitions

Stage 1 of the port of the proof of Arrow's theorem (#23022), which must
eventually replace the `arrow_impossibility` axiom declared above. The notion
is Arrow's: a coalition `D` is decisive on the pair `(x, y)` if, whenever its
members unanimously prefer `x` to `y` and everyone else unanimously prefers
`y` to `x`, the social preference goes the way of `D`.

These lemmas stay in pure Lean core: the auxiliary profiles are built from
integer utility functions (`rank3`) rather than combinatorial orders, which
avoids `Finset`/`Fintype` and keeps the lake dependency-free. Any function
`A → Int` defines a valid preference (`prefOfUtility`), and that is what makes
the constructions available without a library.
-/

/-- Rank of an alternative in a profile that distinguishes three alternatives:
`a` gets `va`, `b` gets `vb`, `c` gets `vc`, every other alternative gets `0`.
Enough to build the auxiliary profiles of Arrow's proof. -/
def rank3 {A : Type} [DecidableEq A] (a b c : A) (va vb vc : Int) : A → Int :=
  fun z => if z = a then va else if z = b then vb else if z = c then vc else 0

/-- Preference induced by an integer utility function: `x` is at least as good
as `y` if and only if its utility is greater than or equal to it. -/
def prefOfUtility {A : Type} (u : A → Int) : Preference A where
  R := fun x y => u x ≥ u y
  complete := fun x y => by
    by_cases h : u x ≥ u y
    · exact Or.inl h
    · exact Or.inr (by omega)
  trans := fun x y z hxy hyz => by omega

/-- `D` is decisive on the pair `(x, y)`: as soon as every member of `D`
strictly prefers `x` to `y` and every non-member strictly prefers `y` to `x`,
society strictly prefers `x` to `y`. -/
def Decisive {I A : Type} (swf : SocialWelfareFunction I A) (D : I → Prop)
    (x y : A) : Prop :=
  ∀ prefs : I → Preference A,
    (∀ i, D i → StrictPref (prefs i) x y) →
    (∀ i, ¬ D i → StrictPref (prefs i) y x) →
    StrictPref (swf.aggregate prefs) x y

/-- Weak Pareto makes the coalition of all agents a decisive coalition on
every pair. -/
theorem decisive_unanimous {I A : Type} (swf : SocialWelfareFunction I A)
    (h : WeakPareto swf) {x y : A} : Decisive swf (fun _ => True) x y := by
  intro prefs hD _
  exact h prefs x y (fun i => hD i trivial)

/-- Field expansion, alternative axis: if `D` is decisive on `(x, y)`, it is
decisive on `(x, z)` for every `z` distinct from `x` and from `y`.

Proof (Arrow's argument): on the auxiliary profile where `D` has `x ≻ y ≻ z`
and the others have `y ≻ z ≻ x`, the decision on `(x, y)` yields `x ≻s y` and
Pareto yields `y ≻s z`, hence `x ≻s z` by transitivity; the comparisons of `x`
against `z` there are those of the target profile, so IIA carries the result. -/
theorem decisive_expand_right {I A : Type} [DecidableEq A]
    (swf : SocialWelfareFunction I A)
    (D : I → Prop) [DecidablePred D] (h_iia : IIA swf) (h_pareto : WeakPareto swf)
    {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h : Decisive swf D x y) : Decisive swf D x z := by
  intro prefs hzD hzND
  let P : I → Preference A :=
    fun i => if D i then prefOfUtility (rank3 x y z 3 2 1)
             else prefOfUtility (rank3 x y z 1 3 2)
  have hPmem : ∀ i, D i → P i = prefOfUtility (rank3 x y z 3 2 1) := by
    intro i hi; simp [P, hi]
  have hPout : ∀ i, ¬ D i → P i = prefOfUtility (rank3 x y z 1 3 2) := by
    intro i hi; simp [P, hi]
  have hdec : StrictPref (swf.aggregate P) x y := by
    apply h P
    · intro i hi
      rw [hPmem i hi]
      exact ⟨by simp [prefOfUtility, rank3, hxy.symm] <;> decide,
        by simp [prefOfUtility, rank3, hxy.symm] <;> decide⟩
    · intro i hi
      rw [hPout i hi]
      exact ⟨by simp [prefOfUtility, rank3, hxy.symm] <;> decide,
        by simp [prefOfUtility, rank3, hxy.symm] <;> decide⟩
  have hpareto : StrictPref (swf.aggregate P) y z :=
    h_pareto P y z (fun i => by
      by_cases hi : D i
      · rw [hPmem i hi]
        exact ⟨by simp [prefOfUtility, rank3, hxy.symm, hxz.symm, hyz.symm] <;> decide,
          by simp [prefOfUtility, rank3, hxy.symm, hxz.symm, hyz.symm] <;> decide⟩
      · rw [hPout i hi]
        exact ⟨by simp [prefOfUtility, rank3, hxy.symm, hxz.symm, hyz.symm] <;> decide,
          by simp [prefOfUtility, rank3, hxy.symm, hxz.symm, hyz.symm] <;> decide⟩)
  have hxzP : StrictPref (swf.aggregate P) x z :=
    ⟨(swf.aggregate P).trans x y z hdec.1 hpareto.1,
     fun hzx => hpareto.2 ((swf.aggregate P).trans z x y hzx hdec.1)⟩
  have h₁ : ∀ i, (P i).R x z ↔ (prefs i).R x z := by
    intro i
    by_cases hi : D i
    · rw [hPmem i hi]
      have hPtrue : (prefOfUtility (rank3 x y z 3 2 1)).R x z := by
        simp [prefOfUtility, rank3, hxz.symm, hyz.symm]
      have hT : (prefs i).R x z := (hzD i hi).1
      exact ⟨fun _ => hT, fun _ => hPtrue⟩
    · rw [hPout i hi]
      have hPfalse : ¬ (prefOfUtility (rank3 x y z 1 3 2)).R x z := by
        simp [prefOfUtility, rank3, hxz.symm, hyz.symm]
      have hT : ¬ (prefs i).R x z := (hzND i hi).2
      exact ⟨fun hc => absurd hc hPfalse, fun hc => absurd hc hT⟩
  have h₂ : ∀ i, (P i).R z x ↔ (prefs i).R z x := by
    intro i
    by_cases hi : D i
    · rw [hPmem i hi]
      have hPfalse : ¬ (prefOfUtility (rank3 x y z 3 2 1)).R z x := by
        simp [prefOfUtility, rank3, hxz.symm, hyz.symm]
      have hT : ¬ (prefs i).R z x := (hzD i hi).2
      exact ⟨fun hc => absurd hc hPfalse, fun hc => absurd hc hT⟩
    · rw [hPout i hi]
      have hPtrue : (prefOfUtility (rank3 x y z 1 3 2)).R z x := by
        simp [prefOfUtility, rank3, hxz.symm, hyz.symm]
      have hT : (prefs i).R z x := (hzND i hi).1
      exact ⟨fun _ => hT, fun _ => hPtrue⟩
  -- IIA is stated for the ordered pair `(x, y)`: the reverse comparison is
  -- obtained by invoking it on `(z, x)` with the two patterns swapped.
  have hiff₁ : (swf.aggregate P).R x z ↔ (swf.aggregate prefs).R x z :=
    h_iia P prefs x z h₁ h₂
  have hiff₂ : (swf.aggregate P).R z x ↔ (swf.aggregate prefs).R z x :=
    h_iia P prefs z x h₂ h₁
  exact ⟨hiff₁.mp hxzP.1, fun hzx => hxzP.2 (hiff₂.mpr hzx)⟩

/-- Field expansion, agent axis: if `D` is decisive on `(x, y)`, it is
decisive on `(z, y)` for every `z` distinct from `x` and from `y`.

Proof: on the auxiliary profile where `D` has `z ≻ x ≻ y` and the others have
`y ≻ z ≻ x`, Pareto yields `z ≻s x`, the decision on `(x, y)` yields `x ≻s y`,
hence `z ≻s y`; the comparisons of `z` against `y` there are those of the
target profile, so IIA carries the result. -/
theorem decisive_expand_left {I A : Type} [DecidableEq A]
    (swf : SocialWelfareFunction I A)
    (D : I → Prop) [DecidablePred D] (h_iia : IIA swf) (h_pareto : WeakPareto swf)
    {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h : Decisive swf D x y) : Decisive swf D z y := by
  intro prefs hzD hzND
  let P : I → Preference A :=
    fun i => if D i then prefOfUtility (rank3 z x y 3 2 1)
             else prefOfUtility (rank3 y z x 3 2 1)
  have hPmem : ∀ i, D i → P i = prefOfUtility (rank3 z x y 3 2 1) := by
    intro i hi; simp [P, hi]
  have hPout : ∀ i, ¬ D i → P i = prefOfUtility (rank3 y z x 3 2 1) := by
    intro i hi; simp [P, hi]
  have hdec : StrictPref (swf.aggregate P) x y := by
    apply h P
    · intro i hi
      rw [hPmem i hi]
      exact ⟨by simp [prefOfUtility, rank3, hxz, hyz, hxy.symm] <;> decide,
        by simp [prefOfUtility, rank3, hxz, hyz, hxy.symm] <;> decide⟩
    · intro i hi
      rw [hPout i hi]
      exact ⟨by simp [prefOfUtility, rank3, hxy, hxz] <;> decide,
        by simp [prefOfUtility, rank3, hxy, hxz] <;> decide⟩
  have hzxP : StrictPref (swf.aggregate P) z x :=
    h_pareto P z x (fun i => by
      by_cases hi : D i
      · rw [hPmem i hi]
        exact ⟨by simp [prefOfUtility, rank3, hxz] <;> decide,
          by simp [prefOfUtility, rank3, hxz] <;> decide⟩
      · rw [hPout i hi]
        exact ⟨by simp [prefOfUtility, rank3, hxy, hxz, hyz.symm] <;> decide,
          by simp [prefOfUtility, rank3, hxy, hxz, hyz.symm] <;> decide⟩)
  have hzyP : StrictPref (swf.aggregate P) z y :=
    ⟨(swf.aggregate P).trans z x y hzxP.1 hdec.1,
     fun hyz' => hdec.2 ((swf.aggregate P).trans y z x hyz' hzxP.1)⟩
  have h₁ : ∀ i, (P i).R z y ↔ (prefs i).R z y := by
    intro i
    by_cases hi : D i
    · rw [hPmem i hi]
      have hPtrue : (prefOfUtility (rank3 z x y 3 2 1)).R z y := by
        simp [prefOfUtility, rank3, hyz, hxy.symm]
      have hT : (prefs i).R z y := (hzD i hi).1
      exact ⟨fun _ => hT, fun _ => hPtrue⟩
    · rw [hPout i hi]
      have hPfalse : ¬ (prefOfUtility (rank3 y z x 3 2 1)).R z y := by
        simp [prefOfUtility, rank3, hyz.symm]
      have hT : ¬ (prefs i).R z y := (hzND i hi).2
      exact ⟨fun hc => absurd hc hPfalse, fun hc => absurd hc hT⟩
  have h₂ : ∀ i, (P i).R y z ↔ (prefs i).R y z := by
    intro i
    by_cases hi : D i
    · rw [hPmem i hi]
      have hPfalse : ¬ (prefOfUtility (rank3 z x y 3 2 1)).R y z := by
        simp [prefOfUtility, rank3, hyz, hxy.symm]
      have hT : ¬ (prefs i).R y z := (hzD i hi).2
      exact ⟨fun hc => absurd hc hPfalse, fun hc => absurd hc hT⟩
    · rw [hPout i hi]
      have hPtrue : (prefOfUtility (rank3 y z x 3 2 1)).R y z := by
        simp [prefOfUtility, rank3, hyz.symm]
      have hT : (prefs i).R y z := (hzND i hi).1
      exact ⟨fun _ => hT, fun _ => hPtrue⟩
  have hiff₁ : (swf.aggregate P).R z y ↔ (swf.aggregate prefs).R z y :=
    h_iia P prefs z y h₁ h₂
  have hiff₂ : (swf.aggregate P).R y z ↔ (swf.aggregate prefs).R y z :=
    h_iia P prefs y z h₂ h₁
  exact ⟨hiff₁.mp hzyP.1, fun hyz' => hzyP.2 (hiff₂.mpr hyz')⟩

/-- Symmetry of the field: if `D` is decisive on `(x, y)`, it is decisive on the
reversed pair `(y, x)`.

This is the step stage 1 did not cross, and it is not free: `IIA` is stated for
the **ordered pair**, so the reversal does not transport by a mere rewriting.
The proof walks three distinct pairs over a pool of three alternatives —
`(x, y) → (x, z) → (y, z) → (y, x)` — each step being a field expansion already
established. -/
theorem decisive_swap {I A : Type} [DecidableEq A]
    (swf : SocialWelfareFunction I A)
    (D : I → Prop) [DecidablePred D] (h_iia : IIA swf) (h_pareto : WeakPareto swf)
    {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h : Decisive swf D x y) : Decisive swf D y x := by
  have h1 : Decisive swf D x z :=
    decisive_expand_right swf D h_iia h_pareto hxy hxz hyz h
  have h2 : Decisive swf D y z :=
    decisive_expand_left swf D h_iia h_pareto hxz hxy hyz.symm h1
  exact decisive_expand_right swf D h_iia h_pareto hyz hxy.symm hxz.symm h2

/-- Closure of the field: over three pairwise distinct alternatives, a coalition
decisive on a single pair is decisive on all six ordered pairs.

The two expansions of stage 1 only cover the pairs that keep one side;
`decisive_swap` supplies the reversed pairs, and the closure follows. This is
the exact hypothesis the rest of the port needs: to shrink the decisive
coalition, one must be able to read a decision on any pair, not only on the one
that established it. -/
theorem decisive_field {I A : Type} [DecidableEq A]
    (swf : SocialWelfareFunction I A)
    (D : I → Prop) [DecidablePred D] (h_iia : IIA swf) (h_pareto : WeakPareto swf)
    {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h : Decisive swf D x y) :
    Decisive swf D x y ∧ Decisive swf D y x ∧ Decisive swf D x z ∧
    Decisive swf D z x ∧ Decisive swf D y z ∧ Decisive swf D z y := by
  have h1 : Decisive swf D x z :=
    decisive_expand_right swf D h_iia h_pareto hxy hxz hyz h
  have h2 : Decisive swf D z y :=
    decisive_expand_left swf D h_iia h_pareto hxy hxz hyz h
  have h3 : Decisive swf D z x :=
    decisive_expand_right swf D h_iia h_pareto hyz.symm hxz.symm hxy.symm h2
  have h4 : Decisive swf D y x :=
    decisive_swap swf D h_iia h_pareto hxy hxz hyz h
  have h5 : Decisive swf D y z :=
    decisive_expand_right swf D h_iia h_pareto hxy.symm hyz hxz h4
  exact ⟨h, h4, h1, h3, h5, h2⟩

/-- Contraction: a decisive coalition splits. If `D` is decisive on `(x, y)`
and is covered by two disjoint parts `D₁` and `D₂`, then one of the two is
decisive — `D₁` on `(x, z)`, `D₂` on `(z, y)`.

This is the brick that makes decisive coalitions **shrink**: combined with
field closure (`decisive_field`), it produces, on a finite set of agents, a
minimal decisive coalition — and minimality will make it a dictator. Proof
(Arrow's argument): on the profile where `D₁` holds `x ≻ y ≻ z`, `D₂` holds
`z ≻ x ≻ y` and the others hold `y ≻ z ≻ x`, every member of `D` prefers
`x` to `y`, so the decision of `D` yields `x ≻s y`. If `z ≳s x`, then
`z ≳s y` by transitivity, and strictly `z ≻s y` (otherwise
`y ≳s z ≳s x ≳s y` would contradict `x ≻s y`); only the members of `D₂`
prefer `z` to `y` in this profile, so IIA transports the decision. Otherwise
`x ≻s z` by completeness, and only the members of `D₁` prefer `x` to `z`:
IIA transports. Pareto plays no role — the initial decision comes from the
decisiveness of `D` itself. -/
theorem decisive_split {I A : Type} [DecidableEq A]
    (swf : SocialWelfareFunction I A)
    (D D1 D2 : I → Prop) [DecidablePred D1] [DecidablePred D2]
    (h_iia : IIA swf)
    (h1in : ∀ i, D1 i → D i) (h2in : ∀ i, D2 i → D i)
    (hcover : ∀ i, D i → D1 i ∨ D2 i) (hdisj : ∀ i, ¬ (D1 i ∧ D2 i))
    {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h : Decisive swf D x y) :
    Decisive swf D1 x z ∨ Decisive swf D2 z y := by
  -- Auxiliary profile: D₁ holds x ≻ y ≻ z, D₂ holds z ≻ x ≻ y, others y ≻ z ≻ x.
  let P : I → Preference A :=
    fun i => if D1 i then prefOfUtility (rank3 x y z 3 2 1)
             else if D2 i then prefOfUtility (rank3 z x y 3 2 1)
             else prefOfUtility (rank3 y z x 3 2 1)
  have hP1 : ∀ i, D1 i → P i = prefOfUtility (rank3 x y z 3 2 1) := by
    intro i hi; simp [P, hi]
  have hP2 : ∀ i, D2 i → P i = prefOfUtility (rank3 z x y 3 2 1) := by
    intro i hi
    have hnd1 : ¬ D1 i := fun hc => hdisj i ⟨hc, hi⟩
    simp [P, hnd1, hi]
  have hPout : ∀ i, ¬ D1 i → ¬ D2 i → P i = prefOfUtility (rank3 y z x 3 2 1) := by
    intro i h1 h2; simp [P, h1, h2]
  -- Every member of D prefers x to y, every non-member y to x:
  -- the decisiveness of D on (x, y) applies to P as is.
  have hdec : StrictPref (swf.aggregate P) x y := by
    apply h P
    · intro i hi
      by_cases h1 : D1 i
      · rw [hP1 i h1]
        exact ⟨by simp [prefOfUtility, rank3, hxy.symm] <;> decide,
          by simp [prefOfUtility, rank3, hxy.symm] <;> decide⟩
      · have h2 : D2 i := ((hcover i hi).resolve_left h1)
        rw [hP2 i h2]
        exact ⟨by simp [prefOfUtility, rank3, hxz, hyz, hxy.symm] <;> decide,
          by simp [prefOfUtility, rank3, hxz, hyz, hxy.symm] <;> decide⟩
    · intro i hi
      have h1 : ¬ D1 i := fun hc => hi (h1in i hc)
      have h2 : ¬ D2 i := fun hc => hi (h2in i hc)
      rw [hPout i h1 h2]
      exact ⟨by simp [prefOfUtility, rank3, hxy, hxz] <;> decide,
        by simp [prefOfUtility, rank3, hxy, hxz] <;> decide⟩
  -- The social orientation on (z, x) decides which half is decisive.
  by_cases hzx : (swf.aggregate P).R z x
  · right
    have hzy : StrictPref (swf.aggregate P) z y :=
      ⟨(swf.aggregate P).trans z x y hzx hdec.1,
       fun hyz' => hdec.2 ((swf.aggregate P).trans y z x hyz' hzx)⟩
    intro prefs hD2 hND2
    have h₁ : ∀ i, (P i).R z y ↔ (prefs i).R z y := by
      intro i
      by_cases hi : D2 i
      · rw [hP2 i hi]
        have hPtrue : (prefOfUtility (rank3 z x y 3 2 1)).R z y := by
          simp [prefOfUtility, rank3, hyz, hxy.symm]
        have hT : (prefs i).R z y := (hD2 i hi).1
        exact ⟨fun _ => hT, fun _ => hPtrue⟩
      · have hPfalse : ¬ (P i).R z y := by
          by_cases h1 : D1 i
          · rw [hP1 i h1]
            simp [prefOfUtility, rank3, hxy.symm, hxz.symm, hyz.symm]
          · rw [hPout i h1 hi]
            simp [prefOfUtility, rank3, hyz.symm]
        have hT : ¬ (prefs i).R z y := (hND2 i hi).2
        exact ⟨fun hc => absurd hc hPfalse, fun hc => absurd hc hT⟩
    have h₂ : ∀ i, (P i).R y z ↔ (prefs i).R y z := by
      intro i
      by_cases hi : D2 i
      · rw [hP2 i hi]
        have hPfalse : ¬ (prefOfUtility (rank3 z x y 3 2 1)).R y z := by
          simp [prefOfUtility, rank3, hyz, hxy.symm]
        have hT : ¬ (prefs i).R y z := (hD2 i hi).2
        exact ⟨fun hc => absurd hc hPfalse, fun hc => absurd hc hT⟩
      · have hPtrue : (P i).R y z := by
          by_cases h1 : D1 i
          · rw [hP1 i h1]
            simp [prefOfUtility, rank3, hxy.symm, hxz.symm, hyz.symm]
          · rw [hPout i h1 hi]
            simp [prefOfUtility, rank3, hyz.symm]
        have hT : (prefs i).R y z := (hND2 i hi).1
        exact ⟨fun _ => hT, fun _ => hPtrue⟩
    have hiff₁ : (swf.aggregate P).R z y ↔ (swf.aggregate prefs).R z y :=
      h_iia P prefs z y h₁ h₂
    have hiff₂ : (swf.aggregate P).R y z ↔ (swf.aggregate prefs).R y z :=
      h_iia P prefs y z h₂ h₁
    exact ⟨hiff₁.mp hzy.1, fun hyz' => hzy.2 (hiff₂.mpr hyz')⟩
  · left
    have hxzS : StrictPref (swf.aggregate P) x z :=
      ⟨((swf.aggregate P).complete x z).resolve_right hzx, hzx⟩
    intro prefs hD1 hND1
    have h₁ : ∀ i, (P i).R x z ↔ (prefs i).R x z := by
      intro i
      by_cases hi : D1 i
      · rw [hP1 i hi]
        have hPtrue : (prefOfUtility (rank3 x y z 3 2 1)).R x z := by
          simp [prefOfUtility, rank3, hxz.symm, hyz.symm]
        have hT : (prefs i).R x z := (hD1 i hi).1
        exact ⟨fun _ => hT, fun _ => hPtrue⟩
      · have hPfalse : ¬ (P i).R x z := by
          by_cases h2 : D2 i
          · rw [hP2 i h2]
            simp [prefOfUtility, rank3, hxz]
          · rw [hPout i hi h2]
            simp [prefOfUtility, rank3, hxy, hxz, hyz.symm]
        have hT : ¬ (prefs i).R x z := (hND1 i hi).2
        exact ⟨fun hc => absurd hc hPfalse, fun hc => absurd hc hT⟩
    have h₂ : ∀ i, (P i).R z x ↔ (prefs i).R z x := by
      intro i
      by_cases hi : D1 i
      · rw [hP1 i hi]
        have hPfalse : ¬ (prefOfUtility (rank3 x y z 3 2 1)).R z x := by
          simp [prefOfUtility, rank3, hxz.symm, hyz.symm]
        have hT : ¬ (prefs i).R z x := (hD1 i hi).2
        exact ⟨fun hc => absurd hc hPfalse, fun hc => absurd hc hT⟩
      · have hPtrue : (P i).R z x := by
          by_cases h2 : D2 i
          · rw [hP2 i h2]
            simp [prefOfUtility, rank3, hxz]
          · rw [hPout i hi h2]
            simp [prefOfUtility, rank3, hxy, hxz, hyz.symm]
        have hT : (prefs i).R z x := (hND1 i hi).1
        exact ⟨fun _ => hT, fun _ => hPtrue⟩
    have hiff₁ : (swf.aggregate P).R x z ↔ (swf.aggregate prefs).R x z :=
      h_iia P prefs x z h₁ h₂
    have hiff₂ : (swf.aggregate P).R z x ↔ (swf.aggregate prefs).R z x :=
      h_iia P prefs z x h₂ h₁
    exact ⟨hiff₁.mp hxzS.1, fun hzx' => hxzS.2 (hiff₂.mpr hzx')⟩

/-!
## Stage 4a: global decisiveness and the dictator

Second-to-last stage of the reduction of the `arrow_impossibility` axiom
(#23022). What remains afterwards is producing a decisive singleton — stage 4b
does it by descending over the tails `{i | m ≤ i}` pre-split by
`decisive_split`, with no cardinality measure at all (the induction runs on
`nI - m`).

- `decisive_global`: a coalition decisive on a single pair of distinct
  alternatives is decisive on every pair. The two expansion lemmas move each
  coordinate independently; only folding the first coordinate onto `y` needs a
  third alternative outside `{x, y}` (hypothesis `hcard`, satisfied as soon as
  the set has three elements).
- `empty_not_decisive`: no empty coalition is decisive under Pareto — the
  unanimous `y ≻ x` profile puts the conclusion in direct contradiction with
  Pareto. This is the anchor that will prevent the contraction from reaching
  the empty set.
- `decisive_singleton_dictator`: a singleton decisive on every pair is a
  dictator in the exact sense of `NonDictatorial`. On the auxiliary profile
  where `d` ranks `z` strictly between `x` and `y` and every other agent keeps
  their exact `x`/`y` relations with `z` moved to last position (`zLast`),
  Pareto yields `x ≻ₛ z` (unanimity) and decisiveness yields `z ≻ₛ y`;
  transitivity produces `x ≻ₛ y`, which IIA transports back to the original
  profile, individual by individual. The `zLast` construction preserves both
  directions of the `x`/`y` relation with no case analysis on other agents'
  preferences; its order proofs (`complete`, `antisymm`) do split on equalities
  over `A` via `by_cases` with no `DecidableEq` instance, which draws
  `Classical.choice` — `zLast` carries `[propext, Classical.choice, Quot.sound]`,
  just like `decisive_split`.
-/

/-- Preference where `z` moves to a strict last position: relations between
alternatives distinct from `z` are exactly those of `p`, and every alternative
distinct from `z` is strictly preferred to `z`. -/
def zLast {A : Type} (p : Preference A) (z : A) : Preference A where
  R := fun a b => (a = z ∧ b = z) ∨ (b = z ∧ a ≠ z) ∨ (a ≠ z ∧ b ≠ z ∧ p.R a b)
  complete := by
    intro a b
    by_cases haz : a = z
    · by_cases hbz : b = z
      · exact Or.inl (Or.inl ⟨haz, hbz⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨haz, hbz⟩))
    · by_cases hbz : b = z
      · exact Or.inl (Or.inr (Or.inl ⟨hbz, haz⟩))
      · rcases p.complete a b with h | h
        · exact Or.inl (Or.inr (Or.inr ⟨haz, hbz, h⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨hbz, haz, h⟩))
  trans := by
    intro a b c hab hbc
    rcases hab with ⟨haz, hbz⟩ | ⟨hbz, haz⟩ | ⟨haz, hbz, hpab⟩
    · rcases hbc with ⟨_, hcz⟩ | ⟨hcz, _⟩ | ⟨hnb, _, _⟩
      · exact Or.inl ⟨haz, hcz⟩
      · exact Or.inl ⟨haz, hcz⟩
      · exact absurd hbz hnb
    · rcases hbc with ⟨_, hcz⟩ | ⟨hcz, _⟩ | ⟨hnb, _, _⟩
      · exact Or.inr (Or.inl ⟨hcz, haz⟩)
      · exact Or.inr (Or.inl ⟨hcz, haz⟩)
      · exact absurd hbz hnb
    · rcases hbc with ⟨hbz', _⟩ | ⟨hcz, _⟩ | ⟨_, hcz, hpbc⟩
      · exact absurd hbz' hbz
      · exact Or.inr (Or.inl ⟨hcz, haz⟩)
      · exact Or.inr (Or.inr ⟨haz, hcz, p.trans a b c hpab hpbc⟩)

/-- No empty coalition is decisive as long as Pareto holds: on the unanimous
`y ≻ x` profile, the "member" premise is vacuous and the "non-member" premise
is satisfied by everyone, so the conclusion would force `x ≻ₛ y` against the
unanimous Pareto verdict. -/
theorem empty_not_decisive {I A : Type} [DecidableEq A]
    (swf : SocialWelfareFunction I A) (h_pareto : WeakPareto swf)
    {x y : A} (hxy : x ≠ y)
    (h : Decisive swf (fun _ => False) x y) : False := by
  let P : I → Preference A := fun _ => prefOfUtility (rank3 y x y 2 1 0)
  have hyx : ∀ i, StrictPref (P i) y x := fun i =>
    ⟨by simp [P, prefOfUtility, rank3, hxy],
     by simp [P, prefOfUtility, rank3, hxy]⟩
  have hsoc : StrictPref (swf.aggregate P) x y :=
    h P (fun i hi => False.elim hi) (fun i _ => hyx i)
  have hpar : StrictPref (swf.aggregate P) y x :=
    h_pareto P y x hyx
  exact hsoc.2 hpar.1

/-- A coalition decisive on a single pair of distinct alternatives is decisive
on every pair: the expansion lemmas move each coordinate independently, and the
only resistant case (folding the first coordinate onto `y`) goes through a
third alternative `w` outside `{x, y}`. -/
theorem decisive_global {I A : Type} [DecidableEq A]
    (swf : SocialWelfareFunction I A)
    (D : I → Prop) [DecidablePred D]
    (h_iia : IIA swf) (h_pareto : WeakPareto swf)
    {x y : A} (hxy : x ≠ y)
    (hcard : ∃ w : A, w ≠ x ∧ w ≠ y)
    (h : Decisive swf D x y) :
    ∀ a b : A, a ≠ b → Decisive swf D a b := by
  intro a b hab
  by_cases hax : a = x
  · by_cases hby : b = y
    · rw [hax, hby]; exact h
    · rw [hax]
      exact decisive_expand_right swf D h_iia h_pareto hxy
        (fun hc => hab (hax.trans hc)) (fun hc => hby hc.symm) h
  · by_cases hay : a = y
    · obtain ⟨w, hwx, hwy⟩ := hcard
      have hxw : Decisive swf D x w :=
        decisive_expand_right swf D h_iia h_pareto hxy
          (fun hc => hwx hc.symm) (fun hc => hwy hc.symm) h
      have hyw : Decisive swf D y w :=
        decisive_expand_left swf D h_iia h_pareto
          (fun hc => hwx hc.symm) hxy hwy hxw
      by_cases hbw : b = w
      · rw [hay, hbw]; exact hyw
      · rw [hay]
        exact decisive_expand_right swf D h_iia h_pareto
          (fun hc => hwy hc.symm) (fun hc => hab (hay.trans hc))
          (fun hc => hbw hc.symm) hyw
    · have hay' : Decisive swf D a y :=
        decisive_expand_left swf D h_iia h_pareto hxy
          (fun hc => hax hc.symm) (fun hc => hay hc.symm) h
      by_cases hby : b = y
      · rw [hby]; exact hay'
      · exact decisive_expand_right swf D h_iia h_pareto hay hab
          (fun hc => hby hc.symm) hay'

/-- A singleton decisive on every pair is a dictator in the sense of
`NonDictatorial`: every strict preference of the dictator becomes the strict
preference of society, on every profile. -/
theorem decisive_singleton_dictator {I A : Type} [DecidableEq I] [DecidableEq A]
    (swf : SocialWelfareFunction I A)
    (h_iia : IIA swf) (h_pareto : WeakPareto swf)
    (d : I) (hdec : ∀ x y : A, x ≠ y → Decisive swf (fun i => i = d) x y)
    (prefs : I → Preference A) {x y z : A}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hd : StrictPref (prefs d) x y) :
    StrictPref (swf.aggregate prefs) x y := by
  let P : I → Preference A :=
    fun i => if i = d then prefOfUtility (rank3 x z y 3 2 1) else zLast (prefs i) z
  have hPd : ∀ i, i = d → P i = prefOfUtility (rank3 x z y 3 2 1) := by
    intro i hi; simp [P, hi]
  have hPo : ∀ i, i ≠ d → P i = zLast (prefs i) z := by
    intro i hi; simp [P, hi]
  -- Pareto leg: strict unanimity `x ≻ z` on the auxiliary profile.
  have hPxz : StrictPref (swf.aggregate P) x z :=
    h_pareto P x z (fun i => by
      by_cases hid : i = d
      · rw [hPd i hid]
        exact ⟨by simp [prefOfUtility, rank3, hxz.symm],
               by simp [prefOfUtility, rank3, hxz.symm]⟩
      · rw [hPo i hid]
        exact ⟨Or.inr (Or.inl ⟨rfl, hxz⟩), by simp [zLast, hxz]⟩)
  -- Decisiveness leg: `z ≻ y` -- the dictator has `z ≻ y`, everyone else has
  -- `y ≻ z` strictly since `z` is their last choice.
  have hPzy : StrictPref (swf.aggregate P) z y :=
    hdec z y (fun hc => hyz hc.symm) P
      (fun i hid => by
        rw [hPd i hid]
        exact ⟨by simp [prefOfUtility, rank3, hyz, hxy.symm, hxz.symm],
               by simp [prefOfUtility, rank3, hyz, hxy.symm, hxz.symm]⟩)
      (fun i hid => by
        rw [hPo i hid]
        exact ⟨Or.inr (Or.inl ⟨rfl, hyz⟩), by simp [zLast, hyz]⟩)
  -- Individual agreement on the `x`/`y` relations: the `zLast` construction.
  have h₁ : ∀ i, (P i).R x y ↔ (prefs i).R x y := by
    intro i
    by_cases hid : i = d
    · rw [hPd i hid, hid]
      exact ⟨fun _ => hd.1,
             fun _ => by simp [prefOfUtility, rank3, hyz, hxy.symm]⟩
    · rw [hPo i hid]
      constructor
      · intro hc
        rcases hc with ⟨_, hyz1⟩ | ⟨hyz1, _⟩ | ⟨_, _, hp⟩
        · exact absurd hyz1 hyz
        · exact absurd hyz1 hyz
        · exact hp
      · intro hp
        exact Or.inr (Or.inr ⟨hxz, hyz, hp⟩)
  have h₂ : ∀ i, (P i).R y x ↔ (prefs i).R y x := by
    intro i
    by_cases hid : i = d
    · rw [hPd i hid, hid]
      have hPF : ¬ (prefOfUtility (rank3 x z y 3 2 1)).R y x := by
        simp [prefOfUtility, rank3, hyz, hxy.symm]
      exact ⟨fun hc => absurd hc hPF, fun hc => absurd hc hd.2⟩
    · rw [hPo i hid]
      constructor
      · intro hc
        rcases hc with ⟨_, hxz1⟩ | ⟨hxz1, _⟩ | ⟨_, _, hp⟩
        · exact absurd hxz1 hxz
        · exact absurd hxz1 hxz
        · exact hp
      · intro hp
        exact Or.inr (Or.inr ⟨hyz, hxz, hp⟩)
  -- Social transitivity, then IIA transport back to the original profile.
  have hPxy : StrictPref (swf.aggregate P) x y :=
    ⟨(swf.aggregate P).trans x z y hPxz.1 hPzy.1,
     fun hyx => hPzy.2 ((swf.aggregate P).trans y x z hyx hPxz.1)⟩
  have hiff₁ : (swf.aggregate P).R x y ↔ (swf.aggregate prefs).R x y :=
    h_iia P prefs x y h₁ h₂
  have hiff₂ : (swf.aggregate P).R y x ↔ (swf.aggregate prefs).R y x :=
    h_iia P prefs y x h₂ h₁
  exact ⟨hiff₁.mp hPxy.1, fun hyx => hPxy.2 (hiff₂.mpr hyx)⟩

/-!
## Stage 4b: extracting the dictator

Final stage of the direct port (#23022): it extracts a dictator from a decisive
coalition, which makes it possible to **prove** `arrow_impossibility` instead of
stating it.

The machinery of stage 4a suffices, **with no cardinality measure at all** —
hence no `Finset`, and without leaving Lean core. Rather than searching for a
minimum among all decisive coalitions (which would require counting them), the
proof splits an **explicit** family of coalitions: the sequence of "tails"
`{i | m ≤ i}`.

- The empty tail is never decisive (`empty_not_decisive`), so the descent cannot
  run out without having found a dictator.
- `decisive_split` on the tail `m` offers two outcomes. Either the singleton
  `{m}` is decisive on the pair `(x₀, w)`, and `decisive_global` turns it into a
  dictator (`decisive_singleton_dictator`). Or the tail `m + 1` is decisive on
  `(w, y₀)`, and the descent proceeds one step further.

The induction runs on `nI - m`, which strictly decreases at each step: no
cardinality measure is needed, and `Finset` stays out of the lake.

Measured axiomatic closure (`#print axioms`): `propext`, `Quot.sound`, and
`Classical.choice` **inherited from two independent sources**, `decisive_split`
and `zLast`. The former decides the social preference on a pair by `by_cases`
with no decidability instance on the social relation; the latter splits on
equalities over `A` in its order proofs, with no `DecidableEq`. Purging
`decisive_split` alone would therefore not remove `Classical.choice` from
`arrow_impossibility` — both would need a decidability instance. This stage
introduces no new axiom; it removes none either.
-/

/-- Individual `d` is a dictator: each of its strict preferences becomes the
society's strict preference, on every profile and every pair. This is exactly the
predicate whose existence `NonDictatorial` denies. -/
def Dictator {I A : Type} (swf : SocialWelfareFunction I A) (d : I) : Prop :=
  ∀ prefs : I → Preference A, ∀ x y : A,
    StrictPref (prefs d) x y → StrictPref (swf.aggregate prefs) x y

/-- Two extensionally equal coalitions have the same decisiveness. -/
theorem decisive_congr {I A : Type} (swf : SocialWelfareFunction I A)
    {D D' : I → Prop} {x y : A} (h : ∀ i, D i ↔ D' i)
    (hdec : Decisive swf D x y) : Decisive swf D' x y := by
  intro prefs hD hND
  exact hdec prefs (fun i hi => hD i ((h i).mp hi))
    (fun i hi => hND i (fun hc => hi ((h i).mpr hc)))

/-- The coalition of agents whose index is at least `m`. -/
def tailCoal {n : Nat} (m : Nat) : Fin n → Prop := fun i => m ≤ i.val

/-- As soon as the set has at least three alternatives, any pair of alternatives
leaves an alternative distinct from both. The witness is looked up among `0`, `1`
and `2`: at most two values are taken. -/
theorem exists_third {n : Nat} (h : n ≥ 3) (x y : Fin n) :
    ∃ z : Fin n, z ≠ x ∧ z ≠ y := by
  by_cases h0 : (0 : Nat) = x.val ∨ 0 = y.val
  · by_cases h1 : (1 : Nat) = x.val ∨ 1 = y.val
    · refine ⟨⟨2, by omega⟩, ?_, ?_⟩
      · intro hc
        have hv : (2 : Nat) = x.val := congrArg Fin.val hc
        rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> omega
      · intro hc
        have hv : (2 : Nat) = y.val := congrArg Fin.val hc
        rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> omega
    · have h1x : (1 : Nat) ≠ x.val := fun e => h1 (Or.inl e)
      have h1y : (1 : Nat) ≠ y.val := fun e => h1 (Or.inr e)
      exact ⟨⟨1, by omega⟩, fun hc => h1x (congrArg Fin.val hc),
        fun hc => h1y (congrArg Fin.val hc)⟩
  · have h0x : (0 : Nat) ≠ x.val := fun e => h0 (Or.inl e)
    have h0y : (0 : Nat) ≠ y.val := fun e => h0 (Or.inr e)
    exact ⟨⟨0, by omega⟩, fun hc => h0x (congrArg Fin.val hc),
      fun hc => h0y (congrArg Fin.val hc)⟩

/-- Under Pareto and IIA, a coalition decisive on a pair of distinct
alternatives contains a dictator.

The descent runs on `nI - m`: at each step, `decisive_split` detaches agent `m`
from the tail, and the empty tail is excluded by `empty_not_decisive`. -/
theorem exists_dictator_of_decisive {nI nA : Nat} (hA : nA ≥ 3)
    (swf : SocialWelfareFunction (Fin nI) (Fin nA))
    (h_iia : IIA swf) (h_pareto : WeakPareto swf)
    {x0 y0 w : Fin nA} (hx0y0 : x0 ≠ y0) (hx0w : x0 ≠ w) (hy0w : y0 ≠ w) :
    ∀ (k : Nat) (m : Nat), m + k = nI →
      Decisive swf (tailCoal m) x0 y0 → ∃ d : Fin nI, Dictator swf d := by
  intro k
  induction k with
  | zero =>
      intro m hm hdec
      have hemp : Decisive swf (fun _ => False) x0 y0 :=
        decisive_congr swf (D := tailCoal m) (D' := fun _ => False)
          (fun i => ⟨fun hi => by
            have hi' : m ≤ i.val := hi
            omega, fun hf => False.elim hf⟩) hdec
      exact False.elim (empty_not_decisive swf h_pareto hx0y0 hemp)
  | succ k ih =>
      intro m hm hdec
      have hmn : m < nI := by omega
      have hsplit :
          Decisive swf (fun i : Fin nI => i = ⟨m, hmn⟩) x0 w ∨
            Decisive swf (fun i : Fin nI => m + 1 ≤ i.val) w y0 :=
        decisive_split swf (tailCoal m) (fun i : Fin nI => i = ⟨m, hmn⟩)
          (fun i : Fin nI => m + 1 ≤ i.val) h_iia
          (fun i hi => by rw [hi]; exact Nat.le_refl m)
          (fun i hi => Nat.le_of_succ_le hi)
          (fun i hi => by
            have hi' : m ≤ i.val := hi
            by_cases hc : i.val = m
            · exact Or.inl (Fin.ext hc)
            · exact Or.inr (by omega))
          (fun i => by
            rintro ⟨h1, h2⟩
            have h2' : m + 1 ≤ i.val := h2
            have h1' : i.val = m := by rw [h1]
            omega)
          hx0y0 hx0w hy0w hdec
      rcases hsplit with hsingle | htail
      · have hall : ∀ a b : Fin nA, a ≠ b →
            Decisive swf (fun i : Fin nI => i = ⟨m, hmn⟩) a b :=
          decisive_global (x := x0) (y := w) swf
            (fun i : Fin nI => i = ⟨m, hmn⟩) h_iia h_pareto
            hx0w ⟨y0, hx0y0.symm, hy0w⟩ hsingle
        refine ⟨⟨m, hmn⟩, ?_⟩
        intro prefs a b hab
        have hne : a ≠ b := by
          intro heq
          subst heq
          exact hab.2 hab.1
        obtain ⟨z, hzx, hzy⟩ := exists_third hA a b
        exact decisive_singleton_dictator swf h_iia h_pareto ⟨m, hmn⟩ hall prefs
          hne hzx.symm hzy.symm hab
      · have hall : ∀ a b : Fin nA, a ≠ b →
            Decisive swf (fun i : Fin nI => m + 1 ≤ i.val) a b :=
          decisive_global (x := w) (y := y0) swf
            (fun i : Fin nI => m + 1 ≤ i.val) h_iia h_pareto
            hy0w.symm ⟨x0, hx0w, hx0y0⟩ htail
        exact ih (m + 1) (by omega) (hall x0 y0 hx0y0)

/-- **Arrow's impossibility theorem.** There is no social welfare function over
at least three alternatives that simultaneously satisfies weak Pareto,
independence of irrelevant alternatives and non-dictatorship.

The theorem is **proved** here: the unanimous profile makes the whole coalition
decisive, and `exists_dictator_of_decisive` extracts a dictator as soon as the
set of alternatives has three elements.

The hypothesis `nI ≥ 2` is the one of the historical statement, kept for fidelity
to the literature; the proof below holds for any `nI`, hence the `_hI` name of
the parameter. -/
theorem arrow_impossibility {nI nA : Nat}
    (_hI : nI ≥ 2)
    (hA : nA ≥ 3)
    (swf : SocialWelfareFunction (Fin nI) (Fin nA))
    (h_pareto : WeakPareto swf)
    (h_iia : IIA swf) :
    ¬NonDictatorial swf := by
  intro hnd
  let x0 : Fin nA := ⟨0, by omega⟩
  let y0 : Fin nA := ⟨1, by omega⟩
  let w : Fin nA := ⟨2, by omega⟩
  have hx0y0 : x0 ≠ y0 := by
    intro h
    have hv : x0.val = y0.val := congrArg Fin.val h
    have h0v : x0.val = 0 := rfl
    have h1v : y0.val = 1 := rfl
    omega
  have hx0w : x0 ≠ w := by
    intro h
    have hv : x0.val = w.val := congrArg Fin.val h
    have h0v : x0.val = 0 := rfl
    have hwv : w.val = 2 := rfl
    omega
  have hy0w : y0 ≠ w := by
    intro h
    have hv : y0.val = w.val := congrArg Fin.val h
    have h1v : y0.val = 1 := rfl
    have hwv : w.val = 2 := rfl
    omega
  have hunan : Decisive swf (fun _ => True) x0 y0 := decisive_unanimous swf h_pareto
  have h0 : Decisive swf (tailCoal 0) x0 y0 :=
    decisive_congr swf (D := fun _ => True) (D' := tailCoal 0)
      (fun i => ⟨fun _ => Nat.zero_le i.val, fun _ => trivial⟩) hunan
  obtain ⟨d, hd⟩ := exists_dictator_of_decisive hA swf h_iia h_pareto
    hx0y0 hx0w hy0w nI 0 (by omega) h0
  exact hnd ⟨d, hd⟩

/-!
## Sen's Impossibility: the proof

The "Sen's Impossibility" section declares `MinimalLiberalism` — one individual
decisive over one pair — and leaves the statement as a comment. That condition
is **too weak to carry a theorem**: `dictatorship_minimally_liberal` below
shows a dictatorship satisfies it, and the file already proves a dictatorship
satisfies Pareto (`dictatorship_satisfies_pareto`) and IIA
(`dictatorship_satisfies_iia`). Concluding an impossibility from
`MinimalLiberalism` and Pareto would therefore prove that a function both
exists and does not exist.

Sen's theorem requires **two** distinct individuals, decisive over **two**
distinct pairs. With three alternatives, two distinct pairs share exactly one
alternative; that overlap is what produces the social cycle. With four
alternatives, two disjoint pairs do not contradict each other: the overlap is
not a detail of the proof, it is its condition.

The proof does **not** use IIA. Sen is in this sense stronger than Arrow: the
cycle comes from Pareto alone, on a profile where every individual remains
transitive.
-/

/-- Liberalism in Sen's sense: two **distinct** individuals are decisive over
two **distinct** pairs of one and the same triple of alternatives.

`i` settles the pair `(x, y)`, `j` settles the pair `(y, z)`; the two pairs
cross on `y`, and the three alternatives are pairwise distinct. This is Sen's
"private matter" case: each decides a pair that concerns them, and the two
decisions meet. -/
def SenLiberalism {I A : Type} (swf : SocialWelfareFunction I A) : Prop :=
  ∃ i j : I, i ≠ j ∧ ∃ x y z : A,
    x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      Decisive swf (fun k => k = i) x y ∧
      Decisive swf (fun k => k = j) y z

/-- Minimal liberalism is satisfied by a dictatorship: the witness is the
dictator themself, on the degenerate pair `(a, a)`.

This is the counter-example that justifies `SenLiberalism`: without it, the
"Sen's Impossibility" section would suggest a theorem is within reach of the
definition that sits there. -/
theorem dictatorship_minimally_liberal {I A : Type} [Nonempty A] (d : I) :
    MinimalLiberalism (dictatorship (I := I) (A := A) d) := by
  obtain ⟨a⟩ := ‹Nonempty A›
  exact ⟨d, a, a, fun _ h => h⟩

/-- **Sen's impossibility theorem.** Over three alternatives, no social welfare
function satisfies both weak Pareto and Sen's liberalism: two distinct
individuals cannot each be decisive over a pair of their own as soon as the two
pairs cross.

The auxiliary profile is explicit — `i` has `z ≻ x ≻ y`, `j` has `y ≻ z ≻ x`,
everyone else `z ≻ y ≻ x` — and it remains transitive for each of them. The two
private decisions give `x ≻s y` and `y ≻s z`, Pareto gives `z ≻s x`, and
social transitivity yields `x ≻s z` against `z ≻s x`. -/
theorem sen_impossibility {I A : Type} [DecidableEq I] [DecidableEq A]
    (swf : SocialWelfareFunction I A) (h_pareto : WeakPareto swf) :
    ¬ SenLiberalism swf := by
  rintro ⟨i, j, hij, x, y, z, hxy, hyz, hxz, hi, hj⟩
  let P : I → Preference A := fun k =>
    if k = i then prefOfUtility (rank3 z x y 3 2 1)
    else if k = j then prefOfUtility (rank3 y z x 3 2 1)
    else prefOfUtility (rank3 z y x 3 2 1)
  have hP_i : ∀ k, k = i → P k = prefOfUtility (rank3 z x y 3 2 1) := by
    intro k hk
    simp [P, hk]
  have hP_j : ∀ k, k = j → P k = prefOfUtility (rank3 y z x 3 2 1) := by
    intro k hk
    simp [P, hk, hij.symm]
  have hP_o : ∀ k, k ≠ i → k ≠ j → P k = prefOfUtility (rank3 z y x 3 2 1) := by
    intro k hki hkj
    simp [P, hki, hkj]
  have hxy_s : StrictPref (swf.aggregate P) x y := by
    apply hi P
    · intro k hk
      rw [hP_i k hk]
      exact ⟨by simp [prefOfUtility, rank3, hxz, hyz, hxy.symm] <;> decide,
        by simp [prefOfUtility, rank3, hxz, hyz, hxy.symm] <;> decide⟩
    · intro k hk
      by_cases hkj : k = j
      · rw [hP_j k hkj]
        exact ⟨by simp [prefOfUtility, rank3, hxy, hxz] <;> decide,
          by simp [prefOfUtility, rank3, hxy, hxz] <;> decide⟩
      · rw [hP_o k hk hkj]
        exact ⟨by simp [prefOfUtility, rank3, hyz, hxz, hxy] <;> decide,
          by simp [prefOfUtility, rank3, hyz, hxz, hxy] <;> decide⟩
  have hyz_s : StrictPref (swf.aggregate P) y z := by
    apply hj P
    · intro k hk
      rw [hP_j k hk]
      exact ⟨by simp [prefOfUtility, rank3, hyz.symm] <;> decide,
        by simp [prefOfUtility, rank3, hyz.symm] <;> decide⟩
    · intro k hk
      by_cases hki : k = i
      · rw [hP_i k hki]
        exact ⟨by simp [prefOfUtility, rank3, hyz, hxy.symm] <;> decide,
          by simp [prefOfUtility, rank3, hyz, hxy.symm] <;> decide⟩
      · rw [hP_o k hki hk]
        exact ⟨by simp [prefOfUtility, rank3, hyz] <;> decide,
          by simp [prefOfUtility, rank3, hyz] <;> decide⟩
  have hzx : StrictPref (swf.aggregate P) z x := by
    apply h_pareto P z x
    intro k
    by_cases hki : k = i
    · rw [hP_i k hki]
      exact ⟨by simp [prefOfUtility, rank3, hxz] <;> decide,
        by simp [prefOfUtility, rank3, hxz] <;> decide⟩
    · by_cases hkj : k = j
      · rw [hP_j k hkj]
        exact ⟨by simp [prefOfUtility, rank3, hyz.symm, hxy, hxz] <;> decide,
          by simp [prefOfUtility, rank3, hyz.symm, hxy, hxz] <;> decide⟩
      · rw [hP_o k hki hkj]
        exact ⟨by simp [prefOfUtility, rank3, hxz, hxy] <;> decide,
          by simp [prefOfUtility, rank3, hxz, hxy] <;> decide⟩
  exact hzx.2 ((swf.aggregate P).trans x y z hxy_s.1 hyz_s.1)

end SocialChoiceEn
