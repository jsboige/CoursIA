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
  definitions, signatures, tactics and the `arrow_impossibility` axiom is
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

/--
Arrow's Impossibility Theorem (Statement):
There is no social welfare function with ≥3 alternatives that satisfies:
1. Weak Pareto
2. Independence of Irrelevant Alternatives
3. Non-dictatorship

Note: Stated with explicit `Fin n` types instead of generic `Fintype`
to avoid Mathlib dependency. The theorem's mathematical content is identical.
-/
-- Port in progress (#23022): the building blocks of the proof live in the
-- "Decisive coalitions" section below; the theorem stays stated as an axiom
-- until the reduction is complete.
axiom arrow_impossibility {nI nA : Nat}
    (hI : nI ≥ 2)
    (hA : nA ≥ 3)
    (swf : SocialWelfareFunction (Fin nI) (Fin nA))
    (h_pareto : WeakPareto swf)
    (h_iia : IIA swf) :
    ¬NonDictatorial swf

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

/- Sen's Impossibility Theorem (Statement):
   No SWF can satisfy both Weak Pareto and Minimal Liberalism
   under certain preference configurations.
   (Weaker statement — the full theorem requires constructing
   specific preference profiles.) -/

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

end SocialChoiceEn
