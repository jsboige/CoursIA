/-
  Lean Examples - LLM Assisted Proofs (EN sibling)

  This file contains examples of proofs that could be
  generated or assisted by LLMs.
  Corresponding to the Lean-7 and Lean-8 notebooks.

  English sibling of llm_assisted_proof.lean (i18n #4980): docstrings and
  comments translated to English; theorems, definitions, tactics, and
  variables are byte-identical to the French original.
-/

-- ============================================================
-- "LLM-style" proofs - clear and well-structured
-- ============================================================

/-
  LLMs often generate proofs with:
  1. Explanatory comments
  2. Intermediate steps with 'have'
  3. Explicit type annotations
  4. A pedagogical style
-/

-- Example 1: Commutativity in LLM style
theorem add_comm_llm_style (a b : Nat) : a + b = b + a := by
  -- Use the commutativity lemma from the standard library
  exact Nat.add_comm a b

-- Example 2: Associativity with decomposition
theorem add_assoc_llm_style (x y z : Nat) : (x + y) + z = x + (y + z) := by
  -- This property is fundamental for arithmetic
  -- It allows grouping additions in any order
  exact Nat.add_assoc x y z

-- Example 3: More detailed proof
theorem distributivity_llm_style (a b c : Nat) : a * (b + c) = a * b + a * c := by
  -- Distributivity of multiplication over addition
  -- This is a characteristic property of rings
  exact Nat.mul_add a b c

-- ============================================================
-- Step-by-step proofs (LeanCopilot style)
-- ============================================================

theorem step_by_step_proof (p q r : Prop)
  (hpq : p -> q) (hqr : q -> r) (hp : p) : r := by
  -- Step 1: Obtain q from p
  have hq : q := hpq hp
  -- Step 2: Obtain r from q
  have hr : r := hqr hq
  -- Step 3: Conclude
  exact hr

-- ============================================================
-- Proofs with automatic tactics
-- ============================================================

-- LLMs often suggest using automatic tactics
-- when they are appropriate

theorem auto_omega (n m : Nat) (h : n < m) : n + 1 <= m := by
  -- omega automatically solves linear arithmetic
  omega

theorem auto_simp (n : Nat) : n + 0 + 0 = n := by
  -- simp automatically simplifies expressions
  simp

-- ============================================================
-- Iteratively generated proofs
-- ============================================================

/-
  Systems like AlphaProof and APOLLO generate proofs
  by iteration:
  1. Generate an attempt
  2. Verify with Lean
  3. If it fails, fix and retry
-/

-- Iteration 1 (potential failure) : sorry
-- theorem iter1 (n : Nat) : n + 0 = n := by sorry

-- Iteration 2 (correction) : rfl
theorem iter2 (n : Nat) : n + 0 = n := by rfl

-- Iteration 3 (alternative) : exact
theorem iter3 (n : Nat) : n + 0 = n := by exact Nat.add_zero n

-- ============================================================
-- Decomposed proofs (Aristotle style)
-- ============================================================

-- Decomposing an equivalence into two implications
theorem iff_decomposed (p q : Prop)
  (hpq : p -> q) (hqp : q -> p) : p <-> q := by
  -- Part 1: Direction p -> q
  constructor
  . -- Prove p -> q
    exact hpq
  . -- Part 2: Direction q -> p
    exact hqp

-- Decomposing a conjunction
theorem and_decomposed (p q : Prop) (hp : p) (hq : q) : p /\ q := by
  -- Build the conjunction from its parts
  constructor
  . -- Left part: p
    exact hp
  . -- Right part: q
    exact hq

-- ============================================================
-- Examples of typical prompts and responses
-- ============================================================

/-
  Prompt: "Prove that addition is commutative over Nat"
  LLM response:
-/
theorem llm_response_example (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-
  Prompt: "Prove that if p implies q and q implies r, then p implies r"
  LLM response:
-/
theorem llm_transitivity (p q r : Prop) : (p -> q) -> (q -> r) -> (p -> r) :=
  fun hpq hqr hp => hqr (hpq hp)

/-
  Prompt: "Prove that there exists a natural number greater than 100"
  LLM response:
-/
theorem llm_exists_large : exists n : Nat, n > 100 :=
  Exists.intro 101 (by decide)

-- ============================================================
-- Patterns for proof generation
-- ============================================================

-- Pattern 1: Direct proof with a lemma
-- "Use lemma X to prove Y"
theorem pattern_direct (n : Nat) : n * 1 = n := Nat.mul_one n

-- Pattern 2: Proof by induction
-- "Prove by induction on n"
theorem pattern_induction (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [Nat.add_succ, ih]

-- Pattern 3: Proof by cases
-- "Case analysis on the disjunction"
theorem pattern_cases (p q : Prop) (hpq : p \/ q) : q \/ p := by
  cases hpq with
  | inl hp => right; exact hp
  | inr hq => left; exact hq

-- Pattern 4: Proof by simplification
-- "Simplify and conclude"
theorem pattern_simp (n : Nat) : n + 0 = n := by simp
