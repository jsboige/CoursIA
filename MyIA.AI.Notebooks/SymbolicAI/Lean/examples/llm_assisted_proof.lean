/-
  Lean Examples - LLM Assisted Proofs

  Ce fichier contient des exemples de preuves qui pourraient etre
  generees ou assistees par des LLMs.
  Correspondant aux notebooks Lean-7 et Lean-8.
-/

-- ============================================================
-- Preuves "style LLM" - claires et bien structurees
-- ============================================================

/-
  Les LLMs generent souvent des preuves avec :
  1. Des commentaires explicatifs
  2. Des etapes intermediaires avec 'have'
  3. Des annotations de type explicites
  4. Un style pedagogique
-/

-- Exemple 1: Commutativite avec style LLM
theorem add_comm_llm_style (a b : Nat) : a + b = b + a := by
  -- Utiliser le lemme de commutativite de la bibliotheque standard
  exact Nat.add_comm a b

-- Exemple 2: Associativite avec decomposition
theorem add_assoc_llm_style (x y z : Nat) : (x + y) + z = x + (y + z) := by
  -- Cette propriete est fondamentale pour l'arithmetique
  -- Elle permet de regrouper les additions dans n'importe quel ordre
  exact Nat.add_assoc x y z

-- Exemple 3: Preuve plus detaillee
theorem distributivity_llm_style (a b c : Nat) : a * (b + c) = a * b + a * c := by
  -- Distributivite de la multiplication sur l'addition
  -- C'est une propriete caracteristique des anneaux
  exact Nat.mul_add a b c

-- ============================================================
-- Preuves par etapes (style LeanCopilot)
-- ============================================================

theorem step_by_step_proof (p q r : Prop)
  (hpq : p -> q) (hqr : q -> r) (hp : p) : r := by
  -- Etape 1: Obtenir q a partir de p
  have hq : q := hpq hp
  -- Etape 2: Obtenir r a partir de q
  have hr : r := hqr hq
  -- Etape 3: Conclure
  exact hr

-- ============================================================
-- Preuves avec tactiques automatiques
-- ============================================================

-- Les LLMs suggerent souvent d'utiliser des tactiques automatiques
-- quand elles sont appropriees

theorem auto_omega (n m : Nat) (h : n < m) : n + 1 <= m := by
  -- omega resout automatiquement l'arithmetique lineaire
  omega

theorem auto_simp (n : Nat) : n + 0 + 0 = n := by
  -- simp simplifie automatiquement les expressions
  simp

-- ============================================================
-- Preuves generees iterativement
-- ============================================================

/-
  Les systemes comme AlphaProof et APOLLO generent des preuves
  par iteration :
  1. Generer une tentative
  2. Verifier avec Lean
  3. Si echec, corriger et recommencer
-/

-- Iteration 1 (echec potentiel) : sorry
-- theorem iter1 (n : Nat) : n + 0 = n := by sorry

-- Iteration 2 (correction) : rfl
theorem iter2 (n : Nat) : n + 0 = n := by rfl

-- Iteration 3 (alternative) : exact
theorem iter3 (n : Nat) : n + 0 = n := by exact Nat.add_zero n

-- ============================================================
-- Preuves decomposees (style Aristotle)
-- ============================================================

-- Decomposition d'une equivalence en deux implications
theorem iff_decomposed (p q : Prop)
  (hpq : p -> q) (hqp : q -> p) : p <-> q := by
  -- Partie 1: Direction p -> q
  constructor
  . -- Prouver p -> q
    exact hpq
  . -- Partie 2: Direction q -> p
    exact hqp

-- Decomposition d'une conjonction
theorem and_decomposed (p q : Prop) (hp : p) (hq : q) : p /\ q := by
  -- Construire la conjonction a partir de ses parties
  constructor
  . -- Partie gauche: p
    exact hp
  . -- Partie droite: q
    exact hq

-- ============================================================
-- Exemples de prompts et reponses typiques
-- ============================================================

/-
  Prompt: "Prouve que l'addition est commutative sur Nat"
  Reponse LLM:
-/
theorem llm_response_example (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

/-
  Prompt: "Prouve que si p implique q et q implique r, alors p implique r"
  Reponse LLM:
-/
theorem llm_transitivity (p q r : Prop) : (p -> q) -> (q -> r) -> (p -> r) :=
  fun hpq hqr hp => hqr (hpq hp)

/-
  Prompt: "Prouve qu'il existe un nombre naturel plus grand que 100"
  Reponse LLM:
-/
theorem llm_exists_large : exists n : Nat, n > 100 :=
  Exists.intro 101 (by decide)

-- ============================================================
-- Patterns pour generation de preuves
-- ============================================================

-- Pattern 1: Preuve directe avec lemme
-- "Utilise le lemme X pour prouver Y"
theorem pattern_direct (n : Nat) : n * 1 = n := Nat.mul_one n

-- Pattern 2: Preuve par recurrence
-- "Prouve par recurrence sur n"
theorem pattern_induction (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [Nat.add_succ, ih]

-- Pattern 3: Preuve par cas
-- "Analyse par cas sur la disjonction"
theorem pattern_cases (p q : Prop) (hpq : p \/ q) : q \/ p := by
  cases hpq with
  | inl hp => right; exact hp
  | inr hq => left; exact hq

-- Pattern 4: Preuve par simplification
-- "Simplifie et conclue"
theorem pattern_simp (n : Nat) : n + 0 = n := by simp
