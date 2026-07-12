/-
  Lean Examples - Tactics Mode

  Ce fichier demontre le mode tactique de Lean
  correspondant au notebook Lean-5.
-/

-- ============================================================
-- Tactiques de base
-- ============================================================

-- exact : fournir le terme exact
theorem exact_demo (p : Prop) (hp : p) : p := by
  exact hp

-- intro : introduction d'hypotheses
theorem intro_demo (p q : Prop) : p -> q -> p := by
  intro hp hq
  exact hp

-- apply : appliquer un lemme
theorem apply_demo (p q r : Prop) (hpq : p -> q) (hqr : q -> r) (hp : p) : r := by
  apply hqr
  apply hpq
  exact hp

-- assumption : chercher dans le contexte
theorem assumption_demo (p q : Prop) (hp : p) (hq : q) : p := by
  assumption

-- ============================================================
-- Gestion du contexte
-- ============================================================

-- have : lemme intermediaire
theorem have_demo (p q r : Prop) (hpq : p -> q) (hqr : q -> r) (hp : p) : r := by
  have hq : q := hpq hp
  have hr : r := hqr hq
  exact hr

-- show : annoter le but
theorem show_demo (p q : Prop) (hp : p) (hq : q) : q /\ p := by
  constructor
  show q
  exact hq
  show p
  exact hp

-- ============================================================
-- Tactiques pour la logique
-- ============================================================

-- constructor pour And
theorem and_tactic (p q : Prop) (hp : p) (hq : q) : p /\ q := by
  constructor
  . exact hp
  . exact hq

-- cases pour Or
theorem or_tactic (p q r : Prop) (hpq : p \/ q) (hpr : p -> r) (hqr : q -> r) : r := by
  cases hpq with
  | inl hp => exact hpr hp
  | inr hq => exact hqr hq

-- left et right pour Or
theorem left_right_demo (p q : Prop) (hp : p) : p \/ q := by
  left
  exact hp

-- contradiction
theorem contradiction_demo (p q : Prop) (hp : p) (hnp : Not p) : q := by
  contradiction

-- ============================================================
-- Reecriture et simplification
-- ============================================================

-- rw : reecriture
theorem rw_demo (a b c : Nat) (h : a = b) : a + c = b + c := by
  rw [h]

-- rw avec plusieurs lemmes
theorem rw_chain (a b c d : Nat) (h1 : a = b) (h2 : b = c) (h3 : c = d) : a = d := by
  rw [h1, h2, h3]

-- simp : simplification automatique
theorem simp_demo (n : Nat) : n + 0 = n := by
  simp

-- simp avec lemmes additionnels
theorem simp_with (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
  simp [h]

-- ============================================================
-- Tactiques automatiques
-- ============================================================

-- omega : arithmetique de Presburger
theorem omega_demo (n m : Nat) (h : n < m) : n + 1 <= m := by
  omega

-- decide : propositions decidables
theorem decide_demo : 3 < 5 := by
  decide

-- ============================================================
-- Structuration des preuves
-- ============================================================

-- Points (bullets) pour focaliser
theorem bullets_demo (p q r : Prop) (hp : p) (hq : q) (hr : r) : p /\ q /\ r := by
  constructor
  . exact hp
  . constructor
    . exact hq
    . exact hr

-- <;> pour appliquer a tous les buts
theorem all_goals_demo (p : Prop) (hp : p) : p /\ p := by
  constructor <;> exact hp

-- ============================================================
-- Induction
-- ============================================================

-- Recurrence sur Nat
theorem induction_demo (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [Nat.add_succ, ih]
