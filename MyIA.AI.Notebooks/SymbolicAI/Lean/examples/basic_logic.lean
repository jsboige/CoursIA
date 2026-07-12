/-
  Lean Examples - Basic Logic

  Ce fichier contient des exemples de base de logique propositionnelle
  correspondant aux notebooks Lean-2 et Lean-3.
-/

-- Variables propositionnelles
variable (p q r : Prop)

-- ============================================================
-- Implication
-- ============================================================

-- Reflexivite de l'implication
theorem impl_refl : p -> p :=
  fun hp => hp

-- Transitivite de l'implication
theorem impl_trans (hpq : p -> q) (hqr : q -> r) : p -> r :=
  fun hp => hqr (hpq hp)

-- K combinator
theorem impl_intro : p -> q -> p :=
  fun hp _ => hp

-- ============================================================
-- Conjonction (And)
-- ============================================================

-- Introduction de And
theorem and_intro (hp : p) (hq : q) : p /\ q :=
  And.intro hp hq

-- Commutativite de And
theorem and_comm : p /\ q -> q /\ p :=
  fun hpq => And.intro hpq.right hpq.left

-- Associativite de And
theorem and_assoc : (p /\ q) /\ r <-> p /\ (q /\ r) :=
  Iff.intro
    (fun h => And.intro h.left.left (And.intro h.left.right h.right))
    (fun h => And.intro (And.intro h.left h.right.left) h.right.right)

-- ============================================================
-- Disjonction (Or)
-- ============================================================

-- Commutativite de Or
theorem or_comm : p \/ q -> q \/ p :=
  fun hpq => Or.elim hpq Or.inr Or.inl

-- Elimination de Or
theorem or_elim_example (hpq : p \/ q) (hpr : p -> r) (hqr : q -> r) : r :=
  Or.elim hpq hpr hqr

-- ============================================================
-- Negation
-- ============================================================

-- Modus tollens
theorem modus_tollens (hpq : p -> q) (hnq : Not q) : Not p :=
  fun hp => hnq (hpq hp)

-- Non-contradiction
theorem non_contradiction : Not (p /\ Not p) :=
  fun h => h.right h.left

-- ============================================================
-- Equivalence (Iff)
-- ============================================================

-- Reflexivite de Iff
theorem iff_refl : p <-> p :=
  Iff.intro (fun hp => hp) (fun hp => hp)

-- Symetrie de Iff
theorem iff_symm (h : p <-> q) : q <-> p :=
  Iff.intro h.mpr h.mp

-- ============================================================
-- Lois de De Morgan
-- ============================================================

-- De Morgan 1 (constructif)
theorem de_morgan_1 : Not (p \/ q) <-> Not p /\ Not q :=
  Iff.intro
    (fun h => And.intro (fun hp => h (Or.inl hp)) (fun hq => h (Or.inr hq)))
    (fun h hpq => Or.elim hpq h.left h.right)

-- De Morgan 2 (necessite logique classique)
open Classical in
theorem de_morgan_2 : Not (p /\ q) <-> Not p \/ Not q :=
  Iff.intro
    (fun h => Or.elim (em p)
      (fun hp => Or.inr (fun hq => h (And.intro hp hq)))
      (fun hnp => Or.inl hnp))
    (fun h hpq => Or.elim h
      (fun hnp => hnp hpq.left)
      (fun hnq => hnq hpq.right))
