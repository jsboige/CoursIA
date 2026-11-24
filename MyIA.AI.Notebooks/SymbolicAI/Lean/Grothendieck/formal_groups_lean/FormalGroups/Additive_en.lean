import FormalGroups.Basic_en

/-!
# The additive law, the reference formal group

The multivariate additive formal group `addMv g R` has law `X + Y`
componentwise. It is the canonical bounded example: identity, identity
linear part and associativity are structural identities there, and the law
is commutative (`IsComm`).
-/

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace FormalGroups_en.MvFormalGroup

/-- The multivariate additive formal group: the law is `X + Y`, component
by component. Reference example, from which the iterates and the height
can be read explicitly. -/
def addMv (g : ℕ) (R : Type*) [CommRing R] : MvFormalGroup g R where
  toPowerSeries := fun i => X (Sum.inl i) + X (Sum.inr i)
  constantCoeff_eq_zero := by
    intro i
    show ((X (Sum.inl i) + X (Sum.inr i) : MvPowerSeries (Fin g ⊕ Fin g) R)).constantCoeff = 0
    rw [map_add, constantCoeff_X, constantCoeff_X, add_zero]
  coeff_single_inl := by
    intro i j
    show ((X (Sum.inl i) + X (Sum.inr i) : MvPowerSeries (Fin g ⊕ Fin g) R)).coeff
        (Finsupp.single (Sum.inl j) 1) = if i = j then 1 else 0
    rw [map_add, coeff_index_single_X, coeff_index_single_X]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  coeff_single_inr := by
    intro i j
    show ((X (Sum.inl i) + X (Sum.inr i) : MvPowerSeries (Fin g ⊕ Fin g) R)).coeff
        (Finsupp.single (Sum.inr j) 1) = if i = j then 1 else 0
    rw [map_add, coeff_index_single_X, coeff_index_single_X]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  assoc := by
    intro i
    have hzB : ∀ s : Fin g ⊕ Fin g, ((Sum.elim
        (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inl l))) s).constantCoeff = 0 := by
      rintro (l | l) <;> simp [constantCoeff_X]
    have hzC : ∀ s : Fin g ⊕ Fin g, ((Sum.elim
        (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inr l))) s).constantCoeff = 0 := by
      rintro (l | l) <;> simp [constantCoeff_X]
    simp only [subst_X_add_X hzB, subst_X_add_X hzC, Sum.elim_inl, Sum.elim_inr]
    have hzA : ∀ s : Fin g ⊕ Fin g, ((Sum.elim
        (fun j => (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R)
          + X (Sum.inr (Sum.inl j)))
        fun j => X (Sum.inr (Sum.inr j))) s).constantCoeff = 0 := by
      rintro (j | j) <;> simp [constantCoeff_X]
    have hzA' : ∀ s : Fin g ⊕ Fin g, ((Sum.elim
        (fun j => (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun j => X (Sum.inr (Sum.inl j)) + X (Sum.inr (Sum.inr j))) s).constantCoeff = 0 := by
      rintro (j | j) <;> simp [constantCoeff_X]
    rw [subst_X_add_X hzA, subst_X_add_X hzA']
    simp only [Sum.elim_inl, Sum.elim_inr]
    exact add_assoc _ _ _

/-- The additive law is commutative: canonical `IsComm` instance. -/
instance (g : ℕ) (R : Type*) [CommRing R] : IsComm (addMv g R) where
  comm := by
    intro i
    have hz : ∀ s : Fin g ⊕ Fin g, ((Sum.elim
        (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
        fun j => X (Sum.inl j)) s).constantCoeff = 0 := by
      rintro (j | j) <;> simp [constantCoeff_X]
    show subst (Sum.elim
        (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
        fun j => X (Sum.inl j))
        (X (Sum.inl i) + X (Sum.inr i)) = X (Sum.inl i) + X (Sum.inr i)
    rw [subst_X_add_X hz]
    simp only [Sum.elim_inl, Sum.elim_inr]
    exact add_comm _ _

section Exemples

/- Bounded examples on the additive law (acceptance #14785): each fact is
checked without development, by definition or via the corresponding
structure field. -/

/-- The law of `addMv` is indeed `X + Y` on each component. -/
example : (addMv 1 ℤ).toPowerSeries 0 = X (Sum.inl 0) + X (Sum.inr 0) := rfl

/-- The constant coefficient of the additive law vanishes (field
`constantCoeff_eq_zero`). -/
example : ((addMv 1 ℤ).toPowerSeries 0).constantCoeff = (0 : ℤ) :=
  (addMv 1 ℤ).constantCoeff_eq_zero 0

/-- The linear part is the identity: coefficient 1 on the matching
variable (field `coeff_single_inl`). -/
example : ((addMv 1 ℤ).toPowerSeries 0).coeff (Finsupp.single (Sum.inl 0) 1) = 1 := by
  have h := (addMv 1 ℤ).coeff_single_inl 0 0
  simpa using h

/-- The additive law is commutative, by instance. -/
example : IsComm (addMv 1 ℤ) := inferInstance

end Exemples

end MvFormalGroup

end FormalGroups_en

end
