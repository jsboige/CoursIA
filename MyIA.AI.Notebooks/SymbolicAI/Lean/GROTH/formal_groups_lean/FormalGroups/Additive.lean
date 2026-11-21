import FormalGroups.Basic

/-!
# La loi additive, groupe formel de référence

Le groupe formel additif multivarié `addMv g R` a pour loi `X + Y`
composante par composante. C'est l'exemple borné canonique : neutre, partie
linéaire identité et associativité y sont des identités structurelles, et
la loi est commutative (`IsComm`).
-/

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace FormalGroups.MvFormalGroup

/-- Le groupe formel additif multivarié : la loi est `X + Y`, composante
par composante. Exemple de référence, à partir duquel les itérés et la
hauteur se lisent explicitement. -/
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

/-- La loi additive est commutative : instance canonique de `IsComm`. -/
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

/- Exemples bornés sur la loi additive (acceptance #14785) : chaque fait se
vérifie sans développement, par définition ou par le champ correspondant de
la structure. -/

/-- La loi de `addMv` est bien `X + Y` sur chaque composante. -/
example : (addMv 1 ℤ).toPowerSeries 0 = X (Sum.inl 0) + X (Sum.inr 0) := rfl

/-- Le terme constant de la loi additive est nul (champ
`constantCoeff_eq_zero`). -/
example : ((addMv 1 ℤ).toPowerSeries 0).constantCoeff = (0 : ℤ) :=
  (addMv 1 ℤ).constantCoeff_eq_zero 0

/-- La partie linéaire est l'identité : coefficient 1 sur la variable
correspondante (champ `coeff_single_inl`). -/
example : ((addMv 1 ℤ).toPowerSeries 0).coeff (Finsupp.single (Sum.inl 0) 1) = 1 := by
  have h := (addMv 1 ℤ).coeff_single_inl 0 0
  simpa using h

/-- La loi additive est commutative, par instance. -/
example : IsComm (addMv 1 ℤ) := inferInstance

end Exemples

end MvFormalGroup

end FormalGroups

end
