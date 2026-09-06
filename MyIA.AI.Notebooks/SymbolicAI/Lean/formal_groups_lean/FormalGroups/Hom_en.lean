import FormalGroups.Basic_en

/-!
# Morphisms of formal groups

A morphism `F → G` is an `h`-tuple of formal power series in `g` variables,
with vanishing constant coefficients, compatible with the laws (in the
substitution sense). This module establishes the identity, composition,
endomorphisms and the change of base ring.
-/

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace FormalGroups_en.MvFormalGroup

variable {g h k : ℕ} {R : Type*} [CommRing R] {S : Type*} [CommRing S]

/-- Morphism of formal groups from `F` to `G`: an `h`-tuple of series in `g`
variables, with vanishing constant coefficients, transporting the law of `F`
to the law of `G`. -/
@[ext]
structure Hom (F : MvFormalGroup g R) (G : MvFormalGroup h R) where

  toPowerSeries : Fin h → MvPowerSeries (Fin g) R

  /-- A morphism maps the origin to the origin. -/
  constantCoeff_eq_zero : ∀ i, (toPowerSeries i).constantCoeff = 0

  /-- Compatibility with the laws: `G` evaluated on the morphism (component
  by component, over each block of variables) coincides with the morphism
  composed with the law of `F`. -/
  subst_eq : ∀ i,
    subst F.toPowerSeries (toPowerSeries i)
      =
    subst
      (Sum.elim
        (fun j => subst
          (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) (toPowerSeries j))
        fun j => subst
          (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) (toPowerSeries j))
      (G.toPowerSeries i)

namespace Hom

/-- A morphism is substitutable: its components have vanishing constant
coefficients. -/
theorem hasSubst_toPowerSeries {F : MvFormalGroup g R} {G : MvFormalGroup h R}
    (φ : Hom F G) : HasSubst φ.toPowerSeries :=
  hasSubst_of_constantCoeff_zero φ.constantCoeff_eq_zero

/-- The identity morphism of a formal group: each component is the
corresponding indeterminate. -/
def id (F : MvFormalGroup g R) : Hom F F where
  toPowerSeries := fun i => X i
  constantCoeff_eq_zero := fun i => constantCoeff_X i
  subst_eq := by
    intro i
    show subst F.toPowerSeries (X i)
        = subst
          (Sum.elim
            (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) (X j))
            fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) (X j))
          (F.toPowerSeries i)
    have h2 : HasSubst (fun l : Fin g => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
      hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
    have h3 : HasSubst (fun l : Fin g => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
      hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
    have hl : (Sum.elim
          (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (X j : MvPowerSeries (Fin g) R))
          fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (X j : MvPowerSeries (Fin g) R))
        = fun s => (X s : MvPowerSeries (Fin g ⊕ Fin g) R) := by
      funext s
      rcases s with j | j
      · simp [subst_X h2]
      · simp [subst_X h3]
    rw [subst_X F.hasSubst_toPowerSeries, hl, subst_self]
    rfl

/-- Composition of morphisms: component `i` is `φ` substituted by component
`i` of `ψ`. -/
def comp {F : MvFormalGroup g R} {G : MvFormalGroup h R} {H : MvFormalGroup k R}
    (ψ : Hom G H) (φ : Hom F G) : Hom F H where
  toPowerSeries := fun i => subst φ.toPowerSeries (ψ.toPowerSeries i)
  constantCoeff_eq_zero := fun i =>
    constantCoeff_subst_eq_zero φ.hasSubst_toPowerSeries φ.constantCoeff_eq_zero
      (ψ.constantCoeff_eq_zero i)
  subst_eq := by
    intro i
    show subst F.toPowerSeries (subst φ.toPowerSeries (ψ.toPowerSeries i))
        = subst
          (Sum.elim
            (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (subst φ.toPowerSeries (ψ.toPowerSeries j)))
            fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (subst φ.toPowerSeries (ψ.toPowerSeries j)))
          (H.toPowerSeries i)
    have hAφ : HasSubst (Sum.elim
        (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
          (φ.toPowerSeries j))
        fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
          (φ.toPowerSeries j)) := by
      apply hasSubst_of_constantCoeff_zero
      rintro (j | j) <;>
        exact constantCoeff_subst_eq_zero
          (hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _)
          (fun l => constantCoeff_X _) (φ.constantCoeff_eq_zero j)
    have hAψ : HasSubst (Sum.elim
        (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin h ⊕ Fin h) R))
          (ψ.toPowerSeries j))
        fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin h ⊕ Fin h) R))
          (ψ.toPowerSeries j)) := by
      apply hasSubst_of_constantCoeff_zero
      rintro (j | j) <;>
        exact constantCoeff_subst_eq_zero
          (hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _)
          (fun l => constantCoeff_X _) (ψ.constantCoeff_eq_zero j)
    rw [subst_comp_subst_apply φ.hasSubst_toPowerSeries F.hasSubst_toPowerSeries]
    have heq1 : (fun s => subst F.toPowerSeries (φ.toPowerSeries s))
        = fun s => subst (Sum.elim
            (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries j))
            fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries j)) (G.toPowerSeries s) :=
      funext fun s => φ.subst_eq s
    rw [heq1, ← subst_comp_subst_apply G.hasSubst_toPowerSeries hAφ, ψ.subst_eq i,
      subst_comp_subst_apply hAψ hAφ]
    have heq2 : (fun s => subst
          (Sum.elim
            (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries j))
            fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries j))
          (Sum.elim
            (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin h ⊕ Fin h) R))
              (ψ.toPowerSeries j))
            (fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin h ⊕ Fin h) R))
              (ψ.toPowerSeries j)) s))
        = Sum.elim
            (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (subst φ.toPowerSeries (ψ.toPowerSeries j)))
            fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (subst φ.toPowerSeries (ψ.toPowerSeries j)) := by
      funext s
      rcases s with j | j
      · show subst
            (Sum.elim
              (fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
                (φ.toPowerSeries j'))
              fun j' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
                (φ.toPowerSeries j'))
            (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin h ⊕ Fin h) R))
              (ψ.toPowerSeries j))
            = subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (subst φ.toPowerSeries (ψ.toPowerSeries j))
        rw [subst_comp_subst_apply
            (hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _) hAφ,
          subst_comp_subst_apply φ.hasSubst_toPowerSeries
            (hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _)]
        have hfam : (fun s : Fin h => subst
            (Sum.elim
              (fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
                (φ.toPowerSeries j'))
              fun j' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
                (φ.toPowerSeries j'))
            (X (Sum.inl s) : MvPowerSeries (Fin h ⊕ Fin h) R))
            = fun s => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries s) := by
          funext l
          simp only [subst_X hAφ, Sum.elim_inl]
        rw [hfam]
      · show subst
            (Sum.elim
              (fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
                (φ.toPowerSeries j'))
              fun j' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
                (φ.toPowerSeries j'))
            (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin h ⊕ Fin h) R))
              (ψ.toPowerSeries j))
            = subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (subst φ.toPowerSeries (ψ.toPowerSeries j))
        rw [subst_comp_subst_apply
            (hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _) hAφ,
          subst_comp_subst_apply φ.hasSubst_toPowerSeries
            (hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _)]
        have hfam : (fun s : Fin h => subst
            (Sum.elim
              (fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
                (φ.toPowerSeries j'))
              fun j' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
                (φ.toPowerSeries j'))
            (X (Sum.inr s) : MvPowerSeries (Fin h ⊕ Fin h) R))
            = fun s => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries s) := by
          funext l
          simp only [subst_X hAφ, Sum.elim_inr]
        rw [hfam]
    rw [heq2]

end Hom

/-- The endomorphisms of a formal group are the morphisms from `F` to
itself. -/
def End (F : MvFormalGroup g R) := Hom F F

/-- Change of base ring: a ring homomorphism `f : R →+* S` transports any
formal group over `R` to a formal group over `S`, by applying `f`
coefficientwise. -/
def map (f : R →+* S) (F : MvFormalGroup g R) : MvFormalGroup g S where
  toPowerSeries := fun i => MvPowerSeries.map f (F.toPowerSeries i)
  constantCoeff_eq_zero := by
    intro i
    rw [constantCoeff_map, F.constantCoeff_eq_zero, map_zero]
  coeff_single_inl := by
    intro i j
    rw [coeff_map, F.coeff_single_inl]
    split <;> simp
  coeff_single_inr := by
    intro i j
    rw [coeff_map, F.coeff_single_inr]
    split <;> simp
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
    have hB := hasSubst_of_constantCoeff_zero hzB
    have hC := hasSubst_of_constantCoeff_zero hzC
    have hA : HasSubst (Sum.elim
        (fun j => subst (Sum.elim
          (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
          fun l => X (Sum.inr (Sum.inl l))) (F.toPowerSeries j))
        fun j => X (Sum.inr (Sum.inr j))) := by
      apply hasSubst_of_constantCoeff_zero
      rintro (j | j)
      · exact constantCoeff_subst_eq_zero hB hzB (F.constantCoeff_eq_zero j)
      · exact constantCoeff_X _
    have hA' : HasSubst (Sum.elim
        (fun j => (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun j => subst (Sum.elim
          (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
          fun l => X (Sum.inr (Sum.inr l))) (F.toPowerSeries j)) := by
      apply hasSubst_of_constantCoeff_zero
      rintro (j | j)
      · exact constantCoeff_X _
      · exact constantCoeff_subst_eq_zero hC hzC (F.constantCoeff_eq_zero j)
    have key := congrArg (MvPowerSeries.map f) (F.assoc i)
    rw [map_subst hA, map_subst hA'] at key
    have hBmap : (fun s => MvPowerSeries.map f ((Sum.elim
        (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inl l))) s))
        = Sum.elim
          (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) S))
          fun l => X (Sum.inr (Sum.inl l)) := by
      funext s
      rcases s with l | l <;> simp [map_X]
    have hCmap : (fun s => MvPowerSeries.map f ((Sum.elim
        (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inr l))) s))
        = Sum.elim
          (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) S))
          fun l => X (Sum.inr (Sum.inr l)) := by
      funext s
      rcases s with l | l <;> simp [map_X]
    have hAmap : (fun s => MvPowerSeries.map f ((Sum.elim
        (fun j => subst (Sum.elim
          (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
          fun l => X (Sum.inr (Sum.inl l))) (F.toPowerSeries j))
        fun j => X (Sum.inr (Sum.inr j))) s))
        = Sum.elim
          (fun j => subst (Sum.elim
            (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) S))
            fun l => X (Sum.inr (Sum.inl l))) (MvPowerSeries.map f (F.toPowerSeries j)))
          fun j => X (Sum.inr (Sum.inr j)) := by
      funext s
      rcases s with j | j
      · show MvPowerSeries.map f (subst (Sum.elim
            (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
            fun l => X (Sum.inr (Sum.inl l))) (F.toPowerSeries j))
            = subst (Sum.elim
              (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) S))
              fun l => X (Sum.inr (Sum.inl l))) (MvPowerSeries.map f (F.toPowerSeries j))
        rw [map_subst hB, hBmap]
      · simp [map_X]
    have hA'map : (fun s => MvPowerSeries.map f ((Sum.elim
        (fun j => (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun j => subst (Sum.elim
          (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
          fun l => X (Sum.inr (Sum.inr l))) (F.toPowerSeries j)) s))
        = Sum.elim
          (fun j => (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) S))
          fun j => subst (Sum.elim
            (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) S))
            fun l => X (Sum.inr (Sum.inr l))) (MvPowerSeries.map f (F.toPowerSeries j)) := by
      funext s
      rcases s with j | j
      · simp [map_X]
      · show MvPowerSeries.map f (subst (Sum.elim
            (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
            fun l => X (Sum.inr (Sum.inr l))) (F.toPowerSeries j))
            = subst (Sum.elim
              (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) S))
              fun l => X (Sum.inr (Sum.inr l))) (MvPowerSeries.map f (F.toPowerSeries j))
        rw [map_subst hC, hCmap]
    rw [hAmap, hA'map] at key
    exact key

end MvFormalGroup

end FormalGroups_en

end
