/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Grothendieck tribute — Part 94 (EN sibling of `Grothendieck/FlasqueAcyclic.lean`):
acyclicity of flasque sheaves — unconditional degree 1, degree shifting,
and the `injective => flasque` boundary.

Alexandre Grothendieck (1928-2014).

Phase 2 extension (#2159, Epic #1646).

This part corrects a gloss and delivers the theorem it was hiding. Part 80
credited Godement II.5.2 with a "flasque => injective by Zorn":
**that statement is false** — on a discrete two-point space, every sheaf is
flasque (every principal sieve amalgamates), and the constant sheaf
(Z, Z) is not injective in Ab x Ab. Godement's true statement is
**flasque => Γ-acyclic** (II.5.1): H^{n+1}(F) = 0 for all n. The Zorn
extension of Part 82 is not a passage to injectivity, it is the
**surjectivity of global sections** — the base case of acyclicity.

Three theorems and one capstone:

  - `shortExact_of_injectivePresentation`: any injective presentation
    F ↪ J (EnoughInjectives) yields a short exact sequence
    0 → F → J → coker → 0. Pure homological algebra
    (`CategoryTheory.ShortComplex.exact_cokernel`),
    but Mathlib does not provide this constructor: the long covariant Ext
    sequence applies to `ShortComplex.ShortExact`, not to bare monos.
    This bridge is the first link.

  - `subsingleton_H_one_of_flasque`: **degree 1, unconditional**. On a short
    exact sequence 0 → X₁ → X₂ → X₃ → 0 of abelian sheaves with X₁ flasque
    (sieves) and X₂ injective, H¹(X₁) = 0. The proof assembles:
    (a) Mathlib's long covariant Ext sequence
    (`Abelian.Ext.covariant_sequence_exact₁`) — an element of H¹(X₁) whose
    image in H¹(X₂) is zero (injective: a Mathlib instance) comes from an
    element of H⁰(X₃); (b) the identification H⁰ ≃ Γ over the terminal
    open (`Sheaf.H.equiv₀`), turning that element into a global section
    of X₃; (c) the Γ-surjectivity of Part 82
    (`epi_of_shortExact_of_isFlasqueSieves` — this is where Zorn works):
    the section lifts to a section of X₂, i.e. the element of H⁰(X₃) lies
    in the image of the degree-0 map; (d) the vanishing of its image under
    the extension class (`comp_extClass`), which traces back to the
    original element and kills it. No hypothesis on X₃: the quotient need
    not be flasque in degree 1.

  - `subsingleton_H_succ_of_flasque_decalage`: **the shift**. Same short
    exact sequence, X₂ injective; if Hⁿ(X₃) is trivial then H^{n+1}(X₁)
    is trivial. The inductive step of acyclicity: each degree is paid for
    by one degree of the quotient.

  - `subsingleton_H_succ_of_flasque_all`: **the conditional capstone**.
    If moreover every injective sheaf is flasque (hypothesis `hInjFlasque`,
    Godement II.4), then every flasque sheaf is Γ-acyclic:
    H^{n+1}(F) = 0 for all n. The induction is complete: the injective
    presentation provides 0 → F → J → Q, Part 83
    (`isFlasqueSieves_of_shortExact_of_isFlasque₁₂`) makes Q flasque (F is,
    J is by hypothesis), and degree 1 or the induction applied to Q
    provides the hypothesis of the shift.

**Boundary explicitly named**: `injective => flasque` ([God58] II.4).
This is the only missing link to discharge the capstone's hypothesis into
an unconditional theorem for all n. The classical proof extends the
section 1 of ℤ_U along the mono inclusion ℤ_U ↪ ℤ_V, which requires the
extension by zero `j_!` of open sheaves — absent from Mathlib to this
day. As long as `j_!` does not exist, degree 1 (unconditional, above)
and the shift are the deliverable bricks; the capstone awaits its
hypothesis.

The conceptual reading: acyclicity of flasque sheaves is not a theorem
of injectivity, it is a theorem of **surjectivity of sections** — the
easy half of the long exact sequence, the one that lives in Γ and not in
Ext. Godement's difficulty is not killing H¹, but keeping the recursion
running: the quotient of a flasque by a flasque is flasque, and it is
the injective that must be flasque to start the engine. That is exactly
the dividing line this part records.

References:
  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §4 (injective => flasque) and §5 (th. 5.1: flasque => Γ-acyclic).
  - Mathlib, `Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences`
    (long covariant Ext sequence, Joel Riou).
  - Mathlib, `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`
    (`Sheaf.H`, `Sheaf.H.equiv₀`, identification H⁰ = Γ).
  - Part 20 (`Grothendieck.SheafCohomology.Basic`): the cohomology bridge.
  - Part 79 (`Grothendieck.Flasque`): `IsFlasqueSieves`.
  - Part 80 (`Grothendieck.FlasqueStability`): stability, the
    flasque-injective crossing (corrected: the "flasque => injective"
    gloss is replaced there by a pointer to this part).
  - Part 82 (`Grothendieck.FlasqueExact`): Γ-surjectivity by Zorn.
  - Part 83 (`Grothendieck.FlasqueQuotient`): quotient of flasques.

i18n convention (EPIC #4980 ratified 2026-07-04): this module is the
canonical English sibling of `Grothendieck/FlasqueAcyclic.lean` — the
`_en` suffix on the namespace and imports, byte-identity of everything
else (signatures, proofs, tactics).
-/

import Grothendieck.FlasqueExact
import Grothendieck.FlasqueQuotient
import Grothendieck.FlasqueStability
import Grothendieck.SheafCohomology.Basic

universe r w u

namespace Grothendieck.FlasqueAcyclic_en

open CategoryTheory Category Limits Opposite

/-!
## 1. The constructor: injective presentation => short exact sequence

Mathlib defines `InjectivePresentation` (fields J injective, f mono) but
does not provide the short exact sequence `0 → F → J → coker f → 0` in
the `ShortComplex.ShortExact` form consumed by the long covariant Ext
sequence. This constructor is the glue:
`CategoryTheory.ShortComplex.exact_cokernel` provides exactness, the
mono/epi fields of the presentation and of the cokernel provide the
other two components.
-/

section Constructeur

variable {A : Type r} [Category.{w} A] [Abelian A]

/-- Any injective presentation `P : InjectivePresentation F` yields a
short exact sequence `0 → F → P.J → coker P.f → 0` in the
`ShortComplex.ShortExact` sense. The three components: exactness at the
cokernel (`CategoryTheory.ShortComplex.exact_cokernel`), the mono of the
presentation (field `P.mono`), the epi of the cokernel (instance). This
is the form consumed by the long covariant Ext sequence
(`Abelian.Ext.covariant_sequence_exact₁`). -/
theorem shortExact_of_injectivePresentation {F : A} (P : InjectivePresentation F) :
    (ShortComplex.mk P.f (cokernel.π P.f) (cokernel.condition P.f)).ShortExact where
  exact := CategoryTheory.ShortComplex.exact_cokernel P.f
  mono_f := P.mono
  epi_g := inferInstance

end Constructeur

/-!
## 2. Degree 1: flasque => H¹ = 0, unconditional

On `0 → X₁ → X₂ → X₃ → 0` with X₁ flasque and X₂ injective, the group
H¹(X₁) is trivial. This is Godement II.5.1 in degree 1: the
Γ-surjectivity of Part 82 (Zorn) suffices, no hypothesis on X₃.
-/

section DegreUn

variable {X : TopCat.{u}}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

open TopCat TopCat.Presheaf TopologicalSpace

/-- **Degree 1 of flasque acyclicity** (Godement II.5.1, case n = 0).
On a short exact sequence `0 → X₁ → X₂ → X₃ → 0` of abelian sheaves on a
topological space X, with X₁ flasque (sieve sense, Part 79) and X₂
injective, the group `H¹(X₁)` is trivial.

The proof: an element x₁ of H¹(X₁) has zero image in H¹(X₂) (injective),
so by the long covariant Ext sequence it comes from an x₃ : H⁰(X₃); via
`Sheaf.H.equiv₀` over the terminal open, x₃ is a global section of X₃;
the Γ-surjectivity of Part 82 lifts it to a section of X₂, i.e. x₃ =
image of an x₂ : H⁰(X₂); then x₃ ∘ δ = 0 by `comp_extClass` and the
associativity of Ext, hence x₁ = 0. -/
theorem subsingleton_H_one_of_flasque
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) [Injective S.X₂]
    [IsFlasqueSieves (S.X₁.obj ⋙ CategoryTheory.forget AddCommGrpCat)] :
    Subsingleton (CategoryTheory.Sheaf.H S.X₁ 1) := by
  refine subsingleton_of_forall_eq 0 fun x₁ => ?_
  -- the image of x₁ in H¹(X₂) is zero: X₂ is injective
  have hx₁ : x₁.comp (CategoryTheory.Abelian.Ext.mk₀ S.f) (add_zero 1) = 0 :=
    Subsingleton.elim _ _
  -- so x₁ comes from an x₃ : H⁰(X₃) (long covariant exact sequence)
  obtain ⟨x₃, hx₃⟩ :=
    CategoryTheory.Abelian.Ext.covariant_sequence_exact₁ _ hS x₁ hx₁ rfl
  -- x₃ is a global section of X₃ (identification H⁰ = Γ, terminal open)
  have hT : IsTerminal (⊤ : Opens X) := Limits.isTerminalTop
  obtain ⟨i, hi⟩ := (AddCommGrpCat.epi_iff_surjective _).mp
    (epi_of_shortExact_of_isFlasqueSieves hS)
    (CategoryTheory.Sheaf.H.equiv₀ S.X₃ hT x₃)
  -- that section lifts to a section of X₂ (Part 82, Zorn)
  set x₂ : CategoryTheory.Sheaf.H S.X₂ 0 :=
    (CategoryTheory.Sheaf.H.equiv₀ S.X₂ hT).symm i with hx₂def
  have hcomp : x₂.comp (CategoryTheory.Abelian.Ext.mk₀ S.g) (add_zero 0) = x₃ := by
    refine (CategoryTheory.Sheaf.H.equiv₀ S.X₃ hT).injective ?_
    rw [← CategoryTheory.Sheaf.H.map_apply]
    rw [← CategoryTheory.Sheaf.H.equiv₀_naturality hT S.g x₂]
    rw [hx₂def, AddEquiv.apply_symm_apply]
    exact hi
  -- then x₃ ∘ δ = 0: the element lies in the image of the degree-0 map
  have hδ : x₃.comp hS.extClass (rfl : (0 : ℕ) + 1 = 1) = 0 := by
    rw [← hcomp, CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero,
      hS.comp_extClass, CategoryTheory.Abelian.Ext.comp_zero]
  exact hx₃.symm.trans hδ

/-- **Unconditional corollary of degree 1**: every flasque sheaf (sieve
sense) on a topological space with abelian sheaves, in a category with
enough injectives, has trivial H¹. The injective presentation of F
provides the short exact sequence of the previous theorem. -/
theorem subsingleton_H_one_of_flasque_presentation
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [IsFlasqueSieves (F.obj ⋙ CategoryTheory.forget AddCommGrpCat)]
    [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] :
    Subsingleton (CategoryTheory.Sheaf.H F 1) := by
  obtain ⟨P⟩ := ‹EnoughInjectives _›.presentation F
  exact subsingleton_H_one_of_flasque (shortExact_of_injectivePresentation P)

end DegreUn

/-!
## 3. The shift: Hⁿ(X₃) = 0 => H^{n+1}(X₁) = 0

The inductive step. No flasqueness hypothesis here: the shift is a
property of the long exact sequence alone, X₂ injective killing the map
from X₁ to X₂ in every degree.
-/

section Decalage

variable {X : TopCat.{u}}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

open TopCat TopCat.Presheaf TopologicalSpace

/-- **Shift**: on a short exact sequence `0 → X₁ → X₂ → X₃ → 0` with X₂
injective, triviality of `Hⁿ(X₃)` implies that of `H^{n+1}(X₁)`. The
element of `H^{n+1}(X₁)` has zero image in X₂ (injective), comes from a
trivial `Hⁿ(X₃)`, hence is zero. This is the inductive step of
acyclicity: each degree of X₁ is paid for by one degree of the quotient. -/
theorem subsingleton_H_succ_of_flasque_decalage
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) [Injective S.X₂] {n : ℕ}
    (hQ : Subsingleton (CategoryTheory.Sheaf.H S.X₃ n)) :
    Subsingleton (CategoryTheory.Sheaf.H S.X₁ (n + 1)) := by
  refine subsingleton_of_forall_eq 0 fun x₁ => ?_
  have hx₁ : x₁.comp (CategoryTheory.Abelian.Ext.mk₀ S.f) (add_zero (n + 1)) = 0 :=
    Subsingleton.elim _ _
  have hex : ∃ x₃ : CategoryTheory.Sheaf.H S.X₃ n,
      x₃.comp hS.extClass (rfl : n + 1 = n + 1) = x₁ :=
    CategoryTheory.Abelian.Ext.covariant_sequence_exact₁ _ hS x₁ hx₁ rfl
  obtain ⟨x₃, hx₃⟩ := hex
  rw [← hx₃, Subsingleton.elim (α := CategoryTheory.Sheaf.H S.X₃ n) x₃ 0]
  simp

end Decalage

/-!
## 4. Conditional capstone: flasque => Γ-acyclic, under `injective => flasque`

The complete induction. The hypothesis `hInjFlasque` (Godement II.4) is
the only missing link: it makes the middle term flasque, Part 83 makes
the quotient flasque, and the recursion runs. Boundary named for
Part 95: the classical proof requires the extension by zero `j_!` of
open sheaves, absent from Mathlib.
-/

section Capstone

variable {X : TopCat.{u}}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

open TopCat TopCat.Presheaf TopologicalSpace

/-- **Conditional capstone** (Godement II.5.1 in full): if every injective
sheaf is flasque — hypothesis `hInjFlasque`, Godement II.4, boundary
named for Part 95 (`j_!` absent from Mathlib) — then every flasque sheaf
is Γ-acyclic: `H^{n+1}(F)` is trivial for all n.

The induction: in degree 0, the degree-1 theorem; in degree n+1, the
injective presentation `0 → F → J → Q`, Part 83 makes Q flasque (F is,
J is by hypothesis), the induction hypothesis applied to Q provides
`H^{n+1}(Q)` trivial, and the shift concludes. -/
theorem subsingleton_H_succ_of_flasque_all
    (hInjFlasque : ∀ I : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u},
      Injective I → IsFlasqueSieves (I.obj ⋙ CategoryTheory.forget AddCommGrpCat))
    [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (n : ℕ) (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [IsFlasqueSieves (F.obj ⋙ CategoryTheory.forget AddCommGrpCat)] :
    Subsingleton (CategoryTheory.Sheaf.H F (n + 1)) := by
  induction n generalizing F with
  | zero =>
    exact subsingleton_H_one_of_flasque_presentation F
  | succ n ih =>
    obtain ⟨P⟩ := ‹EnoughInjectives _›.presentation F
    have hS : (ShortComplex.mk P.f (cokernel.π P.f) (cokernel.condition P.f)).ShortExact :=
      shortExact_of_injectivePresentation P
    haveI hI₁ : IsFlasqueSieves
        ((ShortComplex.mk P.f (cokernel.π P.f) (cokernel.condition P.f)).X₁.obj ⋙
          CategoryTheory.forget AddCommGrpCat) := ‹_›
    haveI hI₂ : IsFlasqueSieves
        ((ShortComplex.mk P.f (cokernel.π P.f) (cokernel.condition P.f)).X₂.obj ⋙
          CategoryTheory.forget AddCommGrpCat) := hInjFlasque P.J P.injective
    haveI hQflasque : IsFlasqueSieves
        ((ShortComplex.mk P.f (cokernel.π P.f) (cokernel.condition P.f)).X₃.obj ⋙
          CategoryTheory.forget AddCommGrpCat) :=
      isFlasqueSieves_of_shortExact_of_isFlasque₁₂ hS
    exact subsingleton_H_succ_of_flasque_decalage hS (ih (cokernel P.f))

end Capstone

end Grothendieck.FlasqueAcyclic_en
