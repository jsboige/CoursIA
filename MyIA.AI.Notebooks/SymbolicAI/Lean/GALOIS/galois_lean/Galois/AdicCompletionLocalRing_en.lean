import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Adic completions of local rings : a first layer

This module sets up, in the `galois_lean` lake, a layer of **local
arithmetic** devoted to the **adic completions** of a local ring `A` with
respect to its maximal ideal.

The content is a pedagogical port of
`Definitions/Def_AdicCompletionLocalRing.lean` from the
[`anthropics/fermats-last-theorem`](https://github.com/anthropics/fermats-last-theorem)
repository (commit `aa2d8b34`, Apache-2.0 licence — attribution and `NOTICE`
preserved, issue #14783). Statements, proofs and theorem names are kept; only
docstrings were written and imports tightened to the Mathlib modules actually
used (no global `import Mathlib`).

The layer is organised into four sections :

- **Kernel** — for an ideal `I`, the kernel of the evaluation `evalₐ I n` is
  exactly the image of `I ^ n` in the completion (`ker_evalₐ_eq_map_pow`); an
  element `1 + x` with `x` in the image of a finitely generated ideal `I` is a
  unit (`isUnit_one_add_of_mem_map`);
- **Exemple** — the `2`-adic truncation of `ℤ`: evaluating at degree `n` is
  reducing modulo `2 ^ n`, and the kernel is the image of `I ^ n` — the
  concrete meaning of the quotients `A ⧸ I ^ n`;
- **Local** — when `A` is local and Noetherian, the maximal ideal of the
  completion is the kernel of the degree-1 evaluation, and its quotient by its
  powers identifies with that of `A` (`quotientMaximalIdealPowAlgEquiv`);
- **Transport** — these identities are transported along an algebra
  isomorphism, in particular an equivalence between completions.

This base is the prerequisite of the downstream grains (Hensel, ramification
groups, issue #14786); it does not modify the existing M22/M23 bundle of the
lake.

The axioms used reduce to `propext`, `Classical.choice` and `Quot.sound` —
checked by the `proof-integrity` gate of the CI (no `sorry`, `sorryAx` nor
`native_decide`).
-/

set_option autoImplicit false

open IsLocalRing

open AdicCompletion

namespace AdicCompletion_en

variable {A : Type*} [CommRing A]

section Kernel

variable (I : Ideal A)

/-- The image in the completion of an element `a`, re-evaluated at degree `n`,
is the class of `a` in `A ⧸ I ^ n`: the algebraMap form is preserved by
`evalₐ`. -/
theorem evalₐ_algebraMap (n : ℕ) (a : A) :
    evalₐ I n (algebraMap A (AdicCompletion I A) a) = Ideal.Quotient.mk _ a := by
  rw [algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, evalₐ_of]

/-- Equivalence of the two descriptions (as a `RingHom` and as a `LinearMap`)
of the kernel of the evaluation `evalₐ I n`. -/
theorem mem_ker_evalₐ_iff (n : ℕ) (x : AdicCompletion I A) :
    x ∈ RingHom.ker (evalₐ I n) ↔ x ∈ LinearMap.ker (eval I A n) := by
  have h : (I ^ n • ⊤ : Ideal A) = I ^ n := by rw [smul_eq_mul, Ideal.mul_top]
  rw [RingHom.mem_ker, LinearMap.mem_ker]
  constructor
  · intro hx; rw [← factor_evalₐ_eq_eval I x h.ge, hx]; exact RingHom.map_zero _
  · intro hx; rw [← factor_eval_eq_evalₐ I x h.le, hx]; exact LinearMap.map_zero _

/-- For a finitely generated `I`, the kernel of `evalₐ I n` is exactly the image
of the power `I ^ n` in the completion: this is the « kernel of evaluation =
power of the ideal » characterization of local geometry. -/
theorem ker_evalₐ_eq_map_pow (hI : I.FG) (n : ℕ) :
    RingHom.ker (evalₐ I n) = (I ^ n).map (algebraMap A (AdicCompletion I A)) := by
  ext x
  rw [mem_ker_evalₐ_iff, ← pow_smul_top_eq_ker_eval hI, Ideal.smul_top_eq_map,
    Submodule.restrictScalars_mem]

/-- Any element of the completion writes as an element of `A` plus an element of
the image of `I ^ n`: the completion is generated over `A` by the small powers
of the ideal. -/
theorem exists_eq_algebraMap_add (hI : I.FG) (n : ℕ) (x : AdicCompletion I A) :
    ∃ a : A, ∃ y ∈ (I ^ n).map (algebraMap A (AdicCompletion I A)),
      x = algebraMap A (AdicCompletion I A) a + y := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
  refine ⟨a, x - algebraMap A _ a, ?_, by ring⟩
  rw [← ker_evalₐ_eq_map_pow I hI, RingHom.mem_ker, map_sub, evalₐ_algebraMap, ha, sub_self]

/-- In the completion, `1 + x` is a unit as soon as `x` is in the image of the
ideal `I` (finitely generated): the image of the maximal ideal stays inside the
Jacobson radical. -/
theorem isUnit_one_add_of_mem_map (hI : I.FG) {x : AdicCompletion I A}
    (hx : x ∈ I.map (algebraMap A (AdicCompletion I A))) : IsUnit (1 + x) := by
  haveI : IsAdicComplete (I.map (algebraMap A (AdicCompletion I A))) (AdicCompletion I A) :=
    (IsAdicComplete.map_algebraMap_iff I (AdicCompletion I A)).mpr (isAdicComplete hI)
  have h := Ideal.mem_jacobson_bot.mp (IsAdicComplete.le_jacobson_bot _ hx) 1
  rwa [mul_one, add_comm] at h

/-- Shifted version of the previous one: `u + x` is a unit as soon as `u` is a
unit and `x` is in the image of `I` (the inverse factor brings it back to
`1 + …`). -/
theorem isUnit_add_of_mem_map (hI : I.FG) {u x : AdicCompletion I A} (hu : IsUnit u)
    (hx : x ∈ I.map (algebraMap A (AdicCompletion I A))) : IsUnit (u + x) := by
  have e : u + x = u * (1 + ↑hu.unit⁻¹ * x) := by
    rw [mul_add, mul_one, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
  rw [e]
  exact hu.mul (isUnit_one_add_of_mem_map I hI (Ideal.mul_mem_left _ _ hx))

end Kernel

section Exemple

/-- Bounded pedagogical example — the 2-adic truncation. In the `2`-adic
completion of `ℤ`, evaluating at degree `3` is reducing modulo `2 ^ 3 = 8`:
the image of `20` evaluates to the class of `4`. This is the concrete meaning
of the quotients `A ⧸ I ^ n`: each level of the completion is arithmetic
modulo `2 ^ n`. -/
example :
    evalₐ (Ideal.span {2} : Ideal ℤ) 3 (algebraMap ℤ (AdicCompletion (Ideal.span {2} : Ideal ℤ) ℤ) 20)
      = Ideal.Quotient.mk _ 4 := by
  rw [evalₐ_algebraMap]
  refine (Ideal.Quotient.eq (I := (Ideal.span {2} : Ideal ℤ) ^ 3)).mpr ?_
  rw [Ideal.span_singleton_pow, show (2 : ℤ) ^ 3 = 8 by norm_num]
  exact Ideal.mem_span_singleton'.mpr ⟨2, by norm_num⟩

/-- The complement: the kernel of the degree-`3` truncation is exactly the
image of `I ^ 3` (`ker_evalₐ_eq_map_pow`) — the image of `8`, a multiple of
`2 ^ 3`, vanishes at level `3`. -/
example :
    algebraMap ℤ (AdicCompletion (Ideal.span {2} : Ideal ℤ) ℤ) 8
      ∈ RingHom.ker (evalₐ (Ideal.span {2} : Ideal ℤ) 3) := by
  rw [ker_evalₐ_eq_map_pow _ (Submodule.fg_span_singleton 2),
    Ideal.span_singleton_pow, show (2 : ℤ) ^ 3 = 8 by norm_num]
  exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self 8)

end Exemple

section Local

variable [IsLocalRing A]

/-- A unit of the completion at the maximal ideal lifts to a unit of `A`:
reducing modulo the maximal ideal creates no new units. -/
theorem isUnit_of_isUnit_algebraMap {a : A}
    (h : IsUnit (algebraMap A (AdicCompletion (maximalIdeal A) A) a)) : IsUnit a := by
  by_contra ha
  have hmem : a ∈ maximalIdeal A ^ 1 := by
    rw [pow_one]; exact (mem_maximalIdeal a).mpr ha
  have h1 := h.map (evalₐ (maximalIdeal A) 1)
  rw [evalₐ_algebraMap, Ideal.Quotient.eq_zero_iff_mem.mpr hmem, isUnit_zero_iff] at h1
  exact (maximalIdeal.isMaximal A).ne_top
    ((pow_one (maximalIdeal A)).symm.trans (Ideal.Quotient.zero_eq_one_iff.mp h1))

/-- Particular case of `isUnit_one_add_of_mem_map` for the maximal ideal: an
element of the form `1 + x` with `x` in the image of the maximal ideal is a
unit. -/
theorem isUnit_one_add_of_mem_map_maximalIdeal (h𝔪 : (maximalIdeal A).FG)
    {x : AdicCompletion (maximalIdeal A) A}
    (hx : x ∈ (maximalIdeal A).map (algebraMap A (AdicCompletion (maximalIdeal A) A))) :
    IsUnit (1 + x) :=
  isUnit_one_add_of_mem_map _ h𝔪 hx

variable [IsNoetherianRing A]

/-- In a Noetherian ring, the maximal ideal is finitely generated. -/
theorem maximalIdeal_fg : (maximalIdeal A).FG := IsNoetherian.noetherian _

/-- The completion of a Noetherian local ring at its maximal ideal is still a
local ring. -/
instance instIsLocalRingMaximalIdeal : IsLocalRing (AdicCompletion (maximalIdeal A) A) :=
  isLocalRing_of_fg maximalIdeal_fg

/-- In the completion, the `n`-th power of the maximal ideal is the kernel of
the evaluation at degree `n`. -/
theorem maximalIdeal_pow_eq_ker_evalₐ (n : ℕ) :
    maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n = RingHom.ker (evalₐ (maximalIdeal A) n) := by
  rw [maximalIdeal_eq_map, ← Ideal.map_pow, ker_evalₐ_eq_map_pow _ maximalIdeal_fg]

/-- Degree 1: the maximal ideal of the completion is the kernel of `evalₐ` at
degree 1. -/
theorem maximalIdeal_eq_ker_evalₐ_one :
    maximalIdeal (AdicCompletion (maximalIdeal A) A) = RingHom.ker (evalₐ (maximalIdeal A) 1) := by
  rw [← maximalIdeal_pow_eq_ker_evalₐ, pow_one]

/-- Membership of the maximal ideal of the completion in terms of the degree-1
evaluation. -/
theorem mem_maximalIdeal_iff (x : AdicCompletion (maximalIdeal A) A) :
    x ∈ maximalIdeal (AdicCompletion (maximalIdeal A) A) ↔ evalₐ (maximalIdeal A) 1 x = 0 := by
  rw [maximalIdeal_eq_ker_evalₐ_one, RingHom.mem_ker]

section Scalars

variable (k : Type*) [CommRing k] [Algebra k A]

/-- The isomorphism (as an algebra over `k`) between the quotient of the
completion by the `n`-th power of its maximal ideal and the quotient of `A` by
`maximalIdeal A ^ n`. -/
noncomputable def quotientMaximalIdealPowAlgHom (n : ℕ) :
    (AdicCompletion (maximalIdeal A) A ⧸ maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n)
      →ₐ[k] A ⧸ maximalIdeal A ^ n :=
  Ideal.Quotient.liftₐ _ ((evalₐ (maximalIdeal A) n).restrictScalars k) fun x hx => by
    rwa [maximalIdeal_pow_eq_ker_evalₐ, RingHom.mem_ker] at hx

/-- Action of `quotientMaximalIdealPowAlgHom` on a class, via the evaluation at
degree `n`. -/
theorem quotientMaximalIdealPowAlgHom_mk (n : ℕ) (x : AdicCompletion (maximalIdeal A) A) :
    quotientMaximalIdealPowAlgHom k n (Ideal.Quotient.mk _ x) = evalₐ (maximalIdeal A) n x :=
  rfl

/-- The previous quotient morphism is bijective: the quotients by the powers of
the maximal ideal are algebraically equivalent. -/
theorem quotientMaximalIdealPowAlgHom_bijective (n : ℕ) :
    Function.Bijective (quotientMaximalIdealPowAlgHom (A := A) k n) := by
  constructor
  · intro x y hxy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [quotientMaximalIdealPowAlgHom_mk, quotientMaximalIdealPowAlgHom_mk] at hxy
    refine Ideal.Quotient.eq.mpr ?_
    rw [maximalIdeal_pow_eq_ker_evalₐ, RingHom.mem_ker, map_sub, hxy, sub_self]
  · intro z
    obtain ⟨x, rfl⟩ := surjective_evalₐ (maximalIdeal A) n z
    exact ⟨Ideal.Quotient.mk _ x, rfl⟩

/-- The algebra equivalence between the quotient of the completion by `𝔪 ^ n` and
the quotient of `A` by `𝔪 ^ n` (`𝔪 = maximalIdeal A`). -/
noncomputable def quotientMaximalIdealPowAlgEquiv (n : ℕ) :
    (AdicCompletion (maximalIdeal A) A ⧸ maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n)
      ≃ₐ[k] A ⧸ maximalIdeal A ^ n :=
  AlgEquiv.ofBijective _ (quotientMaximalIdealPowAlgHom_bijective k n)

/-- Action of `quotientMaximalIdealPowAlgEquiv` on a class. -/
theorem quotientMaximalIdealPowAlgEquiv_mk (n : ℕ) (x : AdicCompletion (maximalIdeal A) A) :
    quotientMaximalIdealPowAlgEquiv k n (Ideal.Quotient.mk _ x) = evalₐ (maximalIdeal A) n x :=
  rfl

/-- The diagram with `algebraMap` commutes: sending the image of an element of
`A` through the equivalence is the same as taking its class in `A ⧸ 𝔪 ^ n`. -/
theorem quotientMaximalIdealPowAlgEquiv_mk_algebraMap (n : ℕ) (a : A) :
    quotientMaximalIdealPowAlgEquiv k n (Ideal.Quotient.mk _ (algebraMap A _ a))
      = Ideal.Quotient.mk _ a := by
  rw [quotientMaximalIdealPowAlgEquiv_mk, evalₐ_algebraMap]

end Scalars

end Local

section Transport

variable [IsLocalRing A] [IsNoetherianRing A]
variable {k : Type*} [CommRing k] [Algebra k A] {B : Type*} [CommRing B] [IsLocalRing B] [Algebra k B]
variable (Φ : AdicCompletion (maximalIdeal A) A ≃ₐ[k] B)

omit [IsNoetherianRing A] [IsLocalRing B] in
/-- An algebra isomorphism preserves the unit property in both directions. -/
theorem isUnit_algEquiv_iff (x : AdicCompletion (maximalIdeal A) A) : IsUnit (Φ x) ↔ IsUnit x :=
  ⟨fun h => by simpa using h.map Φ.symm, fun h => h.map Φ⟩

/-- The pullback of the maximal ideal of `B` along an isomorphism is the maximal
ideal of the completion. -/
theorem comap_maximalIdeal_algEquiv :
    (maximalIdeal B).comap (Φ : AdicCompletion (maximalIdeal A) A →+* B)
      = maximalIdeal (AdicCompletion (maximalIdeal A) A) := by
  ext x
  show Φ x ∈ maximalIdeal B ↔ x ∈ maximalIdeal _
  rw [mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, isUnit_algEquiv_iff]

/-- The image of the maximal ideal of the completion under an isomorphism is the
maximal ideal of `B`. -/
theorem map_maximalIdeal_algEquiv :
    (maximalIdeal (AdicCompletion (maximalIdeal A) A)).map
        (Φ : AdicCompletion (maximalIdeal A) A →+* B) = maximalIdeal B := by
  rw [← comap_maximalIdeal_algEquiv Φ]
  exact Ideal.map_comap_of_surjective _ Φ.surjective _

/-- The maximal ideal of `B` is obtained as the image of the maximal ideal of
`A` via the composite `algebraMap` then `Φ`. -/
theorem maximalIdeal_eq_map_algEquiv :
    maximalIdeal B = (maximalIdeal A).map
      ((Φ : AdicCompletion (maximalIdeal A) A →+* B).comp
        (algebraMap A (AdicCompletion (maximalIdeal A) A))) := by
  rw [← Ideal.map_map, ← maximalIdeal_eq_map, map_maximalIdeal_algEquiv]

/-- Power version of the previous one: the `n`-th power of the maximal ideal of
`B` is the image of `𝔪 ^ n` via the composite. -/
theorem maximalIdeal_pow_eq_map_algEquiv (n : ℕ) :
    maximalIdeal B ^ n = (maximalIdeal A ^ n).map
      ((Φ : AdicCompletion (maximalIdeal A) A →+* B).comp
        (algebraMap A (AdicCompletion (maximalIdeal A) A))) := by
  rw [Ideal.map_pow, ← maximalIdeal_eq_map_algEquiv]

/-- The image under `Φ` of an element of the maximal ideal of `A` stays in the
maximal ideal of `B`. -/
theorem algEquiv_algebraMap_mem_maximalIdeal {a : A} (ha : a ∈ maximalIdeal A) :
    Φ (algebraMap A _ a) ∈ maximalIdeal B := by
  rw [maximalIdeal_eq_map_algEquiv Φ]
  exact Ideal.mem_map_of_mem _ ha

/-- Transport along an isomorphism of the equivalence
`quotientMaximalIdealPowAlgEquiv` onto a completion `B`. -/
noncomputable def quotientMaximalIdealPowAlgEquivOfAlgEquiv (n : ℕ) :
    (B ⧸ maximalIdeal B ^ n) ≃ₐ[k] A ⧸ maximalIdeal A ^ n :=
  (Ideal.quotientEquivAlg (maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n) (maximalIdeal B ^ n)
    Φ (by rw [Ideal.map_pow, map_maximalIdeal_algEquiv])).symm.trans
    (quotientMaximalIdealPowAlgEquiv k n)

/-- The transport diagram commutes: the class of `Φ (algebraMap … a)` is sent to
the class of `a`. -/
theorem quotientMaximalIdealPowAlgEquivOfAlgEquiv_mk (n : ℕ) (a : A) :
    quotientMaximalIdealPowAlgEquivOfAlgEquiv Φ n (Ideal.Quotient.mk _ (Φ (algebraMap A _ a)))
      = Ideal.Quotient.mk _ a := by
  rw [quotientMaximalIdealPowAlgEquivOfAlgEquiv, AlgEquiv.trans_apply,
    ← Ideal.quotientEquivAlg_mk (I := maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n)
      (J := maximalIdeal B ^ n) (f := Φ) (hIJ := by rw [Ideal.map_pow, map_maximalIdeal_algEquiv]),
    AlgEquiv.symm_apply_apply, quotientMaximalIdealPowAlgEquiv_mk_algebraMap]

end Transport

end AdicCompletion_en
