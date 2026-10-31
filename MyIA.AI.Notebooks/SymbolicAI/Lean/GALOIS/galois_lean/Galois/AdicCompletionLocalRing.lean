import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Complétions adiques des anneaux locaux : une première couche

Ce module pose, dans le lake `galois_lean`, une couche d'**arithmétique
locale** dédiée aux **complétions adiques** d'un anneau local `A` par rapport
à son idéal maximal.

Le contenu est un portage pédagogique de
`Definitions/Def_AdicCompletionLocalRing.lean` du dépôt
[`anthropics/fermats-last-theorem`](https://github.com/anthropics/fermats-last-theorem)
(commit `aa2d8b34`, licence Apache-2.0 — attribution et `NOTICE` préservées,
issue #14783). Les énoncés, preuves et noms de théorèmes sont conservés ; seules
les docstrings ont été rédigées et les importations resserrées sur les modules
Mathlib utilisés (pas de `import Mathlib` global).

La couche s'articule en quatre sections :

- **Kernel** — pour un idéal `I`, le noyau de l'évaluation `evalₐ I n` est
  exactement l'image de `I ^ n` dans la complétion (`ker_evalₐ_eq_map_pow`) ;
  un élément `1 + x` avec `x` dans l'image d'un idéal `I` finiment engendré est
  une unité (`isUnit_one_add_of_mem_map`) ;
- **Exemple** — la troncature `2`-adique de `ℤ` : évaluer en degré `n`, c'est
  réduire modulo `2 ^ n`, et le noyau est l'image de `I ^ n` — le sens concret
  des quotients `A ⧸ I ^ n` ;
- **Local** — quand `A` est local et noethérien, l'idéal maximal de la
  complétion est le noyau de l'évaluation en degré 1, et le quotient par ses
  puissances s'identifie à celui de `A`
  (`quotientMaximalIdealPowAlgEquiv`) ;
- **Transport** — ces identités se transportent le long d'un isomorphisme
  d'algèbres, en particulier une équivalence entre complétions.

Ce socle est le prérequis des grains aval (Hensel, groupes de ramification,
issue #14786) ; il ne modifie pas le bundle M22/M23 existant du lake.

Les axiomes utilisés se réduisent à `propext`, `Classical.choice` et
`Quot.sound` — vérifiés par le gate `proof-integrity` de la CI (aucun `sorry`,
`sorryAx` ni `native_decide`).
-/

set_option autoImplicit false

open IsLocalRing

namespace AdicCompletion

variable {A : Type*} [CommRing A]

section Kernel

variable (I : Ideal A)

/-- L'image dans la complétion d'un élément `a`, ré-évaluée en degré `n`, est
la classe de `a` dans `A ⧸ I ^ n` : la forme de l'algèbre `algebraMap` est
préservée par `evalₐ`. -/
theorem evalₐ_algebraMap (n : ℕ) (a : A) :
    evalₐ I n (algebraMap A (AdicCompletion I A) a) = Ideal.Quotient.mk _ a := by
  rw [algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, evalₐ_of]

/-- Équivalence des deux descriptions (homomorphisme de `RingHom` et de
`LinearMap`) du noyau de l'évaluation `evalₐ I n`. -/
theorem mem_ker_evalₐ_iff (n : ℕ) (x : AdicCompletion I A) :
    x ∈ RingHom.ker (evalₐ I n) ↔ x ∈ LinearMap.ker (eval I A n) := by
  have h : (I ^ n • ⊤ : Ideal A) = I ^ n := by rw [smul_eq_mul, Ideal.mul_top]
  rw [RingHom.mem_ker, LinearMap.mem_ker]
  constructor
  · intro hx; rw [← factor_evalₐ_eq_eval I x h.ge, hx]; exact RingHom.map_zero _
  · intro hx; rw [← factor_eval_eq_evalₐ I x h.le, hx]; exact LinearMap.map_zero _

/-- Pour `I` finiment engendré, le noyau de `evalₐ I n` est exactement l'image
de la puissance `I ^ n` dans la complétion : c'est la caractérisation
« noyau d'évaluation = puissance de l'idéal » de la géométrie locale. -/
theorem ker_evalₐ_eq_map_pow (hI : I.FG) (n : ℕ) :
    RingHom.ker (evalₐ I n) = (I ^ n).map (algebraMap A (AdicCompletion I A)) := by
  ext x
  rw [mem_ker_evalₐ_iff, ← pow_smul_top_eq_ker_eval hI, Ideal.smul_top_eq_map,
    Submodule.restrictScalars_mem]

/-- Tout élément de la complétion s'écrit comme un élément de `A` plus un
élément de l'image de `I ^ n` : la complétion est engendrée au-dessus de `A` par
les petites puissances de l'idéal. -/
theorem exists_eq_algebraMap_add (hI : I.FG) (n : ℕ) (x : AdicCompletion I A) :
    ∃ a : A, ∃ y ∈ (I ^ n).map (algebraMap A (AdicCompletion I A)),
      x = algebraMap A (AdicCompletion I A) a + y := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
  refine ⟨a, x - algebraMap A _ a, ?_, by ring⟩
  rw [← ker_evalₐ_eq_map_pow I hI, RingHom.mem_ker, map_sub, evalₐ_algebraMap, ha, sub_self]

/-- Dans la complétion, `1 + x` est une unité dès que `x` est dans l'image de
l'idéal `I` (finiment engendré) : c'est le fait que l'image de l'idéal maximal
reste dans le radical de Jacobson. -/
theorem isUnit_one_add_of_mem_map (hI : I.FG) {x : AdicCompletion I A}
    (hx : x ∈ I.map (algebraMap A (AdicCompletion I A))) : IsUnit (1 + x) := by
  haveI : IsAdicComplete (I.map (algebraMap A (AdicCompletion I A))) (AdicCompletion I A) :=
    (IsAdicComplete.map_algebraMap_iff I (AdicCompletion I A)).mpr (isAdicComplete hI)
  have h := Ideal.mem_jacobson_bot.mp (IsAdicComplete.le_jacobson_bot _ hx) 1
  rwa [mul_one, add_comm] at h

/-- Version décalée du précédent : `u + x` est une unité dès que `u` en est une
et que `x` est dans l'image de `I` (le facteur inverse ramène à `1 + …`). -/
theorem isUnit_add_of_mem_map (hI : I.FG) {u x : AdicCompletion I A} (hu : IsUnit u)
    (hx : x ∈ I.map (algebraMap A (AdicCompletion I A))) : IsUnit (u + x) := by
  have e : u + x = u * (1 + ↑hu.unit⁻¹ * x) := by
    rw [mul_add, mul_one, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
  rw [e]
  exact hu.mul (isUnit_one_add_of_mem_map I hI (Ideal.mul_mem_left _ _ hx))

end Kernel

section Exemple

/-- Exemple pédagogique borné — la troncature 2-adique. Dans la complétion
`2`-adique de `ℤ`, évaluer en degré `3` revient à réduire modulo `2 ^ 3 = 8` :
l'image de `20` s'évalue sur la classe de `4`. C'est le sens concret des
quotients `A ⧸ I ^ n` : chaque niveau de la complétion est l'arithmétique
modulo `2 ^ n`. -/
example :
    evalₐ (Ideal.span {2} : Ideal ℤ) 3 (algebraMap ℤ (AdicCompletion (Ideal.span {2} : Ideal ℤ) ℤ) 20)
      = Ideal.Quotient.mk _ 4 := by
  rw [evalₐ_algebraMap]
  refine (Ideal.Quotient.eq (I := (Ideal.span {2} : Ideal ℤ) ^ 3)).mpr ?_
  rw [Ideal.span_singleton_pow, show (2 : ℤ) ^ 3 = 8 by norm_num]
  exact Ideal.mem_span_singleton'.mpr ⟨2, by norm_num⟩

/-- Le complément : le noyau de la troncature en degré `3` est exactement
l'image de `I ^ 3` (`ker_evalₐ_eq_map_pow`) — l'image de `8`, multiple de
`2 ^ 3`, s'évanouit au niveau `3`. -/
example :
    algebraMap ℤ (AdicCompletion (Ideal.span {2} : Ideal ℤ) ℤ) 8
      ∈ RingHom.ker (evalₐ (Ideal.span {2} : Ideal ℤ) 3) := by
  rw [ker_evalₐ_eq_map_pow _ (Submodule.fg_span_singleton 2),
    Ideal.span_singleton_pow, show (2 : ℤ) ^ 3 = 8 by norm_num]
  exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self 8)

end Exemple

section Local

variable [IsLocalRing A]

/-- Une unité de la complétion en l'idéal maximal se relève en une unité de
`A` : la réduction modulo le maximal ne crée pas de nouvelles unités. -/
theorem isUnit_of_isUnit_algebraMap {a : A}
    (h : IsUnit (algebraMap A (AdicCompletion (maximalIdeal A) A) a)) : IsUnit a := by
  by_contra ha
  have hmem : a ∈ maximalIdeal A ^ 1 := by
    rw [pow_one]; exact (mem_maximalIdeal a).mpr ha
  have h1 := h.map (evalₐ (maximalIdeal A) 1)
  rw [evalₐ_algebraMap, Ideal.Quotient.eq_zero_iff_mem.mpr hmem, isUnit_zero_iff] at h1
  exact (maximalIdeal.isMaximal A).ne_top
    ((pow_one (maximalIdeal A)).symm.trans (Ideal.Quotient.zero_eq_one_iff.mp h1))

/-- Cas particulier de `isUnit_one_add_of_mem_map` pour l'idéal maximal : un
élément de la forme `1 + x` avec `x` dans l'image du maximal est une unité. -/
theorem isUnit_one_add_of_mem_map_maximalIdeal (h𝔪 : (maximalIdeal A).FG)
    {x : AdicCompletion (maximalIdeal A) A}
    (hx : x ∈ (maximalIdeal A).map (algebraMap A (AdicCompletion (maximalIdeal A) A))) :
    IsUnit (1 + x) :=
  isUnit_one_add_of_mem_map _ h𝔪 hx

variable [IsNoetherianRing A]

/-- En anneau noethérien, l'idéal maximal est finiment engendré. -/
theorem maximalIdeal_fg : (maximalIdeal A).FG := IsNoetherian.noetherian _

/-- La complétion d'un anneau local noethérien en son idéal maximal est encore
un anneau local. -/
instance instIsLocalRingMaximalIdeal : IsLocalRing (AdicCompletion (maximalIdeal A) A) :=
  isLocalRing_of_fg maximalIdeal_fg

/-- Dans la complétion, la puissance `n`-ième de l'idéal maximal est le noyau
de l'évaluation en degré `n`. -/
theorem maximalIdeal_pow_eq_ker_evalₐ (n : ℕ) :
    maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n = RingHom.ker (evalₐ (maximalIdeal A) n) := by
  rw [maximalIdeal_eq_map, ← Ideal.map_pow, ker_evalₐ_eq_map_pow _ maximalIdeal_fg]

/-- Le degré 1 : l'idéal maximal de la complétion est le noyau de `evalₐ` en
degré 1. -/
theorem maximalIdeal_eq_ker_evalₐ_one :
    maximalIdeal (AdicCompletion (maximalIdeal A) A) = RingHom.ker (evalₐ (maximalIdeal A) 1) := by
  rw [← maximalIdeal_pow_eq_ker_evalₐ, pow_one]

/-- Membrane de l'idéal maximal de la complétion en fonction de l'évaluation
en degré 1. -/
theorem mem_maximalIdeal_iff (x : AdicCompletion (maximalIdeal A) A) :
    x ∈ maximalIdeal (AdicCompletion (maximalIdeal A) A) ↔ evalₐ (maximalIdeal A) 1 x = 0 := by
  rw [maximalIdeal_eq_ker_evalₐ_one, RingHom.mem_ker]

section Scalars

variable (k : Type*) [CommRing k] [Algebra k A]

/-- L'isomorphisme (en tant qu'algèbre sur `k`) entre le quotient de la
complétion par la puissance `n` de son idéal maximal et le quotient de `A` par
`maximalIdeal A ^ n`. -/
noncomputable def quotientMaximalIdealPowAlgHom (n : ℕ) :
    (AdicCompletion (maximalIdeal A) A ⧸ maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n)
      →ₐ[k] A ⧸ maximalIdeal A ^ n :=
  Ideal.Quotient.liftₐ _ ((evalₐ (maximalIdeal A) n).restrictScalars k) fun x hx => by
    rwa [maximalIdeal_pow_eq_ker_evalₐ, RingHom.mem_ker] at hx

/-- Action de `quotientMaximalIdealPowAlgHom` sur une classe, par l'évaluation
en degré `n`. -/
theorem quotientMaximalIdealPowAlgHom_mk (n : ℕ) (x : AdicCompletion (maximalIdeal A) A) :
    quotientMaximalIdealPowAlgHom k n (Ideal.Quotient.mk _ x) = evalₐ (maximalIdeal A) n x :=
  rfl

/-- Le morphisme de quotient précédent est bijectif : les quotients par les
puissances de l'idéal maximal sont algébriquement équivalents. -/
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

/-- L'équivalence d'algèbres entre le quotient de la complétion par `𝔪 ^ n` et
le quotient de `A` par `𝔪 ^ n` (`𝔪 = maximalIdeal A`). -/
noncomputable def quotientMaximalIdealPowAlgEquiv (n : ℕ) :
    (AdicCompletion (maximalIdeal A) A ⧸ maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n)
      ≃ₐ[k] A ⧸ maximalIdeal A ^ n :=
  AlgEquiv.ofBijective _ (quotientMaximalIdealPowAlgHom_bijective k n)

/-- Action de `quotientMaximalIdealPowAlgEquiv` sur une classe. -/
theorem quotientMaximalIdealPowAlgEquiv_mk (n : ℕ) (x : AdicCompletion (maximalIdeal A) A) :
    quotientMaximalIdealPowAlgEquiv k n (Ideal.Quotient.mk _ x) = evalₐ (maximalIdeal A) n x :=
  rfl

/-- Le diagramme avec `algebraMap` commute : passer l'image d'un élément de `A`
par l'équivalence revient à prendre sa classe dans `A ⧸ 𝔪 ^ n`. -/
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
/-- Un isomorphisme d'algèbres préserve le caractère unité dans les deux sens. -/
theorem isUnit_algEquiv_iff (x : AdicCompletion (maximalIdeal A) A) : IsUnit (Φ x) ↔ IsUnit x :=
  ⟨fun h => by simpa using h.map Φ.symm, fun h => h.map Φ⟩

/-- L'image réciproque du maximal de `B` par un isomorphisme est le maximal de
la complétion. -/
theorem comap_maximalIdeal_algEquiv :
    (maximalIdeal B).comap (Φ : AdicCompletion (maximalIdeal A) A →+* B)
      = maximalIdeal (AdicCompletion (maximalIdeal A) A) := by
  ext x
  show Φ x ∈ maximalIdeal B ↔ x ∈ maximalIdeal _
  rw [mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, isUnit_algEquiv_iff]

/-- L'image du maximal de la complétion par un isomorphisme est le maximal de
`B`. -/
theorem map_maximalIdeal_algEquiv :
    (maximalIdeal (AdicCompletion (maximalIdeal A) A)).map
        (Φ : AdicCompletion (maximalIdeal A) A →+* B) = maximalIdeal B := by
  rw [← comap_maximalIdeal_algEquiv Φ]
  exact Ideal.map_comap_of_surjective _ Φ.surjective _

/-- Le maximal de `B` s'obtient comme image du maximal de `A` via le composé
`algebraMap` puis `Φ`. -/
theorem maximalIdeal_eq_map_algEquiv :
    maximalIdeal B = (maximalIdeal A).map
      ((Φ : AdicCompletion (maximalIdeal A) A →+* B).comp
        (algebraMap A (AdicCompletion (maximalIdeal A) A))) := by
  rw [← Ideal.map_map, ← maximalIdeal_eq_map, map_maximalIdeal_algEquiv]

/-- Version puissance du précédent : la puissance `n` du maximal de `B` est
l'image de `𝔪 ^ n` via le composé. -/
theorem maximalIdeal_pow_eq_map_algEquiv (n : ℕ) :
    maximalIdeal B ^ n = (maximalIdeal A ^ n).map
      ((Φ : AdicCompletion (maximalIdeal A) A →+* B).comp
        (algebraMap A (AdicCompletion (maximalIdeal A) A))) := by
  rw [Ideal.map_pow, ← maximalIdeal_eq_map_algEquiv]

/-- L'image par `Φ` d'un élément du maximal de `A` reste dans le maximal de
`B`. -/
theorem algEquiv_algebraMap_mem_maximalIdeal {a : A} (ha : a ∈ maximalIdeal A) :
    Φ (algebraMap A _ a) ∈ maximalIdeal B := by
  rw [maximalIdeal_eq_map_algEquiv Φ]
  exact Ideal.mem_map_of_mem _ ha

/-- Transport le long d'un isomorphisme de l'équivalence
`quotientMaximalIdealPowAlgEquiv` sur une complétion `B`. -/
noncomputable def quotientMaximalIdealPowAlgEquivOfAlgEquiv (n : ℕ) :
    (B ⧸ maximalIdeal B ^ n) ≃ₐ[k] A ⧸ maximalIdeal A ^ n :=
  (Ideal.quotientEquivAlg (maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n) (maximalIdeal B ^ n)
    Φ (by rw [Ideal.map_pow, map_maximalIdeal_algEquiv])).symm.trans
    (quotientMaximalIdealPowAlgEquiv k n)

/-- Le diagramme de transport commute : la classe d'`Φ (algebraMap … a)` s'envoie
sur la classe de `a`. -/
theorem quotientMaximalIdealPowAlgEquivOfAlgEquiv_mk (n : ℕ) (a : A) :
    quotientMaximalIdealPowAlgEquivOfAlgEquiv Φ n (Ideal.Quotient.mk _ (Φ (algebraMap A _ a)))
      = Ideal.Quotient.mk _ a := by
  rw [quotientMaximalIdealPowAlgEquivOfAlgEquiv, AlgEquiv.trans_apply,
    ← Ideal.quotientEquivAlg_mk (I := maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n)
      (J := maximalIdeal B ^ n) (f := Φ) (hIJ := by rw [Ideal.map_pow, map_maximalIdeal_algEquiv]),
    AlgEquiv.symm_apply_apply, quotientMaximalIdealPowAlgEquiv_mk_algebraMap]

end Transport

end AdicCompletion
