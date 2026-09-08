import Mathlib.RingTheory.Valuation.RamificationGroup
import Galois.LowerRamificationGroup

/-!
# Lower ramification groups : a local-arithmetic layer

This module sets up, in the `galois_lean` lake, the **local arithmetic** layer
devoted to the **lower ramification groups** of a valued field extension,
downstream of the adic-completion base (#14783) and following the Mathlib 4.33
migration (#14773).

The content is a pedagogical port of
`Definitions/Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup.lean` from
the
[`anthropics/fermats-last-theorem`](https://github.com/anthropics/fermats-last-theorem)
repository (commit `aa2d8b34`, Apache-2.0 licence — attribution and `NOTICE`
preserved, issue #14786). Statements, proofs and theorem names are kept; only
the docstrings were written and the imports tightened to the Mathlib module
actually used (no global `import Mathlib`, which forced a useless whole-library
closure and failed to build `.olean` on a partially-extracted cache).

## Where these objects come from

When a group $G$ acts on a local ring $R$ (by `R`-algebra automorphisms), two
subgroups describe "what happens near the point":

- the **decomposition group** — the elements of $G$ that keep the maximal
  ideal stable (hence act on the residue field);
- the **inertia group** — those that act *trivially* on the residue field,
  i.e. send each element to a congruent one modulo the maximal ideal
  (`I.inertia G`).

The **lower ramification groups** refine inertia: for an integer $i$,
`lowerRamificationGroup R G i` is the set of $σ ∈ G$ whose action fixes $R$
**modulo $\mathfrak{m}^{i+1}$**, where $\mathfrak{m}$ is the maximal ideal.
This yields a tower

$$G = \mathrm{LRG}\,(-1) \supseteq \mathrm{LRG}\,0 \supseteq \mathrm{LRG}\,1
\supseteq \cdots$$

which is **antitone** (the larger $i$, the smaller the group). The level
$i = 0$ is precisely the **kernel of the action on the residue field**, that is
the inertia. This is the distinction between *decomposition*, *inertia* and
*ramification* that lower ramification makes quantitative.

## Contents

- **Additive subgroups** (`AddSubgroup`) — monotonicity of inertia: if
  $I ≤ J$, then `I.inertia G ≤ J.inertia G`.
- **Ideals** (`Ideal`) — the inertia of an ideal is monotone, that of the
  top ideal is trivial, and it is **normal** as soon as the ideal is stable
  under the action (`inertia_normal_of_forall_smul_eq`).
- **Local rings** (`IsLocalRing`) — the maximal ideal (and its powers) is
  stable under the action; definition of `lowerRamificationGroup`, its
  monotonicity, its normality, the identification of level zero with the
  kernel of the action on `ResidueField R` and with the inertia, and the
  whole filtration (`iInf_lowerRamificationGroup_eq_bot`).
- **Valuation subrings** (`ValuationSubring`) — wrapper
  `ValuationSubring.lowerRamificationGroup` and inclusion in the inertia
  subgroup (`A.inertiaSubgroup K`).

## Axioms

The theorems use only `propext`, `Classical.choice` and `Quot.sound` —
checked by the final `#guard_msgs` (no `sorry`, `sorryAx` or `native_decide`).
-/

set_option autoImplicit false

open scoped Pointwise
open IsLocalRing Ideal AddSubgroup ValuationSubring

namespace AddSubgroup_en

variable {M : Type*} [AddGroup M] {G : Type*} [Group G] [MulAction G M]

theorem inertia_mono {I J : AddSubgroup M} (h : I ≤ J) : I.inertia G ≤ J.inertia G :=
  fun _ hσ x => h (hσ x)

end AddSubgroup_en

namespace Ideal_en

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [MulSemiringAction G R]

theorem inertia_mono {I J : Ideal R} (h : I ≤ J) :
    I.inertia G ≤ J.inertia G :=
  AddSubgroup_en.inertia_mono (Submodule.toAddSubgroup_mono h)

@[simp]
theorem inertia_top : (⊤ : Ideal R).inertia G = ⊤ := by
  ext; simp [Ideal.inertia, AddSubgroup.inertia]

theorem inertia_normal_of_forall_smul_eq {I : Ideal R}
    (hI : ∀ g : G, g • I = I) : (I.inertia G).Normal := by
  refine ⟨fun σ hσ τ x => ?_⟩

  have key : τ • (σ • (τ⁻¹ • x) - τ⁻¹ • x) ∈ τ • I :=
    Ideal.smul_mem_pointwise_smul _ _ _ (hσ _)
  simpa [smul_sub, smul_smul, mul_assoc, hI τ] using key

end Ideal_en

namespace IsLocalRing_en

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

@[simp]
theorem pointwise_smul_maximalIdeal (g : G) :
    g • maximalIdeal R = maximalIdeal R := by
  refine le_antisymm (le_maximalIdeal_of_isPrime _) ?_
  rw [Ideal.subset_pointwise_smul_iff]
  exact le_maximalIdeal_of_isPrime _

@[simp]
theorem pointwise_smul_maximalIdeal_pow (g : G) (n : ℕ) :
    g • (maximalIdeal R) ^ n = (maximalIdeal R) ^ n := by
  rw [Ideal.pointwise_smul_def, Ideal.map_pow, ← Ideal.pointwise_smul_def,
    pointwise_smul_maximalIdeal]

variable (R G) in

def lowerRamificationGroup (i : ℕ) : Subgroup G :=
  ((maximalIdeal R) ^ (i + 1)).inertia G

variable {i : ℕ}

@[simp]
theorem mem_lowerRamificationGroup {σ : G} :
    σ ∈ lowerRamificationGroup R G i ↔ ∀ x : R, σ • x - x ∈ (maximalIdeal R) ^ (i + 1) :=
  Iff.rfl

theorem lowerRamificationGroup_antitone :
    Antitone (lowerRamificationGroup R G) := fun _ _ hij =>
  Ideal_en.inertia_mono (Ideal.pow_le_pow_right (by omega))

instance lowerRamificationGroup_normal (i : ℕ) :
    (lowerRamificationGroup R G i).Normal :=
  Ideal_en.inertia_normal_of_forall_smul_eq fun g => pointwise_smul_maximalIdeal_pow g (i + 1)

theorem lowerRamificationGroup_zero_eq_ker :
    lowerRamificationGroup R G 0 =
      MonoidHom.ker (MulSemiringAction.toRingAut G (ResidueField R)) := by
  ext σ
  simp only [mem_lowerRamificationGroup, zero_add, pow_one, MonoidHom.mem_ker]
  constructor
  · intro hσ
    ext y
    obtain ⟨r, rfl⟩ := residue_surjective y
    have : residue R (σ • r - r) = 0 := (residue_eq_zero_iff _).mpr (hσ r)
    simpa [sub_eq_zero, ResidueField.residue_smul] using this
  · intro hσ r
    rw [← residue_eq_zero_iff, map_sub, ResidueField.residue_smul, sub_eq_zero]
    exact DFunLike.congr_fun hσ (residue R r)

theorem lowerRamificationGroup_zero_eq_inertia :
    lowerRamificationGroup R G 0 = (maximalIdeal R).inertia G := by
  simp only [lowerRamificationGroup, zero_add, pow_one]

theorem lowerRamificationGroup_le_zero (i : ℕ) :
    lowerRamificationGroup R G i ≤ lowerRamificationGroup R G 0 :=
  lowerRamificationGroup_antitone (Nat.zero_le i)

theorem iInf_lowerRamificationGroup_le_ker_toRingAut
    (hsep : ⨅ n, (maximalIdeal R) ^ n = ⊥) :
    ⨅ i, lowerRamificationGroup R G i ≤
      MonoidHom.ker (MulSemiringAction.toRingAut G R) := by
  intro σ hσ
  simp only [Subgroup.mem_iInf, mem_lowerRamificationGroup] at hσ
  ext x
  have : σ • x - x ∈ ⨅ n, (maximalIdeal R) ^ n := by
    simp only [Ideal.mem_iInf]
    intro n
    rcases n with _ | n
    · simp
    · exact hσ n x
  rw [hsep] at this
  simpa [sub_eq_zero] using this

theorem iInf_lowerRamificationGroup_eq_bot
    (hsep : ⨅ n, (maximalIdeal R) ^ n = ⊥) [FaithfulSMul G R] :
    ⨅ i, lowerRamificationGroup R G i = (⊥ : Subgroup G) := by
  refine le_bot_iff.mp fun σ hσ => ?_
  have h := iInf_lowerRamificationGroup_le_ker_toRingAut hsep hσ
  rw [MonoidHom.mem_ker] at h
  exact FaithfulSMul.eq_of_smul_eq_smul (α := R) fun x => by
    have := DFunLike.congr_fun h x; simpa using this.trans (one_smul G x).symm

end IsLocalRing_en

namespace ValuationSubring_en

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]

def lowerRamificationGroup (A : ValuationSubring L) (i : ℕ) :
    Subgroup (A.decompositionSubgroup K) :=
  IsLocalRing_en.lowerRamificationGroup A (A.decompositionSubgroup K) i

variable {K} {A : ValuationSubring L} {i : ℕ}

@[simp]
theorem mem_lowerRamificationGroup {σ : A.decompositionSubgroup K} :
    σ ∈ A.lowerRamificationGroup K i ↔
      ∀ a : A, σ • a - a ∈ (IsLocalRing.maximalIdeal A) ^ (i + 1) :=
  Iff.rfl

theorem lowerRamificationGroup_antitone :
    Antitone (A.lowerRamificationGroup K) :=
  IsLocalRing.lowerRamificationGroup_antitone

instance lowerRamificationGroup_normal (i : ℕ) :
    (A.lowerRamificationGroup K i).Normal :=
  IsLocalRing.lowerRamificationGroup_normal i

theorem lowerRamificationGroup_zero :
    A.lowerRamificationGroup K 0 = A.inertiaSubgroup K :=
  IsLocalRing.lowerRamificationGroup_zero_eq_ker

theorem lowerRamificationGroup_le_inertiaSubgroup (i : ℕ) :
    A.lowerRamificationGroup K i ≤ A.inertiaSubgroup K :=
  lowerRamificationGroup_zero (K := K) (A := A) ▸ IsLocalRing.lowerRamificationGroup_le_zero i

end ValuationSubring_en

section Gates

example {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] [Subsingleton G] (i : ℕ) :
    IsLocalRing_en.lowerRamificationGroup R G i = ⊤ := by
  ext σ; simp [Subsingleton.elim σ 1]

example {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] :
    IsLocalRing_en.lowerRamificationGroup R G 1 ≤
      IsLocalRing_en.lowerRamificationGroup R G 0 :=
  IsLocalRing_en.lowerRamificationGroup_antitone (by omega)

example {R : Type*} [CommRing R] [IsLocalRing R] {G : Type*} [Group G] [MulSemiringAction G R] :
    (IsLocalRing_en.lowerRamificationGroup R G 0 : Set G) =
      ((IsLocalRing.maximalIdeal R).inertia G : Set G) := by
  rw [IsLocalRing_en.lowerRamificationGroup_zero_eq_inertia]

end Gates

/--
info: 'IsLocalRing_en.lowerRamificationGroup' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing_en.lowerRamificationGroup

/--
info: 'IsLocalRing_en.lowerRamificationGroup_antitone' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing_en.lowerRamificationGroup_antitone

/--
info: 'IsLocalRing_en.lowerRamificationGroup_normal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing_en.lowerRamificationGroup_normal

/--
info: 'IsLocalRing_en.lowerRamificationGroup_zero_eq_ker' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing_en.lowerRamificationGroup_zero_eq_ker

/--
info: 'IsLocalRing_en.iInf_lowerRamificationGroup_eq_bot' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing_en.iInf_lowerRamificationGroup_eq_bot

/--
info: 'ValuationSubring_en.lowerRamificationGroup_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms ValuationSubring_en.lowerRamificationGroup_zero

/--
info: 'ValuationSubring_en.lowerRamificationGroup_le_inertiaSubgroup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms ValuationSubring_en.lowerRamificationGroup_le_inertiaSubgroup
