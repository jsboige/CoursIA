import Mathlib.RingTheory.Valuation.RamificationGroup

/-!
# Groupes de ramification inférieurs : une couche d'arithmétique locale

Ce module pose, dans le lake `galois_lean`, la couche d'**arithmétique locale**
dédiée aux **groupes de ramification inférieurs** d'une extension de corps
valué, en aval du socle de complétion adique (#14783) et à la suite de la
migration de Mathlib 4.33 (#14773).

Le contenu est un portage pédagogique de
`Definitions/Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup.lean` du
dépôt
[`anthropics/fermats-last-theorem`](https://github.com/anthropics/fermats-last-theorem)
(commit `aa2d8b34`, licence Apache-2.0 — attribution et `NOTICE` préservées,
issue #14786). Les énoncés, preuves et noms de théorèmes sont conservés ; seules
les docstrings ont été rédigées et l'importation resserrée sur le module Mathlib
réellement utilisé (pas de `import Mathlib` global, qui forçait une clôture
inutile et faisait échouer la création des `.olean` sur le cache partiellement
extrait).

## D'où viennent ces objets

Quand un groupe $G$ agit sur un anneau local $R$ (par automorphismes de
`R`-algèbres), on dispose de deux sous-groupes qui décrivent « ce qui se passe
près du point » :

- le **groupe de décomposition** — les éléments de $G$ qui laissent l'idéal
  maximal stable (et agissent donc sur le corps résiduel) ;
- le **groupe d'inertie** — ceux qui agissent *trivialement* sur le corps
  résiduel, c'est-à-dire qui envoient chaque élément sur un élément congruent
  modulo l'idéal maximal (`I.inertia G`).

Les **groupes de ramification inférieurs** affinent l'inertie : pour un
entier $i$, `lowerRamificationGroup R G i` est l'ensemble des $σ ∈ G$ dont
l'action fixe $R$ **modulo $\mathfrak{m}^{i+1}$**, où $\mathfrak{m}$ est
l'idéal maximal. On obtient une tour

$$G = \mathrm{LRG}\,(-1) \supseteq \mathrm{LRG}\,0 \supseteq \mathrm{LRG}\,1
\supseteq \cdots$$

qui est **antitone** (plus $i$ grand, plus le groupe est petit). Le niveau
$i = 0$ n'est autre que le **noyau de l'action sur le corps résiduel**, c'est-à-
dire précisément l'inertie. C'est la distinction entre *décomposition*,
*inertie* et *ramification* que la ramification inférieure rend quantitative.

## Contenu

- **Sous-groupes additifs** (`AddSubgroup`) — monotonie de l'inertie : si
  $I ≤ J$, alors `I.inertia G ≤ J.inertia G`.
- **Idéaux** (`Ideal`) — l'inertie d'un idéal est monotone, celle de l'idéal
  trivial est triviale, et elle est **normale** dès que l'idéal est stable sous
  l'action (`inertia_normal_of_forall_smul_eq`).
- **Anneaux locaux** (`IsLocalRing`) — l'idéal maximal (et ses puissances) est
  stable sous l'action ; définition de `lowerRamificationGroup`, son caractère
  antitone, sa normalité, l'identification du niveau zéro au noyau de l'action
  sur `ResidueField R` et à l'inertie, et la filtration complète
  (`iInf_lowerRamificationGroup_eq_bot`).
- **Anneaux de valuation** (`ValuationSubring`) — wrapper
  `ValuationSubring.lowerRamificationGroup` et inclusion dans le sous-groupe
  d'inertie (`A.inertiaSubgroup K`).

## Axiomes

Les théorèmes n'utilisent que `propext`, `Classical.choice` et `Quot.sound` —
vérifié par les `#guard_msgs` de fin de module (aucun `sorry`, `sorryAx` ni
`native_decide`).
-/

set_option autoImplicit false

open scoped Pointwise

namespace AddSubgroup

variable {M : Type*} [AddGroup M] {G : Type*} [Group G] [MulAction G M]

theorem inertia_mono {I J : AddSubgroup M} (h : I ≤ J) : I.inertia G ≤ J.inertia G :=
  fun _ hσ x => h (hσ x)

end AddSubgroup

namespace Ideal

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [MulSemiringAction G R]

theorem inertia_mono {I J : Ideal R} (h : I ≤ J) :
    I.inertia G ≤ J.inertia G :=
  AddSubgroup.inertia_mono (Submodule.toAddSubgroup_mono h)

@[simp]
theorem inertia_top : (⊤ : Ideal R).inertia G = ⊤ := by
  ext; simp [Ideal.inertia, AddSubgroup.inertia]

theorem inertia_normal_of_forall_smul_eq {I : Ideal R}
    (hI : ∀ g : G, g • I = I) : (I.inertia G).Normal := by
  refine ⟨fun σ hσ τ x => ?_⟩

  have key : τ • (σ • (τ⁻¹ • x) - τ⁻¹ • x) ∈ τ • I :=
    Ideal.smul_mem_pointwise_smul _ _ _ (hσ _)
  simpa [smul_sub, smul_smul, mul_assoc, hI τ] using key

end Ideal

namespace IsLocalRing

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
  Ideal.inertia_mono (Ideal.pow_le_pow_right (by omega))

instance lowerRamificationGroup_normal (i : ℕ) :
    (lowerRamificationGroup R G i).Normal :=
  Ideal.inertia_normal_of_forall_smul_eq fun g => pointwise_smul_maximalIdeal_pow g (i + 1)

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

end IsLocalRing

namespace ValuationSubring

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]

def lowerRamificationGroup (A : ValuationSubring L) (i : ℕ) :
    Subgroup (A.decompositionSubgroup K) :=
  IsLocalRing.lowerRamificationGroup A (A.decompositionSubgroup K) i

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

end ValuationSubring

section Gates

example {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] [Subsingleton G] (i : ℕ) :
    IsLocalRing.lowerRamificationGroup R G i = ⊤ := by
  ext σ; simp [Subsingleton.elim σ 1]

example {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] :
    IsLocalRing.lowerRamificationGroup R G 1 ≤
      IsLocalRing.lowerRamificationGroup R G 0 :=
  IsLocalRing.lowerRamificationGroup_antitone (by omega)

example {R : Type*} [CommRing R] [IsLocalRing R] {G : Type*} [Group G] [MulSemiringAction G R] :
    (IsLocalRing.lowerRamificationGroup R G 0 : Set G) =
      ((IsLocalRing.maximalIdeal R).inertia G : Set G) := by
  rw [IsLocalRing.lowerRamificationGroup_zero_eq_inertia]

end Gates

/--
info: 'IsLocalRing.lowerRamificationGroup' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.lowerRamificationGroup

/--
info: 'IsLocalRing.lowerRamificationGroup_antitone' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.lowerRamificationGroup_antitone

/--
info: 'IsLocalRing.lowerRamificationGroup_normal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.lowerRamificationGroup_normal

/--
info: 'IsLocalRing.lowerRamificationGroup_zero_eq_ker' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.lowerRamificationGroup_zero_eq_ker

/--
info: 'IsLocalRing.iInf_lowerRamificationGroup_eq_bot' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.iInf_lowerRamificationGroup_eq_bot

/--
info: 'ValuationSubring.lowerRamificationGroup_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms ValuationSubring.lowerRamificationGroup_zero

/--
info: 'ValuationSubring.lowerRamificationGroup_le_inertiaSubgroup' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms ValuationSubring.lowerRamificationGroup_le_inertiaSubgroup
