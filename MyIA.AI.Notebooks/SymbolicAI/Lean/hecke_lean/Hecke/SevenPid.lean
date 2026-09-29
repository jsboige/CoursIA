import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

/-!
# L'anneau des entiers de Q(ζ₇) est principal

Ce module prouve que si `K` est un corps tel que `IsCyclotomicExtension {7} ℚ K`
(c'est-à-dire `K = ℚ(ζ₇)`, le 7-ième corps cyclotomique), alors son anneau
d'entiers `𝓞 K = ℤ[ζ₇]` est un anneau principal (PID).

**Adaptation pédagogique** : ce fichier est un port du dépôt
`anthropics/fermats-last-theorem` (fichier
`P2M/Sol/S_IsCyclotomicExtension_Rat_seven_pid.lean`, commit
`aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`). Les énoncés et preuves sont
repris tels quels ; la documentation pédagogique et le sibling anglais
`SevenPid_en.lean` sont des additions CoursIA. La licence Apache-2.0 est
préservée (voir `NOTICE.md`).

## La stratégie en trois temps

Mathlib fournit déjà `IsCyclotomicExtension.Rat.three_pid` et `five_pid` :
pour `p = 3` et `p = 5`, la borne de Minkowski `M K` reste **inférieure au
discriminant**, et le critère simple
`RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt` conclut. Pour `p = 7`,
le discriminant `7^5 = 16807` dépasse largement `M K ≈ 4` : le critère simple
ne s'applique plus.

La preuve utilise donc le critère plus fin
`RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc`
(Marcus, *Number Fields*, discussion après le théorème 37) : `𝓞 K` est
principal dès que **chaque idéal premier `P` au-dessus d'un premier `p` avec
`p ^ f ≤ ⌊M K⌋₊** (où `f` est le degré d'inertie) est principal. Les étapes :

1. `floor_minkowskiBound_seven` / `floor_M_seven` : la partie entière de la
   borne de Minkowski de `ℚ(ζ₇)` vaut exactement `4` (approximations de `π`
   à 20 décimales et encadrement de `√16807` par `norm_num`) ;
2. `orderOf_two_zmod_seven`, `orderOf_three_zmod_seven` : les ordres de `2`
   et `3` dans `(ZMod 7)ˣ`, qui donnent les degrés d'inertie des idéaux
   au-dessus de `2` et `3` via `inertiaDeg_eq_of_not_dvd` ;
3. `seven_pid` : par `interval_cases`, les seuls candidats `p ∈ {1, …, 4}`
   sont éliminés — `1` n'est pas premier, les degrés d'inertie au-dessus de
   `2` et `3` produisent `p ^ f > 4`, et `4` n'est pas premier.

Les cas `11` et `13` (le résultat vaut pour tout `p ≤ 19`, mais « the proof
is more and more involved ») sont portés dans des tranches suivantes.
-/

set_option autoImplicit false

namespace CyclotomicPID

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers
open NumberField.RingOfIntegers Finset IsCyclotomicExtension.Rat Polynomial
open Real.Polynomial Polynomial.cyclotomic Ideal NumberField.Ideal

open scoped NumberField NumberField.InfinitePlace.NumberField

variable {K : Type*} [Field K] [NumberField K]

local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)

/-- `7` est premier, en instance `Fact` pour les lemmes de Mathlib. -/
scoped instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- La partie entière de la borne de Minkowski explicite de `ℚ(ζ₇)` vaut `4` :
`π` est encadré à 20 décimales (`pi_gt_d20`, `pi_lt_d20`) et `√16807` par `129`
et `130`, puis `norm_num` conclut. -/
lemma floor_minkowskiBound_seven : ⌊(4 / π) ^ 3 * (6! / 6 ^ 6 * √16807)⌋₊ = 4 := by
  refine (floor_eq_iff (by positivity)).mpr ⟨?_, ?_⟩
  · calc
      _ ≥ (4 / 3.14159265358979323847) ^ 3 * (6! / 6 ^ 6 * √16807) := by
        gcongr; exact pi_lt_d20.le
      _ ≥ (4 / 3.14159265358979323847) ^ 3 * (6! / 6 ^ 6 * 129) := by
        gcongr; exact (le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
      _ ≥ 4 := by norm_num
  · calc
      _ < (4 / 3.14159265358979323846) ^ 3 * (6! / 6 ^ 6 * √16807) := by
        gcongr; exact pi_gt_d20
      _ ≤ (4 / 3.14159265358979323846) ^ 3 * (6! / 6 ^ 6 * 130) := by
        gcongr; exact (sqrt_le_left (by norm_num)).mpr (by norm_num)
      _ ≤ _ := by norm_num

variable [IsCyclotomicExtension {7} ℚ K]

/-- La borne de Minkowski `M K` du 7-ième corps cyclotomique a pour partie
entière `4` : on réécrit `discr K`, `finrank ℚ K` et `nrComplexPlaces K` par
leurs valeurs (`7^5`, `6`, `3`), puis on conclut par
`floor_minkowskiBound_seven`. -/
theorem floor_M_seven : ⌊(M K)⌋₊ = 4 := by
  rw [discr_prime 7 K, IsCyclotomicExtension.finrank (n := 7) K
    (irreducible_rat (by norm_num)), nrComplexPlaces_eq_totient_div_two 7, totient_prime
      (by norm_num)]
  simp only [Nat.add_one_sub_one, reduceDiv, cast_ofNat, Int.reduceNeg, Int.reducePow,
    reduceSub, neg_mul, one_mul, Int.cast_neg, Int.cast_ofNat, abs_neg, abs_ofNat]
  exact floor_minkowskiBound_seven

/-- L'ordre de `2` dans `(ZMod 7)ˣ` vaut `3` : c'est le degré d'inertie des
idéaux au-dessus de `2` dans `ℚ(ζ₇)`. -/
lemma orderOf_two_zmod_seven : orderOf ((2 : ℕ) : ZMod 7) = 3 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm' ↦ ?_⟩
  interval_cases m <;> decide

/-- L'ordre de `3` dans `(ZMod 7)ˣ` vaut `6` : c'est le degré d'inertie des
idéaux au-dessus de `3` dans `ℚ(ζ₇)`. -/
lemma orderOf_three_zmod_seven : orderOf ((3 : ℕ) : ZMod 7) = 6 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm' ↦ ?_⟩
  interval_cases m <;> decide

variable (K) in
/-- **`ℤ[ζ₇]` est un anneau principal.** Si `K = ℚ(ζ₇)`, alors `𝓞 K` est un
PID : par le critère de Marcus, seuls les premiers `p ∈ {2, 3}` peuvent porter
un idéal non principal avec `p ^ f ≤ 4`, or leurs degrés d'inertie (`3` et
`6`) donnent `2 ^ 3 = 8 > 4` et `3 ^ 6 > 4`. -/
theorem seven_pid : IsPrincipalIdealRing (𝓞 K) := by
  refine RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
    (fun p hple hp P hPmem hle ↦ ?_)
  exfalso
  rw [floor_M_seven] at hple hle
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : P.IsPrime := hPmem.1
  haveI : P.LiesOver (span {(p : ℤ)}) := hPmem.2
  obtain ⟨hp1, hp4⟩ := Finset.mem_Icc.mp hple
  interval_cases p
  · exact Nat.not_prime_one hp
  · rw [inertiaDeg_eq_of_not_dvd 2 K P (m := 7) (by norm_num),
      orderOf_two_zmod_seven] at hle
    norm_num at hle
  · rw [inertiaDeg_eq_of_not_dvd 3 K P (m := 7) (by norm_num),
      orderOf_three_zmod_seven] at hle
    norm_num at hle
  · norm_num at hp

end CyclotomicPID
