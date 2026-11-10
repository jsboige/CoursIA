import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.RingTheory.ZMod
import Mathlib.Tactic

/-!
# L'anneau des entiers de Q(ζ₁₁) est principal

Ce module prouve que si `K` est un corps tel que `IsCyclotomicExtension {11} ℚ K`
(c'est-à-dire `K = ℚ(ζ₁₁)`, le 11-ième corps cyclotomique), alors son anneau
d'entiers `𝓞 K = ℤ[ζ₁₁]` est un anneau principal (PID).

**Adaptation pédagogique** : ce fichier est un port du dépôt
`anthropics/fermats-last-theorem` (fichier
`P2M/Sol/S_IsCyclotomicExtension_Rat_eleven_pid.lean`, commit
`aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`). Les énoncés et preuves sont
repris tels quels ; la documentation pédagogique et le sibling anglais
`ElevenPid_en.lean` sont des additions CoursIA. La licence Apache-2.0 est
préservée (voir `NOTICE.md`).

## La stratégie

Comme pour `seven_pid`, la borne de Minkowski `M K` vaut `58` (lemme `crazy11`)
et le critère de Marcus réduit la question aux idéaux premiers au-dessus des
`p` avec `p ^ f ≤ 58` :

1. `p = 11` (le premier ramifié) : l'idéal est engendré par `ζ₁₁ - 1` ;
2. `p = 23` : le lemme `isPrincipal_of_liesOver_twentythree` exhibe un
   générateur explicite — l'image réciproque du morphisme `𝓞 K →+ ZMod 23`
   envoyant `ζ₁₁ ↦ 4` est `span {α}` avec `α = ζ³ + ζ + 1`, via les
   identités `α * β = 23` et `α * γ = ζ - 4` puis un argument galoisien ;
3. les autres `p ∈ {2, …, 58}` : leurs degrés d'inertie (ordres de `p` dans
   `(ZMod 11)ˣ`, lemme générique `not_pow_orderOf_le`) donnent `p ^ f > 58`.
-/

set_option autoImplicit false

namespace CyclotomicPID

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers
open NumberField.RingOfIntegers Finset IsCyclotomicExtension.Rat Polynomial
open Real.Polynomial Polynomial.cyclotomic Ideal NumberField.Ideal

open scoped NumberField NumberField.InfinitePlace.NumberField Pointwise

variable {K : Type*} [Field K] [NumberField K]

local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)

/-- `11` est premier, en instance `Fact` pour les lemmes de Mathlib. -/
scoped instance fact_prime_eleven : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- `23` est premier, en instance `Fact` pour les lemmes de Mathlib. -/
scoped instance fact_prime_twentythree : Fact (Nat.Prime 23) := ⟨by norm_num⟩

/-- La partie entière de la borne de Minkowski explicite de `ℚ(ζ₁₁)` vaut `58` :
`π` est encadré à 20 décimales et `√2357947691 = √(11^9)` par `48558` et `48559`,
puis `norm_num` conclut. -/
lemma crazy11 : ⌊(4 / π) ^ 5 * (10! / 10 ^ 10 * √2357947691)⌋₊ = 58 := by
  refine (floor_eq_iff (by positivity)).mpr ⟨?_, ?_⟩
  · calc
      _ ≥ (4 / 3.14159265358979323847) ^ 5 * (10! / 10 ^ 10 * √2357947691) := by
        gcongr; exact pi_lt_d20.le
      _ ≥ (4 / 3.14159265358979323847) ^ 5 * (10! / 10 ^ 10 * 48558) := by
        gcongr; exact (le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
      _ ≥ 58 := by norm_num
  · calc
      _ < (4 / 3.14159265358979323846) ^ 5 * (10! / 10 ^ 10 * √2357947691) := by
        gcongr; exact pi_gt_d20
      _ ≤ (4 / 3.14159265358979323846) ^ 5 * (10! / 10 ^ 10 * 48559) := by
        gcongr; exact (sqrt_le_left (by norm_num)).mpr (by norm_num)
      _ ≤ _ := by norm_num

section Cyclo

variable [hK : IsCyclotomicExtension {11} ℚ K]

/-- La borne de Minkowski `M K` du 11-ième corps cyclotomique a pour partie
entière `58` : on réécrit `discr K`, `finrank ℚ K` et `nrComplexPlaces K` par
leurs valeurs (`11^9`, `10`, `5`), puis on conclut par `crazy11`. -/
theorem M11 : ⌊(M K)⌋₊ = 58 := by
  rw [discr_prime 11 K, IsCyclotomicExtension.finrank (n := 11) K
    (irreducible_rat (by norm_num)), nrComplexPlaces_eq_totient_div_two 11, totient_prime
      (by norm_num)]
  simp only [Nat.add_one_sub_one, reduceDiv, cast_ofNat, Int.reduceNeg, Int.reducePow,
    reduceSub, neg_mul, one_mul, Int.cast_neg, Int.cast_ofNat, abs_neg, abs_ofNat]
  exact crazy11

/-- Lemme générique : si `a` est d'ordre fini dans `ZMod m` avec `a ^ i ≠ 1`
pour tout `1 ≤ i ≤ k`, alors `p ^ orderOf a` dépasse toute borne `B < p ^ (k + 1)`.
C'est l'outil qui élimine les premiers `p` restants via leurs degrés d'inertie. -/
lemma not_pow_orderOf_le {a : ZMod 11} {p B : ℕ} (k : ℕ) (h10 : a ^ 10 = 1) (hp : 0 < p)
    (hk : B < p ^ (k + 1)) (hne : ∀ i ∈ Finset.Icc 1 k, a ^ i ≠ 1) : ¬ p ^ orderOf a ≤ B := by
  intro hle
  have hfin : IsOfFinOrder a := isOfFinOrder_iff_pow_eq_one.mpr ⟨10, by norm_num, h10⟩
  have hpos : 0 < orderOf a := hfin.orderOf_pos
  have hord : k + 1 ≤ orderOf a := by
    by_contra hlt
    push Not at hlt
    exact hne (orderOf a) (Finset.mem_Icc.mpr ⟨hpos, by omega⟩) (pow_orderOf_eq_one a)
  have := Nat.pow_le_pow_right hp hord
  omega

/-- **Tout idéal premier au-dessus de `23` est principal.** Le morphisme
`𝓞 K →ₐ[ℤ] ZMod 23` envoyant `ζ₁₁ ↦ 4` a pour noyau `span {α}` avec
`α = ζ³ + ζ + 1` (via `α * β = 23` et `α * γ = ζ - 4`) ; un argument
galoisien transporte ce générateur à tout idéal au-dessus de `23`. -/
theorem isPrincipal_of_liesOver_twentythree (P : Ideal (𝓞 K)) [hP : P.IsPrime]
    [hP23 : P.LiesOver (span {(23 : ℤ)})] : Submodule.IsPrincipal P := by
  have hζ := hK.zeta_spec
  set z : 𝓞 K := hζ.toInteger with hz

  have hrel : z ^ 10 + z ^ 9 + z ^ 8 + z ^ 7 + z ^ 6 + z ^ 5 + z ^ 4 + z ^ 3 + z ^ 2 + z + 1 = 0 := by
    have h := hζ.geom_sum_eq_zero (by norm_num : 1 < 11)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero] at h
    have hzK : algebraMap (𝓞 K) K z = IsCyclotomicExtension.zeta 11 ℚ K := by
      rw [hz]; rfl
    refine (map_eq_zero_iff (algebraMap (𝓞 K) K) (RingOfIntegers.coe_injective)).mp ?_
    simp only [map_add, map_pow, map_one, hzK]
    linear_combination h

  let pb := hζ.integralPowerBasis
  have hgen : pb.gen = z := by rw [hz]; exact hζ.integralPowerBasis_gen
  have hmin : minpoly ℤ pb.gen = cyclotomic 11 ℤ := by
    rw [hgen, hz, cyclotomic_eq_minpoly hζ (by norm_num)]
    exact (minpoly.algebraMap_eq RingOfIntegers.coe_injective hζ.toInteger).symm
  have h4 : aeval (4 : ZMod 23) (minpoly ℤ pb.gen) = 0 := by
    rw [hmin, cyclotomic_prime, map_sum]
    simp only [map_pow, aeval_X]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    decide
  let f23 : 𝓞 K →ₐ[ℤ] ZMod 23 := pb.lift 4 h4
  have hφz : f23 z = 4 := by rw [← hgen]; exact pb.lift_gen 4 h4

  set P₀ : Ideal (𝓞 K) := RingHom.ker f23.toRingHom with hP₀
  haveI hP₀prime : P₀.IsPrime := RingHom.ker_isPrime _
  haveI hP₀over : P₀.LiesOver (span {(23 : ℤ)}) := by
    refine ⟨?_⟩
    rw [Ideal.under_def, hP₀, RingHom.comap_ker]
    have : f23.toRingHom.comp (algebraMap ℤ (𝓞 K)) = Int.castRingHom (ZMod 23) :=
      RingHom.ext_int _ _
    rw [this, ZMod.ker_intCastRingHom]
    rfl

  set α : 𝓞 K := z ^ 3 + z + 1 with hα
  set β : 𝓞 K := -15 * z ^ 9 - 6 * z ^ 8 - 16 * z ^ 7 - 10 * z ^ 6 - 9 * z ^ 5 - 5 * z ^ 4
    - 12 * z ^ 3 - 17 * z ^ 2 - 14 * z - 2 with hβ
  set γ : 𝓞 K := 3 * z ^ 9 + z ^ 8 + 3 * z ^ 7 + 2 * z ^ 6 + 2 * z ^ 5 + z ^ 4 + 2 * z ^ 3
    + 3 * z ^ 2 + 3 * z + 1 with hγ
  have hαβ : α * β = 23 := by
    rw [hα, hβ]; linear_combination (-15 * z ^ 2 + 9 * z - 25) * hrel
  have hαγ : α * γ = z - 4 := by
    rw [hα, hγ]; linear_combination (3 * z ^ 2 - 2 * z + 5) * hrel

  have hP₀eq : P₀ = span {α} := by
    apply le_antisymm
    · intro x hx
      have hx0 : f23 x = 0 := hx
      obtain ⟨b, rfl⟩ := pb.exists_eq_aeval' x
      rw [pb.lift_aeval 4 h4] at hx0
      have e4 : aeval (4 : ZMod 23) b = ((b.eval 4 : ℤ) : ZMod 23) := by
        have := Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (A := ZMod 23) (4 : ℤ) b
        simpa using this
      rw [e4, ZMod.intCast_zmod_eq_zero_iff_dvd] at hx0
      obtain ⟨m, hm⟩ := hx0

      obtain ⟨q, hq⟩ := X_sub_C_dvd_sub_C_eval (p := b) (a := (4 : ℤ))
      have hb : b = (X - C 4) * q + C (b.eval 4) := by rw [← hq]; ring
      have ex : aeval pb.gen b = (z - 4) * aeval z q + ((b.eval 4 : ℤ) : 𝓞 K) := by
        rw [hgen]
        conv_lhs => rw [hb]
        rw [map_add, map_mul, map_sub, aeval_X, aeval_C, aeval_C, map_ofNat, eq_intCast]
      rw [ex, hm]
      refine Ideal.mem_span_singleton'.mpr ⟨γ * aeval z q + β * (m : 𝓞 K), ?_⟩
      push_cast
      linear_combination (aeval z q) * hαγ + (m : 𝓞 K) * hαβ
    · rw [span_le, Set.singleton_subset_iff]
      show f23 α = 0
      rw [hα]
      simp only [map_add, map_pow, map_one, hφz]
      decide

  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {(11 : ℕ)} ℚ K
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (span {(23 : ℤ)}) P₀ P Gal(K/ℚ)
  refine ⟨⟨σ • α, ?_⟩⟩
  rw [← hσ, hP₀eq, Ideal.submodule_span_eq, Ideal.smul_closure, Set.smul_set_singleton]

variable (K) in
/-- **`ℤ[ζ₁₁]` est un anneau principal.** Si `K = ℚ(ζ₁₁)`, alors `𝓞 K` est un
PID : par le critère de Marcus avec `⌊M K⌋₊ = 58`, le premier ramifié `11`
donne des idéaux engendrés par `ζ₁₁ - 1`, les idéaux au-dessus de `23` sont
principaux (`isPrincipal_of_liesOver_twentythree`), et les autres premiers
sont éliminés par leurs degrés d'inertie dans `(ZMod 11)ˣ`. -/
theorem eleven_pid : IsPrincipalIdealRing (𝓞 K) := by
  refine RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
    (fun p hple hp P hPmem hle ↦ ?_)
  rw [M11] at hple hle
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : P.IsPrime := hPmem.1
  haveI : P.LiesOver (span {(p : ℤ)}) := hPmem.2
  by_cases h11 : p = 11
  · subst h11
    exact ⟨⟨hK.zeta_spec.toInteger - 1, by
      rw [eq_span_zeta_sub_one_of_liesOver' 11 K hK.zeta_spec P]⟩⟩
  by_cases h23 : p = 23
  · subst h23
    exact isPrincipal_of_liesOver_twentythree P
  exfalso
  have hndvd : ¬ p ∣ 11 := fun h => h11 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)
  rw [inertiaDeg_eq_of_not_dvd p K P (m := 11) hndvd] at hle
  obtain ⟨hp1, hp58⟩ := Finset.mem_Icc.mp hple
  interval_cases p
  all_goals (first
    | (exact absurd rfl h11)
    | (exact absurd rfl h23)
    | (exact absurd hp (by decide))
    | (exact not_pow_orderOf_le 5 (by decide) (by decide) (by decide) (by decide) hle)
    | (exact not_pow_orderOf_le 3 (by decide) (by decide) (by decide) (by decide) hle)
    | (exact not_pow_orderOf_le 1 (by decide) (by decide) (by decide) (by decide) hle))

end Cyclo

end CyclotomicPID
