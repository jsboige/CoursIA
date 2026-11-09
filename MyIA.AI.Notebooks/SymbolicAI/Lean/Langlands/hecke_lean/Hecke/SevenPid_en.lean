import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

/-!
# The ring of integers of Q(ζ₇) is a principal ideal domain

This module proves that if `K` is a field such that `IsCyclotomicExtension {7} ℚ K`
(that is, `K = ℚ(ζ₇)`, the 7th cyclotomic field), then its ring of integers
`𝓞 K = ℤ[ζ₇]` is a principal ideal ring.

**Provenance** : this file is the English documentation sibling of
`Hecke/SevenPid.lean`, itself a port from the `anthropics/fermats-last-theorem`
repository (file `P2M/Sol/S_IsCyclotomicExtension_Rat_seven_pid.lean`, commit
`aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`). Statements and proofs are
byte-identical to the French file; only docstrings and comments differ.
The Apache-2.0 license is preserved (see `NOTICE.md`).

## The three-step strategy

Mathlib already provides `IsCyclotomicExtension.Rat.three_pid` and `five_pid`:
for `p = 3` and `p = 5`, the Minkowski bound `M K` stays **below the
discriminant**, and the simple criterion
`RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt` concludes. For `p = 7`,
the discriminant `7^5 = 16807` far exceeds `M K ≈ 4`: the simple criterion no
longer applies.

The proof therefore uses the finer criterion
`RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc`
(Marcus, *Number Fields*, discussion after Theorem 37): `𝓞 K` is principal as
soon as **every prime ideal `P` above a prime `p` with `p ^ f ≤ ⌊M K⌋₊** (where
`f` is the inertia degree) is principal. The steps:

1. `floor_minkowskiBound_seven` / `floor_M_seven` : the integer part of the
   Minkowski bound of `ℚ(ζ₇)` is exactly `4` (20-decimal approximations of `π`
   and an enclosure of `√16807` by `norm_num`);
2. `orderOf_two_zmod_seven`, `orderOf_three_zmod_seven` : the orders of `2`
   and `3` in `(ZMod 7)ˣ`, giving the inertia degrees of the ideals above `2`
   and `3` via `inertiaDeg_eq_of_not_dvd`;
3. `seven_pid` : by `interval_cases`, the only candidates `p ∈ {1, …, 4}` are
   eliminated — `1` is not prime, the inertia degrees above `2` and `3` yield
   `p ^ f > 4`, and `4` is not prime.

The cases `11` and `13` (the result holds for all `p ≤ 19`, but "the proof
is more and more involved") are ported in later installments.
-/

set_option autoImplicit false

namespace CyclotomicPID_en

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers
open NumberField.RingOfIntegers Finset IsCyclotomicExtension.Rat Polynomial
open Real.Polynomial Polynomial.cyclotomic Ideal NumberField.Ideal

open scoped NumberField NumberField.InfinitePlace.NumberField

variable {K : Type*} [Field K] [NumberField K]

local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)

/-- `7` is prime, as a `Fact` instance for Mathlib lemmas. -/
scoped instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The integer part of the explicit Minkowski bound of `ℚ(ζ₇)` is `4`:
`π` is enclosed to 20 decimals (`pi_gt_d20`, `pi_lt_d20`) and `√16807` by `129`
and `130`, then `norm_num` concludes. -/
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

/-- The Minkowski bound `M K` of the 7th cyclotomic field has integer part
`4` : we rewrite `discr K`, `finrank ℚ K` and `nrComplexPlaces K` to their
values (`7^5`, `6`, `3`), then conclude by `floor_minkowskiBound_seven`. -/
theorem floor_M_seven : ⌊(M K)⌋₊ = 4 := by
  rw [discr_prime 7 K, IsCyclotomicExtension.finrank (n := 7) K
    (irreducible_rat (by norm_num)), nrComplexPlaces_eq_totient_div_two 7, totient_prime
      (by norm_num)]
  simp only [Nat.add_one_sub_one, reduceDiv, cast_ofNat, Int.reduceNeg, Int.reducePow,
    reduceSub, neg_mul, one_mul, Int.cast_neg, Int.cast_ofNat, abs_neg, abs_ofNat]
  exact floor_minkowskiBound_seven

/-- The order of `2` in `(ZMod 7)ˣ` is `3` : this is the inertia degree of
the ideals above `2` in `ℚ(ζ₇)`. -/
lemma orderOf_two_zmod_seven : orderOf ((2 : ℕ) : ZMod 7) = 3 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm' ↦ ?_⟩
  interval_cases m <;> decide

/-- The order of `3` in `(ZMod 7)ˣ` is `6` : this is the inertia degree of
the ideals above `3` in `ℚ(ζ₇)`. -/
lemma orderOf_three_zmod_seven : orderOf ((3 : ℕ) : ZMod 7) = 6 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm' ↦ ?_⟩
  interval_cases m <;> decide

variable (K) in
/-- **`ℤ[ζ₇]` is a principal ideal ring.** If `K = ℚ(ζ₇)`, then `𝓞 K` is a
PID: by Marcus' criterion, only the primes `p ∈ {2, 3}` can carry a
non-principal ideal with `p ^ f ≤ 4`, but their inertia degrees (`3` and `6`)
give `2 ^ 3 = 8 > 4` and `3 ^ 6 > 4`. -/
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

end CyclotomicPID_en
