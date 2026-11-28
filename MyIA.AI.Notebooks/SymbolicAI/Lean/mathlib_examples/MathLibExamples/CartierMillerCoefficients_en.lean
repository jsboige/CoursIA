import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import MathLibExamples.CartierMiller_en

/-!
# The binomial coefficients of the quarter point

The `CartierMiller` module proves the telescoping certificate, the prefix identity and
the quarter-point identity **under** a local recurrence taken as a hypothesis. On
`main`, that recurrence is discharged only by `decide`, over the twenty-four relevant
indices at `p = 97`, and the `j = 1728` base is built without the sequence being
attached to it. This module builds the sequence itself — `a_i = C(2i,i)·8⁻ⁱ`,
equation (32) of the manuscript — and proves its recurrence **at every index, in every
field where `8 ≠ 0`**. Equations (34), (35) and (36) then follow for this explicit
sequence: (36) therefore holds in `ZMod p` for every prime `p ≡ 1 (mod 4)`, not only at
`p = 97`.

Established here: the recurrence, the certificate, the prefix identity and the
quarter-point identity for the binomial sequence, first in an arbitrary field, then in
`ZMod p`.

Not established here, and not to be read into these statements: the identification of
`U_p` with the coefficient sum of the Cartier–Miller evaluation, the equality of `a_n`
with the Frobenius trace of the curve of invariant `j = 1728`, and any statement about
elliptic curves. Those attachments are the next step of the plan of issue #19452.

The source manuscript is an *unrefereed draft* with AI assistance, pinned at `37a9b72`;
the statements quoted here are transcribed from the repository's transcriptions, and
the numeric oracle (`scripts/cartier_miller/verify_quarter_point_identities.py`) is an
execution corroboration, never a proof.
-/

namespace CartierMillerCoefficients_en

open Finset

variable {F : Type*} [Field F]

/-! ### The integer identities on the central coefficients -/

/-- Central identity: `(i+1)·C(2i+1,i) = (2i+1)·C(2i,i)`, the direct form of
`Nat.choose_mul_succ_eq` at arguments `(2i, i)`. -/
theorem succ_mul_central_choose (i : ℕ) :
    (i + 1) * Nat.choose (2 * i + 1) i = (2 * i + 1) * Nat.choose (2 * i) i := by
  have h := Nat.choose_mul_succ_eq (2 * i) i
  rw [show 2 * i + 1 - i = i + 1 from by omega] at h
  rw [mul_comm (i + 1) (Nat.choose (2 * i + 1) i),
    mul_comm (2 * i + 1) (Nat.choose (2 * i) i)]
  exact h.symm

/-- Doubled Pascal: `C(2i+2,i+1) = 2·C(2i+1,i)`, by symmetry of the central
coefficient. -/
theorem central_choose_succ (i : ℕ) :
    Nat.choose (2 * i + 2) (i + 1) = 2 * Nat.choose (2 * i + 1) i := by
  have hsymm : Nat.choose (2 * i + 1) (i + 1) = Nat.choose (2 * i + 1) i := by
    have h := Nat.choose_symm (n := 2 * i + 1) (k := i + 1) (by omega)
    rw [show 2 * i + 1 - (i + 1) = i from by omega] at h
    exact h.symm
  rw [show 2 * i + 2 = 2 * i + 1 + 1 from by omega, Nat.choose_succ_succ', hsymm]
  ring

/-- The integer step, without division: `4(i+1)·C(2i+2,i+1) = 8(2i+1)·C(2i,i)`. This
is the integer skeleton of recurrence (32) of the sequence `aᵢ`. -/
theorem central_binomial_step (i : ℕ) :
    4 * (i + 1) * Nat.choose (2 * (i + 1)) (i + 1) =
      8 * (2 * i + 1) * Nat.choose (2 * i) i := by
  have h2 : 2 * (i + 1) = 2 * i + 2 := by omega
  rw [h2, central_choose_succ]
  have hstep := succ_mul_central_choose i
  linear_combination 8 * hstep

/-! ### The sequence `aᵢ = C(2i,i)·8⁻ⁱ` and its recurrence -/

/-- The sequence of equation (32), in an arbitrary field: `a_i = C(2i,i)·8⁻ⁱ`,
written as a power of the inverse. -/
noncomputable def binomialSeq (i : ℕ) : F := (Nat.choose (2 * i) i : F) * 8⁻¹ ^ i

/-- The definition in the manuscript's shape: `a_i = C(2i,i) / 8ⁱ`. -/
theorem binomialSeq_eq_division (i : ℕ) :
    binomialSeq (F := F) i = (Nat.choose (2 * i) i : F) / 8 ^ i := by
  simp only [binomialSeq]
  rw [div_eq_mul_inv, ← inv_pow]

/-- The first term, `a_0 = 1`, mirroring `t_0 = 1` in (32). -/
theorem binomialSeq_zero : binomialSeq (F := F) 0 = 1 := by
  simp [binomialSeq]

/-- The local recurrence (32) of the binomial sequence, at **every** index, as soon as
`8` is invertible: `4(i+1)·a_{i+1} = (2i+1)·a_i`. -/
theorem binomialSeq_recurrence (i : ℕ) (h8 : (8 : F) ≠ 0) :
    4 * ((i : F) + 1) * binomialSeq (F := F) (i + 1) =
      (2 * (i : F) + 1) * binomialSeq (F := F) i := by
  have hnat : ((4 * (i + 1) * Nat.choose (2 * (i + 1)) (i + 1) : ℕ) : F) =
      ((8 * (2 * i + 1) * Nat.choose (2 * i) i : ℕ) : F) := by
    rw [central_binomial_step i]
  push_cast at hnat
  have hinv : (8 : F) * 8⁻¹ = 1 := mul_inv_cancel₀ h8
  simp only [binomialSeq, pow_succ]
  linear_combination (8⁻¹ ^ i * 8⁻¹) * hnat +
    ((2 * (i : F) + 1) * (Nat.choose (2 * i) i : F) * 8⁻¹ ^ i) * hinv

/-! ### The three equations of the manuscript, for the explicit sequence -/

/-- (34): the telescoping certificate, for the binomial sequence and at every index. -/
theorem binomialSeq_certificate (i : ℕ) (h8 : (8 : F) ≠ 0) :
    ((2 * (i : F) + 1) ^ 2 - 8) * binomialSeq (F := F) i =
      -4 * ((i : F) + 1) * (2 * (i : F) + 7) * binomialSeq (F := F) (i + 1) +
        4 * (i : F) * (2 * (i : F) + 5) * binomialSeq (F := F) i :=
  CartierMiller_en.telescoping_certificate (binomialSeq i) (binomialSeq (i + 1)) (i : F)
    (binomialSeq_recurrence i h8)

/-- (35): the prefix identity, for the binomial sequence and at every prefix. -/
theorem binomialSeq_prefix (h : F) (L : ℕ) (h8 : (8 : F) ≠ 0) (half : 2 * h + 1 = 0) :
    (∑ i ∈ range L, (h + 1 + (i : F)) * ((2 * (i : F) + 1) * binomialSeq (F := F) i)) =
      4 * (∑ i ∈ range L, binomialSeq (F := F) i) -
        2 * (L : F) * (2 * (L : F) + 5) * binomialSeq (F := F) L :=
  CartierMiller_en.prefix_sum_identity binomialSeq h L half
    (fun i _ => binomialSeq_recurrence i h8)

/-- (36): the quarter-point identity, for the binomial sequence, in any field. -/
theorem binomialSeq_quarter_point (h : F) (n : ℕ) (h8 : (8 : F) ≠ 0)
    (half : 2 * h + 1 = 0) (quarter : 4 * (n : F) + 1 = 0) (four_ne : (4 : F) ≠ 0) :
    (∑ i ∈ range n, (h + 1 + (i : F)) * ((2 * (i : F) + 1) * binomialSeq (F := F) i)) =
      4 * (∑ i ∈ range n, binomialSeq (F := F) i) + (9 / 4 : F) * binomialSeq (F := F) n :=
  CartierMiller_en.quarter_point_identity binomialSeq h n half
    (fun i _ => binomialSeq_recurrence i h8) quarter four_ne

/-! ### Modulo a prime: `2`, `4` and `8` are invertible -/

/-- An odd prime divides no power of two. -/
theorem prime_odd_not_dvd_pow_two {p k : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    ¬ p ∣ 2 ^ k := by
  intro h
  have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h
  rw [Nat.dvd_prime Nat.prime_two] at h2
  rcases h2 with h1 | h2
  · exact hp.ne_one h1
  · exact hp2 h2

/-- A power of two is nonzero modulo an odd prime. -/
theorem pow_two_ne_zero_zmod (p k : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    ((2 ^ k : ℕ) : ZMod p) ≠ 0 :=
  fun h => prime_odd_not_dvd_pow_two hp hp2 ((ZMod.natCast_eq_zero_iff (2 ^ k) p).mp h)

/-- `2` is invertible modulo an odd prime. -/
theorem two_ne_zero_zmod (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  have h := pow_two_ne_zero_zmod p 1 hp hp2
  simpa using h

/-- `4` is invertible modulo an odd prime. -/
theorem four_ne_zero_zmod (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) : (4 : ZMod p) ≠ 0 := by
  have h := pow_two_ne_zero_zmod p 2 hp hp2
  simpa using h

/-- `8` is invertible modulo an odd prime. -/
theorem eight_ne_zero_zmod (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) : (8 : ZMod p) ≠ 0 := by
  have h := pow_two_ne_zero_zmod p 3 hp hp2
  simpa using h

/-- The hypothesis `2h + 1 = 0` at the quarter point: `h = (p-1)/2`. -/
theorem half_zmod (p : ℕ) (hp4 : p % 4 = 1) :
    (2 : ZMod p) * (((p - 1) / 2 : ℕ) : ZMod p) + 1 = 0 := by
  have h : 2 * ((p - 1) / 2) + 1 = p := by omega
  have hc := congrArg (fun n : ℕ => (n : ZMod p)) h
  push_cast at hc
  rw [ZMod.natCast_self] at hc
  exact hc

/-- The quarter-point hypothesis: `4n + 1 = 0` for `n = (p-1)/4`. -/
theorem quarter_zmod (p : ℕ) (hp4 : p % 4 = 1) :
    (4 : ZMod p) * (((p - 1) / 4 : ℕ) : ZMod p) + 1 = 0 := by
  have h : 4 * ((p - 1) / 4) + 1 = p := by omega
  have hc := congrArg (fun n : ℕ => (n : ZMod p)) h
  push_cast at hc
  rw [ZMod.natCast_self] at hc
  exact hc

/-- (36) in `ZMod p`: the quarter-point congruence for the binomial sequence, for every
prime `p ≡ 1 (mod 4)`. The manuscript states it under `p = 4n + 1 ≥ 13`; the algebraic
computation uses neither the bound `≥ 13` nor primality beyond the invertibility of `2`,
`4` and `8`. -/
theorem quarter_point_congruence (p : ℕ) [Fact (Nat.Prime p)] (hp4 : p % 4 = 1) :
    (∑ i ∈ range ((p - 1) / 4),
        ((((p - 1) / 2 : ℕ) : ZMod p) + 1 + (i : ZMod p)) *
          ((2 * (i : ZMod p) + 1) * binomialSeq (F := ZMod p) i)) =
      4 * (∑ i ∈ range ((p - 1) / 4), binomialSeq (F := ZMod p) i) +
        (9 / 4 : ZMod p) * binomialSeq (F := ZMod p) ((p - 1) / 4) := by
  have hp : Nat.Prime p := Fact.out
  have hp2 : p ≠ 2 := by
    intro h
    rw [h] at hp4
    norm_num at hp4
  exact binomialSeq_quarter_point (F := ZMod p) (((p - 1) / 2 : ℕ) : ZMod p) ((p - 1) / 4)
    (eight_ne_zero_zmod p hp hp2) (half_zmod p hp4) (quarter_zmod p hp4)
    (four_ne_zero_zmod p hp hp2)

/-- At `p = 97`, the general sequence coincides with the repository's oracle: the value
verified by `decide` on `main` becomes an instance of a theorem. -/
theorem binomialSeq_eq_oracle97 (i : ℕ) :
    binomialSeq (F := ZMod 97) i = CartierMiller_en.oracle97 i := by
  rw [binomialSeq_eq_division, CartierMiller_en.oracle97_binomial]

/-- The manuscript's worked example (`p = 97`, `n = 24`) as an instance of the general
congruence. -/
theorem quarter_point_congruence_97 :
    (∑ i ∈ range 24, (48 + 1 + (i : ZMod 97)) *
        ((2 * (i : ZMod 97) + 1) * binomialSeq (F := ZMod 97) i)) =
      4 * (∑ i ∈ range 24, binomialSeq (F := ZMod 97) i) +
        (9 / 4 : ZMod 97) * binomialSeq (F := ZMod 97) 24 := by
  have h := quarter_point_congruence 97 (by decide)
  simpa using h

end CartierMillerCoefficients_en
