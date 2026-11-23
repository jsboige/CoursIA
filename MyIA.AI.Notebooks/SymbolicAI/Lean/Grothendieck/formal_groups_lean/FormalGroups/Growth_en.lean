import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# Growth of graded algebras: the counting lemmas

This module formalises the counting lemmas on which the Gelfand–Kirillov
dimension computation of the notebook `GROTH-05b-GelfandKirillov-Python.ipynb`
(issue #27589) rests: the cumulative Hilbert function of a polynomial ring,
its strict growth, the free-algebra word count, and the
submultiplicativity lemma that forces exponential growth for a graded
algebra generated in degree one.

This module **does not define** the Gelfand–Kirillov dimension: Mathlib does
not carry it, and the notebook says so. It does not prove Smoktunowicz's
gap theorem either, nor the `log(dim A_n) / log n` asymptotics. It holds
the counting facts a student can replay, at the exact frontier the
notebook designates:

-  `hilbertCumule d n`: monomials of degree at most `n` in `d` variables,
   `C(n + d, d)`;
-  `hilbertCouche d n`: monomials of degree exactly `n`, `C(n + d - 1, d - 1)`;
-  `motsLibres d n`: words of length at most `n` on `d` letters, `2^(n+1) - 1`
   for `d = 2`;
-  `hilbertCumule_deux_lt_motsLibres_deux`: from rank `2` on, the polynomial
   growth of `k[x, y]` falls under the exponential growth of `k⟨x, y⟩`;
-  `sous_multiplicative_le_pow`: a submultiplicative dimension sequence is
   bounded by the powers of its first term.

The bibliographic references of the context are those of the notebook,
section "References"; this module depends on no publication.
-/

set_option autoImplicit false

namespace FormalGroups_en

/-! ### Hilbert function of a polynomial ring -/

/-- Number of monomials of degree **at most** `n` in `d` indeterminates:
this is `dim A_n` for `A = k[x_1, …, x_d]` graded by total degree. -/
def hilbertCumule (d n : ℕ) : ℕ := (n + d).choose d

/-- Number of monomials of degree **exactly** `n` in `d` indeterminates
(`d ≥ 1`): the layer `A_n / A_{n-1}` of the filtration. -/
def hilbertCouche (d n : ℕ) : ℕ := (n + d - 1).choose (d - 1)

/-- With zero indeterminates there is only one monomial: the constant. -/
@[simp]
theorem hilbertCumule_zero_indet (n : ℕ) : hilbertCumule 0 n = 1 := by
  simp [hilbertCumule]

/-- With one indeterminate, `dim A_n = n + 1`: linear growth. -/
theorem hilbertCumule_one_indet (n : ℕ) : hilbertCumule 1 n = n + 1 := by
  simp [hilbertCumule]

/-- With two indeterminates, `dim A_n = (n+1)(n+2)/2`: quadratic growth,
the value the notebook measures for `k[x,y]`. -/
theorem hilbertCumule_two_indet (n : ℕ) :
    hilbertCumule 2 n = (n + 1) * (n + 2) / 2 := by
  have h : n + 2 - 1 = n + 1 := by omega
  simp only [hilbertCumule]
  rw [Nat.choose_two_right, h, Nat.mul_comm]

/-- The layer of degree `n + 1` completes the cumulative count: this is
Pascal's identity `C(n+1+d, d) = C(n+d, d) + C(n+d, d-1)`. -/
theorem hilbertCumule_succ (d n : ℕ) :
    hilbertCumule (d + 1) (n + 1) =
      hilbertCumule (d + 1) n + hilbertCouche (d + 1) (n + 1) := by
  have h1 : n + 1 + (d + 1) = n + d + 1 + 1 := by omega
  have h2 : n + (d + 1) = n + d + 1 := by omega
  have h3 : n + 1 + (d + 1) - 1 = n + d + 1 := by omega
  have h4 : d + 1 - 1 = d := by omega
  simp only [hilbertCumule, hilbertCouche]
  rw [h3, h4, h1, h2]
  simpa [Nat.add_comm] using Nat.choose_succ_succ' (n + d + 1) d

/-- The cumulative count grows with the degree: `dim A_n ≤ dim A_{n+1}`. -/
theorem hilbertCumule_monotone (d : ℕ) : Monotone (hilbertCumule d) := by
  intro m n hmn
  simp only [hilbertCumule]
  exact Nat.choose_le_choose (a := m + d) (b := n + d) d (by omega)

/-- For `d ≥ 1` every layer is non-empty: the growth is strict. -/
theorem hilbertCumule_lt_succ (d n : ℕ) (hd : 1 ≤ d) :
    hilbertCumule d n < hilbertCumule d (n + 1) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [hilbertCumule_succ]
  have hpos : 0 < hilbertCouche (e + 1) (n + 1) := by
    unfold hilbertCouche
    rw [show n + 1 + (e + 1) - 1 = n + e + 1 by omega,
      show e + 1 - 1 = e by omega]
    exact Nat.choose_pos (by omega)
  omega

/-- With two indeterminates, the layer of degree `n` counts `n + 1`
monomials: `x^n, x^{n-1} y, …, y^n`. -/
theorem hilbertCouche_deux (n : ℕ) : hilbertCouche 2 n = n + 1 := by
  have h : hilbertCouche 2 n = (n + 2 - 1).choose 1 := rfl
  rw [h, Nat.choose_one_right]
  omega

/-- With two indeterminates, Pascal's identity reads
`dim A_{n+1} = dim A_n + (n + 2)`: the polynomial ring grows by adding one
layer. -/
theorem hilbertCumule_deux_succ (n : ℕ) :
    hilbertCumule 2 (n + 1) = hilbertCumule 2 n + (n + 2) := by
  have h : hilbertCumule 2 (n + 1)
      = hilbertCumule 2 n + hilbertCouche 2 (n + 1) :=
    hilbertCumule_succ 1 n
  rw [h, hilbertCouche_deux]

/-- From rank `2` on, the layer of the next rank does not exceed the
cumulative count: `n + 2 ≤ dim A_n` for `A = k[x, y]`. -/
theorem hilbertCumule_deux_ge_add_two (n : ℕ) (hn : 2 ≤ n) :
    n + 2 ≤ hilbertCumule 2 n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h1 : hilbertCumule 2 (m + 2) = hilbertCumule 2 (m + 1) + (m + 3) :=
    hilbertCumule_deux_succ (m + 1)
  have h2 : hilbertCumule 2 (m + 1) = hilbertCumule 2 m + (m + 2) :=
    hilbertCumule_deux_succ m
  omega

/-! ### The free algebra: counting words -/

/-- Number of words of length **at most** `n` on an alphabet of `d`
letters — this is `dim A_n` for the free algebra `k⟨x_1, …, x_d⟩`. The
definition is recursive (`motsLibres d (n+1) = motsLibres d n + d^(n+1)`);
it counts the same thing as the sum of the `d^k` for `k` from `0` to `n`. -/
def motsLibres (d : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => motsLibres d n + d ^ (n + 1)

/-- On two letters, `1 + 2 + … + 2^n = 2^(n+1) - 1`: the value the notebook
measures for the free algebra `k⟨x,y⟩`. -/
theorem motsLibres_deux (n : ℕ) : motsLibres 2 n = 2 ^ (n + 1) - 1 := by
  induction n with
  | zero => simp [motsLibres]
  | succ n ih =>
      simp only [motsLibres]
      rw [ih, show n + 1 + 1 = (n + 1) + 1 by omega, pow_succ]
      have hpos : 0 < 2 ^ (n + 1) := by positivity
      omega

/-- Consequence: the free algebra on two letters has `dim A_n ≥ 2^n`, hence
no polynomial bound — its Gelfand–Kirillov dimension is infinite. -/
theorem motsLibres_deux_ge_pow (n : ℕ) : 2 ^ n ≤ motsLibres 2 n := by
  rw [motsLibres_deux]
  have hpos : 0 < 2 ^ n := by positivity
  rw [pow_succ]
  omega

/-- On two letters, going to the next rank doubles the word count: a non-empty
word of length at most `n + 1` is a letter followed by a word of length at
most `n`, and the empty word must be counted. -/
theorem motsLibres_deux_succ (n : ℕ) :
    motsLibres 2 (n + 1) = 2 * motsLibres 2 n + 1 := by
  have hpos : 0 < 2 ^ (n + 1) := by positivity
  have h : motsLibres 2 n + 1 = 2 ^ (n + 1) := by
    rw [motsLibres_deux]
    omega
  simp only [motsLibres]
  omega

/-! ### Polynomial against exponential -/

/-- **Polynomial against exponential.** From rank `2` on, the cumulative
Hilbert function of `k[x, y]` is strictly smaller than the word count of the
free algebra `k⟨x, y⟩`: polynomial growth never catches up with exponential
growth. The proof compares the two recurrences — the polynomial ring adds a
layer of `n + 2` monomials while the free algebra doubles its count. -/
theorem hilbertCumule_deux_lt_motsLibres_deux (n : ℕ) (hn : 2 ≤ n) :
    hilbertCumule 2 n < motsLibres 2 n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  induction m with
  | zero =>
      rw [hilbertCumule_two_indet, motsLibres_deux]
      norm_num
  | succ m ih =>
      rw [show m + 1 + 2 = m + 2 + 1 by omega]
      rw [hilbertCumule_deux_succ, motsLibres_deux_succ]
      have hle : m + 2 + 2 ≤ hilbertCumule 2 (m + 2) :=
        hilbertCumule_deux_ge_add_two (m + 2) (by omega)
      omega

/-- At ranks `0` and `1` the two counts coincide (the constant, then the empty
word and the two letters): rank `2` in the previous theorem is the first one
where the free algebra overtakes the polynomial ring. -/
theorem hilbertCumule_deux_eq_motsLibres_deux (n : ℕ) (hn : n < 2) :
    hilbertCumule 2 n = motsLibres 2 n := by
  interval_cases n
  · rw [hilbertCumule_two_indet, motsLibres_deux]
    norm_num
  · rw [hilbertCumule_two_indet, motsLibres_deux]
    norm_num

/-! ### Submultiplicativity: exponential growth is unavoidable -/

/-- **Submultiplicativity lemma.** If the dimensions of a graded algebra
satisfy `dim A_{m+n} ≤ dim A_m · dim A_n` — the image of the product
`A_m ⊗ A_n → A_{m+n}` is all of `A_{m+n}` — and `dim A_0 = 1`, then
`dim A_n ≤ (dim A_1)^n`. This is the easy half of the Gelfand–Kirillov
dimension computation: as soon as `dim A_1 ≥ 2`, the growth is at least
exponential. -/
theorem sous_multiplicative_le_pow (a : ℕ → ℕ) (h0 : a 0 = 1)
    (h : ∀ m n : ℕ, a (m + n) ≤ a m * a n) : ∀ n : ℕ, a n ≤ a 1 ^ n
  | 0 => by simp [h0]
  | n + 1 => by
      have hstep : a (n + 1) ≤ a n * a 1 := by
        simpa [Nat.add_comm] using h n 1
      calc a (n + 1) ≤ a n * a 1 := hstep
        _ ≤ a 1 ^ n * a 1 :=
            Nat.mul_le_mul_right _ (sous_multiplicative_le_pow a h0 h n)
        _ = a 1 ^ (n + 1) := by rw [pow_succ]

/-- The free-algebra word count satisfies the hypothesis of the lemma, and
its degree-one dimension is `2`: it is the very example where exponential
growth is forced. -/
theorem motsLibres_sous_multiplicative (m n : ℕ) :
    motsLibres 2 (m + n) ≤ motsLibres 2 m * motsLibres 2 n := by
  rw [motsLibres_deux, motsLibres_deux, motsLibres_deux]
  have h1 : 0 < 2 ^ (m + n + 1) := by positivity
  have h2 : 0 < 2 ^ (m + 1) := by positivity
  have h3 : 0 < 2 ^ (n + 1) := by positivity
  zify [h1, h2, h3]
  rw [show (2 : ℤ) ^ (m + n + 1) = 2 ^ (m + 1) * 2 ^ n by
        rw [show m + n + 1 = (m + 1) + n by omega, pow_add]]
  rw [show (2 : ℤ) ^ (n + 1) = 2 ^ n * 2 by rw [pow_succ]]
  have hA : (2 : ℤ) ≤ 2 ^ (m + 1) := by
    rw [pow_succ]
    have hp : (0 : ℤ) < 2 ^ m := by positivity
    linarith
  have hB : (1 : ℤ) ≤ 2 ^ n := by
    have hp : (0 : ℤ) < 2 ^ n := by positivity
    linarith
  nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 ^ (m + 1) - 2 by linarith)
                      (show (0 : ℤ) ≤ 2 ^ n - 1 by linarith)]

end FormalGroups_en
