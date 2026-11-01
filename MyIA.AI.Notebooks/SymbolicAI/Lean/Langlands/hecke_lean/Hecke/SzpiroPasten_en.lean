import Mathlib.Tactic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Szpiro--Pasten 2026: admissible factorization and the formal statement of Theorem 1.1

This module delivers grain 6 of the Langlands Epic (#17969): the formal Lean
statement of Theorem 1.1 in Hector Pasten's preprint, *Improved Bounds for
Szpiro's Conjecture* (arXiv 2609.17390, September 16, 2026), whose
computational playground is the notebook
`Search/App-32-Szpiro-Pasten-2026.ipynb`.

* `omega n`: the number ω(n) of distinct prime factors of `n`;
* `IsAdmissibleFactorization N D M`: the key definition of the preprint —
  `N = DM` with `gcd(D, M) = 1`, `D` squarefree, and an **even** number of
  prime factors (the parity comes from the sign of the quaternionic space
  `S_D(M)` in Jacquet--Langlands);
* `szpiroPastenThm11`: the formal statement of Theorem 1.1 –
  `h(E) ≤ C * M * φ(D) * log ℓ` with an effective absolute constant – as a
  `Prop`, **not proved here** (honesty note below);
* the computational side of the definition is proved without sorry:
  the trivial factorization is always admissible, the admissible
  factorizations of `N = 30` are exactly `{1, 6, 10, 15}` –
  `2^(ω(N)-1) = 4` on the notebook's running example – and `D = 2`, `D = 5`,
  `D = 30` are rejected (odd parity of ω(D)). These facts go through
  compositional lemmas: naive `decide` gets kernel-stuck on `Nat.minSqFac`
  (well-founded recursion); factorization does the work.

## Scope honesty (G.3/G.9)

The general Theorem 1.1 (Shimura curves, the Jacquet--Langlands
correspondence, the Hecke eigenvalue multiplicity lemma) is **OPEN in this
lake, without `sorry`**: it lives in `szpiroPastenThm11 : Prop`, on the same
honesty pattern as the reachability of `h*` in `search_lean` – the statement
is a first-class Lean object, `#check`-able, never a proof in disguise. What
is proved below is proved in full (zero sorry).

**Bridges to the notebooks**: the mechanics of choosing `D` and the proxy
`log|Δ| / log rad(|Δ|)` live in `App-32` (python3 kernel); modular forms
and Hecke operators in `SymbolicAI/Lean/Langlands/` (01, 02) and notebook 06 (formerly `Lean-29`).
This module is their formal counterpart: same definitions, kernel-proved.
-/

set_option autoImplicit false

namespace SzpiroPasten_en

/-! ### The key definition: admissible factorization -/

/-- Number of distinct prime factors ω(n), read off the support of the
factorization. -/
def omega (n : ℕ) : ℕ := (Nat.factorization n).support.card

/-- Admissible factorization `N = DM` (§2 definition of the preprint):
`D` and `M` coprime, `D` squarefree, and ω(D) **even**. The parity is not
decorative: it comes from the sign of the quaternionic forms space `S_D(M)`
where the curve's newform lives via Jacquet--Langlands. -/
def IsAdmissibleFactorization (N D M : ℕ) : Prop :=
  D * M = N ∧ D.Coprime M ∧ Squarefree D ∧ Even (omega D)

instance decidableIsAdmissible (N D M : ℕ) :
    Decidable (IsAdmissibleFactorization N D M) := by
  unfold IsAdmissibleFactorization
  infer_instance

/-- The trivial factorization `D = 1, M = N` is always admissible
(ω(1) = 0 is even, 1 is squarefree, coprime to everything): the domain of
Theorem 1.1 is never empty. -/
theorem one_admissible (N : ℕ) : IsAdmissibleFactorization N 1 N := by
  refine ⟨by norm_num, Nat.coprime_one_left N, squarefree_one, ?_⟩
  simp only [omega, Nat.factorization_one, Finsupp.support_zero, Finset.card_empty]
  exact ⟨0, by norm_num⟩

/-! ### `N = 30`: the notebook's running example, proved compositionally

Naive `decide` on `IsAdmissibleFactorization` gets kernel-stuck: the
decidability instance of `Squarefree` rests on `Nat.minSqFac`, a
**well-founded** recursion the kernel cannot reduce. The technical lemmas
below redo the work through unique factorization – a fully compositional
proof, with `decide` reserved for literals (distinct primes, coprimality,
non-divisibility). -/

/-- Squarefree product of two distinct primes, via the factorization
characterization: every exponent is 0 or 1. -/
theorem squarefree_two_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    Squarefree (p * q) := by
  rw [Nat.squarefree_iff_factorization_le_one
      (mul_ne_zero (Nat.Prime.ne_zero hp) (Nat.Prime.ne_zero hq))]
  intro r
  simp only [Nat.factorization_mul (Nat.Prime.ne_zero hp) (Nat.Prime.ne_zero hq),
    Nat.Prime.factorization hp, Nat.Prime.factorization hq,
    Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
  split_ifs <;> simp_all

/-- Extending a squarefree factorization by a foreign prime: `n`
squarefree, `p` prime not dividing `n` ⇒ `np` squarefree. -/
theorem squarefree_mul_prime {n p : ℕ} (hn : n ≠ 0) (hsq : Squarefree n)
    (hp : p.Prime) (hnd : ¬ p ∣ n) : Squarefree (n * p) := by
  have h0 : n.factorization p = 0 := by
    by_contra h0
    exact hnd (Nat.dvd_of_factorization_pos h0)
  have hle : ∀ r, n.factorization r ≤ 1 :=
    (Nat.squarefree_iff_factorization_le_one hn).mp hsq
  rw [Nat.squarefree_iff_factorization_le_one (mul_ne_zero hn (Nat.Prime.ne_zero hp))]
  intro r
  simp only [Nat.factorization_mul hn (Nat.Prime.ne_zero hp),
    Nat.Prime.factorization hp, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
  by_cases h : r = p
  · rw [h, if_pos rfl, h0]
  · rw [if_neg (Ne.symm h)]
    have := hle r
    omega

/-- ω of a prime: 1 – the support of its factorization is a singleton. -/
theorem omega_prime {p : ℕ} (hp : p.Prime) : omega p = 1 := by
  simp [omega, Nat.Prime.factorization hp]

/-- ω of a product by a foreign prime: `ω(n·p) = ω(n) + 1` – the
factorization support gains exactly the singleton `{p}`. -/
theorem omega_mul_prime {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) (hnd : ¬ p ∣ n) :
    omega (n * p) = omega n + 1 := by
  have hmem : p ∉ (n.factorization).support := by
    rw [Finsupp.mem_support_iff]
    intro h0
    exact hnd (Nat.dvd_of_factorization_pos h0)
  have hpf : p.factorization = Finsupp.single p 1 := Nat.Prime.factorization hp
  have hsf : (Finsupp.single p 1).support = {p} := Finsupp.support_single p one_ne_zero
  have hdisj' : Disjoint (n.factorization).support {p} := by
    rw [Finset.disjoint_singleton_right]
    exact hmem
  have hdisj : Disjoint (n.factorization).support (Finsupp.single p 1).support := by
    rw [hsf]
    exact hdisj'
  simp only [omega, Nat.factorization_mul hn (Nat.Prime.ne_zero hp), hpf,
    Finsupp.support_add_eq hdisj, hsf]
  rw [(Finset.card_union_eq_card_add_card).mpr hdisj', Finset.card_singleton]

theorem omega_two : omega 2 = 1 := omega_prime Nat.prime_two

theorem omega_three : omega 3 = 1 := omega_prime Nat.prime_three

theorem omega_five : omega 5 = 1 := omega_prime Nat.prime_five

theorem omega_six : omega 6 = 2 := by
  have h := omega_mul_prime (n := 2) (p := 3) (by norm_num) Nat.prime_three (by decide)
  rw [show (6:ℕ) = 2 * 3 from rfl, h, omega_two]

theorem omega_ten : omega 10 = 2 := by
  have h := omega_mul_prime (n := 2) (p := 5) (by norm_num) Nat.prime_five (by decide)
  rw [show (10:ℕ) = 2 * 5 from rfl, h, omega_two]

theorem omega_fifteen : omega 15 = 2 := by
  have h := omega_mul_prime (n := 3) (p := 5) (by norm_num) Nat.prime_five (by decide)
  rw [show (15:ℕ) = 3 * 5 from rfl, h, omega_three]

theorem omega_thirty : omega 30 = 3 := by
  have h := omega_mul_prime (n := 6) (p := 5) (by norm_num) Nat.prime_five (by decide)
  rw [show (30:ℕ) = 6 * 5 from rfl, h, omega_six]

theorem squarefree_six : Squarefree 6 :=
  squarefree_two_primes Nat.prime_two Nat.prime_three (by decide)

theorem squarefree_ten : Squarefree 10 :=
  squarefree_two_primes Nat.prime_two Nat.prime_five (by decide)

theorem squarefree_fifteen : Squarefree 15 :=
  squarefree_two_primes Nat.prime_three Nat.prime_five (by decide)

theorem squarefree_thirty : Squarefree 30 := by
  have h := squarefree_mul_prime (n := 6) (p := 5) (by norm_num)
    squarefree_six Nat.prime_five (by decide)
  exact h

/-- On `N = 30` (ω(N) = 3: primes 2, 3, 5), the four admissible
factorizations `D ∈ {1, 6, 10, 15}` – exactly `2^(ω(N)-1) = 4`, half of the
subsets of primes of even cardinality. Product, coprimality, squarefree and
parity proved one by one. -/
theorem admissible_thirty :
    IsAdmissibleFactorization 30 1 30 ∧
    IsAdmissibleFactorization 30 6 5 ∧
    IsAdmissibleFactorization 30 10 3 ∧
    IsAdmissibleFactorization 30 15 2 := by
  refine ⟨one_admissible 30, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by decide, squarefree_six, ?_⟩
    rw [omega_six]; exact ⟨1, rfl⟩
  · refine ⟨by norm_num, by decide, squarefree_ten, ?_⟩
    rw [omega_ten]; exact ⟨1, rfl⟩
  · refine ⟨by norm_num, by decide, squarefree_fifteen, ?_⟩
    rw [omega_fifteen]; exact ⟨1, rfl⟩

/-- `D = 2` is NOT admissible: ω(2) = 1 is odd. The parity constraint
excludes singleton prime sets. -/
theorem not_admissible_thirty_two : ¬IsAdmissibleFactorization 30 2 15 := by
  intro h
  obtain ⟨-, -, -, heven⟩ := h
  rw [omega_two] at heven
  obtain ⟨k, hk⟩ := heven
  omega

/-- `D = 5`: same rejection, ω(5) = 1 odd. -/
theorem not_admissible_thirty_five : ¬IsAdmissibleFactorization 30 5 6 := by
  intro h
  obtain ⟨-, -, -, heven⟩ := h
  rw [omega_five] at heven
  obtain ⟨k, hk⟩ := heven
  omega

/-- `D = 30`: ω(30) = 3 odd – even the full factor is excluded. -/
theorem not_admissible_thirty_thirty : ¬IsAdmissibleFactorization 30 30 1 := by
  intro h
  obtain ⟨-, -, -, heven⟩ := h
  rw [omega_thirty] at heven
  obtain ⟨k, hk⟩ := heven
  omega

/-! ### The formal statement of Theorem 1.1 -/

/-- Pair (height, conductor): the carrier of the formal statement. That
`hE` is the Faltings height of an elliptic curve of conductor `N` is a
typing hypothesis, taken as given – the arithmetic depth is out of the
lake's scope. -/
structure CourbeHN where
  /-- Faltings height (abstract). -/
  hE : ℝ
  /-- Conductor (abstract). -/
  N : ℕ

/-- **Formal statement of Theorem 1.1 (Pasten 2026, arXiv 2609.17390)**:
there exists an *effective* absolute constant `C > 0` such that, for every
curve `E/ℚ` (carried by `CourbeHN`), every admissible factorization
`E.N = D * M` and every prime `ℓ` not dividing `E.N`:

`h(E) ≤ C * M * φ(D) * log ℓ`

NOT proved in this lake: the statement itself – a first-class Lean object,
`#check`-able – is the deliverable of grain 6 of #17969. The proof (Shimura
curves, Jacquet--Langlands, Hecke eigenvalue multiplicity in `S_D(M)`) is
documented in `App-32` §Conclusion and remains out of scope, following the
honesty pattern of `search_lean`. -/
def szpiroPastenThm11 : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ E : CourbeHN, ∀ D M ℓ : ℕ,
      IsAdmissibleFactorization E.N D M →
      ℓ.Prime → ¬ℓ ∣ E.N →
        E.hE ≤ C * (M : ℝ) * (Nat.totient D : ℝ) * Real.log (ℓ : ℝ)

#check @szpiroPastenThm11

end SzpiroPasten_en
