import Mathlib.Tactic
import Hecke.HeckeOperator_en

/-!
# Δ, Ramanujan's τ, and the eigen identity `T_p Δ = τ(p) Δ`

This module connects the modular discriminant Δ — the weight-12 cusp
form — with the Hecke operator `T_p` formalized in `HeckeOperator_en.lean`.
It delivers the "q-coefficient of Δ" of grain 5 of the Langlands Epic
(#17969):

* the truncation of the Euler product Δ(q) = q ∏_{m ≥ 1} (1 - qᵐ)²⁴ is
  represented by **convolution of integer coefficient lists** — Mathlib's
  `Mul (Polynomial ℤ)` instance is `noncomputable` at this lake's pin,
  which rules out any `decide`/`#eval` reading through `Polynomial ℤ`;
  list convolution is computable and the kernel reduces it fully;
* `tau n`: Ramanujan's value τ(n), read off the degree-24 truncation
  through a table **verified by the kernel** (`tau_values`): no value is
  hard-coded without proof — the `decide` fails if a single coefficient
  is wrong. Exact for `n ≤ 25`;
* `heckeT_two_isEigen` / `heckeT_three_isEigen`: the discriminant's
  eigen identity `T_p Δ = τ(p) Δ`, verified coefficient by coefficient on
  indices `n ≤ 12` (p = 2) and `n ≤ 8` (p = 3) via the integer reading
  `coeffHeckeT_twelve_int`. The unbounded version requires the theory of
  modular forms (Δ is a normalized eigenform), outside this lake's scope:
  here the kernel checks what the theory predicts.

**Bridges to the notebooks**: τ and the lacunarity of powers of η are
computed in `SymbolicAI/Lean/Serre100/09-congruences-tau-lacunarite-delta.ipynb`;
the modular forms → Hecke → Moonshine path lives in
`SymbolicAI/Lean/Langlands/` (01 and 02). This module is its formal
counterpart: same numbers, kernel-proved.
-/

set_option autoImplicit false

namespace ModularForm_en

/-- Coefficient at index `i` of the product of two polynomials given by
their coefficient lists (convolution). -/
def prodCoeff (as bs : List ℤ) (i : ℕ) : ℤ :=
  (List.range (i + 1)).foldl (fun acc j => acc + as.getD j 0 * bs.getD (i - j) 0) 0

/-- Product of two polynomials, truncated to `N` coefficients. -/
def mulTrunc (N : ℕ) (as bs : List ℤ) : List ℤ :=
  (List.range N).map (prodCoeff as bs)

/-- Coefficients of `(1 - Xᵐ)²⁴` truncated to `N`, read off the binomial:
`C(24, i/m) (-1)^(i/m)` if `m ∣ i` and `i/m ≤ 24`, `0` otherwise. -/
def etaFactor (N m : ℕ) : List ℤ :=
  (List.range N).map (fun i =>
    if m ∣ i ∧ i / m ≤ 24 then
      (Nat.choose 24 (i / m) : ℤ) * (if i / m % 2 = 0 then (1 : ℤ) else (-1 : ℤ))
    else 0)

/-- Coefficients of `∏_{1 ≤ m ≤ K} (1 - Xᵐ)²⁴`, truncated to 26. The
factor `m` does not touch degrees `< m`: the reading is exact at the
indices of interest as soon as `K` is large enough. -/
def etaProd (K : ℕ) : List ℤ :=
  ((List.range (K + 1)).tail).foldl (fun acc m => mulTrunc 26 acc (etaFactor 26 m)) [1]

/-- Coefficients of truncated Δ: `X ∏_{1 ≤ m ≤ 24} (1 - Xᵐ)²⁴`. The
leading shift is the factor `X`; the reading is exact for indices
`≤ 25` (`deltaSeq_stable`). -/
def deltaSeq : List ℤ := 0 :: etaProd 24

/-- Ramanujan's τ: table of the values `τ(0..25)` read off `deltaSeq` and
**verified by the kernel** (`tau_values` below). The lookup returns 0
beyond index 25: the table serves the bounds of this module, not a
general definition of τ. -/
def tau : ℕ → ℤ := fun n =>
  [0, 1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643, -115920,
   534612, -370944, -577738, 401856, 1217160, 987136, -6905934, 2727432,
   10661420, -7109760, -4219488, -12830688, 18643272, 21288960,
   -25499225].getD n 0

set_option maxRecDepth 200000 in
/-- Exactness of the truncation: going from K = 24 to K = 36 factors
changes none of the first 26 coefficients — the added factors start too
high to matter. -/
theorem deltaSeq_stable :
    (0 :: etaProd 24).take 26 = (0 :: etaProd 36).take 26 := by
  decide

set_option maxRecDepth 200000 in
/-- The `tau` table agrees with the Euler product's coefficients up to
index 25: every value is certified by the Lean kernel. -/
theorem tau_values :
    (List.range 26).map tau = deltaSeq.take 26 := by
  decide

/-- The first values of τ, as the kernel reads them off the product:
τ(1) = 1, τ(2) = -24, τ(3) = 252, τ(4) = -1472… -/
theorem tau_first_values :
    (List.range 13).map tau
      = [0, 1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643,
         -115920, 534612, -370944] := by
  decide

/-- A special case of τ's multiplicativity on coprime indices:
τ(6) = τ(2) τ(3) = (-24) ⬝ 252 = -6048. -/
theorem tau_mult_two_three : tau 6 = tau 2 * tau 3 := by decide

/-- Lacunarity stops at the gates of Δ (Serre 1985): τ(25) ≠ 0, unlike
the powers of η he classified as lacunary. -/
theorem tau_lacunarity_stops : tau 25 ≠ 0 := by decide

/-- Integer reading of the Hecke coefficient formula at weight 12:
applying `T_p` to an integer sequence seen in ℂ amounts to the
combinatorial formula `a(np) + p¹¹ a(n/p)` over ℤ. This is the decidable
bridge between the organ `coeffHeckeT` (over ℂ) and bounded integer
verifications. -/
theorem coeffHeckeT_twelve_int (p : ℕ) (a : ℕ → ℤ) (n : ℕ) :
    coeffHeckeT 12 p (fun m => (a m : ℂ)) n
      = ((a (n * p) + if p ∣ n then (p ^ 11 * a (n / p) : ℤ) else 0 : ℤ) : ℂ) := by
  simp only [coeffHeckeT]
  by_cases h : p ∣ n
  · rw [if_pos h, if_pos h]
    have hp : ((p : ℂ) ^ ((12 : ℤ) - 1)) = ((p ^ 11 : ℤ) : ℂ) := by norm_num
    rw [hp]
    push_cast
    ring
  · rw [if_neg h, if_neg h]
    push_cast
    ring

/-- Integer core of the eigen identity at p = 2: the first twelve
coefficients of `T₂ τ` give back `τ(2) τ(n)`. -/
theorem hecke_two_eigen_core :
    ∀ n ∈ Finset.Icc 1 12,
      (tau (n * 2) + if (2 : ℕ) ∣ n then ((2 : ℕ) ^ 11 * tau (n / 2) : ℤ) else 0)
        = tau 2 * tau n := by
  decide

/-- **The discriminant's eigen identity, p = 2**: for every index
`1 ≤ n ≤ 12`, the coefficient formula of `T₂` applied to τ gives back
`τ(2) ⬝ τ(n) = -24 τ(n)`. -/
theorem heckeT_two_isEigen :
    ∀ n ∈ Finset.Icc 1 12,
      coeffHeckeT 12 2 (fun m => (tau m : ℂ)) n = ((-24 : ℤ) : ℂ) * ((tau n : ℤ) : ℂ) := by
  intro n hn
  rw [coeffHeckeT_twelve_int, hecke_two_eigen_core n hn]
  have h2 : tau 2 = -24 := by decide
  rw [h2]
  push_cast
  ring

/-- Integer core of the eigen identity at p = 3 (indices `n ≤ 8`). -/
theorem hecke_three_eigen_core :
    ∀ n ∈ Finset.Icc 1 8,
      (tau (n * 3) + if (3 : ℕ) ∣ n then ((3 : ℕ) ^ 11 * tau (n / 3) : ℤ) else 0)
        = tau 3 * tau n := by
  decide

/-- **The discriminant's eigen identity, p = 3**: for every index
`1 ≤ n ≤ 8`, `T₃ τ` gives back `τ(3) ⬝ τ(n) = 252 τ(n)`. -/
theorem heckeT_three_isEigen :
    ∀ n ∈ Finset.Icc 1 8,
      coeffHeckeT 12 3 (fun m => (tau m : ℂ)) n = ((252 : ℤ) : ℂ) * ((tau n : ℤ) : ℂ) := by
  intro n hn
  rw [coeffHeckeT_twelve_int, hecke_three_eigen_core n hn]
  have h3 : tau 3 = 252 := by decide
  rw [h3]
  push_cast
  ring

end ModularForm_en
