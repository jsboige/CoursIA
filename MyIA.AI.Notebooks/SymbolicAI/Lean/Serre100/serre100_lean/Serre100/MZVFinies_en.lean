import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Finite multiple zeta values: stuffle and reversal, proved by the kernel

Kernel counterpart of the notebook `02-valeurs-zeta-multiples-finies.ipynb`
(*Serre 100* series, EPIC #16334 — "kernel counterparts" graduation track).
The notebook *measures* the identities of the poor man's adèle ring in
Python; this module *proves* them in `𝔽_p`, for every prime `p`.

Outline, mirroring the notebook:

1. **Definitions** (`ombreZeta`, `ombreZeta2`) — the generalized harmonic
   sums truncated at `p - 1`: depth 1 `ζ_p(s) = ∑ k⁻ˢ` and depth 2
   `ζ_p(m,n) = ∑_{k₂<k₁} k₁⁻ᵐ k₂⁻ⁿ` (notebook, `zeta_p`, `zeta_p2`).
2. **Kernel verifications**: the spectrum `p = 13` (zero everywhere except
   `s = p - 1`), stuffle and reversal on **all** exponent pairs of `𝔽_7`,
   and the odd-weight survivors `ζ₁₃(2,1) = 5`, `ζ₁₃(3,2) = 7` — cell (c)
   of the notebook, but proved.
3. **The silent shadow**: `ζ_p(s) = 0` for `1 ≤ s ≤ p - 2` and
   `ζ_p(p-1) = -1` — the "three-line" cyclic group theorem, proved here
   by the permutation argument of the notebook.
4. **Stuffle**: `ζ_p(m)·ζ_p(n) = ζ_p(m,n) + ζ_p(n,m) + ζ_p(m+n)` — the
   partition of the square into three regions (`a > b`, `b > a`, `a = b`),
   exactly the table in the notebook's reading.
5. **Reversal**: `ζ_p(m,n) = (-1)^(m+n)·ζ_p(n,m)` — the involution
   `(k₁,k₂) ↦ (p-k₁, p-k₂)`.
6. **Differentiation**: when `m + n ≤ p - 2` is **even** (and `p ≠ 2`),
   `ζ_p(m,n) = 0` — silence + stuffle + reversal: even weights die,
   odd ones survive.

Two technical remarks. First, the modular inverse `ZMod.inv` lives in
well-founded recursion: the kernel cannot reduce it, and `decide` fails
on the definitions. The Fermat bridge `k⁻ˢ = k^(p-1-s)` (lemma
`inv_pow_eq_pow`) commutes each shadow to a sum of ordinary powers,
which is computable — this is what makes the §2 verifications possible.
Second, the `p²` layer (Wolstenholme, Leudesdorf, Bernoulli bridge)
stays on the notebook side: it lives in `ℤ/p²`, where inversion is no
longer a field; this is the natural boundary of this module.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Serre100_en

open Finset

variable (p : ℕ) [Fact p.Prime]

/-! ## Definitions — the notebook's vocabulary, in Lean

The depth-one shadow is the generalized harmonic sum truncated at
`p - 1` — the size of the field *is* the summation height. The inverse
`k⁻ˢ` is read in the field `𝔽_p` (every nonzero `k` is invertible
there); this is why the definitions carry `[Fact p.Prime]` from the
start, unlike the `HasseComputee` module where only counting was needed.
-/

/-- Depth-one shadow: `ζ_p(s) = ∑_{k=1}^{p-1} k⁻ˢ` in `𝔽_p`
(notebook, `zeta_p`, layer `N = 1`). -/
def ombreZeta (s : ℕ) : ZMod p :=
  ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹ ^ s)

/-- Depth-two shadow: `ζ_p(m,n) = ∑_{0 < k₂ < k₁ < p} k₁⁻ᵐ k₂⁻ⁿ`
(notebook, `zeta_p2`). -/
def ombreZeta2 (m n : ℕ) : ZMod p :=
  ∑ k1 ∈ Finset.Icc 1 (p - 1), ∑ k2 ∈ Finset.Ico 1 k1,
    ((k1 : ZMod p)⁻¹ ^ m * (k2 : ZMod p)⁻¹ ^ n)

/-- The notebook's summation range: the integers from `1` to `p - 1`. -/
private abbrev plage (p : ℕ) : Finset ℕ :=
  Finset.Icc 1 (p - 1)

private theorem mem_plage {p k : ℕ} : k ∈ plage p ↔ 1 ≤ k ∧ k ≤ p - 1 :=
  Finset.mem_Icc

/-- The ordered pairs of the range: the filter `k₂ < k₁` on the square
`{1..p-1}²`. This is the form in which the §4 partitions read off. -/
private abbrev pairesOrdonnees (p : ℕ) : Finset (ℕ × ℕ) :=
  (plage p ×ˢ plage p).filter (fun ij => ij.2 < ij.1)

/-- An integer from `1` to `p - 1` is nonzero in `𝔽_p`. -/
private theorem cast_ne_zero_of_mem_plage {p : ℕ} [Fact p.Prime] {k : ℕ}
    (hk : k ∈ plage p) : ((k : ℕ) : ZMod p) ≠ 0 := by
  obtain ⟨hk1, hk2⟩ := mem_plage.1 hk
  intro h0
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  have hv : ((k : ℕ) : ZMod p).val = k := ZMod.val_cast_of_lt (by omega)
  rw [h0, ZMod.val_zero] at hv
  omega

/-- Fermat carries the inverse to a power: `k⁻ˢ = k^(p-1-s)` for
`s ≤ p - 1` — the notebook's bridge `t = p - 1 - s`. This is also what
makes the numerical verifications possible: the modular inverse blocks
kernel reduction (`ZMod.inv` lives in well-founded recursion), the
ordinary exponent does not. -/
private theorem inv_pow_eq_pow {p : ℕ} [Fact p.Prime] {k s : ℕ}
    (hk : k ∈ plage p) (hs : s ≤ p - 1) :
    ((k : ZMod p)⁻¹ ^ s) = ((k : ZMod p) ^ (p - 1 - s)) := by
  have hx : ((k : ℕ) : ZMod p) ≠ 0 := cast_ne_zero_of_mem_plage hk
  have hfermat : ((k : ℕ) : ZMod p) ^ (p - 1) = 1 :=
    ZMod.pow_card_sub_one_eq_one hx
  have h1 : (((k : ℕ) : ZMod p)⁻¹ ^ s) * (((k : ℕ) : ZMod p) ^ s) = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hx, one_pow]
  have h2 : (((k : ℕ) : ZMod p) ^ (p - 1 - s)) * (((k : ℕ) : ZMod p) ^ s) = 1 := by
    rw [← pow_add, Nat.sub_add_cancel hs, hfermat]
  exact mul_right_cancel₀ (pow_ne_zero s hx) (h1.trans h2.symm)

/-! ## Kernel verifications — the notebook's tables, proved

The notebook observes (cells "Mesure", "Le produit STUFFLE",
"RETOURNEMENT"); the kernel here proves the same values, exactly, and
sweeps all of `𝔽_7` rather than sampling.
-/

section Verifications

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

/-- The "powers" form of the shadow, decide-able. -/
private theorem ombreZeta_eq_pow {p : ℕ} [Fact p.Prime] {s : ℕ}
    (hs : s ≤ p - 1) :
    ombreZeta p s = ∑ k ∈ plage p, ((k : ZMod p) ^ (p - 1 - s)) :=
  Finset.sum_congr rfl fun _ hk => inv_pow_eq_pow hk hs

/-- Same commutation for depth 2. -/
private theorem ombreZeta2_eq_pow {p : ℕ} [Fact p.Prime] {m n : ℕ}
    (hm : m ≤ p - 1) (hn : n ≤ p - 1) :
    ombreZeta2 p m n = ∑ k1 ∈ plage p, ∑ k2 ∈ Finset.Ico 1 k1,
      ((k1 : ZMod p) ^ (p - 1 - m) * (k2 : ZMod p) ^ (p - 1 - n)) := by
  refine Finset.sum_congr rfl fun k1 hk1 => ?_
  refine Finset.sum_congr rfl fun k2 hk2 => ?_
  obtain ⟨hk11, hk12⟩ := mem_plage.1 hk1
  obtain ⟨hk21, hk22⟩ := (Finset.mem_Ico.1 hk2)
  rw [inv_pow_eq_pow hk1 hm,
    inv_pow_eq_pow (mem_plage.2 ⟨hk21, by omega⟩) hn]

/-- The complete spectrum of `p = 13` (notebook, cell "Mesure"): zero
everywhere for `1 ≤ s ≤ p - 2`. -/
example : ∀ s ∈ Finset.Icc 1 11, ombreZeta 13 s = 0 := by
  intro s hs
  obtain ⟨hs1, hs2⟩ := Finset.mem_Icc.1 hs
  rw [ombreZeta_eq_pow (by omega)]
  interval_cases s
  all_goals decide

/-- The single exception of the spectrum: `ζ_p(p-1) = p - 1 = -1`
(notebook, "Bord s = p-1"). -/
example : ombreZeta 13 12 = 12 := by
  rw [ombreZeta_eq_pow (by omega)]
  decide

/-- Stuffle on **all** pairs `(m, n)` of exponents of `𝔽_7` with
`m + n ≤ p - 1` — the notebook's "112/112", but exhaustive over the
`4 × 4` square. -/
example : ∀ m ∈ Finset.range 4, ∀ n ∈ Finset.range 4,
    ombreZeta 7 m * ombreZeta 7 n
      = ombreZeta2 7 m n + ombreZeta2 7 n m + ombreZeta 7 (m + n) := by
  intro m hm n hn
  have hm2 : m < 4 := Finset.mem_range.1 hm
  have hn2 : n < 4 := Finset.mem_range.1 hn
  rw [ombreZeta_eq_pow (by omega), ombreZeta_eq_pow (by omega),
    ombreZeta2_eq_pow (by omega) (by omega),
    ombreZeta2_eq_pow (by omega) (by omega),
    ombreZeta_eq_pow (by omega)]
  interval_cases m
  all_goals interval_cases n
  all_goals decide

/-- Reversal on **all** pairs of `𝔽_7`. -/
example : ∀ m ∈ Finset.range 4, ∀ n ∈ Finset.range 4,
    ombreZeta2 7 m n = (-1 : ZMod 7) ^ (m + n) * ombreZeta2 7 n m := by
  intro m hm n hn
  have hm2 : m < 4 := Finset.mem_range.1 hm
  have hn2 : n < 4 := Finset.mem_range.1 hn
  rw [ombreZeta2_eq_pow (by omega) (by omega),
    ombreZeta2_eq_pow (by omega) (by omega)]
  interval_cases m
  all_goals interval_cases n
  all_goals decide

/-- The odd-weight survivors (notebook, cell (c)): `ζ₁₃(2,1) = 5` —
nonzero, the information lives here. -/
example : ombreZeta2 13 2 1 = 5 := by
  rw [ombreZeta2_eq_pow (by omega) (by omega)]
  decide

/-- Second survivor of cell (c): `ζ₁₃(3,2) = 7`. -/
example : ombreZeta2 13 3 2 = 7 := by
  rw [ombreZeta2_eq_pow (by omega) (by omega)]
  decide

end Verifications

/-! ## The silent shadow — the cyclic group erases everything

The notebook's proof: take `b` nonzero with `bˢ ≠ 1` (one exists as
soon as `1 ≤ s ≤ p - 2`, because `𝔽_pˣ` is cyclic of order `p - 1`);
multiplication by `b` permutes the nonzeros, so `ζ = b⁻ˢ·ζ`, and since
`b⁻ˢ ≠ 1`, `ζ = 0`. This is the proof of Mathlib's
`sum_subgroup_pow_eq_zero`, replicated on the `Finset` of nonzeros to
stay in the notebook's vocabulary.
-/

section OmbreMuette

/-- Transporting the range to the nonzeros: summing `f` over the
integers from `1` to `p - 1` is summing over the nonzeros of `𝔽_p` —
the notebook's range IS the group `𝔽_pˣ`, seen through its
representatives. -/
private theorem somme_plage_eq_somme_nonNuls {p : ℕ} [Fact p.Prime]
    (f : ZMod p → ZMod p) :
    ∑ k ∈ plage p, f ((k : ℕ) : ZMod p)
      = ∑ x ∈ Finset.univ.filter (fun x : ZMod p => x ≠ 0), f x := by
  letI : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
  have hinj : ∀ k ∈ plage p, ∀ k' ∈ plage p,
      ((k : ℕ) : ZMod p) = ((k' : ℕ) : ZMod p) → k = k' := by
    intro k hk k' hk' h
    obtain ⟨hk1, hk2⟩ := mem_plage.1 hk
    obtain ⟨hk1', hk2'⟩ := mem_plage.1 hk'
    have h1 : ((k : ℕ) : ZMod p).val = k := ZMod.val_cast_of_lt (by omega)
    have h2 : ((k' : ℕ) : ZMod p).val = k' := ZMod.val_cast_of_lt (by omega)
    exact h1.symm.trans ((congrArg ZMod.val h).trans h2)
  have himg : (plage p).image (fun k : ℕ => ((k : ℕ) : ZMod p))
      = Finset.univ.filter (fun x : ZMod p => x ≠ 0) := by
    ext x
    simp only [mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact cast_ne_zero_of_mem_plage hk
    · intro hx
      refine ⟨x.val, ?_, ?_⟩
      · have hv0 : x.val ≠ 0 := fun h0 => hx ((ZMod.val_eq_zero x).1 h0)
        have hvlt : x.val < p := ZMod.val_lt x
        exact mem_plage.2 ⟨by omega, by omega⟩
      · exact ZMod.natCast_zmod_val x
  rw [← himg, Finset.sum_image hinj]

/-- **The silent shadow**: `ζ_p(s) = 0` for `1 ≤ s ≤ p - 2` — the
layer `p` carries no information, neither for even nor odd weights
(notebook, section 1). -/
theorem ombreZeta_eq_zero {p : ℕ} [Fact p.Prime] {s : ℕ}
    (hs : 0 < s) (hs2 : s < p - 1) : ombreZeta p s = 0 := by
  -- The pivot: b nonzero with b^s ≠ 1 (𝔽_pˣ cyclic of order p - 1).
  have hcard : Fintype.card ((ZMod p)ˣ) = p - 1 := ZMod.card_units p
  obtain ⟨u, hu⟩ := exists_pow_ne_one_of_isCyclic (G := (ZMod p)ˣ) hs.ne' (by
    have hnc : Nat.card ((ZMod p)ˣ) = p - 1 := by
      rw [Nat.card_eq_fintype_card, hcard]
    omega)
  set b : ZMod p := ((u : (ZMod p)ˣ) : ZMod p) with hb
  have hb0 : b ≠ 0 := Units.ne_zero u
  have hbs : b ^ s ≠ 1 := by
    intro h1
    refine hu (Units.ext ?_)
    rw [Units.val_pow_eq_pow_val, ← hb]
    exact h1
  -- Multiplication by b permutes the nonzeros of 𝔽_p.
  have hperm : (Finset.univ.filter (fun x : ZMod p => x ≠ 0)).image
      (fun x : ZMod p => b * x)
      = Finset.univ.filter (fun x : ZMod p => x ≠ 0) := by
    ext y
    simp only [mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact mul_ne_zero hb0 hx
    · intro hy
      exact ⟨b⁻¹ * y, mul_ne_zero (inv_ne_zero hb0) hy,
        mul_inv_cancel_left₀ hb0 y⟩
  -- The change of variable: ζ = b⁻ˢ · ζ, hence (1 - b⁻ˢ)·ζ = 0.
  have hc : (b⁻¹ ^ s) ≠ 1 := by
    rw [inv_pow]
    exact fun h1 => hbs (inv_eq_one.mp h1)
  set S : ZMod p :=
    ∑ x ∈ Finset.univ.filter (fun x : ZMod p => x ≠ 0), (x⁻¹ ^ s) with hS
  -- S = sum of the images under x ↦ b·x (the permutation), then factor b⁻ˢ.
  have hsum_perm : S = ∑ x ∈ Finset.univ.filter (fun x : ZMod p => x ≠ 0),
      ((b * x)⁻¹ ^ s) := by
    rw [hS]
    conv_lhs => rw [← hperm]
    exact Finset.sum_image (fun k hk k' hk' h => mul_left_cancel₀ hb0 h)
  have hsplit : ∑ x ∈ Finset.univ.filter (fun x : ZMod p => x ≠ 0),
      ((b * x)⁻¹ ^ s)
      = (b⁻¹ ^ s) * S := by
    rw [hS, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← mul_pow, mul_inv]
  have hSself : S = (b⁻¹ ^ s) * S := hsum_perm.trans hsplit
  have hzero : (1 - b⁻¹ ^ s) * S = 0 := by
    linear_combination hSself
  have hS0 : S = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (by
      simpa using sub_ne_zero_of_ne (Ne.symm hc))
  rw [ombreZeta, somme_plage_eq_somme_nonNuls (fun x : ZMod p => x⁻¹ ^ s)]
  exact hS0

/-- The edge `s = p - 1`: each term equals 1, the sum equals `p - 1 =
-1` in `𝔽_p` (notebook, "Bord s = p-1"). -/
theorem ombreZeta_card_sub_one {p : ℕ} [Fact p.Prime] :
    ombreZeta p (p - 1) = -1 := by
  have hp1 : 1 ≤ p := (Fact.out (p := p.Prime)).pos
  rw [ombreZeta]
  have hterm : ∀ k ∈ Finset.Icc 1 (p - 1),
      (((k : ℕ) : ZMod p)⁻¹ ^ (p - 1)) = 1 := by
    intro k hk
    rw [inv_pow_eq_pow hk (by omega)]
    simp
  have hpm : p - 1 + 1 - 1 = p - 1 := by omega
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Icc,
    nsmul_one, hpm, Nat.cast_sub hp1, Nat.cast_one,
    ZMod.natCast_self p, zero_sub]

end OmbreMuette

/-! ## Stuffle — partitioning the square into three regions

The left-hand side is a sum over the square `{1..p-1}²`; cut it into
`a > b` (the region of `ζ_p(m,n)`), `b > a` (the region of `ζ_p(n,m)`)
and the diagonal `a = b`, where `a⁻ᵐ·a⁻ⁿ = a⁻⁽ᵐ⁺ⁿ⁾` rebuilds
`ζ_p(m+n)`. The table in the notebook's reading, formally.
-/

section Stuffle

/-- The depth-two shadow read on the ordered pairs of the square: the
notebook's domain `0 < k₂ < k₁ < p`, seen as a filter. -/
private theorem ombreZeta2_eq_paires (m n : ℕ) :
    ombreZeta2 p m n = ∑ ij ∈ pairesOrdonnees p,
      (((ij.1 : ZMod p)⁻¹ ^ m) * ((ij.2 : ZMod p)⁻¹ ^ n)) := by
  have hico : ∀ k1 ∈ plage p,
      (Finset.Ico 1 k1 : Finset ℕ) = (plage p).filter (fun k2 => k2 < k1) := by
    intro k1 hk1
    obtain ⟨hk11, hk12⟩ := mem_plage.1 hk1
    ext k2
    simp only [plage, mem_Ico, mem_filter, mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, by omega⟩, h2⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h3⟩
  rw [ombreZeta2]
  rw [Finset.sum_congr rfl (fun k1 hk1 => by
    rw [hico k1 hk1, Finset.sum_filter])]
  rw [Finset.sum_filter]
  exact (Finset.sum_product (Finset.Icc 1 (p - 1)) (plage p)
    (fun x : ℕ × ℕ =>
      if x.2 < x.1 then ((x.1 : ZMod p)⁻¹ ^ m) * ((x.2 : ZMod p)⁻¹ ^ n) else 0)).symm

/-- The partition of the square: any sum over `{1..p-1}²` splits into
the three regions `k₂ < k₁`, `k₁ < k₂` and the diagonal. -/
private theorem partition_carre (f : ℕ × ℕ → ZMod p) :
    ∑ ij ∈ plage p ×ˢ plage p, f ij
      = (∑ ij ∈ (plage p ×ˢ plage p).filter (fun ij => ij.2 < ij.1), f ij)
      + (∑ ij ∈ (plage p ×ˢ plage p).filter (fun ij => ij.1 < ij.2), f ij)
      + (∑ ij ∈ (plage p ×ˢ plage p).filter (fun ij => ij.1 = ij.2), f ij) := by
  classical
  have h1 := Finset.sum_filter_add_sum_filter_not
      (p := fun ij : ℕ × ℕ => ij.2 < ij.1) (s := plage p ×ˢ plage p) (f := f)
  have h2 := Finset.sum_filter_add_sum_filter_not
      (p := fun ij : ℕ × ℕ => ij.1 < ij.2)
      (s := (plage p ×ˢ plage p).filter (fun ij => ¬ ij.2 < ij.1)) (f := f)
  have e1 : ((plage p ×ˢ plage p).filter (fun ij => ¬ ij.2 < ij.1)).filter
        (fun ij => ij.1 < ij.2)
      = (plage p ×ˢ plage p).filter (fun ij => ij.1 < ij.2) := by
    ext ij
    simp only [mem_filter]
    constructor
    · rintro ⟨⟨hprod, _⟩, h⟩
      exact ⟨hprod, h⟩
    · rintro ⟨hprod, h⟩
      exact ⟨⟨hprod, by omega⟩, h⟩
  have e2 : ((plage p ×ˢ plage p).filter (fun ij => ¬ ij.2 < ij.1)).filter
        (fun ij => ¬ ij.1 < ij.2)
      = (plage p ×ˢ plage p).filter (fun ij => ij.1 = ij.2) := by
    ext ij
    simp only [mem_filter]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, by omega⟩, by omega⟩
  rw [← h1, ← h2, e1, e2]
  ring

/-- **Stuffle**: `ζ_p(m)·ζ_p(n) = ζ_p(m,n) + ζ_p(n,m) + ζ_p(m+n)`,
exact in `𝔽_p` for every prime `p` (notebook, section 2: "the proof by
partition"). -/
theorem stuffle (m n : ℕ) :
    ombreZeta p m * ombreZeta p n
      = ombreZeta2 p m n + ombreZeta2 p n m + ombreZeta p (m + n) := by
  classical
  have hdiag : (plage p ×ˢ plage p).filter (fun ij : ℕ × ℕ => ij.1 = ij.2)
      = (plage p).image (fun k : ℕ => (k, k)) := by
    ext ij
    simp only [mem_filter, mem_product, mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨ij.1, h1, by ext <;> simp [h3]⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨hk, hk⟩, rfl⟩
  -- The product unfolds over the square, then partitions.
  rw [ombreZeta, ombreZeta, Finset.sum_mul_sum]
  have hexch : ∑ a ∈ Finset.Icc 1 (p - 1), ∑ b ∈ Finset.Icc 1 (p - 1),
      (((a : ℕ) : ZMod p)⁻¹ ^ m) * (((b : ℕ) : ZMod p)⁻¹ ^ n)
      = ∑ x ∈ plage p ×ˢ plage p,
      (((x.1 : ℕ) : ZMod p)⁻¹ ^ m) * (((x.2 : ℕ) : ZMod p)⁻¹ ^ n) :=
    (Finset.sum_product (Finset.Icc 1 (p - 1)) (Finset.Icc 1 (p - 1))
      (fun x : ℕ × ℕ =>
        ((x.1 : ZMod p)⁻¹ ^ m) * ((x.2 : ZMod p)⁻¹ ^ n))).symm
  rw [hexch]
  simp only [partition_carre (f := fun ij : ℕ × ℕ =>
    (((ij.1 : ZMod p)⁻¹ ^ m) * ((ij.2 : ZMod p)⁻¹ ^ n)))]
  -- Region k₁ < k₂: this is ζ_p(n,m) — same pairs, exponents swapped.
  have hswap : (plage p ×ˢ plage p).filter (fun ij : ℕ × ℕ => ij.1 < ij.2)
      = (pairesOrdonnees p).image (fun ij : ℕ × ℕ => (ij.2, ij.1)) := by
    ext ij
    simp only [mem_filter, mem_image, pairesOrdonnees, plage, mem_product, mem_Icc]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, h5⟩
      exact ⟨(ij.2, ij.1), ⟨⟨⟨h3, h4⟩, ⟨h1, h2⟩⟩, h5⟩, rfl⟩
    · rintro ⟨a, ⟨⟨⟨ha1, ha2⟩, ⟨ha3, ha4⟩⟩, ha5⟩, rfl⟩
      exact ⟨⟨⟨ha3, ha4⟩, ⟨ha1, ha2⟩⟩, ha5⟩
  have hF2 : ∑ ij ∈ (plage p ×ˢ plage p).filter (fun ij : ℕ × ℕ => ij.1 < ij.2),
      (((ij.1 : ZMod p)⁻¹ ^ m) * ((ij.2 : ZMod p)⁻¹ ^ n))
      = ombreZeta2 p n m := by
    rw [hswap, Finset.sum_image (fun a _ b _ h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.2 h.1)]
    rw [ombreZeta2_eq_paires p n m]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hF2, ombreZeta2_eq_paires p m n]
  -- Diagonal: a⁻ᵐ·a⁻ⁿ = a⁻⁽ᵐ⁺ⁿ⁾ rebuilds ζ_p(m+n).
  have hdiag_sum : ∑ ij ∈ (plage p ×ˢ plage p).filter (fun ij => ij.1 = ij.2),
      (((ij.1 : ZMod p)⁻¹ ^ m) * ((ij.2 : ZMod p)⁻¹ ^ n))
      = ombreZeta p (m + n) := by
    rw [hdiag, Finset.sum_image (fun k _ k' _ h => congrArg Prod.fst h),
      ombreZeta]
    exact Finset.sum_congr rfl fun _ _ => by rw [← pow_add]
  rw [hdiag_sum]

end Stuffle

/-! ## Reversal — the involution `k ↦ p - k`

The involution `(k₁,k₂) ↦ (p-k₁, p-k₂)` swaps the order of the
indices, and each inverse flips: `(p-k)⁻¹ = -k⁻¹` in `𝔽_p`. Relabeled,
the sum of `ζ_p(m,n)` becomes `(-1)^(m+n)·ζ_p(n,m)` — the notebook's
three lines.
-/

section Retournement

/-- In `𝔽_p`, the integer `p - k` is the negation of `k`. -/
private theorem cast_sub_plage {p : ℕ} [Fact p.Prime] {k : ℕ}
    (hk : k ∈ plage p) : (((p - k : ℕ) : ZMod p)) = (-((k : ℕ) : ZMod p)) := by
  obtain ⟨hk1, hk2⟩ := mem_plage.1 hk
  have hp1 : 1 ≤ p := (Fact.out (p := p.Prime)).pos
  have hadd : p - k + k = p := by omega
  have hsum : (((p - k : ℕ) : ZMod p)) + ((k : ℕ) : ZMod p) = 0 := by
    have hstep : (((p - k : ℕ) : ZMod p)) + ((k : ℕ) : ZMod p)
        = (((p - k + k : ℕ) : ZMod p)) := by
      rw [Nat.cast_add]
    rw [hstep, hadd, ZMod.natCast_self p]
  exact eq_neg_of_add_eq_zero_left hsum

/-- **Reversal**: `ζ_p(m,n) = (-1)^(m+n)·ζ_p(n,m)` for every prime `p`
(notebook, section 2: "the involution"). -/
theorem retournement (m n : ℕ) :
    ombreZeta2 p m n = (-1 : ZMod p) ^ (m + n) * ombreZeta2 p n m := by
  classical
  -- The involution φ : (k₁,k₂) ↦ (p-k₂, p-k₁). Truncated subtraction
  -- is only injective when bounded: injectivity is taken on the pairs,
  -- not globally — hence `image`/`sum_image` rather than an embedding.
  set φ : ℕ × ℕ → ℕ × ℕ := fun ij => (p - ij.2, p - ij.1) with hphi
  have hφinj : ∀ a ∈ pairesOrdonnees p, ∀ b ∈ pairesOrdonnees p,
      φ a = φ b → a = b := by
    intro a ha b hb hab
    simp only [pairesOrdonnees, plage, mem_filter, mem_product, mem_Icc] at ha hb
    obtain ⟨⟨⟨ha1, ha2⟩, ⟨ha3, ha4⟩⟩, ha5⟩ := ha
    obtain ⟨⟨⟨hb1, hb2⟩, ⟨hb3, hb4⟩⟩, hb5⟩ := hb
    simp only [hphi, Prod.mk.injEq] at hab
    ext <;> omega
  have hφimg : (pairesOrdonnees p).image φ = pairesOrdonnees p := by
    ext ij
    rcases ij with ⟨i1, i2⟩
    simp only [mem_image, hphi, Prod.mk.injEq, pairesOrdonnees, plage,
      mem_filter, mem_product, mem_Icc]
    constructor
    · rintro ⟨a, ⟨⟨⟨ha1, ha2⟩, ⟨ha3, ha4⟩⟩, ha5⟩, ⟨hab1, hab2⟩⟩
      subst hab1
      subst hab2
      exact ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, by omega⟩
    · rintro ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, h5⟩
      refine ⟨(p - i2, p - i1),
        ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, by omega⟩, ?_⟩
      omega
  rw [ombreZeta2_eq_paires p m n, ombreZeta2_eq_paires p n m]
  conv_lhs => rw [← hφimg]
  rw [Finset.sum_image hφinj]
  simp only [hphi]
  -- The term flips: T(m,n)(φ(k₁,k₂)) = (-1)^(m+n) · T(n,m)(k₁,k₂).
  have hterm : ∀ ij ∈ pairesOrdonnees p,
      ((((p - ij.2 : ℕ) : ZMod p))⁻¹ ^ m) * ((((p - ij.1 : ℕ) : ZMod p))⁻¹ ^ n)
      = (-1 : ZMod p) ^ (m + n)
          * ((((ij.1 : ℕ) : ZMod p)⁻¹ ^ n) * (((ij.2 : ℕ) : ZMod p)⁻¹ ^ m)) := by
    rintro ⟨k1, k2⟩ hk
    simp only [pairesOrdonnees, plage, mem_filter, mem_product, mem_Icc] at hk
    obtain ⟨⟨⟨hk11, hk12⟩, ⟨hk21, hk22⟩⟩, hk23⟩ := hk
    have e1 := cast_sub_plage (mem_plage.2 ⟨hk11, hk12⟩)
    have e2 := cast_sub_plage (mem_plage.2 ⟨hk21, hk22⟩)
    rw [e1, e2, inv_neg, inv_neg, neg_pow, neg_pow, pow_add]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.mul_sum]

end Retournement

/-! ## Differentiation — even weights die, odd ones survive

Combine the three acquisitions: depth-one silence (the three simple
shadows vanish), stuffle (hence `ζ_p(m,n) = -ζ_p(n,m)`), and reversal
(if `m + n` is even, `ζ_p(n,m) = ζ_p(m,n)`). Then `2·ζ_p(m,n) = 0`,
and `p ≠ 2` concludes. This is the theorem of cell (b) of the
notebook — proved, not merely measured.
-/

section Derivation

private theorem deux_ne_zero_zmod {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  have hp2le : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  have hd : p ∣ (2 : ℕ) := (ZMod.natCast_eq_zero_iff 2 p).mp h
  have hple : p ≤ 2 := Nat.le_of_dvd two_pos hd
  omega

/-- **Differentiation**: for `m + n ≤ p - 2` **even** and `p ≠ 2`,
`ζ_p(m,n) = 0` — the even weights of depth 2 vanish in the layer `p`
(notebook, cell (b)). -/
theorem ombre_poids_pair (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hp2 : p ≠ 2) (hw : m + n ≤ p - 2) (hpar : Even (m + n)) :
    ombreZeta2 p m n = 0 := by
  -- 1. Depth-one silence.
  have h0m : ombreZeta p m = 0 := ombreZeta_eq_zero hm (by omega)
  have h0n : ombreZeta p n = 0 := ombreZeta_eq_zero hn (by omega)
  have h0w : ombreZeta p (m + n) = 0 :=
    ombreZeta_eq_zero (Nat.add_pos_right m hn) (by omega)
  -- 2. Stuffle: ζ_p(m,n) + ζ_p(n,m) = 0.
  have hst : ombreZeta2 p m n + ombreZeta2 p n m = 0 := by
    have h := stuffle p m n
    rw [h0m, h0n, h0w] at h
    simpa using h.symm
  -- 3. Reversal, even parity: (-1)^(m+n) = 1.
  have hmoinsun : (-1 : ZMod p) ^ (m + n) = 1 := by
    obtain ⟨k, hk⟩ := hpar
    rw [hk, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have hret : ombreZeta2 p n m = ombreZeta2 p m n := by
    have h := retournement p m n
    rw [hmoinsun, one_mul] at h
    exact h.symm
  -- 2·ζ_p(m,n) = 0 and 2 invertible: conclusion.
  have hdeux : (2 : ZMod p) * ombreZeta2 p m n = 0 := by
    linear_combination hst - hret
  exact (mul_eq_zero.mp hdeux).resolve_left (deux_ne_zero_zmod hp2)

end Derivation

end Serre100_en
