import Mathlib

/-!
# Szpiro — Mathlib anchoring of the Pasten 2026 bounds (homage to Serre)

English mirror of `Szpiro.lean` (FR-first canonical), issue #16549 (option A),
per the i18n sibling-pair convention of this lake (EPIC #4980): distinct FR +
EN sibling files, both compile; namespace `Szpiro_en` (anti-collision with FR
`Szpiro`); non-docstring content byte-identical (CI drift-detectable); EN
docstrings manually translated.

Companion Lean file of the notebook
[`App-32-Szpiro-Pasten-2026.ipynb`](../Applications/Search/App-32-Szpiro-Pasten-2026.ipynb):
Pasten 2026, *Improved Bounds for Szpiro's Conjecture*, arXiv 2609.17390
(preprint, archived under `Bibliographie IA\NumberTheory`).

## What this module does — and does not do

The Faltings height `h(E)` does not exist in Mathlib: Pasten's statements are
therefore **not formally proved here** (no `sorry`, no added axiom — this file
only declares objects and mechanically checked facts). The paper's theorems,
quoted faithfully:

> **Theorem 1.1 (Main result).** For an elliptic curve `E` over ℚ, let
> `N = DM` be an **admissible** factorization and `ℓ` a prime not dividing
> `N`. Then `h(E) ≪ M·φ(D)·log ℓ`, with an absolute effective implicit
> constant.
>
> **Corollary 1.2.** For all elliptic curves `E` over ℚ: `h(E) ≪ N·log log N`
> — unconditional (previously known under GRH only; 2013: `h(E) ≪ N·log N`).
>
> **Corollary 1.3.** For `E` semistable outside a finite set `S` of primes:
> `h(E) ≪_S N`.

The conjectural landscape (Szpiro `log Δ ≪ log N`, Frey's stronger form
`h(E) ≪ log N`, and `log Δ ≪ max{1, h(E)}`) is unfolded in the notebook §1;
the proof goes through Jacquet–Langlands and quaternionic modular forms — the
Serre tradition (modularity, ℓ-adic) to which this file is an homage entry
point.

What the module anchors in Mathlib, mirroring the notebook:

- the **admissible factorization** `N = DM` (paper definition: `gcd(D,M) = 1`,
  `D` squarefree, an **even** number of prime factors — the parity comes from
  the sign of the quaternionic forms space), checked on the `N = 30` examples
  of notebook §2 (including the parity counter-example `D = 2`);
- the **identity `M·φ(D) ≤ N`** (notebook §2, `borne_11`): the quantity of
  Theorem 1.1 never exceeds `N` — a direct consequence of `φ(D) ≤ D`;
- the **Weierstrass discriminant** of the witness curve `E : y² = x³ + x + 1`
  (notebook §3, first table row): `Δ = -496`, and `E` is nonsingular.

Numerical conventions: `WeierstrassCurve.Δ` is the full classical
discriminant (for `y² = x³ + ax + b` in characteristic ≠ 2, 3:
`Δ = -16·(4a³ + 27b²)`, same convention as the notebook's `delta_modele`).
-/

namespace Szpiro_en

/-- Admissible factorization `N = D * M` in the sense of Pasten 2026
(definition preceding Theorem 1.1): `D` and `M` coprime, `D` squarefree, and
`D` with an **even** number of prime factors. -/
def AdmissibleFactorization (D M : ℕ) : Prop :=
  D.gcd M = 1 ∧ Squarefree D ∧ Even D.primeFactorsList.length

/-- `N = 30 = 2·3·5`: the trivial factorization (`D = 1`, zero prime factors
— zero is even) is admissible. First row of the notebook §2 table. (`decide`
cannot evaluate `primeFactorsList` — well-founded recursion, not
kernel-executable: each fact is proved by the matching Mathlib lemma, only
`gcd` is decided.) -/
theorem admissible_trente_triviale : AdmissibleFactorization 1 30 :=
  ⟨by decide, squarefree_one, by rw [Nat.primeFactorsList_one]; exact ⟨0, rfl⟩⟩

/-- `N = 30`: `D = 15 = 3·5` (two prime factors, even) is admissible.
Proof by rewriting with the `primeFactorsList` equations (the idiom of
Mathlib's own `primeFactorsList_two`): `Squarefree` via
`squarefree_iff_nodup_primeFactorsList`, parity on the reduced list. -/
theorem admissible_trente_quinze : AdmissibleFactorization 15 2 :=
  ⟨by decide,
    by apply Nat.squarefree_iff_nodup_primeFactorsList.2
       simp [Nat.primeFactorsList],
    by show Even 2; exact ⟨1, rfl⟩⟩

/-- Parity counter-example of notebook §2: `D = 2` has exactly **one** prime
factor (odd), so `30 = 2·15` is NOT admissible — although `gcd(2, 15) = 1`
and `2` is squarefree. The parity constraint alone carries the exclusion
(`primeFactorsList_two`, then `odd_one`). -/
theorem non_admissible_trente_deux : ¬AdmissibleFactorization 2 15 := by
  intro h
  unfold AdmissibleFactorization at h
  rw [Nat.primeFactorsList_two] at h
  have h1 : Even 1 := h.2.2
  exact Nat.not_odd_iff_even.2 h1 odd_one

/-- φ(15) = 8: the value used by notebook §2 (`borne_11`) for the best
admissible factorization of `N = 30`. -/
theorem phi_quinze : Nat.totient 15 = 8 := by decide

/-- Identity of notebook §2: the quantity `M·φ(D)` of Theorem 1.1 never
exceeds `N = D·M`, since `φ(D) ≤ D`. Up to an absolute constant, the bound
`h(E) ≪ M·φ(D)·log ℓ` is thus always at least as sharp as
`h(E) ≪ N·log ℓ`. -/
theorem borne_shape_le_N {D M N : ℕ} (h : N = D * M) :
    M * Nat.totient D ≤ N := by
  rw [h]
  calc M * Nat.totient D ≤ M * D :=
        Nat.mul_le_mul (Nat.le_refl M) (Nat.totient_le D)
    _ = D * M := Nat.mul_comm M D

section Courbe

/-- Witness curve of notebook §3 (first table row): `E : y² = x³ + x + 1`
over ℚ, in general Weierstrass coefficients (`a₁ = a₂ = a₃ = 0`,
`a₄ = a₆ = 1`). -/
def E : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := 1
  a₆ := 1

/-- The model discriminant equals `Δ = -496 = -16·(4·1³ + 27·1²)`: the value
printed by `delta_modele(1, 1)` in notebook §3 (same convention: full
classical discriminant). -/
theorem delta_E : E.Δ = -496 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, E]
  norm_num

/-- `Δ ≠ 0`, hence the curve `E` is nonsingular — elliptic in the sense of
`WeierstrassCurve.IsElliptic`. -/
theorem E_est_elliptique : E.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by rw [delta_E]; norm_num)⟩

end Courbe

end Szpiro_en
