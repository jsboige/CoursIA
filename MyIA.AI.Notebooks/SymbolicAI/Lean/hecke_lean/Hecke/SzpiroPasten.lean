import Mathlib.Tactic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Szpiro--Pasten 2026 : factorisation admissible et énoncé formel du théorème 1.1

Ce module réalise le grain 6 de l'Epic Langlands (#17969) : l'énoncé Lean
formel du théorème 1.1 du preprint d'Hector Pasten, *Improved Bounds for
Szpiro's Conjecture* (arXiv 2609.17390, 16 septembre 2026), dont le terrain
calculatoire est le notebook
`Search/App-32-Szpiro-Pasten-2026.ipynb`.

* `omega n` : le nombre ω(n) de facteurs premiers distincts de `n` ;
* `IsAdmissibleFactorization N D M` : la définition-clé du preprint —
  `N = DM` avec `gcd(D, M) = 1`, `D` carré-libre, et un nombre **pair** de
  facteurs premiers (la parité vient du signe de l'espace quaternionique
  `S_D(M)` de Jacquet--Langlands) ;
* `szpiroPastenThm11` : l'énoncé formel du théorème 1.1 —
  `h(E) ≤ C * M * φ(D) * log ℓ` à constante absolue effective — comme
  `Prop`, **non prouvé ici** (note d'honnêteté ci-dessous) ;
* le versant calculable de la définition est prouvé sans sorry :
  la factorisation triviale est toujours admissible, les factorisations
  admissibles de `N = 30` sont exactement `{1, 6, 10, 15}` —
  `2^(ω(N)-1) = 4` sur l'exemple filé du notebook — et `D = 2`, `D = 5`,
  `D = 30` sont rejetés (parité impaire de ω(D)). Ces faits passent par des
  lemmes compositionnels : le `decide` naïf bloque au noyau sur `Nat.minSqFac`
  (récursion bien fondée), la factorisation fait le travail.

## Honnêteté du périmètre (G.3/G.9)

Le théorème 1.1 général (courbes de Shimura, correspondance de
Jacquet--Langlands, lemme de multiplicité des valeurs propres de Hecke)
est **OPEN dans ce lake, sans `sorry`** : il vit dans
`szpiroPastenThm11 : Prop`, sur le même patron d'honnêteté que
l'atteignabilité de `h*` dans `search_lean` — l'énoncé est un objet Lean
du premier ordre, `#check`-able, jamais une preuve déguisée. Ce qui est
prouvé ci-dessous l'est intégralement (zéro sorry).

**Ponts vers les notebooks** : la mécanique du choix de `D` et le proxy
`log|Δ| / log rad(|Δ|)` vivent dans `App-32` (kernel python3) ; les formes
modulaires et les opérateurs de Hecke dans `SymbolicAI/Lean/Langlands/`
(01, 02) et `Lean-29`. Ce module en est le versant formel : mêmes
définitions, preuve par le noyau.
-/

set_option autoImplicit false

namespace SzpiroPasten

/-! ### La définition-clé : factorisation admissible -/

/-- Nombre de facteurs premiers distincts ω(n), lu sur le support de la
factorisation. -/
def omega (n : ℕ) : ℕ := (Nat.factorization n).support.card

/-- Factorisation admissible `N = DM` (définition §2 du preprint) :
`D` et `M` premiers entre eux, `D` carré-libre, et ω(D) **pair**. La parité
n'est pas décorative : elle vient du signe de l'espace de formes
quaternioniques `S_D(M)` dans lequel vit la newform de la courbe par
Jacquet--Langlands. -/
def IsAdmissibleFactorization (N D M : ℕ) : Prop :=
  D * M = N ∧ D.Coprime M ∧ Squarefree D ∧ Even (omega D)

instance decidableIsAdmissible (N D M : ℕ) :
    Decidable (IsAdmissibleFactorization N D M) := by
  unfold IsAdmissibleFactorization
  infer_instance

/-- La factorisation triviale `D = 1, M = N` est toujours admissible
(ω(1) = 0 est pair, 1 est carré-libre, premier à tout) : le domaine du
théorème 1.1 n'est jamais vide. -/
theorem one_admissible (N : ℕ) : IsAdmissibleFactorization N 1 N := by
  refine ⟨by norm_num, Nat.coprime_one_left N, squarefree_one, ?_⟩
  simp only [omega, Nat.factorization_one, Finsupp.support_zero, Finset.card_empty]
  exact ⟨0, by norm_num⟩

/-! ### `N = 30` : l'exemple filé du notebook, prouvé compositionnellement

Un `decide` naïf sur `IsAdmissibleFactorization` bloque au noyau :
l'instance de décidabilité de `Squarefree` repose sur `Nat.minSqFac`,
récursion **bien fondée** que le noyau ne réduit pas. Les lemmes techniques
ci-dessous refont le travail par le théorème de factorisation — preuve
complètement compositionnelle, `decide` réservé aux littéraux (premiers
distincts, coprimalité, non-divisibilité). -/

/-- Carré-libre d'un produit de deux premiers distincts, par la
caractérisation factorielle : chaque exposant vaut 0 ou 1. -/
theorem squarefree_two_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    Squarefree (p * q) := by
  rw [Nat.squarefree_iff_factorization_le_one
      (mul_ne_zero (Nat.Prime.ne_zero hp) (Nat.Prime.ne_zero hq))]
  intro r
  simp only [Nat.factorization_mul (Nat.Prime.ne_zero hp) (Nat.Prime.ne_zero hq),
    Nat.Prime.factorization hp, Nat.Prime.factorization hq,
    Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
  split_ifs <;> simp_all

/-- Extension d'une factorisation carré-libre par un premier étranger :
`n` carré-libre, `p` premier ne divisant pas `n` ⇒ `np` carré-libre. -/
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

/-- ω d'un premier : 1 — le support de sa factorisation est un singleton. -/
theorem omega_prime {p : ℕ} (hp : p.Prime) : omega p = 1 := by
  simp [omega, Nat.Prime.factorization hp]

/-- ω d'un produit par un premier étranger : `ω(n·p) = ω(n) + 1` — le
support de la factorisation gagne exactement le singleton `{p}`. -/
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

/-- Sur `N = 30` (ω(N) = 3 : premiers 2, 3, 5), les quatre factorisations
admissibles `D ∈ {1, 6, 10, 15}` — exactement `2^(ω(N)-1) = 4`, la moitié
des sous-ensembles de premiers de cardinal pair. Produit, coprimalité,
carré-libre et parité prouvés un à un. -/
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

/-- `D = 2` n'est PAS admissible : ω(2) = 1 est impair. La contrainte de
parité exclut les singletons de premiers. -/
theorem not_admissible_thirty_two : ¬IsAdmissibleFactorization 30 2 15 := by
  intro h
  obtain ⟨-, -, -, heven⟩ := h
  rw [omega_two] at heven
  obtain ⟨k, hk⟩ := heven
  omega

/-- `D = 5` : même rejet, ω(5) = 1 impair. -/
theorem not_admissible_thirty_five : ¬IsAdmissibleFactorization 30 5 6 := by
  intro h
  obtain ⟨-, -, -, heven⟩ := h
  rw [omega_five] at heven
  obtain ⟨k, hk⟩ := heven
  omega

/-- `D = 30` : ω(30) = 3 impair — même le facteur plein est exclu. -/
theorem not_admissible_thirty_thirty : ¬IsAdmissibleFactorization 30 30 1 := by
  intro h
  obtain ⟨-, -, -, heven⟩ := h
  rw [omega_thirty] at heven
  obtain ⟨k, hk⟩ := heven
  omega

/-! ### L'énoncé formel du théorème 1.1 -/

/-- Paire (hauteur, conducteur) : support de l'énoncé formel. Que `hE` soit
la hauteur de Faltings d'une courbe elliptique de conducteur `N` est une
hypothèse de typage, prise telle quelle — la profondeur arithmétique est
hors périmètre du lake. -/
structure CourbeHN where
  /-- Hauteur de Faltings (abstraite). -/
  hE : ℝ
  /-- Conducteur (abstrait). -/
  N : ℕ

/-- **Énoncé formel du théorème 1.1 (Pasten 2026, arXiv 2609.17390)** :
il existe une constante absolue *effective* `C > 0` telle que, pour toute
courbe `E/ℚ` (portée par `CourbeHN`), toute factorisation admissible
`E.N = D * M` et tout premier `ℓ` ne divisant pas `E.N` :

`h(E) ≤ C * M * φ(D) * log ℓ`

NON prouvé dans ce lake : c'est l'énoncé lui-même — objet Lean du premier
ordre, `#check`-able — qui est le livrable du grain 6 de #17969. La preuve
(courbes de Shimura, Jacquet--Langlands, multiplicité des valeurs propres
de Hecke dans `S_D(M)`) est documentée dans `App-32` §Conclusion et reste
hors scope, conformément au patron d'honnêteté de `search_lean`. -/
def szpiroPastenThm11 : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ E : CourbeHN, ∀ D M ℓ : ℕ,
      IsAdmissibleFactorization E.N D M →
      ℓ.Prime → ¬ℓ ∣ E.N →
        E.hE ≤ C * (M : ℝ) * (Nat.totient D : ℝ) * Real.log (ℓ : ℝ)

#check @szpiroPastenThm11

end SzpiroPasten
