import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Valeurs zêta multiples finies : stuffle et retournement prouvés par le noyau

Pendant kernel du notebook `02-valeurs-zeta-multiples-finies.ipynb` (série
*Serre 100*, EPIC #16334 — voie de graduation « pendants kernel »).
Le notebook *mesure* les identités de l'anneau des adèles du pauvre en
Python ; ce module les *démontre* dans `𝔽_p`, pour tout premier `p`.

Plan, en miroir du notebook :

1. **Définitions** (`ombreZeta`, `ombreZeta2`) — les sommes harmoniques
   généralisées tronquées à `p - 1` : profondeur 1 `ζ_p(s) = ∑ k⁻ˢ` et
   profondeur 2 `ζ_p(m,n) = ∑_{k₂<k₁} k₁⁻ᵐ k₂⁻ⁿ` (notebook, `zeta_p`,
   `zeta_p2`).
2. **Vérifications par le noyau** : le spectre `p = 13` (nul partout sauf
   `s = p - 1`), le stuffle et le retournement sur **toutes** les paires
   d'exposants de `𝔽_7`, et les survivants de poids impair `ζ₁₃(2,1) = 5`,
   `ζ₁₃(3,2) = 7` — la cellule (c) du notebook, mais prouvée.
3. **L'ombre muette** : `ζ_p(s) = 0` pour `1 ≤ s ≤ p - 2` et
   `ζ_p(p-1) = -1` — le théorème « de trois lignes » du groupe cyclique,
   démontré ici par la preuve de permutation du notebook.
4. **Le stuffle** : `ζ_p(m)·ζ_p(n) = ζ_p(m,n) + ζ_p(n,m) + ζ_p(m+n)` —
   la partition du carré en trois régions (`a > b`, `b > a`, `a = b`),
   exactement le tableau de la lecture du notebook.
5. **Le retournement** : `ζ_p(m,n) = (-1)^(m+n)·ζ_p(n,m)` — l'involution
   `(k₁,k₂) ↦ (p-k₁, p-k₂)`.
6. **La dérivation** : quand `m + n ≤ p - 2` est **pair** (et `p ≠ 2`),
   `ζ_p(m,n) = 0` — mutisme + stuffle + retournement : les poids pairs
   meurent, les impairs survivent.

Deux remarks techniques. D'abord, l'inverse modulaire `ZMod.inv` vit en
récursion bien fondée : le noyau ne peut pas le réduire, et `decide`
échoue sur les définitions. Le pont de Fermat `k⁻ˢ = k^(p-1-s)` (lemme
`inv_pow_eq_pow`) commute chaque ombre vers une somme de puissances
ordinaires, calculable — c'est ce qui rend les vérifications du §2
possibles. Ensuite, la couche `p²` (Wolstenholme, Leudesdorf, pont de
Bernoulli) reste du côté du notebook : elle vit dans `ℤ/p²`, où
l'inversion n'est plus un corps ; c'est la frontière naturelle de ce
module.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Serre100

open Finset

variable (p : ℕ) [Fact p.Prime]

/-! ## Définitions — le vocabulaire du notebook, en Lean

L'ombre d'indice simple est la somme harmonique généralisée tronquée à
`p - 1` — la taille du corps *est* la hauteur de sommation. L'inverse
`k⁻ˢ` se lit dans le corps `𝔽_p` (tout `k` non nul y est inversible) ;
c'est pourquoi les définitions portent `[Fact p.Prime]` dès le départ,
contrairement au module `HasseComputee` où seul le comptage était requis.
-/

/-- Ombre de profondeur 1 : `ζ_p(s) = ∑_{k=1}^{p-1} k⁻ˢ` dans `𝔽_p`
(notebook, `zeta_p`, couche `N = 1`). -/
def ombreZeta (s : ℕ) : ZMod p :=
  ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹ ^ s)

/-- Ombre de profondeur 2 : `ζ_p(m,n) = ∑_{0 < k₂ < k₁ < p} k₁⁻ᵐ k₂⁻ⁿ`
(notebook, `zeta_p2`). -/
def ombreZeta2 (m n : ℕ) : ZMod p :=
  ∑ k1 ∈ Finset.Icc 1 (p - 1), ∑ k2 ∈ Finset.Ico 1 k1,
    ((k1 : ZMod p)⁻¹ ^ m * (k2 : ZMod p)⁻¹ ^ n)

/-- La plage de sommation du notebook : les entiers de `1` à `p - 1`. -/
private abbrev plage (p : ℕ) : Finset ℕ :=
  Finset.Icc 1 (p - 1)

private theorem mem_plage {p k : ℕ} : k ∈ plage p ↔ 1 ≤ k ∧ k ≤ p - 1 :=
  Finset.mem_Icc

/-- Les paires ordonnées de la plage : le filtre `k₂ < k₁` sur le carré
`{1..p-1}²`. C'est la forme où les partitions du §4 se lisent. -/
private abbrev pairesOrdonnees (p : ℕ) : Finset (ℕ × ℕ) :=
  (plage p ×ˢ plage p).filter (fun ij => ij.2 < ij.1)

/-- Un entier de `1` à `p - 1` est non nul dans `𝔽_p`. -/
private theorem cast_ne_zero_of_mem_plage {p : ℕ} [Fact p.Prime] {k : ℕ}
    (hk : k ∈ plage p) : ((k : ℕ) : ZMod p) ≠ 0 := by
  obtain ⟨hk1, hk2⟩ := mem_plage.1 hk
  intro h0
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  have hv : ((k : ℕ) : ZMod p).val = k := ZMod.val_cast_of_lt (by omega)
  rw [h0, ZMod.val_zero] at hv
  omega

/-- Fermat porte l'inverse en puissance : `k⁻ˢ = k^(p-1-s)` pour
`s ≤ p - 1` — le pont `t = p - 1 - s` du notebook. C'est aussi ce qui
rend les vérifications numériques possibles : l'inverse modulaire
bloque la réduction du noyau (`ZMod.inv` vit en récursion bien fondée),
l'exposant ordinaire ne la bloque pas. -/
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

/-! ## Vérifications par le noyau — les tables du notebook, prouvées

Le notebook observe (cellules « Mesure », « Le produit STUFFLE »,
« RETOURNEMENT ») ; le noyau démontre ici les mêmes valeurs, exactement,
et balaie `𝔽_7` en entier plutôt que d'échantillonner.
-/

section Verifications

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

/-- La forme « puissances » de l'ombre, decide-able. -/
private theorem ombreZeta_eq_pow {p : ℕ} [Fact p.Prime] {s : ℕ}
    (hs : s ≤ p - 1) :
    ombreZeta p s = ∑ k ∈ plage p, ((k : ZMod p) ^ (p - 1 - s)) :=
  Finset.sum_congr rfl fun _ hk => inv_pow_eq_pow hk hs

/-- Même commutation pour la profondeur 2. -/
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

/-- Le spectre complet de `p = 13` (notebook, cellule « Mesure ») : nul
partout pour `1 ≤ s ≤ p - 2`. -/
example : ∀ s ∈ Finset.Icc 1 11, ombreZeta 13 s = 0 := by
  intro s hs
  obtain ⟨hs1, hs2⟩ := Finset.mem_Icc.1 hs
  rw [ombreZeta_eq_pow (by omega)]
  interval_cases s
  all_goals decide

/-- La seule exception du spectre : `ζ_p(p-1) = p - 1 = -1`
(notebook, « Bord s = p-1 »). -/
example : ombreZeta 13 12 = 12 := by
  rw [ombreZeta_eq_pow (by omega)]
  decide

/-- Le stuffle sur **toutes** les paires `(m, n)` d'exposants de `𝔽_7`
avec `m + n ≤ p - 1` — le « 112/112 » du notebook, mais exhaustif sur
le carré `4 × 4`. -/
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

/-- Le retournement sur **toutes** les paires de `𝔽_7`. -/
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

/-- Les survivants de poids impair (notebook, cellule (c)) :
`ζ₁₃(2,1) = 5` — non nul, l'information vit ici. -/
example : ombreZeta2 13 2 1 = 5 := by
  rw [ombreZeta2_eq_pow (by omega) (by omega)]
  decide

/-- Deuxième survivant de la cellule (c) : `ζ₁₃(3,2) = 7`. -/
example : ombreZeta2 13 3 2 = 7 := by
  rw [ombreZeta2_eq_pow (by omega) (by omega)]
  decide

end Verifications

/-! ## L'ombre muette — le groupe cyclique efface tout

La preuve du notebook : soit `b` non nul avec `bˢ ≠ 1` (il en existe dès
que `1 ≤ s ≤ p - 2`, parce que `𝔽_pˣ` est cyclique d'ordre `p - 1`) ; la
multiplication par `b` permute les non-zéros, donc `ζ = b⁻ˢ·ζ`, et comme
`b⁻ˢ ≠ 1`, `ζ = 0`. C'est la preuve de `sum_subgroup_pow_eq_zero` de
Mathlib, répliquée sur le `Finset` des non-zéros pour rester au
vocabulaire du notebook.
-/

section OmbreMuette

/-- Le transport de la plage aux non-zéros : sommer `f` sur les entiers
de `1` à `p - 1`, c'est sommer sur les non-zéros de `𝔽_p` — la plage du
notebook EST le groupe `𝔽_pˣ`, vu par ses représentants. -/
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

/-- **L'ombre muette** : `ζ_p(s) = 0` pour `1 ≤ s ≤ p - 2` — la couche
`p` ne porte aucune information, ni pour les pairs ni pour les impairs
(notebook, section 1). -/
theorem ombreZeta_eq_zero {p : ℕ} [Fact p.Prime] {s : ℕ}
    (hs : 0 < s) (hs2 : s < p - 1) : ombreZeta p s = 0 := by
  -- Le pivot : b non nul avec b^s ≠ 1 (𝔽_pˣ cyclique d'ordre p - 1).
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
  -- La multiplication par b permute les non-zéros de 𝔽_p.
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
  -- Le changement de variable : ζ = b⁻ˢ · ζ, donc (1 - b⁻ˢ)·ζ = 0.
  have hc : (b⁻¹ ^ s) ≠ 1 := by
    rw [inv_pow]
    exact fun h1 => hbs (inv_eq_one.mp h1)
  set S : ZMod p :=
    ∑ x ∈ Finset.univ.filter (fun x : ZMod p => x ≠ 0), (x⁻¹ ^ s) with hS
  -- S = somme des images par x ↦ b·x (la permutation), puis facteur b⁻ˢ.
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

/-- Le bord `s = p - 1` : chaque terme vaut 1, la somme vaut `p - 1 =
-1` dans `𝔽_p` (notebook, « Bord s = p-1 »). -/
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

/-! ## Le stuffle — la partition du carré en trois régions

Le membre de gauche est une somme sur le carré `{1..p-1}²` ; on le
coupe en `a > b` (région de `ζ_p(m,n)`), `b > a` (région de `ζ_p(n,m)`)
et la diagonale `a = b`, où `a⁻ᵐ·a⁻ⁿ = a⁻⁽ᵐ⁺ⁿ⁾` reconstruit
`ζ_p(m+n)`. Le tableau de la lecture du notebook, formellement.
-/

section Stuffle

/-- L'ombre de profondeur 2 lue sur les paires ordonnées du carré : le
domaine `0 < k₂ < k₁ < p` du notebook, vu comme filtre. -/
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

/-- La partition du carré : toute somme sur `{1..p-1}²` se coupe en les
trois régions `k₂ < k₁`, `k₁ < k₂` et la diagonale. -/
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

/-- **Le stuffle** : `ζ_p(m)·ζ_p(n) = ζ_p(m,n) + ζ_p(n,m) + ζ_p(m+n)`,
exact dans `𝔽_p` pour tout premier `p` (notebook, section 2 : « la
preuve par partition »). -/
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
  -- Le produit se déploie sur le carré, puis se partitionne.
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
  -- Région k₁ < k₂ : c'est ζ_p(n,m) — mêmes paires, exposants échangés.
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
  -- Diagonale : a⁻ᵐ·a⁻ⁿ = a⁻⁽ᵐ⁺ⁿ⁾ reconstruit ζ_p(m+n).
  have hdiag_sum : ∑ ij ∈ (plage p ×ˢ plage p).filter (fun ij => ij.1 = ij.2),
      (((ij.1 : ZMod p)⁻¹ ^ m) * ((ij.2 : ZMod p)⁻¹ ^ n))
      = ombreZeta p (m + n) := by
    rw [hdiag, Finset.sum_image (fun k _ k' _ h => congrArg Prod.fst h),
      ombreZeta]
    exact Finset.sum_congr rfl fun _ _ => by rw [← pow_add]
  rw [hdiag_sum]

end Stuffle

/-! ## Le retournement — l'involution `k ↦ p - k`

L'involution `(k₁,k₂) ↦ (p-k₁, p-k₂)` échange l'ordre des indices, et
chaque inverse bascule : `(p-k)⁻¹ = -k⁻¹` dans `𝔽_p`. Réétiquetée, la
somme de `ζ_p(m,n)` devient `(-1)^(m+n)·ζ_p(n,m)` — les trois lignes du
notebook.
-/

section Retournement

/-- Dans `𝔽_p`, l'entier `p - k` est l'opposé de `k`. -/
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

/-- **Le retournement** : `ζ_p(m,n) = (-1)^(m+n)·ζ_p(n,m)` pour tout
premier `p` (notebook, section 2 : « l'involution »). -/
theorem retournement (m n : ℕ) :
    ombreZeta2 p m n = (-1 : ZMod p) ^ (m + n) * ombreZeta2 p n m := by
  classical
  -- L'involution φ : (k₁,k₂) ↦ (p-k₂, p-k₁). La soustraction tronquée
  -- n'est injective que bornée : l'injectivité se prend sur les paires,
  -- pas globalement — d'où `image`/`sum_image` plutôt qu'un plongement.
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
  -- Le terme bascule : T(m,n)(φ(k₁,k₂)) = (-1)^(m+n) · T(n,m)(k₁,k₂).
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

/-! ## La dérivation — les poids pairs meurent, les impairs survivent

Combiner les trois acquis : mutisme de profondeur 1 (les trois ombres
simples s'annulent), stuffle (donc `ζ_p(m,n) = -ζ_p(n,m)`), et
retournement (si `m + n` est pair, `ζ_p(n,m) = ζ_p(m,n)`). Alors
`2·ζ_p(m,n) = 0`, et `p ≠ 2` conclut. C'est le théorème de la cellule
(b) du notebook — prouvé, pas seulement mesuré.
-/

section Derivation

private theorem deux_ne_zero_zmod {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  have hp2le : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  have hd : p ∣ (2 : ℕ) := (ZMod.natCast_eq_zero_iff 2 p).mp h
  have hple : p ≤ 2 := Nat.le_of_dvd two_pos hd
  omega

/-- **La dérivation** : pour `m + n ≤ p - 2` **pair** et `p ≠ 2`,
`ζ_p(m,n) = 0` — les poids pairs de profondeur 2 s'effacent dans la
couche `p` (notebook, cellule (b)). -/
theorem ombre_poids_pair (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hp2 : p ≠ 2) (hw : m + n ≤ p - 2) (hpar : Even (m + n)) :
    ombreZeta2 p m n = 0 := by
  -- 1. Mutisme de profondeur 1.
  have h0m : ombreZeta p m = 0 := ombreZeta_eq_zero hm (by omega)
  have h0n : ombreZeta p n = 0 := ombreZeta_eq_zero hn (by omega)
  have h0w : ombreZeta p (m + n) = 0 :=
    ombreZeta_eq_zero (Nat.add_pos_right m hn) (by omega)
  -- 2. Stuffle : ζ_p(m,n) + ζ_p(n,m) = 0.
  have hst : ombreZeta2 p m n + ombreZeta2 p n m = 0 := by
    have h := stuffle p m n
    rw [h0m, h0n, h0w] at h
    simpa using h.symm
  -- 3. Retournement, parité paire : (-1)^(m+n) = 1.
  have hmoinsun : (-1 : ZMod p) ^ (m + n) = 1 := by
    obtain ⟨k, hk⟩ := hpar
    rw [hk, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have hret : ombreZeta2 p n m = ombreZeta2 p m n := by
    have h := retournement p m n
    rw [hmoinsun, one_mul] at h
    exact h.symm
  -- 2·ζ_p(m,n) = 0 et 2 inversible : conclusion.
  have hdeux : (2 : ZMod p) * ombreZeta2 p m n = 0 := by
    linear_combination hst - hret
  exact (mul_eq_zero.mp hdeux).resolve_left (deux_ne_zero_zmod hp2)

end Derivation

end Serre100
