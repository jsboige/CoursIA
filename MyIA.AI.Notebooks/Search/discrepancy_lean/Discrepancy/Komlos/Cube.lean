/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapté à `discrepancy_lean` (issue #17845, distillation Karingula–Lovett
arXiv:2609.20979) : toolchain v4.33.0, Mathlib `db584cd6`, convention i18n #4980.

Le source Dahia original vit dans le dépôt `gdahia/Komlos` (module
`Komlos/Cube.lean`, toolchain v4.34.0, cadre `Finsupp` sur `E → ₀ ℝ`).
L'adaptation suit la convention du lake (support `Finset` explicite, établie
par k1.1 `ShiftDistance.lean`) : le poids produit `cubeF d N` est une
**fonction** `(Fin d → ℤ) → ℝ` — comme `gridF` en dimension un —, son support
est une **boîte** décrite par `Fintype.piFinset`, et la masse se calcule sur
un `Finset` quelconque contenant le support translaté.

**Portée de ce commit** (brique k4.2a, `lake build SUCCESS` requis, 0 `sorry`) :

Briques closes : `cubeF`, `support_cubeF_sub_subset`, `support_cubeF_subset`,
`sum_cubeF_sub_mul_cubeF_sub` (la corrélation de deux translatés est le
produit des corrélations coordonnée par coordonnée),
`sum_cubeF_sub_sq` (masse `1` du poids produit, translaté ou non),
`sum_cubeF_sq`, `shiftBox`, `support_gridF_subset_shiftBox`,
`support_gridF_sub_subset_shiftBox`.

**Livré par k4.2b** : la borne `shiftDist_cubeP_sq_le` de l'oracle
(`shiftDist (cubeP d N) h ^ 2 ≤ (∑ k, (h k / N) ^ 2) / 12`), sous le nom
`shiftDistance_cubeF_sq_le`. Elle consomme la version « distribution » de
l'inégalité de Hellinger (`tvDist_sq_le` chez Dahia) — reportée par
`Hellinger.lean` jusqu'à ce que ce module en fixe l'appel — désormais livrée
par `Komlos/TvDistance.lean` (k4.2b, même commit). Reste la chaîne `Cube` →
`NearInvariant` (Lemme 1.5, brique k4.3 : le transport du réseau entier vers la
grille `N⁻¹ • ℤ^d`), qui attend `shiftDist_push` (seul reporté de k2.3).

L'état détaillé vit dans `FORMAL_STATUS.md` (« Distillation
Karingula–Lovett, briques k1..k5 »).
-/

import Discrepancy.Komlos.Grid
import Discrepancy.Komlos.TvDistance

/-!
# Poids produit sur le réseau entier (Lemme 1.5, Karingula–Lovett)

`cubeF d N g = ∏ k, gridF N (g k)` est le poids produit de `d` copies du
poids normalisé unidimensionnel `gridF N` (brique k3.2). Son carré est une
probabilité sur `ℤ^d` — masse totale `1`, calculée sur tout `Finset` contenant
le support translaté — et son support est contenu dans la boîte
`[-6N, 6N]^d`.

C'est l'objet que le Lemme 1.5 transporte vers la grille `N⁻¹ • ℤ^d` par
l'application coordonnée par coordonnée `g ↦ g / N`.
-/

namespace Discrepancy.Komlos

open Finset

/-- Le poids produit `d`-dimensionnel sur le réseau entier : le produit des
`d` coordonnées du poids normalisé unidimensionnel `gridF N`. -/
noncomputable def cubeF (d N : ℕ) (g : Fin d → ℤ) : ℝ := ∏ k, gridF N (g k)

/-- Le support d'un **translaté** de `cubeF` est inclus dans la boîte `K^d`,
dès que `K` contient le support de chaque `gridF N (· - a k)`. -/
lemma support_cubeF_sub_subset {d N : ℕ} {a : Fin d → ℤ} {K : Finset ℤ}
    (hK : ∀ k, Function.support (fun j ↦ gridF N (j - a k)) ⊆ K) :
    Function.support (fun g ↦ cubeF d N (g - a)) ⊆
      (Fintype.piFinset fun _ : Fin d ↦ K : Set (Fin d → ℤ)) := by
  intro g hg
  rw [mem_coe, Fintype.mem_piFinset]
  intro k
  exact hK k (prod_ne_zero_iff.1 hg k (mem_univ k))

/-- Le support de `cubeF` est inclus dans la boîte `K^d`, dès que `K`
contient le support de `gridF N`. -/
lemma support_cubeF_subset {d N : ℕ} {K : Finset ℤ} (hK : Function.support (gridF N) ⊆ K) :
    Function.support (cubeF d N) ⊆
      (Fintype.piFinset fun _ : Fin d ↦ K : Set (Fin d → ℤ)) := by
  intro g hg
  refine support_cubeF_sub_subset (N := N) (a := 0) ?_ ?_
  · intro k
    simpa only [Pi.zero_apply, sub_zero] using hK
  · simpa only [sub_zero] using hg

/-- La corrélation de deux translatés de `cubeF` — produit scalaire non
normalisé — est le produit de leurs corrélations coordonnée par coordonnée.
C'est la factorisation sur laquelle la borne `L²` de la brique k4.2b
s'appuiera : chaque coordonnée se traite indépendamment. -/
lemma sum_cubeF_sub_mul_cubeF_sub (d N : ℕ) (K : Finset ℤ) (a b : Fin d → ℤ) :
    ∑ g ∈ Fintype.piFinset (fun _ : Fin d ↦ K),
        cubeF d N (g - a) * cubeF d N (g - b)
      = ∏ k, ∑ j ∈ K, gridF N (j - a k) * gridF N (j - b k) := by
  simp [Finset.prod_univ_sum, cubeF, Finset.prod_mul_distrib]

/-- Le carré du translaté de `cubeF` par `a` est de masse totale `1` — la
mesure produit est une probabilité. La somme est calculée sur tout `Finset`
contenant le support du translaté. -/
lemma sum_cubeF_sub_sq {d N : ℕ} (hN : 0 < N) (a : Fin d → ℤ) {K : Finset ℤ}
    (hK : ∀ k, Function.support (fun j ↦ gridF N (j - a k)) ⊆ K) :
    ∑ g ∈ Fintype.piFinset (fun _ : Fin d ↦ K), cubeF d N (g - a) ^ 2 = 1 := by
  simp_rw [sq, sum_cubeF_sub_mul_cubeF_sub, ← sq, sum_gridF_sub_sq hN _ (hK _),
    prod_const_one]

/-- Le carré de `cubeF` est de masse totale `1`, sans translation. -/
lemma sum_cubeF_sq {d N : ℕ} (hN : 0 < N) {K : Finset ℤ}
    (hK : Function.support (gridF N) ⊆ K) :
    ∑ g ∈ Fintype.piFinset (fun _ : Fin d ↦ K), cubeF d N g ^ 2 = 1 := by
  simpa only [sub_zero] using
    sum_cubeF_sub_sq (d := d) (N := N) hN (0 : Fin d → ℤ) (K := K)
      (fun _ ↦ by simpa only [Pi.zero_apply, sub_zero] using hK)

/-- Un `Finset` contenant le support de `gridF N` **et** celui de tous ses
translatés par les `h k` — la boîte de travail de la brique k4.2b. -/
noncomputable def shiftBox {d : ℕ} (N : ℕ) (h : Fin d → ℤ) : Finset ℤ :=
  Icc (-(gridM N : ℤ)) (gridM N) ∪
    univ.biUnion fun k ↦
      (Icc (-(gridM N : ℤ)) (gridM N)).map (Equiv.addRight (h k)).toEmbedding

/-- Le support de `gridF N` est inclus dans la boîte de travail `shiftBox`. -/
lemma support_gridF_subset_shiftBox {d : ℕ} (N : ℕ) (h : Fin d → ℤ) :
    Function.support (gridF N) ⊆ shiftBox N h :=
  (support_gridF_subset N).trans (by simp [shiftBox])

/-- Le support de chaque translaté `gridF N (· - h k)` est inclus dans la
boîte de travail `shiftBox`. -/
lemma support_gridF_sub_subset_shiftBox {d : ℕ} (N : ℕ) (h : Fin d → ℤ) (k : Fin d) :
    Function.support (fun j ↦ gridF N (j - h k)) ⊆ shiftBox N h := by
  intro j hj
  simp only [shiftBox, coe_union, coe_biUnion, coe_map, Set.mem_union, Set.mem_iUnion]
  right
  exact ⟨k, mem_coe.2 (mem_univ k), j - h k, support_gridF_subset N hj, by simp⟩

/-- Le carré du décalage du poids produit `cubeF d N ^ 2` est au plus
`(Σ k, ((h k) / N) ^ 2) / 12`.

C'est le `shiftDist_cubeP_sq_le` de l'oracle — la **dernière** brique de la
boute k4.2 : la variation totale entre la distribution produit et son translaté
est quadratiquement petite, ce qui est exactement la forme que le Lemme 1.5
(k4.3) transporte ensuite sur la grille `N⁻¹ • ℤ^d`.

`h` est le décalage du **poids** (le translaté est `cubeF d N (· - h)`), donc
le décalage correspondant de `shiftDistance` est `-h` (convention
`½ · Σ |P (x + u) − P x|` de k1.1). Le décalage nul est le cas `h = 0`.

Le `Finset` sur lequel `shiftDistance` somme est la **boîte**
`(shiftBox N h)^d` (`Fintype.piFinset`) : c'est l'analogue explicite du
support que l'oracle laisse implicite — `shiftDist` somme sur le support de
`cubeP - tr h cubeP`, qui est inclus dans cette boîte
(`support_cubeF_sub_subset`, k4.2a).

Preuve : `tvDistance_sq_le` (k4.2b) ramène la variation totale à la distance
`L²` entre les poids, `sum_cubeF_sub_mul_cubeF_sub` (k4.2a) factorise la
corrélation par coordonnée, `one_sub_sum_le_prod` (k4.1, Weierstrass) convertit
la borne additive en borne sur le produit, et `sum_gridF_sub_sq_le` (k3.2)
fournit la borne unidimensionnelle. -/
lemma shiftDistance_cubeF_sq_le {d N : ℕ} (hN : 0 < N) (h : Fin d → ℤ) :
    shiftDistance (Fintype.piFinset fun _ : Fin d ↦ shiftBox N h)
      (fun g ↦ cubeF d N g ^ 2) (-h) ^ 2
      ≤ (∑ k, ((h k : ℝ) / N) ^ 2) / 12 := by
  set K := shiftBox N h
  set A : Fin d → ℝ := fun k ↦ ∑ j ∈ K, gridF N j * gridF N (j - h k)
  have hp : ∑ g ∈ Fintype.piFinset (fun _ ↦ K), cubeF d N (g - 0) ^ 2 = 1 :=
    sum_cubeF_sub_sq hN 0 (fun k ↦ by
      simpa only [Pi.zero_apply, sub_zero] using support_gridF_subset_shiftBox N h)
  have hq : ∑ g ∈ Fintype.piFinset (fun _ ↦ K), cubeF d N (g - h) ^ 2 = 1 :=
    sum_cubeF_sub_sq hN h (support_gridF_sub_subset_shiftBox N h)
  rw [shiftDistance_eq_tvDistance, tvDistance_comm]
  refine (tvDistance_sq_le (s := Fintype.piFinset (fun _ ↦ K))
    (p := fun g ↦ cubeF d N (g - 0)) (q := fun g ↦ cubeF d N (g - h))
    ?_ ?_ hp hq).trans ?_
  · intro g _
    simp only [sub_zero]
  · intro g _
    simp only [sub_eq_add_neg]
  · rw [sum_sub_sq_eq hp hq, sum_cubeF_sub_mul_cubeF_sub]
    simp only [Pi.zero_apply, sub_zero]
    refine le_trans (b := ∑ k, 2 * (1 - A k)) ?_ ?_
    · suffices 1 - ∏ k, A k ≤ ∑ k, (1 - A k) by
        simpa only [Finset.mul_sum, mul_sub, mul_one] using
          mul_le_mul_of_nonneg_left this (by norm_num : (0 : ℝ) ≤ 2)
      rw [sub_le_comm]
      refine (one_sub_sum_le_prod univ (fun k ↦ 1 - A k) ?_ ?_).trans_eq ?_
      · intro k _
        apply sub_nonneg.mpr
        apply (Real.sum_mul_le_sqrt_mul_sqrt K (gridF N) (fun j ↦ gridF N (j - h k))).trans
        rw [sum_gridF_sq hN (support_gridF_subset_shiftBox N h),
          sum_gridF_sub_sq hN (h k) (support_gridF_sub_subset_shiftBox N h k),
          Real.sqrt_one, mul_one]
      · intro k _
        exact sub_le_self _ (sum_nonneg fun j _ ↦
          mul_nonneg (gridF_nonneg N j) (gridF_nonneg N (j - h k)))
      · simp only [sub_sub_cancel]
    · rw [sum_div]
      refine sum_le_sum ?_
      intro k _
      rw [mul_sub, mul_one, ← sum_sub_sq_eq
        (sum_gridF_sq hN (support_gridF_subset_shiftBox N h))
        (sum_gridF_sub_sq hN (h k) (support_gridF_sub_subset_shiftBox N h k))]
      simpa only [div_pow, div_div, mul_comm (12 : ℝ)] using
        sum_gridF_sub_sq_le hN (h k) K

/-! ## Note d'adaptation (brique k4.2)

**Statut** : 10 briques closes — le `Komlos/Cube.lean` de l'oracle est porté
**en intégralité**. Le poids produit `d`-dimensionnel existe, son support est
une boîte, sa corrélation se factorise par coordonnée, sa masse vaut `1`, et
son décalage est quadratiquement petit (`shiftDistance_cubeF_sq_le`, la
deuxième moitié de la boute, livrée par k4.2b).

**Barrière d'encodage, franchie par la convention du lake.** L'oracle pose
`cubeP d N : (Fin d → ℤ) →₀ ℝ` (un `Finsupp` supporté par
`Fintype.piFinset (fun _ ↦ Icc (-(gridM N)) (gridM N))`) et écrit sa masse via
`IsDist`/`mass_eq_sum`. Ce lake n'a ni `IsDist` ni `Finsupp` dans sa chaîne
Komlos : le poids est une **fonction** et le support se **passe** (convention
`shiftDistance S P u` de k1.1). La perte est nulle — `sum_cubeF_sub_sq` est
l'énoncé de masse exact, sur un `Finset` quelconque contenant le support — et
le gain est que k4.2b consomme `shiftDistance` tel quel, sans pont
`Finsupp → Finset`.

**Portage v4.34 → v4.33.0, preuve par preuve** :

- Syntaxe de modules v4.34 (`module`, `public import`, `@[expose] public
  section`) retirée — imports Lean 4 classiques.
- `support_cubeF_sub_subset`, `support_cubeF_subset`,
  `sum_cubeF_sub_mul_cubeF_sub`, `sum_cubeF_sub_sq` : port verbatim de
  l'oracle (`prod_ne_zero_iff`, `Fintype.mem_piFinset`,
  `Finset.prod_univ_sum`, `Finset.prod_mul_distrib`, `prod_const_one`), la
  seule substitution systématique étant `Finsupp.onFinset` → `Finset` explicite.
- `shiftBox` : le `noncomputable` de l'oracle est conservé (l'union indexée
  passe par `Fintype`/`DecidableEq` sur `Fin d`).
- `sum_cubeF_sq` n'a pas d'équivalent chez l'oracle : c'est la forme
  « sans translation » de `sum_cubeF_sub_sq`, écrite ici parce que k4.2b
  l'utilise (`a = 0`, cas de la copie non translatée).
- `shiftDistance_cubeF_sq_le` (k4.2b) : port de `shiftDist_cubeP_sq_le`. Deux
  écarts seulement, tous deux **par disparition** — l'oracle passe six
  arguments à `tvDist_sq_le` (deux hypothèses de support `hPs`/`hQs` puis
  `hP`, `hQ`, `hp`, `hq`), ce module quatre (les deux hypothèses de support
  sont absorbées par la somme explicite sur `Fintype.piFinset K`) ; et le
  décalage s'écrit `-h` là où `shiftDist (cubeP d N) h` porte `h` dans son
  argument, l'orientation `P (· + u) − P` de `shiftDistance` (k1.1) étant
  inverse de celle de `tr h P`. Le corps de preuve est verbatim.

L'état détaillé vit dans `FORMAL_STATUS.md` (« Distillation Karingula–Lovett »).
-/

end Discrepancy.Komlos