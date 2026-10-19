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

**Reporté à k4.2b** : la borne `shiftDist_cubeP_sq_le` de l'oracle
(`shiftDist (cubeP d N) h ^ 2 ≤ (∑ k, (h k / N) ^ 2) / 12`), qui consomme la
version « distribution » de l'inégalité de Hellinger (`tvDist_sq_le` chez
Dahia) — elle-même reportée par `Hellinger.lean` jusqu'à ce que ce module en
fixe l'appel — puis la chaîne `Cube` → `NearInvariant` (Lemme 1.5, brique
k4.3 : le transport du réseau entier vers la grille `N⁻¹ • ℤ^d`).

L'état détaillé vit dans `FORMAL_STATUS.md` (« Distillation
Karingula–Lovett, briques k1..k5 »).
-/

import Discrepancy.Komlos.Grid

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

/-! ## Note d'adaptation (brique k4.2a)

**Statut** : 9 briques closes — la **première moitié** du `Komlos/Cube.lean` de
l'oracle est portée. Le poids produit `d`-dimensionnel existe, son support est
une boîte, sa corrélation se factorise par coordonnée, et sa masse vaut `1`.

**Barrière d'encodage, franchie par la convention du lake.** L'oracle pose
`cubeP d N : (Fin d → ℤ) →₀ ℝ` (un `Finsupp` supporté par
`Fintype.piFinset (fun _ ↦ Icc (-(gridM N)) (gridM N))`) et écrit sa masse via
`IsDist`/`mass_eq_sum`. Ce lake n'a ni `IsDist` ni `Finsupp` dans sa chaîne
Komlos : le poids est une **fonction** et le support se **passe** (convention
`shiftDistance S P u` de k1.1). La perte est nulle — `sum_cubeF_sub_sq` est
l'énoncé de masse exact, sur un `Finset` quelconque contenant le support — et
le gain est que k4.2b pourra consommer `shiftDistance` tel quel, sans pont
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
  l'utilise telle quelle (`a = 0`, cas de la copie non translatée).

L'état détaillé vit dans `FORMAL_STATUS.md` (« Distillation Karingula–Lovett »).
-/

end Discrepancy.Komlos