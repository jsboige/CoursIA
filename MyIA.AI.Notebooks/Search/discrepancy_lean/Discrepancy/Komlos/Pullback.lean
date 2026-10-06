/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapté à `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979) : toolchain v4.33.0, Mathlib `db584cd6`, convention i18n #4980.

Le source Dahia original vit dans le dépôt `gdahia/Komlos` (module
`Komlos/Pullback.lean`, toolchain v4.34.0, cadre `Finsupp` sur `E →₀ ℝ`).
L'adaptation reprend le module **nom pour nom**, mais n'en livre d'abord que
la partie **sans convexité** — voir la portée ci-dessous.

**Portée de ce commit** (brique k2.1, `lake build SUCCESS` requis, 0 `sorry`) :

Le **pas de pullback** du Lemme 1.4 se décompose, chez Dahia, en trois lemmes :
`exists_sign_mul_add_eq` (arithmétique réelle), `add_smul_mem_convexHull`
(enveloppe convexe d'un segment) et `pullback` (le pas complet). Les deux
derniers **consomment `convexHull`**, que ce lake n'importe nulle part
(`convexHull` : 0 occurrence avant ce module). Cette brique livre donc les
**trois ingrédients qui n'en dépendent pas**, de sorte que la surface de
convexité s'ouvre ensuite sur une base déjà vérifiée :

- `exists_sign_mul_add_eq` — la **clé arithmétique** : pour `β ≥ 1/3` et
  `|a| ≤ 1 − β`, il existe une signe `e ∈ {±1}` et un coefficient `c` avec
  `|c| ≤ 1` tel que `c·β + a = e/3`. C'est ce qui produit le signe `ε` de la
  conclusion de k2 ;
- `segment_repr` — l'**identité de segment** : tout point `x + c·v` avec
  `|c| ≤ 1` s'écrit comme combinaison convexe de `x − v` et `x + v`, de poids
  `(1 − c)/2` et `(1 + c)/2`. C'est l'algèbre que `add_smul_mem_convexHull`
  enveloppe chez Dahia, mais **l'algèbre seule**, sans `convexHull` ;
- `sum_mul_add_split` — la **linéarité pondérée** consommée par le calcul de
  `pullback` : la somme `Σ R y · (h y · c + g y)` se scinde en
  `c · (Σ R y · h y) + Σ R y · g y`. C'est la seule manipulation de sommes
  du pas de pullback qui ne soit pas de la convexité.

**Reporté à k2.2** (surface de convexité) : `add_smul_mem_convexHull` et
`pullback` — les deux seuls lemmes du module Dahia qui exigent `convexHull ℝ`.
L'état détaillé vit dans `FORMAL_STATUS.md`.
-/

import Discrepancy.Basic

/-!
# Algèbre du pas de pullback (Lemme 1.4, Karingula–Lovett)

Le Lemme 1.4 conclut `μ(P) + Σ ε_i v_i ∈ conv(supp P)`. Son pas d'induction
scinde dans la direction du dernier vecteur, applique l'hypothèse d'induction
dans l'espace produit, puis **ramène** le point obtenu dans `conv(supp P)` :
c'est le *pullback*. Ce module livre l'algèbre de ce pas, indépendamment de
toute notion d'enveloppe convexe.

**Pourquoi séparer.** Ouvrir `convexHull` dans ce lake est un geste structurel
(première surface d'analyse convexe du lake) ; le mêler à de l'arithmétique
réelle et à de la manipulation de sommes rendrait le diagnostic d'un échec de
build ambigu. Livrés séparément, les trois lemmes ci-dessous sont vérifiables
**sans** `convexHull`, et la brique suivante n'apporte qu'un ingrédient
nouveau.

**Portée du résultat.** `exists_sign_mul_add_eq` est l'ingrédient qui produit
la **conclusion signée** : `e ∈ {±1}` est le signe `ε` de la conclusion de k2,
et la borne `|c| ≤ 1` est ce qui autorise la lecture de `x + c·v` comme point
du segment `[x − v, x + v]` — d'où `segment_repr`, qui rend cette lecture
explicite. Les deux lemmes sont énoncés sur `ℝ` (aucune base requise) ; seul
`segment_repr` demande un groupe abélien muni d'une structure de module réel,
i.e. le cadre minimal dans lequel l'énoncé a un sens.
-/

namespace Discrepancy.Komlos

/-- **Clé arithmétique du pullback.** Si `β ≥ 1/3` et `|a| ≤ 1 − β`, il existe
un signe `e ∈ {±1}` et un coefficient `c` tel que `|c| ≤ 1` et
`c * β + a = e / 3`.

C'est le lemme `exists_sign_mul_add_eq` de Dahia (`Komlos/Pullback.lean`),
transposé tel quel : l'énoncé ne porte que sur `ℝ`, aucune structure de base
n'est requise. Le signe `e` est le signe `ε` de la conclusion du Lemme 1.4 ;
la borne `|c| ≤ 1` est ce qui fait de `x + c • v` un point du segment
`[x − v, x + v]` (cf `segment_repr`).

Preuve : cas sur le signe de `a`. Pour `a ≥ 0`, on prend `e = 1` et
`c = (1/3 − a) / β` ; l'appartenance `|c| ≤ 1` se réduit à `|1/3 − a| ≤ β`,
que `linarith` ferme avec `hβ` et `|a| ≤ 1 − β`. Le cas `a < 0` est
symétrique avec `e = −1`. -/
lemma exists_sign_mul_add_eq {β a : ℝ} (hβ : 3⁻¹ ≤ β) (ha : |a| ≤ 1 - β) :
    ∃ e c : ℝ, (e = 1 ∨ e = -1) ∧ |c| ≤ 1 ∧ c * β + a = e / 3 := by
  have hβ0 : 0 < β := by linarith
  obtain ⟨ha₁, ha₂⟩ := abs_le.1 ha
  rcases le_total 0 a with h | h
  · refine ⟨1, (3⁻¹ - a) / β, by norm_num, ?_, by field_simp; ring⟩
    rw [abs_div, abs_of_pos hβ0, div_le_one hβ0, abs_le]
    constructor <;> linarith
  · refine ⟨-1, (-3⁻¹ - a) / β, by norm_num, ?_, by field_simp; ring⟩
    rw [abs_div, abs_of_pos hβ0, div_le_one hβ0, abs_le]
    constructor <;> linarith

/-- **Identité de segment.** Pour `|c| ≤ 1`, le point `x + c • v` est la
combinaison convexe de `x − v` et `x + v` de poids `(1 − c) / 2` et
`(1 + c) / 2` :

`((1 − c) / 2) • (x − v) + ((1 + c) / 2) • (x + v) = x + c • v`.

Les deux poids sont positifs et de somme 1 dès que `|c| ≤ 1` — précisément
l'hypothèse `hc` du lemme `add_smul_mem_convexHull` chez Dahia, qui enveloppe
cette identité dans `Convex.add_smul_sub_mem` **sans** la partie enveloppe
convexe (celle-ci reste à la brique k2.2).

Le sens des poids est celui de l'énoncé : `x − v` reçoit `(1 − c) / 2` et
`x + v` reçoit `(1 + c) / 2`, de sorte que le coefficient de `v` vaut
`−(1 − c)/2 + (1 + c)/2 = c`. Échanger les deux poids donne `x − c • v`, pas
`x + c • v` — l'erreur exacte commise et corrigée lors de la rédaction de ce
lemme, consignée ici parce qu'elle est facile à refaire.

Preuve : `module` (linéarité des `•` et distributivité sur `x ± v`). -/
lemma segment_repr {E : Type*} [AddCommGroup E] [Module ℝ E] (x v : E) (c : ℝ) :
    ((1 - c) / 2) • (x - v) + ((1 + c) / 2) • (x + v) = x + c • v := by
  module

/-- **Linéarité pondérée d'une somme.** Pour un `Finset` `T` et des fonctions
`R`, `h`, `g : ι → ℝ`,

`Σ y ∈ T, R y * (h y * c + g y) = c * (Σ y ∈ T, R y * h y) + Σ y ∈ T, R y * g y`.

C'est la manipulation de sommes du calcul de `pullback` chez Dahia —
`mul_sub`, `sum_sub_distrib`, `mul_sum` — extraite sous sa forme réutilisable.
Elle ne dépend ni de la base ni de la convexité.

Preuve : distributivité (`mul_add`), additivité de la somme
(`Finset.sum_add_distrib`), puis extraction du facteur constant `c`
(`Finset.mul_sum`) et commutativité. -/
lemma sum_mul_add_split {ι : Type*} (T : Finset ι) (R h g : ι → ℝ) (c : ℝ) :
    ∑ y ∈ T, R y * (h y * c + g y)
      = c * (∑ y ∈ T, R y * h y) + ∑ y ∈ T, R y * g y := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

end Discrepancy.Komlos
