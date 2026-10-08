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

**Portée de ce commit** (briques k2.1 puis k2.2, `lake build SUCCESS` requis, 0 `sorry`) :

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

**Brique k2.2 (surface de convexité)** — `convexHull` entre dans ce lake
(0 occurrence avant ce commit) par les deux lemmes génériques que le pas de
`pullback` consomme :

- `add_smul_mem_convexHull` — le point `x + c • v` du segment `[x − v, x + v]`
  appartient à l'enveloppe convexe de tout ensemble contenant les deux
  extrémités. Transposé **verbatim** de Dahia (`Komlos/Pullback.lean`,
  l.43-50) : l'énoncé ne dépend que de la structure de `ℝ`-module de `E` ;
- `sum_smul_mem_convexHull` — l'étape de clôture du pas (`Convex.sum_mem`
  appliqué à `convex_convexHull`, l.83 chez Dahia) : une combinaison convexe
  finie de points d'une enveloppe reste dans l'enveloppe.

**`pullback` reste reporté, et son bloqueur est désormais mesuré** : chez
Dahia il s'énonce sur `E →₀ ℝ` avec `E` un `ℝ`-module, l'enveloppe étant
prise dans `convexHull ℝ (P.support : Set E)`. La base de ce lake est
`Fin d → ℤ`, qui **n'est pas** un `ℝ`-module — `convexHull ℝ` n'y a pas de
sens sans plongement coordonnée-par-coordonnée dans `Fin d → ℝ` (le
« transport de dimension » de `FORMAL_STATUS.md`). L'état détaillé vit dans
`FORMAL_STATUS.md`.
-/

import Discrepancy.Basic

/-!
# Algèbre du pas de pullback (Lemme 1.4, Karingula–Lovett)

Le Lemme 1.4 conclut `μ(P) + Σ ε_i v_i ∈ conv(supp P)`. Son pas d'induction
scinde dans la direction du dernier vecteur, applique l'hypothèse d'induction
dans l'espace produit, puis **ramène** le point obtenu dans `conv(supp P)` :
c'est le *pullback*. Ce module livre l'algèbre de ce pas (k2.1), puis la
surface de convexité qu'elle enveloppe (k2.2) — les deux **génériques**, le
pas complet restant conditionné au transport de dimension.

**Pourquoi séparer.** Ouvrir `convexHull` dans ce lake est un geste structurel
(première surface d'analyse convexe du lake) ; le mêler à de l'arithmétique
réelle et à de la manipulation de sommes rendrait le diagnostic d'un échec de
build ambigu. Livrés séparément, les trois lemmes de k2.1 sont vérifiables
**sans** `convexHull` — et c'est sur ce socle vérifié que la brique k2.2 a
ouvert la surface : un échec de build sur les lemmes de convexité ne peut plus
venir que d'eux.

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

/-- **Point d'un segment dans une enveloppe convexe.** Pour `|c| ≤ 1`, le point
`x + c • v` appartient à l'enveloppe convexe de tout ensemble `s` contenant
les deux extrémités `x − v` et `x + v`.

C'est le lemme `add_smul_mem_convexHull` de Dahia (`Komlos/Pullback.lean`,
l.43-50), transposé **verbatim** : l'énoncé ne dépend que de la structure de
`ℝ`-module de `E`. C'est la **première occurrence de `convexHull` dans ce
lake** — la surface d'analyse convexe s'ouvre sur la base déjà vérifiée de
k2.1 : la borne `|c| ≤ 1` est celle que produit `exists_sign_mul_add_eq`, et
`segment_repr` est l'identité de segment que ce lemme enveloppe.

Preuve : `x + c • v` est la combinaison convexe de `x − v` (poids `(1 − c)/2`)
et `x + v` (poids `(1 + c)/2`) ; `Convex.add_smul_sub_mem` (Mathlib
`Analysis.Convex.Basic:492`) la produit pour le paramètre `t = (1 + c)/2`, les
deux bornes `0 ≤ t ≤ 1` tombant de `|c| ≤ 1` par `linarith` ; `convert … using
1` puis `module` referment l'identité algébrique résiduelle — le même argument
que `segment_repr`. -/
lemma add_smul_mem_convexHull {E : Type*} [AddCommGroup E] [Module ℝ E]
    {s : Set E} {x v : E} (h₁ : x - v ∈ s) (h₂ : x + v ∈ s) {c : ℝ}
    (hc : |c| ≤ 1) : x + c • v ∈ convexHull ℝ s := by
  obtain ⟨hc₁, hc₂⟩ := abs_le.1 hc
  convert (convex_convexHull ℝ s).add_smul_sub_mem (subset_convexHull ℝ s h₁)
    (subset_convexHull ℝ s h₂) (t := (1 + c) / 2) ⟨by linarith, by linarith⟩ using 1
  module

/-- **Combinaison convexe finie de points d'une enveloppe.** Si `R` est une
famille de poids positive de somme `1` sur un `Finset` `T`, et si chaque point
`f y` (pour `y ∈ T`) appartient à `convexHull ℝ s`, alors la combinaison
convexe `∑ y ∈ T, R y • f y` appartient à `convexHull ℝ s`.

C'est l'étape de clôture du pas de `pullback` chez Dahia
(`(convex_convexHull ℝ _).sum_mem hR0 hR1`, l.83), extraite sous la forme
`Finset` du lake : c'est ce qui referme la preuve du pas une fois chaque point
de la somme ramené dans l'enveloppe. Énoncé générique ; la décomposition
inverse — lire une appartenance à l'enveloppe comme des poids — existe déjà au
pin de ce lake sous le nom `Finset.centerMass_mem_convexHull` (Mathlib
`Analysis.Convex.Combination:253`).

Preuve : `Convex.sum_mem` (Mathlib `Analysis.Convex.Combination:214`) appliqué
à `convex_convexHull ℝ s` — l'enveloppe convexe est convexe, et une combinaison
convexe de points d'un convexe reste dans le convexe. -/
lemma sum_smul_mem_convexHull {E : Type*} [AddCommGroup E] [Module ℝ E]
    {s : Set E} {ι : Type*} (T : Finset ι) (R : ι → ℝ) (f : ι → E)
    (hR0 : ∀ y ∈ T, 0 ≤ R y) (hR1 : ∑ y ∈ T, R y = 1)
    (hmem : ∀ y ∈ T, f y ∈ convexHull ℝ s) :
    ∑ y ∈ T, R y • f y ∈ convexHull ℝ s :=
  (convex_convexHull ℝ s).sum_mem hR0 hR1 hmem

end Discrepancy.Komlos
