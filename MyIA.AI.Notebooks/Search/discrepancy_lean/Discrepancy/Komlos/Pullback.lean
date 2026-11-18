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

**Brique k2.4 (le pas complet)** — `pullback` livré dans le cadre du lake,
sur le transport de dimension k2.3 qui a levé le bloqueur mesuré en k2.2 :

- `toRealProd` + `toRealProd_injective` — l'embedding **produit** : la
  grille entière × hauteur `Bool` dans la grille réelle × `ℝ` (la hauteur
  `false ↦ 0`, `true ↦ 1` — c'est là que la hauteur du lake, un `Bool`,
  devient la coordonnée réelle `(y, β)` de l'oracle) ;
- `split_apply_zero_ne_iff` / `split_apply_one_ne_iff` — les
  **caractérisations de support** de la scission sous `P ≥ 0`, lues point
  par point (l'oracle les a gratuitement via `Finsupp.support` :
  `mk_zero_mem_support_split` / `mk_one_mem_support_split` ; le cadre Finset
  explicite du lake les exige comme hypothèses d'exactitude sur le support
  `SQ` passé) ;
- `pullback` — **le pas complet** : si `(z, β)` est dans l'enveloppe du
  support transporté de `split v P` avec `v = 3·w` coordonnée par
  coordonnée et `β ≥ 1/3`, un signe `e ∈ {±1}` ramène `z + e • toReal w`
  dans l'enveloppe du support transporté de `P`. Transposé de
  `Komlos/Pullback.lean` l.55-92, les trois ingrédients livrés en k2.1/k2.2
  (`exists_sign_mul_add_eq`, `add_smul_mem_convexHull`,
  `sum_smul_mem_convexHull`) et les ponts k2.3 (`toReal_mem_map_iff`)
  étant consommés nommément.

L'état détaillé vit dans `FORMAL_STATUS.md`.
-/

import Discrepancy.Basic
import Discrepancy.Komlos.Split
import Discrepancy.Komlos.Transport

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

/-! ### Brique k2.4 : l'embedding produit et les caractérisations de support

Le pas complet de `pullback` exige deux ingrédients de cadre que k2.1-k2.3
n'ont pas encore rencontrés : l'embedding **produit** (grille × hauteur →
grille réelle × `ℝ`, là où la hauteur `Bool` devient la coordonnée `β` de
l'oracle) et les caractérisations de **support** de la scission (que
l'oracle obtient gratuitement via `Finsupp.support` et que le cadre Finset
explicite du lake doit énoncer comme hypothèses). -/

/-- **Embedding produit.** La grille entière munie de sa hauteur `Bool` se
plonge dans la grille réelle × `ℝ` : la composante spatiale par `toReal`
(le transport de dimension de la brique k2.3), la hauteur `false ↦ 0`,
`true ↦ 1`.

C'est ce plongement qui fait de la hauteur du lake — un `Bool` — la
coordonnée réelle `(y, β)` de l'oracle : l'enveloppe de la conclusion du
`pullback` oracle vit dans `E × ℝ`, et c'est dans `(Fin d → ℝ) × ℝ` que le
lake la rejoint.

L'injectivité est le papier de l'`Finset.map` du support transporté : sans
elle, `SQ.map toRealProdEmb` pourrait contracter des points et l'hypothèse
d'exactitude `hSQ` du théorème `pullback` perdrait des informations. La
composante spatiale est injective par `toReal_injective` (k2.3) ; la
composante hauteur sépare `false` de `true` par `0 ≠ 1`. -/
def toRealProd {d : ℕ} : ((Fin d → ℤ) × Bool) → ((Fin d → ℝ) × ℝ) :=
  fun y => (toReal y.1, if y.2 then (1 : ℝ) else 0)

lemma toRealProd_injective {d : ℕ} : Function.Injective (toRealProd (d := d)) := by
  rintro ⟨x₁, b₁⟩ ⟨x₂, b₂⟩ h
  simp only [toRealProd, Prod.mk.injEq] at h
  obtain ⟨hxe, hbe⟩ := h
  cases b₁ <;> cases b₂ <;> simp_all [toReal_injective.eq_iff]

/-- La version `Finset.Embedding` de `toRealProd`, pour les `Finset.map`
des supports transportés. -/
def toRealProdEmb {d : ℕ} : ((Fin d → ℤ) × Bool) ↪ ((Fin d → ℝ) × ℝ) :=
  ⟨toRealProd, toRealProd_injective⟩

/-- **Hauteur d'un point du support transporté.** Tout point de l'image
`SQ.map toRealProdEmb` porte une hauteur dans `{0, 1}` — la traduction
finie de `snd_eq_zero_or_one_of_mem_support_split` chez l'oracle. -/
lemma mem_map_toRealProd_snd {d : ℕ} {y : (Fin d → ℝ) × ℝ}
    {SQ : Finset ((Fin d → ℤ) × Bool)} (hy : y ∈ SQ.map toRealProdEmb) :
    y.2 = 0 ∨ y.2 = 1 := by
  rw [Finset.mem_map] at hy
  obtain ⟨y', -, hye⟩ := hy
  have h2 : (if y'.2 then (1 : ℝ) else 0) = y.2 := congrArg Prod.snd hye
  cases b : y'.2 <;> rw [b] at h2 <;> simp_all

/-- **Caractérisation du support, tranche basse.** Sous `P ≥ 0`, la tranche
`false` de la scission porte une masse non nulle exactement quand l'une des
deux translatées `P (x ± v)` est non nulle.

C'est la lecture point-par-point de `mk_zero_mem_support_split` chez
l'oracle (`(x, 0) ∈ (split v P).support ↔ x + v ∈ P.support ∨ x - v ∈
P.support`) : le cadre `Finsupp` de l'oracle la donne via le support, le
cadre Finset explicite du lake l'énonce sur la valeur. Sous `P ≥ 0`,
`½ · max a b ≠ 0` équivaut à `a ≠ 0 ∨ b ≠ 0` : c'est la positivité qui fait
traverser le `max`. -/
lemma split_apply_zero_ne_iff {d : ℕ} {P : (Fin d → ℤ) → ℝ} (hP : ∀ x, 0 ≤ P x)
    (v x : Fin d → ℤ) :
    split v P (x, false) ≠ 0 ↔ P (x + v) ≠ 0 ∨ P (x - v) ≠ 0 := by
  rw [split_apply_zero]
  constructor
  · intro h
    by_contra hcon
    obtain ⟨h1, h2⟩ := not_or.mp hcon
    rw [not_not.mp h1, not_not.mp h2, max_self] at h
    norm_num at h
  · rintro (h | h)
    · intro hcon
      have hlt : (0 : ℝ) < P (x + v) := lt_of_le_of_ne (hP _) (Ne.symm h)
      exact absurd hcon (ne_of_gt (mul_pos one_half_pos
        (lt_of_lt_of_le hlt (le_max_left _ _))))
    · intro hcon
      have hlt : (0 : ℝ) < P (x - v) := lt_of_le_of_ne (hP _) (Ne.symm h)
      exact absurd hcon (ne_of_gt (mul_pos one_half_pos
        (lt_of_lt_of_le hlt (le_max_right _ _))))

/-- **Caractérisation du support, tranche haute.** Sous `P ≥ 0`, la tranche
`true` de la scission porte une masse non nulle exactement quand les deux
translatées `P (x ± v)` sont non nulles — le `min` exige la conjonction,
là où le `max` de la tranche basse exige la disjonction.

Lecture point-par-point de `mk_one_mem_support_split` chez l'oracle
(`(x, 1) ∈ (split v P).support ↔ x + v ∈ P.support ∧ x - v ∈ P.support`). -/
lemma split_apply_one_ne_iff {d : ℕ} {P : (Fin d → ℤ) → ℝ} (hP : ∀ x, 0 ≤ P x)
    (v x : Fin d → ℤ) :
    split v P (x, true) ≠ 0 ↔ P (x + v) ≠ 0 ∧ P (x - v) ≠ 0 := by
  rw [split_apply_one]
  constructor
  · intro hcon
    constructor
    · intro hzero
      apply hcon
      rw [hzero, min_eq_left (hP (x - v)), mul_zero]
    · intro hzero
      apply hcon
      rw [hzero, min_eq_right (hP (x + v)), mul_zero]
  · rintro ⟨h, h'⟩
    have hlt : (0 : ℝ) < P (x + v) := lt_of_le_of_ne (hP _) (Ne.symm h)
    have hlt' : (0 : ℝ) < P (x - v) := lt_of_le_of_ne (hP _) (Ne.symm h')
    exact ne_of_gt (mul_pos one_half_pos (lt_min hlt hlt'))

/-! ### Brique k2.4 : le pas complet -/

/-- **Le pas de pullback (Lemme 1.4).** Si la distribution `P` sur la
grille entière est non négative, de support contenu dans `SP`, et si
`(z, β)` appartient à l'enveloppe convexe du support **transporté** de la
scission `split v P` — transporté par l'embedding produit `toRealProd` —
avec `v = 3 · w` coordonnée par coordonnée et `β ≥ 1/3`, alors un signe
`e ∈ {±1}` ramène `z + e • toReal w` dans l'enveloppe convexe du support
transporté de `P`.

C'est la transposition du théorème `pullback` de Dahia
(`Komlos/Pullback.lean`, l.55-92) au cadre du lake. Trois écarts de cadre
sont arbitrés :

- **le point `z` vit côté `ℝ`** : chez l'oracle, l'hypothèse d'induction
  produit un point de `E × ℝ` quelconque dans l'enveloppe ; ici le
  consommateur final (le Lemme 1.4) produit un barycentre côté grille
  réelle, d'où `z : Fin d → ℝ` et l'hypothèse sur l'enveloppe **dans
  l'image transportée**, pas dans la grille entière ;
- **`hSQ` est une hypothèse, pas un calcul** : chez l'oracle le support
  `(split v P).support` est calculé (`mk_zero_mem_support_split`) ; le
  cadre Finset explicite du lake exige de connaître le support `SQ` de la
  scission et son exactitude (`∀ y ∈ SQ, split v P y ≠ 0`) — c'est la
  contrepartie de l'absence de `Finsupp` ;
- **`hPsupp` relaie le support de `P`** : de même, `SP` doit contenir le
  support de `P` pour que les extrémités des segments y atterrissent.

La preuve est celle de l'oracle, décomposée sur les ingrédients livrés en
k2.1-k2.3 : `Finset.mem_convexHull'` décompose l'appartenance de `(z, β)`
en poids `R` ; `abs_sum_le_sum_abs` borne la part des poids hauteurs `0` ;
`exists_sign_mul_add_eq` (k2.1) produit le signe `e` et le coefficient
`c` ; chaque point de la combinaison est ramené dans l'enveloppe du
support transporté de `P` par `add_smul_mem_convexHull` (k2.2, tranches
hautes) ou par l'appartenance directe d'une extrémité (tranches basses,
via `toReal_mem_map_iff` de k2.3) ; `sum_smul_mem_convexHull` (k2.2)
referme. -/
theorem pullback {d : ℕ} {P : (Fin d → ℤ) → ℝ} (hP : ∀ x, 0 ≤ P x)
    {SP : Finset (Fin d → ℤ)} (hPsupp : ∀ x, P x ≠ 0 → x ∈ SP)
    {v w : Fin d → ℤ} (hv : ∀ i, v i = 3 * w i)
    {SQ : Finset ((Fin d → ℤ) × Bool)} (hSQ : ∀ y ∈ SQ, split v P y ≠ 0)
    {β : ℝ} (hβ : 3⁻¹ ≤ β) {z : Fin d → ℝ}
    (hmem : (z, β) ∈ convexHull ℝ
      (↑(SQ.map toRealProdEmb) : Set ((Fin d → ℝ) × ℝ))) :
    ∃ e : ℝ, (e = 1 ∨ e = -1) ∧
      z + e • toReal w ∈ convexHull ℝ
        (↑(SP.map ⟨⇑toReal, toReal_injective⟩) : Set (Fin d → ℝ)) := by
  classical
  -- la direction du transport : toReal v = 3 • toReal w
  have hvR : toReal v = (3 : ℝ) • toReal w := by
    funext i
    simp only [toReal_apply, hv i, Int.cast_mul, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  -- décomposition de l'appartenance en poids
  obtain ⟨R, hR0, hR1, hRc⟩ := Finset.mem_convexHull'.1 hmem
  have hz : ∑ y ∈ SQ.map toRealProdEmb, R y • y.1 = z := by
    have h := congrArg Prod.fst hRc
    rw [Prod.fst_sum] at h
    exact h
  have hb : ∑ y ∈ SQ.map toRealProdEmb, R y * y.2 = β := by
    have h := congrArg Prod.snd hRc
    rw [Prod.snd_sum] at h
    exact h
  -- les hauteurs du support transporté sont dans {0, 1}
  have hsnd : ∀ y ∈ SQ.map toRealProdEmb, y.2 = 0 ∨ y.2 = 1 :=
    fun y hy => mem_map_toRealProd_snd hy
  -- chaque point du support transporté provient d'un point de SQ
  have hpre : ∀ y ∈ SQ.map toRealProdEmb, ∃ y' ∈ SQ, toRealProd y' = y := by
    intro y hy
    rw [Finset.mem_map] at hy
    obtain ⟨y', hy', hye⟩ := hy
    exact ⟨y', hy', hye⟩
  -- les extrémités des tranches basses atterrissent dans le support de P
  have hfalse : ∀ y ∈ SQ.map toRealProdEmb, y.2 = 0 →
      y.1 + toReal v ∈ (SP.map ⟨⇑toReal, toReal_injective⟩ : Finset (Fin d → ℝ)) ∨
      y.1 - toReal v ∈ (SP.map ⟨⇑toReal, toReal_injective⟩ : Finset (Fin d → ℝ)) := by
    intro y hy y0
    obtain ⟨y', hy', hye⟩ := hpre y hy
    obtain ⟨x', b'⟩ := y'
    cases b' with
    | false =>
      have hx := (split_apply_zero_ne_iff hP v x').1 (hSQ (x', false) hy')
      have hy1 : toReal x' = y.1 := congrArg Prod.fst hye
      rcases hx with h | h
      · left
        have hmem' := (toReal_mem_map_iff (x' + v) SP).2 (hPsupp _ h)
        rwa [map_add, hy1] at hmem'
      · right
        have hmem' := (toReal_mem_map_iff (x' - v) SP).2 (hPsupp _ h)
        rwa [map_sub, hy1] at hmem'
    | true =>
      exfalso
      have h1 : y.2 = 1 := by
        have := congrArg Prod.snd hye
        simpa [toRealProd] using this.symm
      rw [y0] at h1
      norm_num at h1
  -- les extrémités des tranches hautes atterrissent dans le support de P
  have htrue : ∀ y ∈ SQ.map toRealProdEmb, y.2 = 1 →
      y.1 + toReal v ∈ (SP.map ⟨⇑toReal, toReal_injective⟩ : Finset (Fin d → ℝ)) ∧
      y.1 - toReal v ∈ (SP.map ⟨⇑toReal, toReal_injective⟩ : Finset (Fin d → ℝ)) := by
    intro y hy y1
    obtain ⟨y', hy', hye⟩ := hpre y hy
    obtain ⟨x', b'⟩ := y'
    cases b' with
    | true =>
      obtain ⟨h, h'⟩ := (split_apply_one_ne_iff hP v x').1 (hSQ (x', true) hy')
      have hy1 : toReal x' = y.1 := congrArg Prod.fst hye
      constructor
      · have hmem' := (toReal_mem_map_iff (x' + v) SP).2 (hPsupp _ h)
        rwa [map_add, hy1] at hmem'
      · have hmem' := (toReal_mem_map_iff (x' - v) SP).2 (hPsupp _ h')
        rwa [map_sub, hy1] at hmem'
    | false =>
      exfalso
      have h0 : y.2 = 0 := by
        have := congrArg Prod.snd hye
        simpa [toRealProd] using this.symm
      rw [y1] at h0
      norm_num at h0
  -- la borne sur la part des poids de hauteur 0 : |σ y| = 1 dans les deux branches
  have ha : |∑ y ∈ SQ.map toRealProdEmb, R y * ((1 - y.2) *
      (if y.1 + toReal v ∈ (SP.map ⟨⇑toReal, toReal_injective⟩ : Finset (Fin d → ℝ))
        then (1 : ℝ) else -1))| ≤ 1 - β := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum (g := fun y => R y * (1 - y.2)) ?_).trans_eq ?_)
    · intro y hy
      rcases hsnd y hy with h | h
      · rw [h, sub_zero, mul_one, abs_mul, abs_of_nonneg (hR0 y hy)]
        by_cases hyv : y.1 + toReal v ∈
            (SP.map ⟨⇑toReal, toReal_injective⟩ : Finset (Fin d → ℝ))
        · rw [if_pos hyv]; simp
        · rw [if_neg hyv]; simp
      · rw [h, sub_self, mul_zero, zero_mul, mul_zero, abs_zero]
    · simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
      rw [hR1, hb]
  -- le signe e et le coefficient c
  obtain ⟨e, c, he, hc, hce⟩ := exists_sign_mul_add_eq hβ ha
  refine ⟨e, he, ?_⟩
  -- l'identité de barycentre
  have hsum : ∑ y ∈ SQ.map toRealProdEmb,
      R y * (y.2 * c + (1 - y.2) *
        (if y.1 + toReal v ∈ (SP.map ⟨⇑toReal, toReal_injective⟩ : Finset (Fin d → ℝ))
          then (1 : ℝ) else -1)) = e / 3 := by
    rw [← hce, ← hb, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  have hzw : ∑ y ∈ SQ.map toRealProdEmb, R y •
      (y.1 + (y.2 * c + (1 - y.2) *
        (if y.1 + toReal v ∈ (SP.map ⟨⇑toReal, toReal_injective⟩ : Finset (Fin d → ℝ))
          then (1 : ℝ) else -1)) • toReal v) = z + e • toReal w := by
    simp only [smul_add, smul_smul, Finset.sum_add_distrib]
    rw [← Finset.sum_smul, hsum, hvR, smul_smul]
    have hkey : (e / 3) * (3 : ℝ) = e := div_mul_cancel₀ e (by norm_num)
    rw [hkey, hz]
  rw [← hzw]
  -- chaque point de la combinaison est dans l'enveloppe du support de P
  refine sum_smul_mem_convexHull _ R
    (fun y => y.1 + (y.2 * c + (1 - y.2) *
      (if y.1 + toReal v ∈ (SP.map ⟨⇑toReal, toReal_injective⟩ : Finset (Fin d → ℝ))
        then (1 : ℝ) else -1)) • toReal v) hR0 hR1 ?_
  intro y hy
  rcases hsnd y hy with h | h
  · -- tranche basse : le coefficient vaut ±1, l'extrémité correspondante est dans le support
    have hcoef : (y.2 * c + (1 - y.2) *
        (if y.1 + toReal v ∈ (SP.map ⟨⇑toReal, toReal_injective⟩ : Finset (Fin d → ℝ))
          then (1 : ℝ) else -1)) • toReal v
        = (if y.1 + toReal v ∈ (SP.map ⟨⇑toReal, toReal_injective⟩ : Finset (Fin d → ℝ))
          then (1 : ℝ) else -1) • toReal v := by
      simp only [h, zero_mul, sub_zero, one_mul, zero_add]
    rw [hcoef]
    by_cases hyv : y.1 + toReal v ∈ (SP.map ⟨⇑toReal, toReal_injective⟩ : Finset (Fin d → ℝ))
    · rw [if_pos hyv, one_smul]
      exact subset_convexHull ℝ _ hyv
    · rw [if_neg hyv]
      have hyv' : y.1 - toReal v ∈
          (SP.map ⟨⇑toReal, toReal_injective⟩ : Finset (Fin d → ℝ)) :=
        ((hfalse y hy h).resolve_left hyv)
      have hconv : y.1 + (-1 : ℝ) • toReal v = y.1 - toReal v := by
        rw [neg_one_smul, sub_eq_add_neg]
      rw [hconv]
      exact subset_convexHull ℝ _ hyv'
  · -- tranche haute : le coefficient vaut c, les deux extrémités sont dans le support
    have hcoef : (y.2 * c + (1 - y.2) *
        (if y.1 + toReal v ∈ (SP.map ⟨⇑toReal, toReal_injective⟩ : Finset (Fin d → ℝ))
          then (1 : ℝ) else -1)) • toReal v = c • toReal v := by
      simp only [h, one_mul, sub_self, zero_mul, add_zero]
    rw [hcoef]
    obtain ⟨hplus, hminus⟩ := htrue y hy h
    exact add_smul_mem_convexHull hminus hplus hc

end Discrepancy.Komlos
