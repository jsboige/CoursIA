/-
Brique k5.2 du lake `discrepancy_lean` (issue #17845, distillation de
Karingula–Lovett, arXiv:2609.20979). Convention i18n #4980 : jumeau
`GridCase_en.lean`, preuves byte-identiques, docstrings seules traduites.

Sans contrepartie directe dans l'oracle `gdahia/Komlos` : la découpe suit
la carte d'usage du lake. Le cran P4 du chantier #21417
(`SignedSums.lean`) livre le Lemme 1.4 **prêt à consommer** ; ce module
franchit le pas suivant, celui que l'oracle laisse implicite — de
l'appartenance à l'enveloppe convexe à une **borne de discrépance**.
-/

import Discrepancy.Komlos.SignedSums

/-!
# k5.2 — le cas de la grille : de l'enveloppe convexe à la borne de discrépance

Le Lemme 1.4 (`exists_isColouring_mean_add_sum_mem_convexHull_of_clauseSet`,
cran P4) conclut une **appartenance** :

```
μ(P) + ∑ i, ε i • v i  ∈  conv (support de P)
```

C'est une conclusion géométrique, pas encore un énoncé de discrépance : un
lecteur ne peut pas en lire une constante. Le pas franchi ici est celui que
le Théorème 1.2 exige — **situer ce point, donc borner la somme colorée**.

Le raisonnement tient en deux inégalités, et c'est ce qui rend la brique
consommable sans hypothèse supplémentaire :

1. si le support est contenu dans la boîte fermée de rayon `R`, son
   enveloppe convexe y est contenue aussi (**convexité** de la boîte) ;
2. le moment `μ(P)` est une **combinaison convexe** des coordonnées du
   support (masse `1`, poids positifs), donc il est dans la même boîte.

La somme colorée est leur différence : elle est majorée par `2 R`.

## Ce que la brique ne prétend pas

La constante du papier n'est **pas** reproduite ici, et le module ne la
nomme pas. Le rayon `R` reste un **paramètre** : c'est l'appelant qui
l'instancie à la boîte de la distribution qu'il construit (k5.1 fournit
l'approximation sur la grille `N⁻¹ • ℤ ^ d` par `exists_grid_approx`, dont
l'hypothèse de norme est ce que la construction de densité convertit en
boîte). Écrire une constante ici reviendrait à figer une composition que
les lemmes 4.1 et 1.5 du papier portent, et que ce lake n'a pas encore
distillée.

## Vocabulaire

- `closedCoordBox R` : la boîte `{x | ∀ j, |x j| ≤ R}` de `Fin d → ℝ`.
- `abs_coordMoment_le` : le moment d'une distribution de masse `1` à poids
  positifs reste dans la boîte de son support.
- `abs_le_two_mul_of_add_mem_convexHull` : le noyau géométrique, sans
  aucune hypothèse de distance — `μ + s ∈ conv(support)` et deux bornes en
  boîte donnent `|s j| ≤ 2 R`.
- `exists_signs_abs_sum_smul_le_of_grid` : **le cas de la grille** — la
  composition des deux avec le Lemme 1.4.
-/

namespace Discrepancy.Komlos

open Finset

variable {d : ℕ}

/-- La **boîte fermée de rayon `R`** dans `Fin d → ℝ` : toutes les
coordonnées sont majorées en valeur absolue par `R`. C'est le cadre dans
lequel le cas de la grille situe le support d'une distribution : les
témoins de discrépance du lake vivent sur des grilles finies bornées. -/
def closedCoordBox (R : ℝ) : Set (Fin d → ℝ) := {x | ∀ j, |x j| ≤ R}

/-- La boîte coordonnée est le produit des intervalles `[-R, R]` : la forme
qui rend sa convexité gratuite (produit d'intervalles, `convex_pi`). -/
lemma closedCoordBox_eq_pi (R : ℝ) :
    closedCoordBox (d := d) R = Set.univ.pi (fun _ : Fin d => Set.Icc (-R) R) := by
  ext x
  simp only [closedCoordBox, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_Icc, abs_le]

/-- La boîte coordonnée est **convexe**, sans hypothèse sur `R` : une
combinaison convexe de deux points de la boîte reste dans la boîte
coordonnée par coordonnée. -/
lemma convex_closedCoordBox (R : ℝ) : Convex ℝ (closedCoordBox (d := d) R) := by
  rw [closedCoordBox_eq_pi]
  exact convex_pi fun _ _ => convex_Icc _ _

/-- **L'enveloppe convexe d'un support en boîte reste en boîte.** C'est
l'étape 1 du raisonnement : `conv (support) ⊆ boîte` dès que le support y
est, par minimalité de l'enveloppe convexe (`convexHull_min`) et convexité
de la boîte. -/
lemma convexHull_map_toReal_subset_closedCoordBox {S : Finset (Fin d → ℤ)} {R : ℝ}
    (hbox : ∀ x ∈ S, ∀ j, |(x j : ℝ)| ≤ R) :
    convexHull ℝ ↑(S.map (⟨⇑toReal, toReal_injective⟩ : (Fin d → ℤ) ↪ (Fin d → ℝ)))
      ⊆ closedCoordBox (d := d) R := by
  refine convexHull_min ?_ (convex_closedCoordBox R)
  intro x hx
  simp only [Finset.coe_map, Set.mem_image, Function.Embedding.coeFn_mk] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  intro j
  simpa using hbox y hy j

/-- **Le moment d'une distribution reste dans la boîte de son support.**
`μ j = ∑ x ∈ S, P x * x j` est une combinaison convexe des coordonnées
(`∑ P = 1`, `P ≥ 0`), donc son module est majoré par le rayon. -/
lemma abs_coordMoment_le {S : Finset (Fin d → ℤ)} {P : (Fin d → ℤ) → ℝ} {R : ℝ}
    (hP0 : ∀ x, 0 ≤ P x) (hmass : ∑ x ∈ S, P x = 1)
    (hbox : ∀ x ∈ S, ∀ j, |(x j : ℝ)| ≤ R) (j : Fin d) :
    |coordMoment P S j| ≤ R := by
  have h1 : |∑ x ∈ S, P x * (x j : ℝ)| ≤ ∑ x ∈ S, |P x * (x j : ℝ)| :=
    Finset.abs_sum_le_sum_abs (s := S) (f := fun x => P x * (x j : ℝ))
  have h2 : ∑ x ∈ S, |P x * (x j : ℝ)| = ∑ x ∈ S, P x * |(x j : ℝ)| := by
    refine Finset.sum_congr rfl ?_
    intro x _
    rw [abs_mul, abs_of_nonneg (hP0 x)]
  have h3 : ∑ x ∈ S, P x * |(x j : ℝ)| ≤ ∑ x ∈ S, P x * R := by
    refine Finset.sum_le_sum ?_
    intro x hx
    exact mul_le_mul_of_nonneg_left (hbox x hx j) (hP0 x)
  have h4 : ∑ x ∈ S, P x * R = R := by
    rw [← Finset.sum_mul, hmass, one_mul]
  unfold coordMoment
  linarith

/-- **Le noyau géométrique du cas de la grille** : si un point de la forme
`μ + s` tombe dans l'enveloppe convexe d'un support en boîte de rayon `R`,
et si `μ` est lui-même en boîte, alors chaque coordonnée de `s` est bornée
par `2 R`. Aucune hypothèse de distance n'entre ici : c'est de l'algèbre
de boîte, séparée du Lemme 1.4 pour rester réutilisable. -/
lemma abs_le_two_mul_of_add_mem_convexHull {S : Finset (Fin d → ℤ)}
    {μ s : Fin d → ℝ} {R : ℝ}
    (hmem : (fun j => μ j + s j) ∈
      convexHull ℝ ↑(S.map (⟨⇑toReal, toReal_injective⟩ : (Fin d → ℤ) ↪ (Fin d → ℝ))))
    (hbox : ∀ x ∈ S, ∀ j, |(x j : ℝ)| ≤ R)
    (hμ : ∀ j, |μ j| ≤ R) :
    ∀ j, |s j| ≤ 2 * R := by
  intro j
  have hX : |μ j + s j| ≤ R :=
    convexHull_map_toReal_subset_closedCoordBox (d := d) hbox hmem j
  have hμj : |μ j| ≤ R := hμ j
  have hEq : s j = (μ j + s j) - μ j := by ring
  rw [hEq]
  calc |(μ j + s j) - μ j| ≤ |μ j + s j| + |μ j| := abs_sub _ _
    _ ≤ R + R := add_le_add hX hμj
    _ = 2 * R := by ring

/-- **k5.2 — le cas de la grille.** Composé du Lemme 1.4 (cran P4) et du
noyau géométrique : sous les hypothèses du Lemme 1.4 et une borne de boîte
`R` sur le support, il existe des signes tels que la **somme colorée** soit
majorée coordonnée par coordonnée par `2 R`.

C'est la forme sous laquelle le Théorème 1.2 consomme le Lemme 1.4 : le
Lemme 1.4 donne l'existence des signes et le point de l'enveloppe, ce
théorème en tire l'inégalité. `R` reste un paramètre — voir l'en-tête du
module pour ce que cette brique ne prétend pas. -/
theorem exists_signs_abs_sum_smul_le_of_grid {n : ℕ} (R : ℝ)
    (S : Finset (Fin d → ℤ)) (P : (Fin d → ℤ) → ℝ) (hP0 : ∀ x, 0 ≤ P x)
    (hmass : ∑ x ∈ S, P x = 1) (hPsupp : ∀ x, P x ≠ 0 → x ∈ S)
    (v : Fin n → (Fin d → ℤ))
    (hbox : ∀ x ∈ S, ∀ j, |(x j : ℝ)| ≤ R)
    (hB : SupportContained S P (clauseSet v))
    (hv : ∀ i, shiftDistance S P (6 • v i) ≤ 3⁻¹) :
    ∃ ε : Fin n → ℤ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ j, |∑ i, (ε i : ℝ) * (v i j : ℝ)| ≤ 2 * R := by
  obtain ⟨ε, hε, hmem⟩ :=
    exists_isColouring_mean_add_sum_mem_convexHull_of_clauseSet n d S P hP0 hmass hPsupp v hB hv
  exact ⟨ε, hε,
    abs_le_two_mul_of_add_mem_convexHull hmem hbox (abs_coordMoment_le hP0 hmass hbox)⟩

end Discrepancy.Komlos
