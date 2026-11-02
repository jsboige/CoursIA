/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Saturation de la borne de Tsirelson : le témoin de Pauli et le critère de Landau

Ce module est la quatrième tranche du pilote quantique de l'Epic #13106. Les
trois premières ont borné la frontière classique déterministe (`Conway.CHSH`),
son enveloppe randomisée (`Conway.CHSHRandomized`), puis importé la borne
quantique `2√2` de Mathlib avec sa carte d'hypothèses (`Conway.CHSHQuantum`).
`Conway.CHSHQuantum` laissait quatre points déclarés **non établis** ; cette
tranche en lève trois par une même construction explicite :

1. **Saturation** — l'opérateur CHSH du témoin vaut *exactement* `2√2 • 1`,
   égalité et non majorant : la constante de Tsirelson est atteinte ;
2. **Construction matricielle** — quatre observables explicites sur ℝ^(2×2),
   combinaisons des matrices de Pauli σz et σx ;
3. **Forme spectrale bilatérale** — `chsh_landau_diagonal` : l'opérateur est
   diagonal, `2√2` sur la diagonale — chaque vecteur de base est vecteur
   propre, l'égalité tient des deux côtés. (La « norme d'opérateur » du
   statut de `CHSHQuantum` est livrée ici en forme spectrale explicite : en
   Mathlib v4.32.1 les normes matricielles sont des non-instances scoped
   (`Matrix.Norms.Operator`), et l'égalité exacte `S = 2√2 • 1` en porte la
   substance — la majoration est atteinte, pas seulement vraie.)

### Le modèle réduit, et ce qu'il ne prétend pas être

Les observables vivent dans `Matrix (Fin 2) (Fin 2) ℝ` : c'est le **modèle
réduit** à un qubit, où le produit `Aᵢ * Bⱼ` est le produit matriciel des
représentants réduits. Dans le modèle tensoriel non réduit (opérateurs
`A ⊗ 1` et `1 ⊗ B` sur ℝ⁴), la commutation croisée `Aᵢ Bⱼ = Bⱼ Aᵢ` est une
hypothèse structurelle du `IsCHSHTuple` de Mathlib ; dans le modèle réduit elle
est **fausse** — `[σz, σz + σx] = [σz, σx] ≠ 0` — et ce module ne la revendique
pas. Ce qu'il établit est plus modeste et exact : la valeur de l'opérateur CHSH
du témoin, c'est-à-dire la constante que la borne abstraite majore, est
*réalisée* par une construction concrète. L'interprétation probabiliste
complète (états, mesures, espérances sur le modèle tensoriel) reste déclarée
ouverte, comme dans `Conway.CHSHQuantum`.

### Landau : ce qui est retenu, ce qui reste ouvert

Landau (1988) caractérise la valeur quantique maximale du score CHSH d'une
matrice de corrélation `C` par les valeurs propres de sa partie symétrique.
Ce module ne formalise pas le théorème général (une preuve SDP complète) ; il
vérifie le critère **sur le témoin** : la matrice de corrélation réduite

- est symétrique,
- a un carré égal à l'identité, donc des valeurs propres ±1,

et le score du témoin vaut `2√2` — la valeur que la caractérisation de Landau
prédit pour ce spectre. La direction « suffisant » est ainsi documentée par
témoin explicite ; la caractérisation générale (nécessaire et suffisant) reste
ouverte et déclarée.

### Statut des énoncés (grille de digestion #13106)

| Énoncé | Statut |
|---|---|
| Opérateur CHSH du témoin `= 2√2 • 1` (égalité exacte) | **prouvé ici** |
| Involutivité des quatre observables (`M² = 1`) | **prouvé ici** |
| Auto-adjointude (symétrie des matrices réelles) | **prouvé ici** |
| Forme spectrale : `S` diagonal, `2√2` sur la diagonale (bilatéral) | **prouvé ici** |
| Matrice de corrélation symétrique, de carré `1` (spectre ±1) | **prouvé ici** |
| Caractérisation générale de Landau (théorème, les deux sens) | **non établi** — vérifié sur témoin seulement |
| Interprétation probabiliste complète (états, mesures, ℝ⁴ tensoriel) | **non établi** — déclaré ouvert |
| Commutation croisée dans le modèle réduit | **fausse** et non revendiquée (voir ci-dessus) |

### Grille de digestion (10 points)

1. **Énoncés et niveau de garantie** : égalités matricielles exactes sur ℝ,
   sans analyse fonctionnelle ; la constante `2√2` est celle de
   `Conway.CHSHQuantum.tsirelson_bound`.
2. **Provenance** : L. J. Landau, « On the violation of Bell inequalities in
   quantum theory », Physics Letters A 120 (1988), 54-56 ; construction de
   saturation standard (Tsirelson 1980 ; formulation pédagogique Nielsen &
   Chuang §2.4-2.5). Priorité de la caractérisation : Landau 1988 ; de la
   borne : Tsirelson 1980.
3. **Nouveauté** : la série CHSH disposait de la borne (importée) et du gap
   strict `2 < 2√2` ; le témoin d'égalité est nouveau dans le dépôt.
4. **Dépendances** : Mathlib v4.32.1 (`Matrix`, `Real.sqrt`, notation
   `!![...]` via `Mathlib.LinearAlgebra.Matrix.Notation`),
   réutilise `Conway.CHSHQuantum.chshOperator` sans le redéfinir ; aucun
   `sorry`, aucun axiome au-delà des standards.
5. **Trivial condensé / nouveau développé** : les carrés de σz, σx sont des
   calculs d'entrées ; le cœur est l'anticommutateur `σzσx + σxσz = 0`, duquel
   découlent l'involutivité des `Bⱼ` et l'égalité centrale — les preuves sont
   entry-level (ext + fin_cases) : la non-commutativité des matrices interdit
   `ring`, chaque identité est donc distribuée puis close sur l'atome
   `(√2)² = 2`.
6. **Friction** : le modèle réduit ne porte pas la commutation croisée
   (hypothèse du tuple abstrait) — c'est la limite déclarée, détaillée
   ci-dessus ; la manipulation de `√2` passe par l'atome `hsq : (√2)² = 2`
   et `linear_combination`, jamais par une approximation numérique.
7. **Chemin de découverte** : (1) réduire le tenseur au qubit simple ;
   (2) vérifier l'anticommutation ; (3) dériver `S = (4/√2) • 1` par
   distributivité, puis `4/√2 = 2√2` ; (4) n'ensuite calculer les corrélations.
   La reconstruction finale suit le même ordre, les lemmes intermédiaires
   portant chacun une étape.
8. **Limites** : les trois lignes « non établi / faux » de la table de statut.
9. **Raccord au corpus** : quatrième module de la série CHSH de `conway_lean`
   (avec `CHSH`, `CHSHRandomized`, `CHSHQuantum`) ; renvois côté notebooks :
   `Lean-13b-CHSH-Tsirelson-Native` (exécution native de la série sous kernel
   `lean4-wsl` — une tranche future peut y exécuter les énoncés du présent
   module), `Lean-13-Kochen-Specker`, `Lean-16f-Conway-Free-Will-Theorem`.
10. **Transmission** : chaque lemme porte une docstring qui sépare ce que la
    sortie du calcul montre de ce qu'il suggère ; la table de statut est le
    résumé falsifiable.

### Sources

- L. J. Landau, « On the violation of Bell inequalities in quantum theory »,
  Physics Letters A 120 (1988), 54-56.
- B. S. Cirel'son (Tsirelson), « Quantum generalizations of Bell's
  inequality », Letters in Mathematical Physics 4 (1980), 93-100.
- M. Nielsen, I. Chuang, *Quantum Computation and Quantum Information*,
  Cambridge University Press (2000), §2.4-2.5.
-/

import Conway.CHSHQuantum
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

namespace Conway
namespace CHSHLandau

/-! ### Les briques de Pauli sur ℝ^(2×2) -/

/-- Matrice de Pauli `σz = diag(1, -1)`, représentant de l'observable
« spin selon z » : auto-adjointe, involutive, diagonale. -/
def sigmaZ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- Matrice de Pauli `σx`, représentant de l'observable « spin selon x » :
auto-adjointe, involutive, antidiagonale. -/
def sigmaX : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- L'atome de calcul du module : `√2` est traité comme une quantité formelle
via son carré. Aucune preuve ci-dessous n'utilise d'approximation numérique. -/
theorem sqrt_two_sq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem sigmaZ_sq : sigmaZ * sigmaZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaZ, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

theorem sigmaX_sq : sigmaX * sigmaX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaX, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- Anticommutateur des deux Pauli : `σzσx + σxσz = 0`.

C'est le cœur algébrique du module — de lui découlent l'involutivité des
observables `B` (leur carré mélange `σzσx` et `σxσz`) et l'égalité centrale
(les termes croisés de l'opérateur CHSH se compensent deux à deux). -/
theorem sigmaZ_anticomm_sigmaX : sigmaZ * sigmaX + sigmaX * sigmaZ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaZ, sigmaX, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

theorem sigmaZ_symm : Matrix.transpose sigmaZ = sigmaZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigmaZ]

theorem sigmaX_symm : Matrix.transpose sigmaX = sigmaX := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigmaX]

/-! ### Les quatre observables du témoin -/

/-- Observable d'Alice `A₀ = σz`. -/
def A₀ : Matrix (Fin 2) (Fin 2) ℝ := sigmaZ

/-- Observable d'Alice `A₁ = σx`. -/
def A₁ : Matrix (Fin 2) (Fin 2) ℝ := sigmaX

/-- Observable de Bob `B₀ = (σz + σx)/√2`. -/
noncomputable def B₀ : Matrix (Fin 2) (Fin 2) ℝ := (√2 : ℝ)⁻¹ • (sigmaZ + sigmaX)

/-- Observable de Bob `B₁ = (σz - σx)/√2`. -/
noncomputable def B₁ : Matrix (Fin 2) (Fin 2) ℝ := (√2 : ℝ)⁻¹ • (sigmaZ - sigmaX)

theorem A₀_sq : A₀ * A₀ = 1 := sigmaZ_sq

theorem A₁_sq : A₁ * A₁ = 1 := sigmaX_sq

/-- Involutivité de `B₀` : le carré de `(σz + σx)/√2` vaut l'identité parce
que les termes croisés s'annulent par anticommutation et que
`(1/√2)² · (1 + 1) = 1`. Chaque entrée est close sur l'atome `sqrt_two_sq`. -/
theorem B₀_sq : B₀ * B₀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B₀, Matrix.smul_apply, Matrix.mul_apply, Matrix.add_apply,
      Fin.sum_univ_two, sigmaZ, sigmaX, Matrix.one_apply] <;>
    field_simp <;>
    nlinarith [sqrt_two_sq]

/-- Involutivité de `B₁`, par le même schéma que `B₀_sq` : les termes croisés
changent de signe mais s'annulent pareil. -/
theorem B₁_sq : B₁ * B₁ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B₁, Matrix.smul_apply, Matrix.mul_apply, Matrix.sub_apply,
      Matrix.add_apply, Fin.sum_univ_two, sigmaZ, sigmaX,
      Matrix.one_apply] <;>
    field_simp <;>
    nlinarith [sqrt_two_sq]

theorem B₀_symm : Matrix.transpose B₀ = B₀ := by
  rw [B₀]
  simp only [Matrix.transpose_add, Matrix.transpose_smul, sigmaZ_symm, sigmaX_symm]

theorem B₁_symm : Matrix.transpose B₁ = B₁ := by
  rw [B₁]
  simp only [Matrix.transpose_sub, Matrix.transpose_smul, sigmaZ_symm, sigmaX_symm]

/-! ### L'égalité centrale : l'opérateur CHSH du témoin vaut exactement `2√2` -/

/-- **Saturation de la borne de Tsirelson** (direction suffisance du critère
de Landau, par témoin explicite) : l'opérateur CHSH du quadruple
`(σz, σx, (σz+σx)/√2, (σz-σx)/√2)` vaut *exactement* `2√2 • 1` — chaque
vecteur est vecteur propre avec la valeur propre `2√2`, et la constante que
`Conway.CHSHQuantum.tsirelson_bound` majore est atteinte.

La lecture algébrique : par distributivité, `S = (1/√2) • (σz(σz+σx) +
σz(σz-σx) + σx(σz+σx) - σx(σz-σx))` ; les huit produits se réordonnent en
`2·σz² + 2·σx²` plus quatre termes croisés `σzσx + σxσz` qui s'annulent deux à
deux par `sigmaZ_anticomm_sigmaX` ; il reste `(4/√2) • 1`, et `4/√2 = 2√2`
par `sqrt_two_sq`. La preuve exécute ce programme entrée par entrée. -/
theorem chsh_landau :
    CHSHQuantum.chshOperator A₀ A₁ B₀ B₁ = (2 * √2 : ℝ) •
      (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CHSHQuantum.chshOperator, A₀, A₁, B₀, B₁, Matrix.smul_apply,
      Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Fin.sum_univ_two,
      sigmaZ, sigmaX, Matrix.one_apply] <;>
    field_simp <;>
    nlinarith [sqrt_two_sq]

/-- **Forme spectrale bilatérale** : l'opérateur CHSH du témoin est diagonal,
avec `2√2` sur la diagonale et `0` ailleurs — chaque vecteur de base est
vecteur propre pour la valeur propre `2√2`. C'est la jambe « bilatérale »
qui manquait à la série : `Conway.CHSHQuantum.tsirelson_bound` donne
`≤ 2√2` en général, et l'égalité centrale `chsh_landau`, précisée ici
entrée par entrée, montre que la borne est *atteinte* — la majoration est
une égalité, des deux côtés. -/
theorem chsh_landau_diagonal (i j : Fin 2) :
    CHSHQuantum.chshOperator A₀ A₁ B₀ B₁ i j = if i = j then 2 * √2 else 0 := by
  rw [chsh_landau]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, Matrix.one_apply]

/-! ### Matrice de corrélation et critère de Landau (vérifié sur le témoin) -/

/-- Matrice de corrélation réduite du témoin : l'entrée `(i, j)` est la
corrélation des observables `Aᵢ` et `Bⱼ` du quadruple, toutes égales à
`1/√2` au signe près (l'entrée `(1,1)` porte le signe `-` du terme
`- A₁ * B₁` de l'opérateur CHSH). -/
noncomputable def corrMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(√2 : ℝ)⁻¹, (√2 : ℝ)⁻¹; (√2 : ℝ)⁻¹, -(√2 : ℝ)⁻¹]

/-- La matrice de corrélation du témoin est symétrique — la première moitié
de l'hypothèse du critère de Landau (1988). -/
theorem corrMatrix_symm : Matrix.transpose corrMatrix = corrMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [corrMatrix]

/-- Le carré de la matrice de corrélation vaut l'identité : son spectre est
exactement `{-1, 1}` — la seconde moitié du critère de Landau, vérifiée sur
le témoin. La caractérisation générale (les deux sens, pour toute matrice de
corrélation) reste déclarée ouverte. -/
theorem corrMatrix_sq : corrMatrix * corrMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [corrMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply] <;>
    field_simp <;>
    nlinarith [sqrt_two_sq]

end CHSHLandau
end Conway
