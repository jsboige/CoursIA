/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Inégalité CHSH : borne quantique de Tsirelson

Ce module est la troisième tranche du pilote quantique de l'Epic #13106. Les
deux premières ont borné la frontière **classique** (`Conway.CHSH`) puis son
enveloppe **randomisée** (`Conway.CHSHRandomized`). Celle-ci franchit le pas
algébrique : dans une algèbre étoilée ordonnée réelle, le score CHSH d'un
quadruple d'observables auto-adjointes involutives qui commutent par paires
croisées est majoré par `2√2`, et non plus par `2`.

Cette seconde borne n'est pas redémontrée ici. Elle est **importée avec sa
preuve noyau** depuis Mathlib (`Mathlib.Algebra.Star.CHSH.tsirelson_inequality`,
Kim Morrison), qui l'établit par décomposition en somme de carrés. Redémontrer
la preuve SOS serait un travail de formalisation lourd sans bénéfice
pédagogique : ce que ce module apporte est la **carte des hypothèses** — dire
exactement ce que le théorème exige, sous quelle forme usuelle il s'énonce, et
où passe la frontière entre ce qui est prouvé ici, ce qui est importé, et ce
qui reste ouvert.

### Statut des énoncés (grille de digestion #13106)

| Énoncé | Statut |
|---|---|
| Frontière classique déterministe (`\|score\| = 2`) | **prouvé localement** — `Conway.CHSH` |
| Frontière classique randomisée (`\|expectedScore\| ≤ 2`) | **prouvé localement** — `Conway.CHSHRandomized` |
| Borne quantique `2√2` sous hypothèses d'algèbre étoilée ordonnée | **importé**, preuve noyau Mathlib |
| Réécriture scalaire `√2 ^ 3 = 2 * √2` et gap `2 < 2√2` | **prouvé ici** |
| Saturation de `2√2` par un état quantique | **non établi** dans cette tranche |
| Construction matricielle / matrices de Pauli | **non établi** dans cette tranche |
| Interprétation probabiliste complète d'un état quantique | **non établi** dans cette tranche |
| Borne bilatérale en norme d'opérateur | **non établi** dans cette tranche |

L'absence de ces quatre derniers points est **déclarée**, pas maquillée : la
borne établie ici est un majorant *unilatéral* `≤ 2√2`, et il n'existe dans ce
module aucun témoin exhibant l'égalité. C'est précisément la limite que la
tranche suivante devra lever si elle veut démontrer que `2√2` est **atteint**.

### Dépendances et axiomes

L'axiomatisation de `tsirelson_bound` ne fait apparaître que les axiomes
standards de Mathlib (`propext`, `Classical.choice`, `Quot.sound`) : le module
n'introduit **aucun `sorry`**, ni directement, ni transitivement via
`tsirelson_inequality`. Le booléen `Classical.choice` est non constructif mais
légitime ici — Mathlib l'utilise dans sa propre preuve, et le whitelister par
nom explicite est la pratique admise du dépôt.

### Chemin de découverte et reconstruction finale

Le chemin suivi par cette tranche est : (1) vérifier au pin v4.32.1 la
signature exacte du théorème Mathlib ; (2) établir séparément la réécriture
scalaire et le gap numérique ; (3) assembler le pont générique sous les
hypothèses exactes ; (4) seulement ensuite exposer la forme usuelle `2√2`.
Un `simpa using tsirelson_inequality` sans carte d'hypothèses aurait produit un
wrapper jouet : il n'aurait ni nommé les hypothèses, ni exposé `2√2`, ni rendu
le gap classique/quantique inspectable. La reconstruction finale est donc
séparée du chemin de découverte, et les deux sont lisibles ici.

### Sources

- J. F. Clauser, M. A. Horne, A. Shimony, R. A. Holt,
  « Proposed Experiment to Test Local Hidden-Variable Theories »,
  Physical Review Letters 23 (1969), 880-884.
- B. S. Tsirelson, « Quantum generalizations of Bell's inequality »,
  Letters in Mathematical Physics 4 (1980), 93-100.

### Raccords dans la série

- `Lean-13-Kochen-Specker.ipynb` : autre obstruction à l'accord classique, mais
  de nature combinatoire (colorabilité des vecteurs) et non analytique comme la
  borne de Tsirelson.
- `Lean-16f-Conway-Free-Will-Theorem.ipynb` : le théorème du libre arbitre de
  Conway et Kochen, qui exploite la même frontière entre corrélations
  classiques et quantiques.
- `Lean-13b-CHSH-Tsirelson-Native.ipynb` : le notebook natif de cette tranche,
  qui exécute les énoncés de ce module sous le kernel `lean4-wsl`.
-/

import Conway.CHSH
import Conway.CHSHRandomized
import Mathlib.Algebra.Star.CHSH

namespace Conway
namespace CHSHQuantum

/-- L'opérateur CHSH non commutatif d'un quadruple `(A₀, A₁, B₀, B₁)` :
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁`.

Ce nom pédagogique ne duplique pas la structure `IsCHSHTuple` de Mathlib, qui
reste la porte d'entrée des hypothèses ; il donne seulement un nom lisible à
l'expression que les deux bornes majorent. -/
def chshOperator {R : Type*} [Ring R] (A₀ A₁ B₀ B₁ : R) : R :=
  A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁

/-- Réécriture scalaire : `√2 ^ 3 = 2 * √2`.

Mathlib énonce la borne avec le scalaire `√2 ^ 3` ; la forme usuelle en
physique est `2√2`. Cette égalité est le pont entre les deux écritures, et
c'est elle qui rend la borne lisible sans réécrire la preuve de Mathlib. -/
theorem sqrt_two_cubed : (√2 : ℝ) ^ 3 = 2 * √2 := by
  have h2 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  calc (√2 : ℝ) ^ 3 = (√2 : ℝ) ^ 2 * √2 := by ring
    _ = 2 * √2 := by rw [h2]

/-- Gap numérique strict entre la borne classique `2` et la borne quantique
`2√2`.

C'est le seul témoin de séparation que cette tranche peut exhiber sans
fabriquer une construction matricielle absente : la borne classique `2` est
**strictement** inférieure à `2√2`, donc l'intervalle `(2, 2√2]` est non vide.
Ce que le module ne démontre pas est qu'un système quantique **atteint** la
borne supérieure de cet intervalle. -/
theorem classical_quantum_gap : (2 : ℝ) < 2 * √2 := by
  have h : (1 : ℝ) < √2 := Real.one_lt_sqrt_two
  linarith

/-- Frontière classique déterministe, transposée dans `ℝ`.

`Conway.CHSH.classical_bound` est énoncée sur `ℤ` ; la comparer à la borne
quantique `2√2`, qui vit dans `ℝ`, demande de la transporter. Cette forme est
celle qu'utilise le tableau comparatif
`classique déterministe / classique randomisé / quantique`. -/
theorem classical_deterministic_bound_real (a₀ a₁ b₀ b₁ : CHSH.Outcome) :
    ((|CHSH.score a₀ a₁ b₀ b₁| : ℤ) : ℝ) ≤ 2 := by
  exact_mod_cast CHSH.classical_bound a₀ a₁ b₀ b₁

/-- Frontière classique randomisée, transposée dans `ℝ`.

Même transport que ci-dessus, depuis `Conway.CHSHRandomized.randomized_bound`
qui vit dans `ℚ`. -/
theorem classical_randomized_bound_real (μ : CHSHRandomized.Strategy)
    (h_nonneg : ∀ p, 0 ≤ μ p)
    (h_total : (∑ p : CHSHRandomized.Profile, μ p) = 1) :
    ((|CHSHRandomized.expectedScore μ| : ℚ) : ℝ) ≤ 2 := by
  exact_mod_cast CHSHRandomized.randomized_bound μ h_nonneg h_total

/-- **Borne de Tsirelson**, sous sa forme usuelle.

Pour toute algèbre étoilée ordonnée réelle `R` et tout quadruple
`(A₀, A₁, B₀, B₁)` formant un `IsCHSHTuple`, le score CHSH est majoré par
`2√2 • 1`.

Les hypothèses sont exactement celles de
`Mathlib.Algebra.Star.CHSH.tsirelson_inequality`, reproduites ici sans
élargissement ni restriction : `[Ring R] [PartialOrder R] [StarRing R]
[StarOrderedRing R] [Algebra ℝ R] [IsOrderedModule ℝ R] [StarModule ℝ R]`.
La preuve applique le théorème de Mathlib, puis transporte la réécriture
scalaire établie dans ce module. -/
theorem tsirelson_bound {R : Type*} [Ring R] [PartialOrder R] [StarRing R]
    [StarOrderedRing R] [Algebra ℝ R] [IsOrderedModule ℝ R] [StarModule ℝ R]
    (A₀ A₁ B₀ B₁ : R) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    chshOperator A₀ A₁ B₀ B₁ ≤ (2 * √2) • (1 : R) := by
  have h := tsirelson_inequality A₀ A₁ B₀ B₁ T
  rw [sqrt_two_cubed] at h
  simpa only [chshOperator] using h

end CHSHQuantum
end Conway
