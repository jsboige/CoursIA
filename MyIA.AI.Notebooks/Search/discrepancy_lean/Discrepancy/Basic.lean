import Mathlib

/-!
# Discrépance combinatoire : définitions, lemmes élémentaires, conjectures

Fondations du lake `discrepancy_lean` (issue #12823). Étant donné une famille
finie `F` de parties d'un ensemble d'éléments, la **discrépance** mesure à
quel point on peut colorer chaque élément en `±1` de sorte que chaque somme
colorée `∑_{x ∈ S} c x` reste petite en valeur absolue — pour la **pire**
partie de la famille. C'est l'objet central de la théorie de la discrépance
combinatoire (Spencer, Beck–Fiala, Banaszczyk, Bansal–Jiang 2025).

## Désambiguïsation (une ligne, obligatoire)

`Search-13-LimitedDiscrepancySearch` (même série `Search/`) utilise
« discrepancy » en un **autre sens** : la Limited Discrepancy Search de
Harvey & Ginsberg, où la discrépance d'une branche = le nombre de choix où
l'on contredit l'heuristique au fil d'une recherche arborescente. Aucun
rapport mathématique avec les sommes signées formalisées ici.

## Le fil « découplage »

Les bornes modernes (Banaszczyk 1998, Bansal–Jiang 2025,
arXiv:2508.03961) reposent sur un geste que le dépôt enseigne déjà par
ailleurs : **découpler** des quantités qui conspirent — reparamétrisation
non centrée qui déplie le funnel (PyMC-12), découplage
`|empError − μ| ≥ ε ⟺ (nε ≤ Z) ∨ (Z ≤ −nε)` (Hoeffding.lean), double
estimateur Q1/Q2 du RL. Ici, le découplage est *spectral et affine* : des
contraintes sur une SDP font cesser aux évolutions de discrépance des
différentes lignes de conspirer, rendant la concentration applicable.

## Conjectures = `Prop` nommées

Les énoncés ouverts (Beck–Fiala `O(√k)` ci-dessous, Komlós `O(1)` et formes
Bansal–Jiang dans `Discrepancy.Komlos`) sont des `def ... : Prop` **sans
preuve** — jamais des théorèmes tronqués par `sorry`. Le lake ne contient
aucun `sorry` (convention anti-régression D du dépôt) ; l'état des preuves
vit dans `FORMAL_STATUS.md`.
-/

namespace Discrepancy

/-- Une coloration en `±1` : chaque élément reçoit exactement `1` ou `-1`. -/
def IsColoring {α : Type*} (c : α → ℤ) : Prop :=
  ∀ x, c x = 1 ∨ c x = -1

/-- Discrépance d'une famille finie de parties finies sous une coloration :
le maximum des valeurs absolues des sommes colorées, pris sur toutes les
parties de la famille. -/
def discrepancy {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (c : α → ℤ) : ℕ :=
  (F.image fun S => (S.sum c).natAbs).sup id

/-- Degré d'un élément `x` : nombre de parties de la famille qui contiennent
`x`. L'hypothèse « degré au plus `k` » est celle de Beck–Fiala : chaque
élément n'apparaît que dans au plus `k` contraintes. -/
def degree {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x : α) : ℕ :=
  (F.filter fun S => x ∈ S).card

/-- Degré maximal d'une famille sur un type fini : le `k` des énoncés
Beck–Fiala. -/
def maxDegree {α : Type*} [DecidableEq α] [Fintype α] (F : Finset (Finset α)) : ℕ :=
  Finset.univ.sup fun x => degree F x

/-! ## Lemmes élémentaires

Trois faits immédiats, prouvés d'emblée : ils ancrent les définitions dans
des exemples limites vérifiables (et servent de tests de fumée du lake). -/

/-- La famille vide est de discrépance nulle, pour toute coloration. -/
theorem discrepancy_empty {α : Type*} [DecidableEq α] (c : α → ℤ) :
    discrepancy ∅ c = 0 := by
  simp [discrepancy]

/-- Une famille réduite à la partie vide est de discrépance nulle : sommer
sur `∅` ne donne jamais rien. -/
theorem discrepancy_singleton_empty {α : Type*} [DecidableEq α] (c : α → ℤ) :
    discrepancy {∅} c = 0 := by
  simp [discrepancy]

/-- Le degré d'un élément est majoré par le nombre de parties de la
famille. -/
theorem degree_le_card {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x : α) :
    degree F x ≤ F.card := by
  simp only [degree]
  exact Finset.card_filter_le _ _

/-! ## Conjectures et cible (énoncés, sans preuve) -/

/-- **Conjecture de Beck–Fiala (1981)** : il existe une constante universelle
`C` telle que toute famille de parties de `Fin n` de degré au plus `k` admet
une coloration `±1` de discrépance au plus `C * √k`.

C'est la conjecture ouverte centrale du domaine. Bansal–Jiang (2025) la
résolvent en régime grand degré `k ≥ (log n)²` — voir
`Discrepancy.BansalJiangLargeDegree`. -/
def BeckFialaConjecture : Prop :=
  ∃ C : ℕ, ∀ (n k : ℕ) (F : Finset (Finset (Fin n))) (_hk : maxDegree F ≤ k),
    ∃ c : Fin n → ℤ, IsColoring c ∧ discrepancy F c ≤ C * Nat.sqrt k

/-- **Théorème classique de Beck–Fiala** : toute famille de parties de
`Fin n` de degré au plus `k` (avec `k ≥ 1`) admet une coloration `±1` de
discrépance au plus `2k - 1`.

C'est la « noix » visée par le palier P1 de l'issue #12823 : preuve par
*variables flottantes* et coloration partielle, découpée en boutes `b1`–`b4`
(voir `FORMAL_STATUS.md`). Tant que la preuve n'est pas assemblée, l'énoncé
vit comme `Prop` nommée ; la boute `b4` le convertira en `theorem`. -/
def BeckFialaClassic : Prop :=
  ∀ (n k : ℕ) (F : Finset (Finset (Fin n))) (_hk : maxDegree F ≤ k) (_hk1 : 1 ≤ k),
    ∃ c : Fin n → ℤ, IsColoring c ∧ (discrepancy F c : ℤ) ≤ 2 * (k : ℤ) - 1

end Discrepancy
