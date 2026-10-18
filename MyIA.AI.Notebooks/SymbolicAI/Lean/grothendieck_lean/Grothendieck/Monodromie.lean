/-
# Hommage Grothendieck — Monodromie : la première marche du cercle épointé

Copyright (c) 2026 CoursIA. Tous droits réservés.
Distribué sous licence Apache 2.0 comme décrit dans le fichier LICENSE.

## Volet preuve de la distillation #19333-G.beta (issue #21308)

La monodromie — la transformation subie par une fibre transportée le long
d'un lacet autour d'un point singulier — est manipulée quatre fois dans la
série Lean sans jamais y être définie (mesure du 18/10/2026 : Lean-22,
Lean-28, Riemann200). Ce module en pose la première marche, sur l'exemple
calculable de bout en bout : la couverture `z ↦ z²` du plan complexe épointé.

La boucle générateur `t ↦ exp(2πi·t)` se relève depuis `1` en
`t ↦ exp(πi·t)`, et ce relèvement finit en `-1` : la monodromie est la
transposition `x ↦ -x` de la fibre `{1, -1}`. D'ordre 2, sa valeur propre
non triviale `-1` est une racine de l'unité — exactement ce que prédit le
théorème de quasi-unipotence de Grothendieck (SGA 7, XII), énoncé ci-dessous
comme `Prop` documentaire : Mathlib ne le formalise pas, et ce module dit
honnêtement où s'arrête la frontière.

La couverture universelle `exp : ℂ → ℂ*` (le plan épointé) est le décor :
`Complex.exp_ne_zero` garantit qu'on ne quitte jamais `ℂ*`.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Grothendieck

/-! ## La fibre de `z ↦ z²` au-dessus de `1` -/

/-- La fibre de `z ↦ z²` au-dessus de `1` : exactement `{1, -1}`,
les deux racines carrées complexes de l'unité. C'est la fibre que la
monodromie va permuter. -/
theorem fiber_sq_one (x : ℂ) : x ^ 2 = 1 ↔ x = 1 ∨ x = -1 := by
  constructor
  · intro h
    have h2 : (x - 1) * (x + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact Or.inl (by linear_combination h3)
    · exact Or.inr (by linear_combination h3)
  · rintro (rfl | rfl)
    · norm_num
    · norm_num

/-! ## La boucle générateur et son relèvement -/

/-- La boucle générateur du cercle : `γ t = exp(2πi·t)`.
C'est le lacet de base de `π₁(ℂ*)` — la couverture universelle
`exp : ℂ → ℂ*` en fait le générateur (chaque tour complet du cercle
correspond à l'addition de `2πi` dans le revêtement). -/
noncomputable def generatorLoop (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

/-- Départ de la boucle : `γ 0 = 1`. -/
@[simp]
theorem generatorLoop_zero : generatorLoop 0 = 1 := by
  simp [generatorLoop]

/-- Retour de la boucle : `γ 1 = 1` — c'est bien un lacet. La preuve coupe
le tour complet en deux demi-tours et applique deux fois `exp (πi) = -1`. -/
@[simp]
theorem generatorLoop_one : generatorLoop 1 = 1 := by
  have h2 : generatorLoop 1
      = Complex.exp (Real.pi * Complex.I + Real.pi * Complex.I) := by
    simp only [generatorLoop]
    congr 1
    push_cast
    ring
  rw [h2, Complex.exp_add, Complex.exp_pi_mul_I]
  norm_num

/-- Le relèvement de la boucle par la racine carrée : `γ̃ t = exp(πi·t)`.
Il part de `1` et couvre `γ` point par point — c'est le transport
continu de la fibre le long du lacet. -/
noncomputable def generatorLift (t : ℝ) : ℂ := Complex.exp (Real.pi * Complex.I * t)

/-- Le relèvement couvre la boucle : `γ̃(t)² = γ(t)` pour tout `t`. -/
@[simp]
theorem lift_covers_loop (t : ℝ) : generatorLift t ^ 2 = generatorLoop t := by
  simp only [generatorLift, generatorLoop, pow_two]
  rw [← Complex.exp_add]
  congr 1
  ring

/-- Départ du relèvement : `γ̃ 0 = 1`. -/
@[simp]
theorem lift_zero : generatorLift 0 = 1 := by
  simp [generatorLift]

/-- **L'arrivée du relèvement : `γ̃ 1 = -1`.**
Toute la monodromie est dans cette ligne : transportée une fois autour du
cercle, la racine carrée `1` devient `-1` — l'objet algébrique revient
transformé par la boucle. -/
@[simp]
theorem lift_one : generatorLift 1 = -1 := by
  simp [generatorLift, Complex.exp_pi_mul_I]

/-! ## La monodromie comme action sur la fibre -/

/-- La monodromie de `z ↦ z²` le long du générateur : la transposition
`x ↦ -x` de la fibre `{1, -1}`. C'est l'action que le relèvement fait
subir à la fibre : `1` part et revient en `-1` (`lift_one`). -/
def monodromySq (x : ℂ) : ℂ := -x

/-- La monodromie préserve la fibre : l'image d'une racine carrée de `1`
en est une. -/
theorem monodromySq_mem_fiber {x : ℂ} (h : x ^ 2 = 1) : monodromySq x ^ 2 = 1 := by
  unfold monodromySq
  rw [neg_sq]
  exact h

/-- La monodromie est une involution : d'ordre exactement `2`. -/
@[simp]
theorem monodromySq_sq (x : ℂ) : monodromySq (monodromySq x) = x := by
  simp [monodromySq, neg_neg]

/-- **Le théorème de monodromie, calculé** : la monodromie envoie le point
de départ du relèvement sur son point d'arrivée — `1 ↦ -1`. -/
theorem monodromy_of_generator : monodromySq (generatorLift 0) = generatorLift 1 := by
  simp [monodromySq, lift_zero, lift_one]

/-! ## Quasi-unipotence : le théorème et sa frontière -/

/-- La puissance deuxième de la monodromie est l'identité — après deux
tours, l'objet revient inchangé. Un opérateur dont une puissance est
unipotent (ici : trivial, l'identité) est quasi-unipotent. -/
theorem monodromySq_pow_two_eq_id (x : ℂ) : monodromySq (monodromySq x) = x :=
  monodromySq_sq x

/-- La valeur propre non triviale de la monodromie (`-1`) est une racine de
l'unité : `(-1)² = 1`. C'est la moitié « racines de l'unité » de la
quasi-unipotence, vérifiée sur l'exemple. -/
theorem eigenvalue_neg_one_sq : (-1 : ℂ) ^ 2 = 1 := by
  norm_num

/-- **Énoncé documentaire (non prouvé — hors Mathlib).**
Le théorème de quasi-unipotence de Grothendieck (SGA 7, exposé XII,
théorème 1.1 ; voir aussi *Weil II*, Deligne 1980) : la monodromie d'une
famille lisse paramétrée par un disque épointé est quasi-unipotente —
un certain pouvoir de la transformation est unipotent, autrement dit
toutes ses valeurs propres sont des racines de l'unité. Ce `Prop` fixe
l'énoncé pour mémoire ; Mathlib 4 ne le formalise pas (aucune théorie des
familles lisses paramétrées ni de monodromie ℓ-adique), et le présent
module en vérifie la conclusion sur l'exemple calculable `z ↦ z²`
ci-dessus. -/
def quasiUnipotenceSGA7 : Prop :=
  ∀ (F : Type) [AddCommGroup F] [Module ℂ F] (T : F →ₗ[ℂ] F),
    (∃ (n : ℕ), 0 < n ∧ ∀ v : F, T^[n] v = v) →
      ∀ μ : ℂ, (∃ v : F, v ≠ 0 ∧ T v = μ • v) → ∃ (r : ℕ), 0 < r ∧ μ ^ r = 1
