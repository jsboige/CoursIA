/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapted to `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979) : toolchain v4.33.0, Mathlib `db584cd6`, convention i18n #4980.

Le source Dahia original vit dans le dépôt `gdahia/Komlos` (module
`Komlos/ShiftDistance.lean`, toolchain v4.34.0, cadre `Finsupp` sur `E →₀ ℝ`,
`overlap P Q = mass (P ⊓ Q)` avec `tvDist` et `shiftDist` dans le même
module). L'adaptation ci-dessous suit la convention du lake établie par la
brique k1.1 (`ShiftDistance.lean`) : cadre **Finset explicite**
`P : (Fin d → ℤ) → ℝ` avec support `S` passé en argument — l'infimum de
Finsupp devient le `min` ponctuel, le support devient un argument explicite,
sans `Finsupp` ni ordre pointillé.

**Portée de ce commit** (brique k1.3, `lake build SUCCESS` requis, 0
`sorry`) :

Briques closes : `overlap` (opérateur de recouvrement), `overlap_comm`,
`overlap_self` (le recouvrement d'une fonction avec elle-même est sa masse),
`overlap_nonneg`, `overlap_mono`, `overlap_le_sum_left`, `overlap_le_sum_right`
(le recouvrement est dominé par chaque masse), `sum_le_overlap` (toute
fonction sous-minorée par les deux arguments est dominée par le
recouvrement — `mass_le_overlap` chez Dahia), `min_eq_half_add_sub_abs`
(l'identité ponctuelle `min a b = ½ (a + b − |a − b|)` — la brique locale de
l'identité pivot).

**Reporté à k1.4** : l'identité pivot `overlap P (P ∘ (· + u)) = 1 − Δ(P, u)`
sous masse 1 et invariance du support par `u` (exige la ré-indexation
`sum_translate_image` de k1.2 et la convention forward de `ShiftDistance`) ;
`overlap_tr` (invariance du recouvrement par translation commune, même
chemin) ; Claim 3.2 (`Δ(T_v P, (u, 0)) ≤ Δ(P, u)`) et `split_tr` (suivent
l'identité pivot). L'état détaillé vit dans `FORMAL_STATUS.md`.
-/

import Discrepancy.Basic

/-!
# Opérateur de recouvrement `overlap` (Karingula–Lovett)

`Discrepancy.Komlos.overlap P Q S` est la somme des minima ponctuels
`min (P x) (Q x)` sur le support fini explicite `S` : la **masse commune**
de `P` et `Q`. Pour deux distributions de probabilité, le recouvrement
vaut `1 − tvDist` (identité pivot reportée à k1.4) — c'est la quantité que
la preuve élémentaire de Komlós fait passer de `P` à sa translate, puis
contrôle à travers la scission `split` (k1.2).

Cette brique ne suppose que `Discrepancy.Basic` (aucune dépendance sur
`ShiftDistance` ou `Split` : elle se situe en amont de l'identité pivot).
Le pin Mathlib `db584cd6` est dans la cohorte fleet v4.32.1
(mutualisation #4363) ; l'écart avec la toolchain locale v4.33.0 est pris
en charge par `lake build`.
-/

namespace Discrepancy.Komlos

/-- Opérateur de recouvrement : la somme des minima ponctuels sur le
support explicite `S`. C'est le `Komlos.overlap P Q = mass (P ⊓ Q)` de
Dahia transposé au cadre Finset du lake — la masse commune de `P` et `Q`,
sans `Finsupp` artificiel. -/
noncomputable def overlap {d : ℕ} (P Q : (Fin d → ℤ) → ℝ)
    (S : Finset (Fin d → ℤ)) : ℝ := ∑ x ∈ S, min (P x) (Q x)

/-- Symétrie du recouvrement : `min` est commutatif terme à terme. -/
lemma overlap_comm {d : ℕ} (P Q : (Fin d → ℤ) → ℝ)
    (S : Finset (Fin d → ℤ)) :
    overlap P Q S = overlap Q P S := by
  unfold overlap
  exact Finset.sum_congr rfl (fun x _ => min_comm (P x) (Q x))

/-- Le recouvrement d'une fonction avec elle-même est sa masse sur `S`. -/
lemma overlap_self {d : ℕ} (P : (Fin d → ℤ) → ℝ)
    (S : Finset (Fin d → ℤ)) :
    overlap P P S = ∑ x ∈ S, P x := by
  unfold overlap
  exact Finset.sum_congr rfl (fun x _ => min_self (P x))

/-- Positivité : le recouvrement de deux fonctions positives sur `S` est
positif. -/
lemma overlap_nonneg {d : ℕ} {P Q : (Fin d → ℤ) → ℝ}
    {S : Finset (Fin d → ℤ)}
    (hP : ∀ x ∈ S, 0 ≤ P x) (hQ : ∀ x ∈ S, 0 ≤ Q x) :
    0 ≤ overlap P Q S := by
  unfold overlap
  exact Finset.sum_nonneg (fun x hx => le_min (hP x hx) (hQ x hx))

/-- Monotonie en les deux arguments : le recouvrement transporte l'ordre
ponctuel. -/
lemma overlap_mono {d : ℕ} {P P' Q Q' : (Fin d → ℤ) → ℝ}
    {S : Finset (Fin d → ℤ)}
    (hP : ∀ x ∈ S, P x ≤ P' x) (hQ : ∀ x ∈ S, Q x ≤ Q' x) :
    overlap P Q S ≤ overlap P' Q' S := by
  unfold overlap
  exact Finset.sum_le_sum (fun x hx => min_le_min (hP x hx) (hQ x hx))

/-- Le recouvrement est dominé par chaque masse. -/
lemma overlap_le_sum_left {d : ℕ} (P Q : (Fin d → ℤ) → ℝ)
    (S : Finset (Fin d → ℤ)) :
    overlap P Q S ≤ ∑ x ∈ S, P x := by
  unfold overlap
  exact Finset.sum_le_sum (fun x _ => min_le_left (P x) (Q x))

/-- Variante symétrique : le recouvrement est dominé par la seconde
masse. -/
lemma overlap_le_sum_right {d : ℕ} (P Q : (Fin d → ℤ) → ℝ)
    (S : Finset (Fin d → ℤ)) :
    overlap P Q S ≤ ∑ x ∈ S, Q x := by
  unfold overlap
  exact Finset.sum_le_sum (fun x _ => min_le_right (P x) (Q x))

/-- Toute fonction sous-minorée par les deux arguments est dominée par le
recouvrement (`mass_le_overlap` chez Dahia) : la masse commune majore
toute masse partagée. C'est le sens qui servira à k1.4 pour minorer le
recouvrement par la masse conservée par la scission. -/
lemma sum_le_overlap {d : ℕ} {R P Q : (Fin d → ℤ) → ℝ}
    {S : Finset (Fin d → ℤ)}
    (hRP : ∀ x ∈ S, R x ≤ P x) (hRQ : ∀ x ∈ S, R x ≤ Q x) :
    ∑ x ∈ S, R x ≤ overlap P Q S := by
  unfold overlap
  exact Finset.sum_le_sum (fun x hx => le_min (hRP x hx) (hRQ x hx))

/-- Identité ponctuelle du minimum : `min a b = ½ (a + b − |a − b|)` — la
brique locale de l'identité pivot `overlap = 1 − tvDist` (k1.4) : sommée
terme à terme, elle relie recouvrement et distance de translation. -/
lemma min_eq_half_add_sub_abs (a b : ℝ) :
    min a b = (1 / 2 : ℝ) * (a + b - |a - b|) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, abs_of_nonpos (by linarith)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (by linarith)]
    ring

end Discrepancy.Komlos
