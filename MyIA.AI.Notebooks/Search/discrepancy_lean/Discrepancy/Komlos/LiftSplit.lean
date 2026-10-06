/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapté à `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979) : toolchain v4.33.0, Mathlib `db584cd6`, convention i18n #4980.

Le source Dahia original vit dans le dépôt `gdahia/Komlos` (toolchain
v4.34.0, cadre `Finsupp` sur `E →₀ ℝ`). Ce module n'a **pas de contrepartie
oracle nom pour nom** : chez l'oracle, l'hypothèse d'induction s'applique à
la distribution scindée dans `E × ℝ` sans aucune précondition de support —
le `Finsupp` transporte son support gratuitement (`Finsupp.embDomain`) ;
c'est le cadre `Finset` explicite du lake qui doit payer ce transport, et
ce paiement est précisément l'objet de cette brique.

**Portée de ce commit** (brique k2.6b, `lake build SUCCESS` requis, 0
`sorry`) — la scission sous contention, lue dans la dimension agrandie
`Fin (d+1) → ℤ` :

- `pushUp_split_ne_zero` — lecture du support de la poussée : toute masse
  de `pushUp (split w P)` vit sur l'image de `liftUp` et provient d'une
  masse de `P` à distance `± w` de sa base (l'auxiliaire que consomme le
  transfert de contenance) ;
- `supportContained_pushUp_split` — **le transfert de contenance à
  travers la scission** : si `S` contient le support de `P` et ses
  translatés par `A`, et `A` est stable par `± w`, alors l'image liftée
  `(S ×ˢ univ).map liftUpEmb` contient le support de `pushUp (split w P)`
  et ses translatés par les décalages embarqués `Fin.snoc · 0` de `A` ;
- `coordMoment_pushUp_split_of_support` — **la conservation du moment de
  base sous contenance, au niveau lifté** : le moment coordonné de la
  scission-poussée, lu en coordonnée héritée `i.castSucc`, est le moment
  de `P` en `i` — la composition du pont `coordMoment_pushUp_castSucc`
  (k2.6a) avec `prodMoment_split_of_support` (k2.0) ;
- `coordMoment_pushUp_split_last` — la composante de hauteur : le moment
  de la scission-poussée en dernière coordonnée est le bit de scission
  (`coordMoment_pushUp_last` (k2.6a) × `heightMoment_split` (k2.0)) ;
- `supportContained_pushUp_split_three` — la forme `{0, snoc u 0,
  −snoc u 0}` que le cran suivant de l'induction consomme : instance du
  transfert par monotonie (`SupportContained.mono`), les trois décalages
  étant les images `snoc · 0` de `0`, `u`, `−u`.

**Consommateur mesuré** : l'induction du Lemme 1.4 (brique k2.6c, oracle
`Komlos/SignedSums.lean` l.44-55) applique son hypothèse d'induction à
`split (3 • v_last) P` dans l'espace agrandi — chez nous, à `pushUp
(split w P)` dans `Fin (d+1) → ℤ`. Les préconditions de support et les
ré-écritures de barycentre que cet appel exige sont exactement les cinq
énoncés ci-dessus : la contenance pour instancier l'hypothèse
(`supportContained_pushUp_split_three`), les moments pour réécrire le
point qu'elle produit (`coordMoment_pushUp_split_of_support` et
`_last`, le miroir lake du `rw [mean_split, …] at hmem` de l.54).

**Différé** : l'induction elle-même (`SignedSums.lean` nom pour nom,
k2.6c). L'état détaillé vit dans `FORMAL_STATUS.md`.
-/

import Discrepancy.Komlos.Containment
import Discrepancy.Komlos.Lift
import Discrepancy.Komlos.MeanSplit
import Discrepancy.Komlos.Split

/-!
# La scission sous contention, dans la dimension agrandie (k2.6b)

Chez l'oracle, le pas de l'induction du Lemme 1.4 est gratuit côté
support : `split v P` est un `Finsupp` sur `E × ℝ`, dont le support se
transporte par `Finsupp.embDomain` sans précondition. Dans le cadre
`Finset` explicite du lake, le même pas doit **prouver** que le support
de la scission-poussée `pushUp (split w P)` est contenu — et le restera
au cran suivant de l'induction — dans l'image liftée du support de
départ.

Ce module paie ce double coût en une brique : le **transfert de
contention** (le support scindé-poussé obéit à la contention transportée
par `snoc · 0`) et la **conservation des moments sous contenance** au
niveau lifté (les deux composantes de `mean_split_of_support` k2.0 lues
à travers les ponts de k2.6a).
-/

namespace Discrepancy.Komlos

/-- **Toute masse de la scission-poussée provient d'une masse de `P` à
distance `± w`** : si `pushUp (split w P) z ≠ 0`, alors `z` est sur
l'image de `liftUp` — `z = liftUp (x, b)` — et l'un de `P (x + w)`,
`P (x − w)` est non nul. La moitié vient de `pushUp_eq_zero` (hors
image, la poussée est nulle), l'autre des formes `max`/`min` de `split`
(une moitié non nulle force l'un des deux arguments non nul).

C'est l'auxiliaire de support que consomme le transfert de contenance
`supportContained_pushUp_split` : il ramène toute question de support
sur la poussée à une question de support sur `P`. -/
lemma pushUp_split_ne_zero {d : ℕ} (w : Fin d → ℤ) {P : (Fin d → ℤ) → ℝ}
    {z : Fin (d + 1) → ℤ} (hz : pushUp (split w P) z ≠ 0) :
    ∃ (x : Fin d → ℤ) (b : Bool), z = liftUp (x, b) ∧
      (P (x + w) ≠ 0 ∨ P (x - w) ≠ 0) := by
  by_cases hex : ∃ y : (Fin d → ℤ) × Bool, liftUp y = z
  · obtain ⟨⟨x, b⟩, rfl⟩ := hex
    rw [pushUp_apply] at hz
    refine ⟨x, b, rfl, ?_⟩
    cases b with
    | false =>
        rw [split_apply_zero] at hz
        rcases le_total (P (x + w)) (P (x - w)) with h | h
        · rw [max_eq_right h] at hz
          exact Or.inr (by intro h0; rw [h0, mul_zero] at hz; exact hz rfl)
        · rw [max_eq_left h] at hz
          exact Or.inl (by intro h0; rw [h0, mul_zero] at hz; exact hz rfl)
    | true =>
        rw [split_apply_one] at hz
        rcases le_total (P (x + w)) (P (x - w)) with h | h
        · rw [min_eq_left h] at hz
          exact Or.inl (by intro h0; rw [h0, mul_zero] at hz; exact hz rfl)
        · rw [min_eq_right h] at hz
          exact Or.inr (by intro h0; rw [h0, mul_zero] at hz; exact hz rfl)
  · rw [pushUp_eq_zero _ (fun y hy => hex ⟨y, hy⟩)] at hz
    exact absurd rfl hz

/-- **Transfert de contenance à travers la scission** : si `S` contient
le support de `P` et ses translatés par `A`, et si `A` est stable par
`± w`, alors l'image liftée `(S ×ˢ univ).map liftUpEmb` contient le
support de la scission-poussée `pushUp (split w P)` et ses translatés
par les décalages embarqués `Fin.snoc · 0` de `A`.

C'est la précondition de support que le pas de l'induction (k2.6c) doit
établir pour appliquer l'hypothèse d'induction à la dimension `d + 1` :
chez l'oracle (`Komlos/SignedSums.lean` l.44-53), le `Finsupp` paie ce
transport gratuitement (`Finsupp.embDomain`) ; le cadre `Finset` du lake
le paie ici. La stabilité de `A` par `± w` est le prix exact de la
scission : un point de masse `P (x ± w) ≠ 0` déplacé de `a` atterrit en
`x + a`, atteint depuis `x ± w` par le décalage `a ∓ w ∈ A`. -/
theorem supportContained_pushUp_split {d : ℕ} (w : Fin d → ℤ)
    {P : (Fin d → ℤ) → ℝ} {S A : Finset (Fin d → ℤ)}
    (hS : SupportContained S P A)
    (hA : ∀ a ∈ A, a + w ∈ A ∧ a - w ∈ A) :
    SupportContained ((S ×ˢ (Finset.univ : Finset Bool)).map liftUpEmb)
      (pushUp (split w P)) (A.image (fun a => Fin.snoc a 0)) := by
  intro z hz t ht
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨x, b, rfl, hPw⟩ := pushUp_split_ne_zero w hz
  rw [liftUp_add_snoc]
  show liftUp (x + a, b) ∈ (S ×ˢ (Finset.univ : Finset Bool)).map liftUpEmb
  refine Finset.mem_map.mpr ⟨(x + a, b), ?_, liftUpEmb_apply _⟩
  refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
  rcases hPw with h | h
  · have hxw := hS (x + w) h (a - w) (hA a ha).2
    have hxa : (x + w) + (a - w) = x + a := by
      funext j; simp only [Pi.add_apply, Pi.sub_apply]; ring
    rw [← hxa]; exact hxw
  · have hxw := hS (x - w) h (a + w) (hA a ha).1
    have hxa : (x - w) + (a + w) = x + a := by
      funext j; simp only [Pi.add_apply, Pi.sub_apply]; ring
    rw [← hxa]; exact hxw

/-- **Conservation du moment de base sous contenance, au niveau lifté** :
le moment coordonné de la scission-poussée, lu en coordonnée héritée
`i.castSucc`, est le moment de `P` en `i` — sous la même contention
`SupportContained S P {0, w, −w}` que `prodMoment_split_of_support`
(k2.0). C'est la composition du pont de moment `coordMoment_pushUp_castSucc`
(k2.6a, inconditionnel) avec l'identité de conservation de k2.0 : le
barycentre de base traverse la scission **puis** le pont de niveau sans
changement.

Consommateur mesuré : le `rw [mean_split, sum_smul_inl, …] at hmem` du
pas de l'induction (`Komlos/SignedSums.lean` l.54), composante spatiale. -/
theorem coordMoment_pushUp_split_of_support {d : ℕ} (w : Fin d → ℤ)
    {P : (Fin d → ℤ) → ℝ} {S : Finset (Fin d → ℤ)}
    (hS : SupportContained S P ({0, w, -w} : Finset (Fin d → ℤ)))
    (i : Fin d) :
    coordMoment (pushUp (split w P))
        ((S ×ˢ (Finset.univ : Finset Bool)).map liftUpEmb) i.castSucc
      = coordMoment P S i := by
  rw [coordMoment_pushUp_castSucc, prodMoment_split_of_support w hS i]

/-- **Le moment de hauteur de la scission-poussée, au niveau lifté** :
lu en dernière coordonnée, il est le bit de scission `splitBit w P S` —
la composante de hauteur de `mean_split_of_support` (k2.0) à travers le
pont `coordMoment_pushUp_last` (k2.6a). Aucune contention n'est
requise : le moment de hauteur se lit tranche par tranche
(`heightMoment_split`, k2.0).

Consommateur mesuré : le `rw [mean_split, …] at hmem` du pas de
l'induction (`Komlos/SignedSums.lean` l.54), composante de hauteur. -/
theorem coordMoment_pushUp_split_last {d : ℕ} (w : Fin d → ℤ)
    (P : (Fin d → ℤ) → ℝ) (S : Finset (Fin d → ℤ)) :
    coordMoment (pushUp (split w P))
        ((S ×ˢ (Finset.univ : Finset Bool)).map liftUpEmb) (Fin.last d)
      = splitBit w P S := by
  rw [coordMoment_pushUp_last, heightMoment_split]

/-- **La contenance du cran suivant, sous la forme exacte que
l'induction consomme** : si `A` contient `0`, `u` et `−u` et est stable
par `± w`, la scission-poussée obéit à la contention `{0, snoc u 0,
−snoc u 0}` sur l'image liftée. C'est l'instance par monotonie
(`SupportContained.mono`) du transfert générique, les trois décalages
étant les images `snoc · 0` de `0` (`snoc 0 0 = 0`), `u` et `−u`
(`−snoc u 0 = snoc (−u) 0`).

Le cran suivant de l'induction (k2.6c) scinde `pushUp (split w P)` dans
la direction `u` embarquée à hauteur nulle — les formes `_of_support` de
k2.0 (appliquées à la dimension `d + 1`) exigent exactement cette
contention à trois décalages. -/
theorem supportContained_pushUp_split_three {d : ℕ} (w u : Fin d → ℤ)
    {P : (Fin d → ℤ) → ℝ} {S A : Finset (Fin d → ℤ)}
    (hS : SupportContained S P A)
    (hA : ∀ a ∈ A, a + w ∈ A ∧ a - w ∈ A)
    (h0 : (0 : Fin d → ℤ) ∈ A) (hu : u ∈ A) (hu' : -u ∈ A) :
    SupportContained ((S ×ˢ (Finset.univ : Finset Bool)).map liftUpEmb)
      (pushUp (split w P))
      ({0, Fin.snoc u 0, -(Fin.snoc u 0)} : Finset (Fin (d + 1) → ℤ)) := by
  refine (supportContained_pushUp_split w hS hA).mono ?_
  intro t ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl
  · refine Finset.mem_image.mpr ⟨0, h0, ?_⟩
    funext j
    induction j using Fin.lastCases <;> simp
  · exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
  · refine Finset.mem_image.mpr ⟨-u, hu', ?_⟩
    funext j
    induction j using Fin.lastCases <;> simp [Pi.neg_apply]

end Discrepancy.Komlos
