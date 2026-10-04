/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapté à `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979) : toolchain v4.33.0, Mathlib `db584cd6`, convention i18n #4980.

Le source Dahia original vit dans le dépôt `gdahia/Komlos` (module
`Komlos/Transport.lean`, toolchain v4.34.0, cadre `Finsupp` sur `E →₀ ℝ`).
L'adaptation reprend le module **nom pour nom** dans le cadre Finset explicite
du lake (convention k1.1) — voir la portée ci-dessous.

**Portée de ce commit** (brique k2.3, `lake build SUCCESS` requis, 0 `sorry`) :

La brique k2.2 a **mesuré** le bloqueur de `pullback` : l'oracle l'énonce sur
`E →₀ ℝ` avec `E` un `ℝ`-module, l'enveloppe étant prise dans
`convexHull ℝ (P.support : Set E)` ; la base de ce lake est `Fin d → ℤ`, qui
n'est **pas** un `ℝ`-module. Cette brique livre le **transport de dimension**
qui lève ce bloqueur : le plongement coordonnée-par-coordonnée
`toReal : (Fin d → ℤ) →+ (Fin d → ℝ)`, sa poussée `push`, et les **deux ponts**
que la conclusion de convexité de k2.4 lit sur le support transporté —
l'appartenance (`toReal_mem_map_iff`) et le barycentre (`coordMoment_toReal`).

Transposé de `Komlos/Transport.lean` (l.27-67) :

- `toReal` + `toReal_injective` — l'instance du transport pour la grille du
  lake (`g ↦ g` coordonnée-par-coordonnée, le `g ↦ g / N` de l'oracle étant
  une homothétie de plus) ;
- `push e P` — la poussée le long d'un morphisme additif quelconque `e`
  entre les deux grilles, sur `Function.extend` (l'organe Mathlib du
  prolongement le long d'une injection — l'équivalent exact de
  `Finsupp.embDomain` chez l'oracle ; l'injectivité n'est requise que par
  les lemmes) ;
- `push_apply`, `push_eq_zero` — les deux identités de calcul (l.32 et le
  cas hors image) ;
- `sum_push` — la ré-indexation (l.35-36), forme `Finset` du lake ;
- `push_mass` — la masse est conservée (l.41-42, `mass_push`) ;
- `coordMomentReal_push` puis `coordMoment_toReal` — le barycentre transporté
  (l.66-67, `mean_push`) : côté grille réelle, le moment coordonné de la
  poussée par `toReal` **est** le `coordMoment` du lake (k2.0) ;
- `toReal_mem_map_iff`, `toReal_mem_coe_iff` — le pont d'appartenance que
  `convexHull ℝ ↑(S.map …)` consommera en k2.4.

**Reportés, avec raison mesurée** :

1. `shiftDist_push` (l.63-64) — la distance de décalage transportée. Chez
   l'oracle, `shiftDist` vit sur le support Finsupp **canonique** ; la
   convention du lake (k1.1) passe le support `Finset` **explicitement**, et
   l'énoncé transporté exige côté cible une ré-indexation de `S ∪ (S + u)` —
   une union de `Finset` dont la somme n'est pas la somme des sommes.
   Aucun consommateur k2.4 ne la lit : la conclusion de convexité ne lit que
   le support et le barycentre, tous deux livrés ci-dessus.
2. `tvDist_push`, `IsDist.push` (l.44-55) — le vocabulaire `tvDist`/`IsDist`
   n'existe pas dans ce lake (décision de cadre k1.1 : fonctions simples,
   support explicite). Les re-stater ici serait du **nouveau vocabulaire**,
   pas du transport ; si k4 en a besoin, il viendra avec son cadre.

L'état détaillé vit dans `FORMAL_STATUS.md`.
-/

import Discrepancy.Komlos.MeanSplit

/-!
# Transport de dimension (brique k2.3, Karingula–Lovett)

`Fin d → ℤ` n'est pas un `ℝ`-module : c'est le bloqueur que k2.2 a mesuré
pour `pullback`. Ce module le lève en plongeant la grille entière dans
`Fin d → ℝ` — où `convexHull ℝ` a un sens — par `toReal`, et en livrant les
deux ponts que la conclusion de Lemme 1.4 lit sur l'image : l'appartenance
au support transporté, et la conservation du barycentre coordonnée par
coordonnée.

**Pourquoi un module séparé.** Le transport est la pièce qui **change de
catégorie** (de ℤ à ℝ) : l'isoler rend chaque futur échec de build
attribuable — l'algèbre du pullback (k2.1), la convexité (k2.2) et le
transport (k2.3) vivent chacun dans leur module, et le pas complet (k2.4)
les consommera nommément.

**Généricité.** Comme chez l'oracle, la poussée `push` est livrée pour tout
morphisme additif **injectif** entre les deux grilles — `toReal` n'en est
qu'une instance. Le papier transporte aussi par homothétie `g ↦ g / N`
(`N > 0`) : composée avec `toReal`, elle entre dans la même généralité.
-/

namespace Discrepancy.Komlos

/-- **Transport de dimension** : le plongement coordonnée-par-coordonnée de
la grille entière dans la grille réelle, `(x i : ℤ) ↦ ((x i : ℤ) : ℝ)`.

C'est le morphisme qui lève le bloqueur mesuré en k2.2 : `Fin d → ℤ` n'est
pas un `ℝ`-module, `Fin d → ℝ` l'est — c'est là que `convexHull ℝ` (k2.2)
devient exprimable sur le support transporté. Additif par additivité
coordonnée du cast `ℤ → ℝ` ; injectif car le cast l'est. -/
def toReal {d : ℕ} : (Fin d → ℤ) →+ (Fin d → ℝ) where
  toFun x := fun i => (x i : ℝ)
  map_zero' := by funext i; simp
  map_add' := by intro x y; funext i; simp

/-- Lecture coordonnée du transport : `toReal x i = ((x i : ℤ) : ℝ)`. -/
@[simp] lemma toReal_apply {d : ℕ} (x : Fin d → ℤ) (i : Fin d) :
    toReal x i = (x i : ℝ) := rfl

/-- Le transport est **injectif** : le cast `ℤ → ℝ` l'est coordonnée par
coordonnée. C'est ce qui fait de `toReal` un plongement et permet la
ré-indexation `sum_push` sur l'image. -/
lemma toReal_injective {d : ℕ} : Function.Injective (toReal (d := d)) := by
  intro x y h
  funext i
  exact Int.cast_injective (congrFun h i)

/-- **Poussée d'une distribution le long d'un morphisme additif** :
`push e P (e x) = P x` (sous injectivité, cf `push_apply`) et `push e P y = 0`
hors de l'image de `e` (cf `push_eq_zero`).

C'est le `Finsupp.embDomain` de l'oracle (`Komlos/Transport.lean` l.27-28),
transposé aux fonctions simples du lake : l'organe Mathlib du prolongement
le long d'une injection est `Function.extend`, dont le défaut hors image est
ici la fonction nulle. Générique en `e` (morphisme additif quelconque entre
les deux grilles — l'injectivité n'est requise que par les **lemmes**,
`Function.extend` étant bien défini sans) ; `toReal` en est l'instance du
lake. -/
noncomputable def push {d : ℕ} (e : (Fin d → ℤ) →+ (Fin d → ℝ))
    (P : (Fin d → ℤ) → ℝ) :
    (Fin d → ℝ) → ℝ :=
  Function.extend ⇑e P 0

/-- Sur l'image, la poussée relit la distribution source : `push e P (e x) = P x`
— sous injectivité de `e`, sans quoi deux antécédents partageraient une
image. (Chez l'oracle : `push_apply`, l.32.) -/
@[simp] lemma push_apply {d : ℕ} (e : (Fin d → ℤ) →+ (Fin d → ℝ))
    (he : Function.Injective e) (P : (Fin d → ℤ) → ℝ) (x : Fin d → ℤ) :
    push e P (e x) = P x :=
  Function.Injective.extend_apply he P 0 x

/-- Hors de l'image du morphisme, la poussée est nulle : les points de la
grille réelle sans antécédent entier ne portent aucune masse. -/
lemma push_eq_zero {d : ℕ} (e : (Fin d → ℤ) →+ (Fin d → ℝ))
    (P : (Fin d → ℤ) → ℝ) {y : Fin d → ℝ}
    (hy : ∀ x, e x ≠ y) : push e P y = 0 := by
  have hb : ¬∃ a, ⇑e a = y := by
    rintro ⟨a, rfl⟩
    exact hy a rfl
  exact Function.extend_apply' P (0 : (Fin d → ℝ) → ℝ) y hb

/-- **Ré-indexation de la poussée** : sommer sur le support transporté,
c'est sommer sur le support source. (Chez l'oracle : `sum_push`, l.35-36,
forme `Finset` du lake — le contenu est la ré-indexation par le
plongement.) -/
lemma sum_push {d : ℕ} {β : Type*} [AddCommMonoid β]
    (e : (Fin d → ℤ) →+ (Fin d → ℝ)) (he : Function.Injective e)
    (S : Finset (Fin d → ℤ)) (f : (Fin d → ℝ) → β) :
    ∑ y ∈ S.map ⟨⇑e, he⟩, f y = ∑ x ∈ S, f (e x) :=
  Finset.sum_map S ⟨⇑e, he⟩ f

/-- **La masse est conservée par la poussée** : le moment d'ordre 0 se
transporte sans perte. (Chez l'oracle : `mass_push`, l.41-42.) -/
lemma push_mass {d : ℕ} (e : (Fin d → ℤ) →+ (Fin d → ℝ))
    (he : Function.Injective e) (P : (Fin d → ℤ) → ℝ) (S : Finset (Fin d → ℤ)) :
    ∑ y ∈ S.map ⟨⇑e, he⟩, push e P y = ∑ x ∈ S, P x := by
  rw [sum_push]
  exact Finset.sum_congr rfl fun x _ => push_apply e he P x

/-- **Moment coordonné côté grille réelle** : le barycentre d'une
distribution sur `Fin d → ℝ`, lu coordonnée par coordonnée. C'est le
pendant exact de `coordMoment` (k2.0) pour la grille cible — les
coordonnées y sont déjà réelles, le cast est l'identité. -/
noncomputable def coordMomentReal {d : ℕ} (Q : (Fin d → ℝ) → ℝ)
    (T : Finset (Fin d → ℝ)) (i : Fin d) : ℝ :=
  ∑ y ∈ T, Q y * y i

/-- **Forme générique du barycentre transporté** : le moment coordonné de la
poussée, sur le support transporté, se lit sur la source coordonnée par
coordonnée — chacune poussée dans `ℝ` par `e`. (Chez l'oracle : `mean_push`,
l.66-67, la scalarisation `r • e x` devenant la lecture coordonnée du lake.) -/
lemma coordMomentReal_push {d : ℕ} (e : (Fin d → ℤ) →+ (Fin d → ℝ))
    (he : Function.Injective e) (P : (Fin d → ℤ) → ℝ) (S : Finset (Fin d → ℤ))
    (i : Fin d) :
    coordMomentReal (push e P) (S.map ⟨⇑e, he⟩) i = ∑ x ∈ S, P x * e x i := by
  rw [coordMomentReal, sum_push]
  exact Finset.sum_congr rfl fun x _ => by rw [push_apply e he P x]

/-- **Le pont de barycentre** : pour le transport du lake (`e = toReal`), le
moment coordonné de la poussée sur le support transporté **est** le
`coordMoment` du lake (k2.0). C'est la pièce que la conclusion de convexité
de k2.4 lira : le barycentre affirmé dans l'enveloppe est exactement celui
que les moments k2.0 calculent. -/
lemma coordMoment_toReal {d : ℕ} (P : (Fin d → ℤ) → ℝ) (S : Finset (Fin d → ℤ))
    (i : Fin d) :
    coordMomentReal (push toReal P)
        (S.map ⟨⇑toReal, toReal_injective⟩) i = coordMoment P S i := by
  rw [coordMomentReal_push, coordMoment]
  exact Finset.sum_congr rfl fun x _ => by rw [toReal_apply]

/-- **Pont d'appartenance (forme `Finset`)** : `toReal x` appartient au
support transporté exactement quand `x` appartient au support source —
l'injectivité interdit à deux points entiers de partager une image. -/
lemma toReal_mem_map_iff {d : ℕ} (x : Fin d → ℤ) (S : Finset (Fin d → ℤ)) :
    toReal x ∈ (S.map ⟨⇑toReal, toReal_injective⟩ : Finset (Fin d → ℝ)) ↔ x ∈ S := by
  rw [Finset.mem_map]
  constructor
  · rintro ⟨x', hx', hxx'⟩
    have hxe : x' = x := toReal_injective hxx'
    rw [hxe] at hx'
    exact hx'
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- **Pont d'appartenance (forme `Set`)** : la même lecture au niveau
ensemble — c'est la forme que `convexHull ℝ (↑(S.map …) : Set (Fin d → ℝ))`
consommera en k2.4. -/
lemma toReal_mem_coe_iff {d : ℕ} (x : Fin d → ℤ) (S : Finset (Fin d → ℤ)) :
    toReal x ∈ (↑(S.map ⟨⇑toReal, toReal_injective⟩) : Set (Fin d → ℝ)) ↔ x ∈ S := by
  rw [Finset.mem_coe]
  exact toReal_mem_map_iff x S

end Discrepancy.Komlos
