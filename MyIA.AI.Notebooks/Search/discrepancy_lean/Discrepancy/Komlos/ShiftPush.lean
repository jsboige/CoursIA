/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapté à `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979) : toolchain v4.33.0, Mathlib `db584cd6`, convention i18n #4980.

Le source Dahia original vit dans le dépôt `gdahia/Komlos` : `Komlos/Transport.lean`
(l.54-64 — `tvDist_push` et `shiftDist_push`). Ces deux énoncés y sont écrits sur des
`Finsupp` (`E →₀ ℝ`), où la distance de décalage vit sur le support **canonique**.
k2.3 les avait reportés avec leur raison mesurée : la convention du lake (k1.1) passe
le support `Finset` **explicitement**, et l'énoncé transporté semblait exiger une
ré-indexation de `S ∪ (S + u)` — une union de `Finset` dont la somme n'est pas la
somme des sommes.

**Ce commit lève le reporté, et la barrière se dissout au lieu de se franchir.** Le
k4.2b (`TvDistance.lean`) a livré `tvDistance`, générique en son type d'indices, et la
passerelle `shiftDistance_eq_tvDistance` : un décalage *est* une variation totale,
celle d'un poids contre son translaté. Sous cette forme, le décalage est porté par la
**fonction** (`x ↦ P (x + u)`), pas par l'ensemble de sommation : une seule `Finset`
suffit des deux côtés, et l'union `S ∪ (S + u)` n'apparaît jamais. La ré-indexation
requise est celle, déjà livrée, de `sum_push` (k2.3).

**Portée de ce commit** (brique k4.2c, `lake build SUCCESS` requis, 0 `sorry`) :

Briques closes : `shiftDistanceTV` (la distance de décalage sous forme variation
totale — la forme qui se transporte), `tvDistance_push` (le `tvDist_push` de l'oracle,
l.54-55), `shiftDistanceTV_push` (le `shiftDist_push` de l'oracle, l.63-64 — **le
dernier reporté de k2.3**), `shiftDistance_eq_shiftDistanceTV` (le pont vers le
`shiftDistance` de k1.1) et `shiftDistanceTV_push_toReal` (l'instance du transport du
lake, `toReal`).

**Reporté, avec raison mesurée** : `IsDist.push` (l.44-49) — il attend le vocabulaire
`IsDist` (« est une distribution »), que ce lake n'a pas (décision de cadre k1.1 :
fonctions simples, support explicite). Ce n'est pas du transport à re-stater, c'est un
vocabulaire à payer avec son consommateur ; k4.3 le paiera s'il l'exige, comme k4.2c
paie ici le sien.

**Consommé par** : la boute k4.3 (`NearInvariant.lean`, Lemme 1.5), dont
`exists_nearInvariant` lit `shiftDist_push` sur `gridEmb d N` dans son troisième but.
-/

import Discrepancy.Komlos.TvDistance
import Discrepancy.Komlos.Transport

/-!
# Distance de décalage transportée (brique k4.2c)

`shiftDistanceTV s P u = tvDistance s (fun x ↦ P (x + u)) P` : la distance de
décalage écrite comme **une variation totale entre un poids et son translaté** — la
forme sous laquelle elle se transporte le long d'un plongement additif.

Deux formes de la même quantité coexistent désormais dans le lake : `shiftDistance`
(k1.1), posée sur la grille entière `Fin d → ℤ`, et `shiftDistanceTV`, générique en
tout type d'indices **additif** — donc disponible sur la grille cible `Fin d → ℝ`, où
`Fin d → ℤ` n'est pas un `ℝ`-module. Le pont `shiftDistance_eq_shiftDistanceTV` les
identifie sur la grille entière.

Le résultat porteur est `shiftDistanceTV_push` : **pousser un poids le long d'un
morphisme additif injectif ne change pas sa distance de décalage**, le décalage
devenant l'image du décalage source. C'est l'énoncé dont k4.3 (Lemme 1.5) a besoin
pour lire la borne de `Komlos.Cube` sur la grille réelle : le poids `cubeF` y est
poussé par `gridEmb d N` (`g ↦ g / N`), et `shiftDistanceTV_push` transporte la
distance sans la recalculer.
-/

namespace Discrepancy.Komlos

open Finset

variable {ι : Type*} [Add ι]

/-- **Distance de décalage en forme de variation totale** :
`shiftDistanceTV s P u = tvDistance s (fun x ↦ P (x + u)) P`.

C'est la distance de décalage de k1.1 sous la forme que le transport lit : le
décalage est porté par la **fonction** (`x ↦ P (x + u)`), et une seule `Finset` `s`
porte les deux poids — là où la lecture « translation de l'ensemble de sommation »
demanderait une union `S ∪ (S + u)`.

Générique en tout type d'indices additif `ι` : c'est ce qui la rend disponible sur la
grille cible `Fin d → ℝ` (k4.3), là où le `shiftDistance` de k1.1 est posé sur la
grille entière `Fin d → ℤ`. -/
noncomputable def shiftDistanceTV (s : Finset ι) (P : ι → ℝ) (u : ι) : ℝ :=
  tvDistance s (fun x ↦ P (x + u)) P

/-- **Le pont vers la distance de décalage de k1.1** : sur la grille entière, les
deux formes sont la même quantité — c'est la passerelle `shiftDistance_eq_tvDistance`
du k4.2b, relue dans le vocabulaire de ce module.

Elle rend le résultat porteur applicable au `shiftDistance` de k1.1 sans le
ré-énoncer : `shiftDistance S P u = shiftDistanceTV S P u`. -/
lemma shiftDistance_eq_shiftDistanceTV {d : ℕ} (S : Finset (Fin d → ℤ))
    (P : (Fin d → ℤ) → ℝ) (u : Fin d → ℤ) :
    shiftDistance S P u = shiftDistanceTV S P u := by
  unfold shiftDistanceTV
  exact shiftDistance_eq_tvDistance S P u

/-- **La variation totale est conservée par la poussée** (chez l'oracle :
`tvDist_push`, `Komlos/Transport.lean` l.54-55).

Pousser deux poids le long d'un même morphisme additif injectif et sommer sur l'image
du support, c'est sommer sur le support source : la ré-indexation est `sum_push`
(k2.3), et sur l'image la poussée relit la source (`push_apply`). La forme `Finset`
rend l'énoncé **inconditionnel** — pas d'hypothèse de support à porter, l'ensemble de
sommation est un paramètre. -/
lemma tvDistance_push {d : ℕ} (e : (Fin d → ℤ) →+ (Fin d → ℝ))
    (he : Function.Injective e) (S : Finset (Fin d → ℤ))
    (P Q : (Fin d → ℤ) → ℝ) :
    tvDistance (S.map ⟨⇑e, he⟩) (push e P) (push e Q) = tvDistance S P Q := by
  unfold tvDistance
  congr 1
  rw [sum_push e he S (fun y ↦ |push e P y - push e Q y|)]
  exact sum_congr rfl fun x _ ↦ by rw [push_apply e he P x, push_apply e he Q x]

/-- **La distance de décalage est conservée par la poussée** — le `shiftDist_push` de
l'oracle (`Komlos/Transport.lean` l.63-64), **dernier reporté de k2.3**.

Pousser un poids le long d'un morphisme additif injectif `e` transporte sa distance de
décalage : celle du poids poussé sous le décalage image `e u` est celle du poids source
sous `u`. La preuve est la ré-indexation `sum_push` (k2.3) — le décalage n'a pas à être
transporté séparément, parce qu'il est **déjà** porté par la fonction (`shiftDistanceTV`)
et que `e` est additif : `e x + e u = e (x + u)`. L'union `S ∪ (S + u)` que k2.3
redoutait n'apparaît nulle part. -/
lemma shiftDistanceTV_push {d : ℕ} (e : (Fin d → ℤ) →+ (Fin d → ℝ))
    (he : Function.Injective e) (S : Finset (Fin d → ℤ))
    (P : (Fin d → ℤ) → ℝ) (u : Fin d → ℤ) :
    shiftDistanceTV (S.map ⟨⇑e, he⟩) (push e P) (e u) = shiftDistanceTV S P u := by
  unfold shiftDistanceTV tvDistance
  congr 1
  rw [sum_push e he S (fun y ↦ |push e P (y + e u) - push e P y|)]
  exact sum_congr rfl fun x _ ↦ by
    rw [← map_add, push_apply e he P (x + u), push_apply e he P x]

/-- **L'instance du transport du lake** : le décalage se transporte par `toReal`, le
plongement coordonnée-par-coordonnée de k2.3 — le morphisme additif injectif sur
lequel tout le transport de dimension est bâti.

C'est le cas que k4.3 instancie, son `gridEmb d N` (`g ↦ g / N`) étant une homothétie
composée à `toReal` : la distance de décalage de `push toReal P` sous `toReal u` est
celle de `P` sous `u`. -/
lemma shiftDistanceTV_push_toReal {d : ℕ} (S : Finset (Fin d → ℤ))
    (P : (Fin d → ℤ) → ℝ) (u : Fin d → ℤ) :
    shiftDistanceTV (S.map ⟨⇑toReal, toReal_injective⟩) (push toReal P) (toReal u)
      = shiftDistanceTV S P u :=
  shiftDistanceTV_push toReal toReal_injective S P u

/-! ## Note d'adaptation (brique k4.2c)

**Statut** : 5 briques closes — le `tvDist_push` / `shiftDist_push` de l'oracle
(`Komlos/Transport.lean` l.54-64) est porté dans la convention `Finset` du lake, et
le **dernier reporté de k2.3** est soldé. La boute k4.3 (Lemme 1.5) n'attend plus
aucun énoncé reporté.

**Ce qui a changé par rapport à l'oracle** : chez lui la poussée est un
`Finsupp.embDomain`, qui transporte le support **avec** le poids, et son `shiftDist`
somme sur ce support canonique — l'énoncé se prouve alors par réécriture
(`rw [shiftDist, tr_push, tvDist_push, shiftDist]`). Dans le lake, le support est un
paramètre : la poussée transporte l'**ensemble** de sommation (`S.map ⟨e, he⟩`), et
le décalage reste dans la fonction. Les deux énoncés portent donc sur des objets
différents — mais disent la même chose, et c'est le second qui se compose avec
`convexHull ℝ` (k2.4) et avec la borne de `Komlos.Cube` (k4.2).

**Ce que le transport ne fait pas** : il ne change pas la distance, il la **relit**
sur la cible. `shiftDistanceTV_push` est une égalité, pas une inégalité — il n'y a
aucune perte à transporter, et k4.3 peut donc lire la borne
`shiftDistance_cubeF_sq_le` (k4.2, sur `Fin d → ℤ`) sur la grille réelle sans
re-prouver quoi que ce soit.

**Vérification** : `lake build Discrepancy.Komlos.ShiftPush` (module + jumeau),
0 `sorry`, `distinct_code_sorry = 0` sur le lake. -/

end Discrepancy.Komlos