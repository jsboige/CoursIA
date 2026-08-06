/-
Grothendieck hommage — Partie 6 : identités de pullback et lois de treillis
sur les cribles.

Alexandre Grothendieck (1928-2014).

Extension Phase 2 (#2159, Epic #2162).

La Partie 1 (`CategoryAndSites.lean`) introduit les cribles, les trois
axiomes, et le treillis complet `Sieve X`. Ce module enregistre les
identités fondamentales du **pullback le long de morphismes** :

  - `pullback_id` : pullback le long de l'identité = identité
  - `pullback_pullback` : pullback compose contravariance
  - `pullback_bot` : pullback du crible vide = crible vide
  - `pullback_monotone` : pullback monotone dans le crible
  - `pullback_inf` (Partie 8, `SieveOps.lean`) : pullback préserve ⊓
  - `pullback_union` : pullback préserve ⋃ (joins finis)
  - `pullback_ofObjects` : pullback distribue `Sieve.ofObjects` selon la cible
  - `mem_iff_pullback_eq_top` : `f ∈ S` ssi `Sieve.pullback f S = ⊤`

Ces identités complètent le tableau commencé par la calibration P2
(`pullback_top` dans `Calibration.lean`) et ouvrent la voie aux
travaux de Phase 3 sur la génération de cribles et la faisceautisation.

Epic #1646, Phase 2 (#2159). Tous les `sorry`s éliminés à la création.

### i18n — convention #4980 ratifiée 2026-07-04

Ce module est jumelé avec sa version anglaise canonique dans le fichier
sibling `SieveLattice_en.lean` (modèle sibling pair, voir PR #6154 pour le
pilote sur `Utility.lean`). Les énoncés de théorèmes, les noms de lemmes,
les tactiques Lean (`:= by`, `rfl`, `exact`, etc.) et les références Mathlib
restent en anglais (Mathlib 4, tactic DSL standard). Seules les **docstrings
`/-- ... -/`** et **commentaires `-- ...`** diffèrent entre les deux fichiers.
Anti-§D byte-identity garanti : le namespace body est préservé bit-pour-bit
(énoncés et preuves byte-identiques entre `SieveLattice.lean` et
`SieveLattice_en.lean`).
-/

import Mathlib.CategoryTheory.Sites.Grothendieck

namespace Grothendieck

open CategoryTheory

/-!
## Pullback le long de l'identité = identité

`Sieve.pullback (𝟙 X) S = S`. Tirer en arrière le long de l'identité ne
fait rien : `g` est dans le pullback ssi `g ≫ 𝟙 X = g` est dans `S`.
-/

/-- CALIBRATION (ext + simp) : pullback le long du morphisme identité
    est l'identité sur les cribles. -/
theorem pullback_id {C : Type*} [Category C] {X : C} (S : Sieve X) :
    (Sieve.pullback (𝟙 X) S) = S := by
  ext Y f
  simp [Sieve.pullback]

/-!
## Pullback compose contravariance

Pour un crible `S` sur `X` et des morphismes `f : Y ⟶ X`, `g : Z ⟶ Y`,
tirer `S` en arrière le long de `f` puis le long de `g` donne le même
crible que tirer `S` en arrière le long du composite `g ≫ f`.
-/

/-- CALIBRATION (ext + simp + assoc) : pullback compose contravariance.
    Tirer en arrière le long de `g ≫ f` égale tirer en arrière le long
    de `f` puis `g`. -/
theorem pullback_pullback {C : Type*} [Category C] {X Y Z : C} (S : Sieve X)
    (f : Y ⟶ X) (g : Z ⟶ Y) :
    (Sieve.pullback g (Sieve.pullback f S)) = Sieve.pullback (g ≫ f) S := by
  ext W h
  simp [Sieve.pullback, Category.assoc]

/-!
## Pullback du crible vide = crible vide

Le crible vide n'a aucune flèche ; le tirer en arrière le long d'un
morphisme quelconque donne encore le crible vide. Dual de `pullback_top`
(Calibration P2).
-/

/-- CALIBRATION (ext + simp) : pullback du crible vide le long d'un
    morphisme quelconque est le crible vide. -/
theorem pullback_bot {C : Type*} [Category C] {X Y : C} (f : Y ⟶ X) :
    (Sieve.pullback f (⊥ : Sieve X)) = (⊥ : Sieve Y) := by
  ext Z g
  simp [Sieve.pullback]

/-!
## Pullback est monotone dans le crible

Si `S ≤ T`, alors pour tout `f : Y ⟶ X`, `Sieve.pullback f S ≤ Sieve.pullback f T`.
C'est la composante order-théorique de la fonctorialité du pullback.
-/

/-- CALIBRATION (intro + simp + apply) : pullback est monotone dans le crible. -/
theorem pullback_monotone {C : Type*} [Category C] {X Y : C} (f : Y ⟶ X)
    {S T : Sieve X} (hST : S ≤ T) :
    Sieve.pullback f S ≤ Sieve.pullback f T := by
  intro Z g hg
  simp [Sieve.pullback] at hg ⊢
  exact hST _ hg

/-!
## Pullback distribue sur la join (union) de cribles

Dual de `pullback_inf` (Partie 9, `SieveOps.lean`) : le pullback preserve
egalement `⊔`. Tire en arriere de la join de deux cribles egale la join
de leurs pullbacks. Le resultat suit de la definition de `Sieve.union`
(une fleche `g : Z ⟶ Y` est dans `(S ⊔ R).pullback f` ssi
`g ≫ f` est dans `S` ou dans `R`, ce qui equivaut a etre dans
`S.pullback f` ou dans `R.pullback f`).

Identite non couverte par `Mathlib.CategoryTheory.Sites.Sieves`
(qui fournit `pullback_inter` mais pas son dual `pullback_union`) ;
extension Phase 2 (Issue #2159, Epic #1646).
-/

/-- CALIBRATION (ext + simp) : pullback distribue sur la join
    de cribles. Dual de `pullback_inf` (`SieveOps.lean`). -/
theorem pullback_union {C : Type*} [Category C] {X Y : C} (f : Y ⟶ X)
    (S R : Sieve X) :
    Sieve.pullback f (S ⊔ R) = Sieve.pullback f S ⊔ Sieve.pullback f R := by
  ext Z g
  simp [Sieve.pullback]

/-!
## Pullback distribue `ofObjects` selon la cible

`Sieve.ofObjects X Y` est le crible maximal « sous-objet » engendre par la
famille d'objets `X : I → C` au-dessus d'un objet `Y`. Le tirer en arriere
le long d'un morphisme `f : Z ⟶ Y` donne le crible « sous-objet » de la
meme famille au-dessus de `Z`. C'est la fonctorialite de `ofObjects` par
rapport a la cible.
-/

/-- CALIBRATION (ext + simp) : pullback distribue `ofObjects` selon la
    cible : `(Sieve.ofObjects X Y).pullback f = Sieve.ofObjects X Z`. -/
theorem pullback_ofObjects {C : Type*} [Category C] {I : Type*} (X : I → C)
    {Y Z : C} (f : Z ⟶ Y) :
    (Sieve.ofObjects X Y).pullback f = Sieve.ofObjects X Z := by
  ext W g
  simp [Sieve.pullback, Sieve.ofObjects]

/-!
## Caracterisation de l'appartenance par pullback

L'appartenance d'une fleche a un crible est exactement caracterisee par
son pullback : `f ∈ S` ssi `Sieve.pullback f S = ⊤`. C'est l'enonce
fondamental qui sous-tend les manipulations de stabilite et de
couverture dans les topologies de Grothendieck.
-/

/-- CALIBRATION (rfl) : `f ∈ S` ssi `Sieve.pullback f S = ⊤`. Restatement
    direct de `Sieve.mem_iff_pullback_eq_top`. -/
theorem mem_iff_pullback_eq_top {C : Type*} [Category C] {X Y : C}
    (S : Sieve X) (f : Y ⟶ X) :
    S f ↔ Sieve.pullback f S = ⊤ :=
  Sieve.mem_iff_pullback_eq_top f

end Grothendieck