/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Partie 36 : la couverture bundlee

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Les parties 1-29 ont etabli les fondamentaux : categories, cribles, topologies,
lois de treillis, identites de pullback, bases de faisceaux, cloture couvrante,
calibration, sous-canonicalite, topologies denses, faisceaux, hom interne,
cohomologie de Cech, limite de Mayer-Vietoris, extensions de Kan, adjonctions,
monades, equivalences, categories monoidales, limites et colimites, couples
comma, images directes. La partie 35 a enregistre les theoremes propres sur la
forme fleche de la couverture (`J.Covers S f`).

Ce module enregistre des **theoremes propres** sur la **couverture bundlee** :
pour une topologie de Grothendieck `J` sur une categorie `C` et un objet `X`,
le type `J.Cover X` regroupe les cribles couvrants de `X` :
`J.Cover X = { S : Sieve X // S ∈ J X }` (sous-type avec coefficient coercible
`↑S : Sieve X` et membership `S f` via `CoeFun`). La couverture bundlee
transporte l'ordre, le treillis, les lois de pullback, la structure `Arrow`
(les fleches de `S`) et l'operation de raffinage `bind` — toute la structure
issue de l'axiome de stabilite par pullback.

Les theoremes enonces ici sont des **preuves tactiques reelles** (veine DEEP,
a la difference des ponts re-export des parties precedentes) :

  - `cover_iff_coe_mem` : un crible `S` est couvrant ssi il est le coefficient
    d'une couverture (le sous-type reconstruit la famille).
  - `coe_injective` : le coefficient est injectif (le sous-type est fidele).
  - `top_coe`, `top_apply` : le plus grand element est le crible universel.
  - `inf_apply` : l'infimum de deux couvertures est leur intersection.
  - `pullback_top`, `pullback_inf` : le pullback commute avec top et inf.
  - `pullback_monotone` : le pullback est monotone.
  - `pullbackId_apply`, `pullbackComp_apply` : lois d'identite et de
    composition du pullback (coincident avec `pullbackId`/`pullbackComp`).
  - `precomp_condition`, `base_condition` : les conditions de membership des
    fleches precomposees et remontees.
  - `precompRelation_spec` : la relation de precomposition est un raffinage
    (egalite dans le carre).
  - `bind_mem_iff` : la membership exacte de `S.bind T`.
  - `bindToBase_le` : le raffinage est au-dessus de la base (le bind est plus
    fin que la couverture de depart).

Chaque preuve mobilise un lemme Mathlib distinct (`Sieve.ext`, `Subtype.ext`,
`Sieve.top_apply`, `Sieve.inter_apply`, `Sieve.pullback_monotone`,
`Category.id_comp`, `Category.assoc`, `Sieve.downward_closed`) et les lois
definitionnelles de la structure `J.Cover` — aucune preuve n'est un simple
re-export.

EPIC #1646, Phase 5 (#2159). Tous les `sorry`s elimines a la creation.

### Convention i18n (EPIC #4980 ratifiee par user 2026-07-04)

Ce module est apparie avec son jumeau anglais dans le fichier sibling
`Cover_en.lean` (modele sibling pair, voir PR #6154 pour le pilote sur
`Utility.lean`). Namespace suffix `_en` applique au fichier EN (anti-collision,
conforme code-style.md #4980). Les enonces de theoremes, les noms de lemmes,
les tactiques Lean et les references Mathlib restent en anglais ; seules les
docstrings `/-- ... -/` et les commentaires `-- ...` different entre les deux
fichiers (preservation byte-identity).
-/

import Mathlib.CategoryTheory.Sites.Grothendieck

namespace Grothendieck.Cover

open CategoryTheory

/-!
## Section 1 : extensionalite et constantes

Rappel : `J.Cover X` est definitionnellement `{ S : Sieve X // S ∈ J X }`, le
coefficient est la projection `(T : Sieve X)` et la membership `T f` est celle
du coefficient. Le premier theoreme caracterise l'appartenance `S ∈ J X` par
l'existence d'une couverture de coefficient `S` ; le second exprime la
fidelite du sous-type.
-/

/-- Un crible `S` est couvrant ssi il existe une couverture de coefficient
    `S` : `S ∈ J X ↔ ∃ T : J.Cover X, (T : Sieve X) = S`.
    Preuve : le sens direct construit le sous-type `⟨S, h⟩` (l'appartenance
    est l'hypothese) et conclut par reflexivite ; le sens reciproque reecrit
    l'appartenance de `S` en celle de `T` (`rw [← hT]`) et invoque
    `T.condition`, la propriete du sous-type. -/
theorem cover_iff_coe_mem {C : Type*} [Category C] {X : C}
    (J : GrothendieckTopology C) (S : Sieve X) :
    S ∈ J X ↔ ∃ T : J.Cover X, (T : Sieve X) = S := by
  constructor
  · intro h
    exact ⟨⟨S, h⟩, rfl⟩
  · rintro ⟨T, hT⟩
    rw [← hT]
    exact T.condition

/-- Le coefficient est injectif : `Function.Injective (fun T : J.Cover X =>
    (T : Sieve X))`.
    Preuve : on decompose les deux sous-types `⟨S, _hS⟩` et `⟨T, _hT⟩` ; la
    preuve d'egalite des coefficients fournit `S = T` (beta-reduction du
    lambda), que `Subtype.ext` releve en egalite des sous-types. -/
theorem coe_injective {C : Type*} [Category C] {X : C}
    (J : GrothendieckTopology C) :
    Function.Injective (fun T : J.Cover X => (T : Sieve X)) := by
  rintro ⟨S, _hS⟩ ⟨T, _hT⟩ h
  change S = T at h
  exact Subtype.ext h

/-- Le coefficient du plus grand element est le crible universel :
    `((⊤ : J.Cover X) : Sieve X) = ⊤`.
    Preuve : definitionnelle — le `OrderTop` de `J.Cover X` est le sous-type
    `⟨⊤, J.top_mem _⟩` et le coefficient est la projection. -/
theorem top_coe {C : Type*} [Category C] {X : C}
    (J : GrothendieckTopology C) : ((⊤ : J.Cover X) : Sieve X) = ⊤ := rfl

/-- Le plus grand element est couvrant pour toute fleche :
    `(⊤ : J.Cover X) f`.
    Preuve : on passe au coefficient, on reecrit par `top_coe` puis on
    invoque `Sieve.top_apply`, la membership du crible universel (qui n'est
    pas une regle `simp` : l'appel est explicite). -/
theorem top_apply {C : Type*} [Category C] {X Y : C} (J : GrothendieckTopology C)
    (f : Y ⟶ X) : (⊤ : J.Cover X) f := by
  rw [top_coe]
  exact Sieve.top_apply f

/-- La membership de l'infimum est la conjonction des memberships :
    `(S ⊓ T) f ↔ S f ∧ T f`.
    Preuve : l'infimum du sous-type est le sous-type de l'intersection des
    coefficients (`SemilatticeInf.inf = fun S T => ⟨↑S ⊓ ↑T, _⟩`), donc on
    passe aux coefficients puis on invoque `Sieve.inter_apply` (regle
    `simp`). -/
theorem inf_apply {C : Type*} [Category C] {X Y : C} (J : GrothendieckTopology C)
    (S T : J.Cover X) (f : Y ⟶ X) :
    (S ⊓ T) f ↔ S f ∧ T f := by
  change ((S : Sieve X) ⊓ (T : Sieve X)) f ↔ (S : Sieve X) f ∧ (T : Sieve X) f
  rw [Sieve.inter_apply]

/-!
## Section 2 : identites de pullback

Les cinq theoremes suivants portent sur `pullback (S : J.Cover X)
(f : Y ⟶ X)`, la couverture `S.pullback f` sur `Y`, dont la membership est
donnee par la regle `simp` `GrothendieckTopology.Cover.coe_pullback : (S.pullback f) g ↔ S (g ≫ f)`.
-/

/-- Le pullback du plus grand element est le plus grand element :
    `(⊤ : J.Cover X).pullback f = ⊤`.
    Preuve : on raisonne par extensionalite (`Cover.ext`), on reecrit par
    `GrothendieckTopology.Cover.coe_pullback` puis par `top_coe` des deux cotes, et on conclut par
    `Sieve.top_apply` dans chaque direction. -/
theorem pullback_top {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) (f : Y ⟶ X) :
    (⊤ : J.Cover X).pullback f = ⊤ := by
  apply GrothendieckTopology.Cover.ext
  intro Z g
  rw [GrothendieckTopology.Cover.coe_pullback, top_coe, top_coe]
  exact ⟨fun _ => Sieve.top_apply g, fun _ => Sieve.top_apply (g ≫ f)⟩

/-- Le pullback commute avec l'infimum :
    `(S ⊓ T).pullback f = S.pullback f ⊓ T.pullback f`.
    Preuve : extensionalite puis reecriture par `GrothendieckTopology.Cover.coe_pullback` et
    `inf_apply` de chaque cote (le `rw` reduit les trois membres a la meme
    conjonction). -/
theorem pullback_inf {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) (S T : J.Cover X) (f : Y ⟶ X) :
    (S ⊓ T).pullback f = S.pullback f ⊓ T.pullback f := by
  apply GrothendieckTopology.Cover.ext
  intro Z g
  rw [GrothendieckTopology.Cover.coe_pullback, inf_apply, inf_apply, GrothendieckTopology.Cover.coe_pullback, GrothendieckTopology.Cover.coe_pullback]

/-- Le pullback est monotone : si `S ≤ T` alors `S.pullback f ≤ T.pullback f`.
    Preuve : les ordres sont pointwise ; on ramene l'hypothese aux
    coefficients, on transforme les membres de la conclusion en pullbacks de
    cribles, et on invoque `Sieve.pullback_monotone`. -/
theorem pullback_monotone {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) {S T : J.Cover X} (f : Y ⟶ X) (h : S ≤ T) :
    S.pullback f ≤ T.pullback f := by
  change (S : Sieve X) ≤ (T : Sieve X) at h
  change (S : Sieve X).pullback f ≤ (T : Sieve X).pullback f
  exact Sieve.pullback_monotone f h

/-- Le pullback le long de l'identite est l'identite :
    `S.pullback (𝟙 X) = S`.
    Preuve : extensionalite puis reecriture par `GrothendieckTopology.Cover.coe_pullback` ; la
    membership devient `S (g ≫ 𝟙 X)` et `simp` reduit `g ≫ 𝟙 X` a `g`
    (`Category.comp_id`). -/
theorem pullbackId_apply {C : Type*} [Category C] {X : C}
    (J : GrothendieckTopology C) (S : J.Cover X) :
    S.pullback (𝟙 X) = S := by
  apply GrothendieckTopology.Cover.ext
  intro Y g
  rw [GrothendieckTopology.Cover.coe_pullback]
  simp

/-- Le pullback le long d'une composition est la composition des pullbacks :
    `S.pullback (f ≫ g) = (S.pullback g).pullback f`.
    Preuve : extensionalite, trois reecritures par `GrothendieckTopology.Cover.coe_pullback` puis
    `Category.assoc` (orientation inverse) ramenent la membership de gauche a
    celle de droite. -/
theorem pullbackComp_apply {C : Type*} [Category C] {X Y Z : C}
    (J : GrothendieckTopology C) (S : J.Cover X) (f : Z ⟶ Y) (g : Y ⟶ X) :
    S.pullback (f ≫ g) = (S.pullback g).pullback f := by
  apply GrothendieckTopology.Cover.ext
  intro W h
  rw [GrothendieckTopology.Cover.coe_pullback, GrothendieckTopology.Cover.coe_pullback, GrothendieckTopology.Cover.coe_pullback, ← Category.assoc]

/-!
## Section 3 : fleches de la couverture

Rappel : `S.Arrow` est la structure des fleches `I : I.Y ⟶ X` dont la
membership `S I.f` est la condition `I.hf`. La precomposition `I.precomp g`
repond a la stabilite par precomposition : `(I.precomp g).f = g ≫ I.f`
(simps de `precomp`).
-/

/-- La fleche precomposee est encore une fleche de la couverture :
    `S (g ≫ I.f)`.
    Preuve : definitionnelle — `(I.precomp g).f` est `g ≫ I.f` (le corps de
    `precomp`), donc `(I.precomp g).hf` a exactement le type cherche. -/
theorem precomp_condition {C : Type*} [Category C] {X Z : C}
    (J : GrothendieckTopology C) {S : J.Cover X} (I : S.Arrow)
    (g : Z ⟶ I.Y) : S (g ≫ I.f) :=
  (I.precomp g).hf

/-- La fleche remontee le long de `f` est une fleche de la couverture de
    depart : `S (I.f ≫ f)`.
    Preuve : definitionnelle — `I.base` est `⟨I.Y, I.f ≫ f, I.hf⟩`, donc
    `I.base.hf` a exactement le type cherche (la membership de `S.pullback f`
    est la membership de `S` apres composition par `f`). -/
theorem base_condition {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) {S : J.Cover X} (f : Y ⟶ X)
    (I : (S.pullback f).Arrow) : S (I.f ≫ f) :=
  I.base.hf

/-- La relation de precomposition est un raffinage :
    `𝟙 Z ≫ (I.precomp g).f = g ≫ I.f`.
    Preuve : le champ `w` de `I.precompRelation g` enonce
    `g₁ ≫ (I.precomp g).f = g₂ ≫ I.f` avec `g₁ = 𝟙 (I.precomp g).Y` et
    `g₂ = g` ; comme `(I.precomp g).Y` se reduit definitionnellement a `Z`,
    `w` a exactement le type de la conclusion et `exact` conclut. -/
theorem precompRelation_spec {C : Type*} [Category C] {X Z : C}
    (J : GrothendieckTopology C) {S : J.Cover X} (I : S.Arrow)
    (g : Z ⟶ I.Y) : 𝟙 Z ≫ (I.precomp g).f = g ≫ I.f := by
  exact (I.precompRelation g).w

/-!
## Section 4 : le raffinage bind

Rappel : `S.bind T` assemble une famille de couvertures `T I` indexee par les
fleches de `S` en une couverture de `X` : `f` y appartient ssi il se factorise
a travers une fleche `e2` de `S` (celle-ci couvrant `e1`).
-/

/-- La membership de `S.bind T` :
    `(S.bind T) f ↔ ∃ (Z) (e1 : Y ⟶ Z) (e2 : Z ⟶ X) (hS : S e2),
     (T ⟨Z, e2, hS⟩) e1 ∧ e1 ≫ e2 = f`.
    Preuve : definitionnelle — le membre gauche est la membership du crible
    `Sieve.bind S (fun Y f hf => T ⟨Y, f, hf⟩)` dont la definition est
    exactement cette factorisation (binder par binder, la conjonction
    comprise). -/
theorem bind_mem_iff {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) {S : J.Cover X} (T : ∀ I : S.Arrow, J.Cover I.Y)
    (f : Y ⟶ X) :
    (S.bind T) f ↔
      ∃ (Z : C) (e1 : Y ⟶ Z) (e2 : Z ⟶ X) (hS : S e2),
        (T ⟨Z, e2, hS⟩) e1 ∧ e1 ≫ e2 = f := by
  rfl

/-- Le raffinage est au-dessus de la base : `S.bind T ≤ S`.
    Preuve : les ordres sont pointwise ; une membership de `S.bind T` se
    factorise en `e1 ≫ e2 = f` avec `S e2`, on reecrit puis on invoque
    `Sieve.downward_closed` (l'argument `h1` puis le morphisme `e1`), la
    stabilite par precomposition du crible. -/
theorem bindToBase_le {C : Type*} [Category C] {X : C}
    (J : GrothendieckTopology C) {S : J.Cover X} (T : ∀ I : S.Arrow, J.Cover I.Y) :
    S.bind T ≤ S := by
  intro Y f hf
  rcases hf with ⟨Z, e1, e2, h1, _hT, h3⟩
  rw [← h3]
  exact (S : Sieve X).downward_closed h1 e1

end Grothendieck.Cover
