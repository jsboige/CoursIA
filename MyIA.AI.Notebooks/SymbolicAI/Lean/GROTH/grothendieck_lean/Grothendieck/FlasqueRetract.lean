/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Hommage Grothendieck — Partie 81 : la flasquité descend aux rétractes.

Alexandre Grothendieck (1928-2014).

Extension Phase 2 (#2159, Epic #1646).

La Partie 79 a défini la flasquité au niveau des sites
(`Grothendieck.Flasque`, `IsFlasqueSieves`) : toute famille compatible sur
n'importe quel crible possède une amalgamation. La Partie 80 (branche
`feature/grothendieck-partie-80`) a étudié la stabilité par isomorphisme et
par produits. Cette partie généralise le premier maillon : la flasquité
descend le long d'une rétraction **unilatérale**.

  - `isFlasqueSieves_of_retract` : si `Q` est un rétracte de `P` — une
    paire `e : P ⟶ Q`, `s : Q ⟶ P` avec `s ≫ e = 𝟙 Q` — et si `P` est
    flasque, alors `Q` est flasque. L'invariance par isomorphisme
    (Godement II.3.1) en est le cas symétrique (les deux compositions
    égales à l'identité) ; ici une seule égalité suffit. La preuve pousse
    la famille le long de la section `s`, amalgame dans `P`, et revient
    par `e` : la compatibilité suit la naturalité de `s`, la conclusion
    celle de `e` et l'égalité `e ≫ s = 𝟙`.

  - `isFlasqueSieves_of_retract'` : la même lecture avec les rôles
    échangés — si `e ≫ s = 𝟙 P` et `Q` est flasque, alors `P` est
    flasque. C'est le théorème précédent renommé (`P` est alors le
    rétracte de `Q`) : les deux sens d'une split pair sont couverts par
    un seul énoncé, enregistrés séparément pour la consommation aval.

  - `isFlasqueSieves_of_iso'` : l'invariance par isomorphisme comme
    corollaire du rétracte (`e.inv ≫ e.hom = 𝟙`). Doublon délibéré du
    théorème de la Partie 80 (branche en cours de review) : ici il
    témoigne que le rétracte est bien la généralisation.

  - `isFlasqueSieves_of_retract_addCommGrp` : le pont vers le monde
    abélien — pour des préfaisceaux de groupes abéliens, le rétracte se
    transporte par `forget` (whiskering), donc la flasquité lue à travers
    `forget` descend aussi aux rétractes de préfaisceaux abéliens. C'est
    le cadre où vivent les rétractes utiles en pratique (faisceaux
    scindés, images directes fendues).

La lecture conceptuelle, dans le prolongement de la Partie 80 : ce qui se
transporte **sans choix**, ce n'est pas seulement l'isomorphisme — c'est
tout ce qui est rétracte. Une section `s` fournit le transport du retour ;
aucune donnée n'est choisie, tout est canoniquement déplacé. La frontière
établie en Partie 80 (le maillon `flasque => injectif` exige Zorn) est
confirmée : un rétracte ne coûte aucun choix, une extension maximale en
coûte un.

Références :
  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §3 (prop. 3.1 : l'invariance par isomorphisme, dont le
    rétracte est la forme unilatérale).
  - SGA 4, Exposé II (sites et cribles).
  - Partie 79 (`Grothendieck.Flasque`) : `IsFlasqueSieves`.
  - Partie 80 (`Grothendieck.FlasqueStability`, branche
    `feature/grothendieck-partie-80`) : invariance par iso, produits,
    frontière de l'acyclicité.

Convention i18n (EPIC #4980 ratifiée 2026-07-04) : ce module est jumelé avec
sa version anglaise canonique dans le fichier sibling
`Grothendieck/FlasqueRetract_en.lean` — suffixe `_en` sur le namespace
(`Grothendieck.FlasqueRetract_en`), imports identiques, docstrings et
commentaires traduits. Les énoncés de théorèmes, tactiques Lean, noms de
lemmes et références Mathlib restent en anglais (Mathlib 4, tactic DSL
standard). Seules les docstrings `/-- ... -/` et commentaires `-- ...`
diffèrent entre les deux fichiers. Anti-§D byte-identity garanti : le
namespace body est préservé bit-à-bit (énoncés et preuves byte-identiques
entre `FlasqueRetract.lean` et `FlasqueRetract_en.lean`).

Epic #1646, Phase 2 (#2159). Tous les `sorry`s éliminés à la création.
-/

import Mathlib.CategoryTheory.Sites.IsSheafFor
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.CategoryTheory.Whiskering
import Grothendieck.Flasque

namespace Grothendieck

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

section Retracte

variable {C : Type u} [Category.{v} C]

/-- **La flasquité descend aux rétractes** : si `Q` est un rétracte de `P`
(`e : P ⟶ Q`, `s : Q ⟶ P`, `s ≫ e = 𝟙 Q`) et `P` est flasque, `Q` est
flasque. La famille `Q` se pousse en famille `P` via la section `s`, la
compatibilité suit la naturalité, et l'amalgamation `t` revient par `e`.
L'invariance par isomorphisme (Godement II.3.1) en est le cas symétrique :
ici une seule composition égale à l'identité suffit. -/
theorem isFlasqueSieves_of_retract {P Q : Cᵒᵖ ⥤ Type (max v u)} (e : P ⟶ Q)
    (s : Q ⟶ P) (h : s ≫ e = 𝟙 Q) [IsFlasqueSieves P] : IsFlasqueSieves Q where
  amalgamates := by
    intro X S x hx
    obtain ⟨t, ht⟩ := IsFlasqueSieves.amalgamates (P := P) S
      (fun Y f hf => s.app (op Y) (x f hf))
      (fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ h' => by
        show P.map g₁.op (s.app (op Y₁) (x f₁ hf₁))
          = P.map g₂.op (s.app (op Y₂) (x f₂ hf₂))
        rw [← NatTrans.naturality_apply (φ := s) g₁.op (x f₁ hf₁),
          ← NatTrans.naturality_apply (φ := s) g₂.op (x f₂ hf₂),
          hx g₁ g₂ hf₁ hf₂ h'])
    refine ⟨e.app (op X) t, ?_⟩
    intro Y f hf
    have nat : (Q.map f.op) (e.app (op X) t)
        = e.app (op Y) ((P.map f.op) t) :=
      (NatTrans.naturality_apply (φ := e) f.op t).symm
    have hid : ∀ {Y : C} (z : Q.obj (op Y)),
        e.app (op Y) (s.app (op Y) z) = z := by
      intro Y z
      have hz := congrFun (congrArg (fun φ => φ.app (op Y)) h) z
      simpa using hz
    rw [nat, ht f hf, hid]

/-- **La même lecture, rôles échangés** : si `e ≫ s = 𝟙 P` (c'est alors
`P` qui est rétracte de `Q`) et `Q` est flasque, `P` est flasque. Les deux
sens d'une split pair sont couverts par un seul théorème ; cet alias
nommé sert la consommation aval. -/
theorem isFlasqueSieves_of_retract' {P Q : Cᵒᵖ ⥤ Type (max v u)} (e : P ⟶ Q)
    (s : Q ⟶ P) (h : e ≫ s = 𝟙 P) [IsFlasqueSieves Q] : IsFlasqueSieves P :=
  isFlasqueSieves_of_retract s e h

end Retracte

section Corollaires

variable {C : Type u} [Category.{v} C]

/-- **Invariance par isomorphisme comme corollaire du rétracte** : le
théorème de la Partie 80 se redéduit ici en une ligne, témoignant que le
rétracte unilatéral est bien la généralisation. -/
theorem isFlasqueSieves_of_iso' {P Q : Cᵒᵖ ⥤ Type (max v u)} (e : P ≅ Q)
    [IsFlasqueSieves P] : IsFlasqueSieves Q :=
  isFlasqueSieves_of_retract e.hom e.inv e.inv_hom_id

end Corollaires

section Abelian

variable {C : Type u} [Category.{v} C]

/-- **Pont vers le monde abélien** : pour des préfaisceaux de groupes
abéliens, le rétracte se transporte par `forget` (whiskering droit
préserve la composition et l'identité), donc la flasquité lue à travers
`forget` descend aux rétractes de préfaisceaux abéliens — le cadre où
vivent les rétractes utiles en pratique. -/
theorem isFlasqueSieves_of_retract_addCommGrp
    {F G : Cᵒᵖ ⥤ AddCommGrpCat.{max v u}} (e : F ⟶ G) (s : G ⟶ F)
    (h : s ≫ e = 𝟙 G)
    [IsFlasqueSieves (F ⋙ forget AddCommGrpCat.{max v u})] :
    IsFlasqueSieves (G ⋙ forget AddCommGrpCat.{max v u}) :=
  isFlasqueSieves_of_retract (Functor.whiskerRight e (forget AddCommGrpCat.{max v u}))
    (Functor.whiskerRight s (forget AddCommGrpCat.{max v u})) (by rw [← Functor.whiskerRight_comp, h, Functor.whiskerRight_id'])

end Abelian

end Grothendieck
