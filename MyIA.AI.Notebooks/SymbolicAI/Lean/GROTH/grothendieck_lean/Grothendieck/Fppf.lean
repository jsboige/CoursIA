/-
Copyright (c) 2026 Anthropic PBC. All rights reserved.
Released under Apache 2.0 license as described in `LICENSE-Apache-2.0.txt`.

Adaptation pédagogique de `Definitions/Def_AlgebraicGeometry_FppfSiteCohomology.lean`
du dépôt `anthropics/fermats-last-theorem`, commit
aa2d8b34692b16c70f699536de0d8e75b9a3e9ef. Voir `NOTICE.md`.

# Propriété, précouverture et topologie fppf

La topologie fppf est engendrée par les familles de morphismes fidèlement
plats et localement de présentation finie qui sont conjointement surjectives.
Ce module isole le socle formel réutilisable :

- la propriété `fppfProperty = Flat ⊓ LocallyOfFinitePresentation` ;
- les ponts entre précouverture, prétopologie et topologie de Grothendieck ;
- les inclusions `étale ≤ fppf` et `Zariski ≤ fppf`.

Le petit site fppf et sa cohomologie restent hors périmètre de ce premier
socle. Mathlib 4.33 requiert ici que l'unification examine les définitions
transparentes pour synthétiser les instances de l'intersection de propriétés.
L'option `backward.isDefEq.respectTransparency` est donc désactivée dans ce
seul module, au lieu d'être propagée au `lakefile` et aux autres modules.

Convention i18n #4980 : le sibling anglais `Fppf_en.lean` conserve les mêmes
énoncés et preuves ; seuls namespace, docstrings et commentaires diffèrent.
-/

import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat

universe u

open CategoryTheory

namespace Grothendieck.Fppf

open AlgebraicGeometry AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency.types false

/-- Les morphismes localement de présentation finie sont multiplicatifs. -/
instance : MorphismProperty.IsMultiplicative @LocallyOfFinitePresentation where
  id_mem _ := inferInstance

/-- Propriété fppf : plat et localement de présentation finie. -/
abbrev fppfProperty : MorphismProperty Scheme.{u} :=
  @Flat ⊓ @LocallyOfFinitePresentation

example : fppfProperty.{u}.IsStableUnderBaseChange := inferInstance
example : fppfProperty.{u}.IsMultiplicative := inferInstance
example : fppfProperty.{u}.IsStableUnderComposition := inferInstance
example : fppfProperty.{u}.RespectsIso := inferInstance
example : fppfProperty.{u}.ContainsIdentities := inferInstance
example : fppfProperty.{u}.HasPullbacks := inferInstance

/-- La précouverture fppf de Mathlib est celle engendrée par `fppfProperty`. -/
theorem fppfPrecoverage_eq_precoverage_fppfProperty :
    fppfPrecoverage.{u} = Scheme.precoverage fppfProperty := rfl

instance : fppfPrecoverage.{u}.HasIsos :=
  inferInstanceAs (Scheme.precoverage fppfProperty.{u}).HasIsos

instance : fppfPrecoverage.{u}.HasPullbacks :=
  inferInstanceAs (Scheme.precoverage fppfProperty.{u}).HasPullbacks

/-- Prétopologie associée à la propriété fppf. -/
def fppfPretopology : Pretopology Scheme.{u} :=
  Scheme.pretopology fppfProperty

/-- La topologie fppf est la topologie de Grothendieck engendrée par la propriété fppf. -/
theorem fppfTopology_eq_grothendieckTopology :
    fppfTopology.{u} = Scheme.grothendieckTopology fppfProperty := rfl

/-- La prétopologie fppf engendre exactement la topologie fppf. -/
theorem fppfTopology_eq_toGrothendieck_fppfPretopology :
    fppfTopology.{u} = fppfPretopology.toGrothendieck :=
  Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck.symm

/-- Tout morphisme étale est fppf. -/
theorem etale_le_fppfProperty : @Etale ≤ fppfProperty.{u} := by
  intro X Y f hf
  have h := Etale.iff_flat_and_formallyUnramified.mp hf
  exact ⟨h.1, h.2.2⟩

/-- Toute famille couvrante étale est une famille couvrante fppf. -/
theorem etalePrecoverage_le_fppfPrecoverage :
    etalePrecoverage.{u} ≤ fppfPrecoverage :=
  Scheme.precoverage_mono etale_le_fppfProperty

/-- La topologie étale est plus fine que la topologie fppf. -/
theorem etaleTopology_le_fppfTopology :
    etaleTopology.{u} ≤ fppfTopology :=
  Precoverage.toGrothendieck_mono etalePrecoverage_le_fppfPrecoverage

/-- La topologie de Zariski est plus fine que la topologie fppf. -/
theorem zariskiTopology_le_fppfTopology :
    zariskiTopology.{u} ≤ fppfTopology :=
  Precoverage.toGrothendieck_mono zariskiPrecoverage_le_fppfPrecoverage

end Grothendieck.Fppf
