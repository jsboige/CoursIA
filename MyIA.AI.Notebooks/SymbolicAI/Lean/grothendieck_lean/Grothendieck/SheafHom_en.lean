/-
# Grothendieck tribute — Part 17: Internal hom of sheaves

Alexandre Grothendieck (1928-2014).

Phase 5 extension (#2159, Epic #1646).

Parts 1-16 established the fundamentals: categories, sieves, topologies,
lattice operations, pullback identities, sheaf basics, covering closure,
calibration, subcanonicity, dense topologies, and coverage generation.

This module introduces the **internal hom of sheaves** (SheafHom): given two
sheaves F and G on a site (C, J) with values in a category A, the sheaf
`sheafHom F G` sends an object X : C to the type of morphisms between the
restrictions of F and G to the slice category Over X.

Key constructions bridged from Mathlib (`CategoryTheory.Sites.SheafHom`):

  - `presheafHom F G` : the presheaf-of-types underlying the internal hom
  - `presheafHomSectionsEquiv` : sections of presheafHom ≃ morphisms F ⟶ G
  - `Presheaf.IsSheaf.hom` : when G is a sheaf, presheafHom F G is a sheaf
  - `sheafHom F G` : the internal hom as a Sheaf J (Type _)
  - `sheafHomSectionsEquiv` : sections of sheafHom ≃ sheaf morphisms F ⟶ G
  - `sheafHom'Iso` : the canonical iso between sheafHom' and presheafHom

This is the first step towards Cartesian closed structure on Sheaf J (Type _),
a fundamental property of Grothendieck toposes (SGA 4 II).

Epic #1646, Phase 5 (#2159), See #2159. All `sorry`s eliminated at creation.

### Accessibility note (Epics #1452/#1453)

This module exposes **5 theorem + 2 def** on the internal hom of sheaves
(bridge Presheaf → Sheaf, section-morphism roundtrips), progressive
accessibility by 5 thematic sections: (1) presheaf-level internal hom,
(2) sheaf condition for the internal hom, (3) sheaf-level internal hom,
(4) iso sheafHom' vs presheafHom, (5) section-morphism roundtrips.

### i18n convention (EPIC #4980 ratified by user 2026-07-04)

This substantial module is paired with its English twin in the sibling file
`SheafHom_en.lean` (sibling pair model, see PR #6154 for the pilot on
`Utility.lean` and #6275/#6277/#6280/#6284 for the rollout continuity).
Namespace suffix `_en` applied to the EN file (anti-collision, per code-style.md #4980).
For the canonical French version, see `SheafHom.lean`.
-/

import Mathlib.CategoryTheory.Sites.SheafHom

universe v v' u u'

namespace Grothendieck.SheafHom_en

open CategoryTheory Category Opposite Limits

/-!
## Presheaf-level internal hom

Given presheaves F and G, `presheafHom F G` is a presheaf of types whose
sections over X are natural transformations between the restrictions of
F and G to Over X. Its global sections are exactly morphisms F ⟶ G.
-/

-- The presheaf internal hom: sections over X are morphisms between
-- restrictions of F and G to the slice category Over X.
#check @presheafHom

-- The sections of the presheaf internal hom identify to morphisms F ⟶ G.
-- (presheafHom F G).sections ≃ (F ⟶ G)
#check @presheafHomSectionsEquiv

/-!
## Sheaf condition for the internal hom

When G is a sheaf, the presheaf internal hom `presheafHom F G` is itself
a sheaf. This is the key technical fact enabling the sheaf-level internal hom.
-/

-- When G is a sheaf, the presheaf internal hom presheafHom F G is a sheaf.
#check @Presheaf.IsSheaf.hom

/-- Bridge theorem: when G is a sheaf, presheafHom F G satisfies the sheaf
    condition (via the isSheaf_of_type equivalence). -/

theorem presheafHom_isSheaf_of_isSheaf (F G : Cᵒᵖ ⥤ A)
    (hG : Presheaf.IsSheaf J G) :
    Presheaf.IsSheaf J (presheafHom F G) :=
  Presheaf.IsSheaf.hom F G hG

/-!
## Sheaf-level internal hom

The sheaf internal hom `sheafHom F G` is the sheafification-ready version
living in Sheaf J (Type _). Its sections identify to sheaf morphisms F ⟶ G.
-/

-- The sheaf internal hom: sheafHom F G sends X to the morphisms between
-- restrictions of F and G to Over X, as a Sheaf J (Type _).
#check @sheafHom

-- The sections of the sheaf internal hom identify to sheaf morphisms F ⟶ G.
#check @sheafHomSectionsEquiv

-- The underlying presheaf of the sheaf internal hom.
#check @sheafHom'

-- The canonical isomorphism between sheafHom' and presheafHom.
#check @sheafHom'Iso

/-!
## The internal hom preserves the sheaf condition

The internal hom construction preserves the sheaf condition, making the
category of sheaves enriched over itself. This is the first step toward
the Cartesian closed structure of Sheaf J (Type _).
-/

/-- Construction bridge: from a sheaf morphism F ⟶ G, obtain a section
    of the sheaf internal hom. This is the inverse direction of
    sheafHomSectionsEquiv. -/

noncomputable def sheafHomSectionOfHom (F G : Sheaf J A) (φ : F ⟶ G) :
    (sheafHom F G).1.sections :=
  (sheafHomSectionsEquiv F G).symm φ

/-- Construction bridge: from a section of the sheaf internal hom, obtain
    a sheaf morphism F ⟶ G. This is the forward direction of
    sheafHomSectionsEquiv. -/

noncomputable def sheafHomOfSection (F G : Sheaf J A)
    (s : (sheafHom F G).1.sections) : F ⟶ G :=
  (sheafHomSectionsEquiv F G) s

/-- The sheaf internal hom sheafHom F G is indeed a sheaf (by construction). -/

theorem sheafHom_isSheaf (F G : Sheaf J A) :
    Presheaf.IsSheaf J (sheafHom F G).1 :=
  (sheafHom F G).2

/-- The underlying presheaf of sheafHom is isomorphic to presheafHom. -/

theorem sheafHom'_iso_presheafHom (F G : Sheaf J A) :
    Nonempty (sheafHom' F G ≅ presheafHom F.1 G.1) :=
  ⟨sheafHom'Iso F G⟩

/-!
## Section-morphism roundtrips

The equivalence between sections and morphisms gives us roundtrip lemmas
that witness the bijection (sheafHom F G).sections ≃ (F ⟶ G).
-/

/-- Roundtrip: section → morphism → section is the identity. -/

theorem sheafHomSectionsEquiv_roundtrip (F G : Sheaf J A)
    (s : (sheafHom F G).1.sections) :
    sheafHomSectionOfHom F G (sheafHomOfSection F G s) = s := by
  dsimp [sheafHomSectionOfHom, sheafHomOfSection]
  exact (sheafHomSectionsEquiv F G).left_inv s

/-- Roundtrip: morphism → section → morphism is the identity. -/

theorem sheafHomSectionsEquiv_roundtrip_symm (F G : Sheaf J A)
    (φ : F ⟶ G) :
    sheafHomOfSection F G (sheafHomSectionOfHom F G φ) = φ := by
  dsimp [sheafHomSectionOfHom, sheafHomOfSection]
  exact (sheafHomSectionsEquiv F G).right_inv φ

end Grothendieck.SheafHom_en
