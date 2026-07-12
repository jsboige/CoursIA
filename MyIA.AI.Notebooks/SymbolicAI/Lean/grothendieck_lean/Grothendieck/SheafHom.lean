-/
# Hommage Grothendieck — Partie 17 : Hom interne des faisceaux

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Les parties 1-16 ont etabli les fondamentaux : categories, cribles, topologies,
lois de treillis, identites de pullback, bases de faisceaux, cloture couvrante,
calibration, sous-canonicalite, topologies denses, generation de couvertures.

Ce module introduit le **hom interne des faisceaux** (SheafHom) : pour deux
faisceaux F et G sur un site (C, J) a valeurs dans une categorie A, le faisceau
`sheafHom F G` envoie un objet X : C vers le type des morphismes entre les
restrictions de F et G a la categorie tranchee Over X.

Constructions clefs pontées depuis Mathlib (`CategoryTheory.Sites.SheafHom`) :

  - `presheafHom F G` : le préfaisceau-de-types sous-jacent au hom interne
  - `presheafHomSectionsEquiv` : sections de presheafHom ≃ morphismes F ⟶ G
  - `Presheaf.IsSheaf.hom` : quand G est un faisceau, presheafHom F G est un faisceau
  - `sheafHom F G` : le hom interne comme un Sheaf J (Type _)
  - `sheafHomSectionsEquiv` : sections de sheafHom ≃ morphismes de faisceaux F ⟶ G
  - `sheafHom'Iso` : l'iso canonique entre sheafHom' et presheafHom

C'est la premiere etape vers la structure cartesienne fermee sur Sheaf J (Type _),
une propriete fondamentale des topos de Grothendieck (SGA 4 II).

EPIC #1646, Phase 5 (#2159), voir #2159. Tous les `sorry`s elimines a la creation.

### Note d'accessibilite (Epics #1452/#1453)

Ce module expose **5 theorem + 2 def** sur le hom interne des faisceaux
(bridge Presheaf → Sheaf, sections-morphismes roundtrips), accessibilite
progressive par 5 sections thematiques : (1) hom interne au niveau préfaisceau,
(2) condition de faisceau pour le hom interne, (3) hom interne au niveau faisceau,
(4) iso sheafHom' vs presheafHom, (5) sections-morphismes roundtrips.

### Convention i18n (EPIC #4980 ratifiee par user 2026-07-04)

Ce module substantiel est apparie avec son jumeau anglais dans le fichier sibling
`SheafHom_en.lean` (modele sibling pair, voir PR #6154 pour le pilote sur
`Utility.lean` et #6275/#6277/#6280/#6284 pour la continuite du rollout).
Namespace suffix `_en` applique au fichier EN (anti-collision, conforme code-style.md #4980).
-/

import Mathlib.CategoryTheory.Sites.SheafHom

universe v v' u u'

namespace Grothendieck.SheafHom

open CategoryTheory Category Opposite Limits

/-!
## Hom interne au niveau préfaisceau

Étant donnés des préfaisceaux F et G, `presheafHom F G` est un préfaisceau de
types dont les sections sur X sont les transformations naturelles entre les
restrictions de F et G à Over X. Ses sections globales sont exactement les
morphismes F ⟶ G.
-/

-- The presheaf internal hom: sections over X are morphisms between
-- restrictions of F and G to the slice category Over X.
#check @presheafHom

-- The sections of the presheaf internal hom identify to morphisms F ⟶ G.
-- (presheafHom F G).sections ≃ (F ⟶ G)
#check @presheafHomSectionsEquiv

/-!
## Condition de faisceau pour le hom interne

Quand G est un faisceau, le préfaisceau hom interne `presheafHom F G` est lui-même
un faisceau. C'est le fait technique clé qui permet le hom interne au niveau faisceau.
-/

-- When G is a sheaf, the presheaf internal hom presheafHom F G is a sheaf.
#check @Presheaf.IsSheaf.hom

/-- Théorème pont : quand G est un faisceau, presheafHom F G satisfait la
    condition de faisceau (via l'équivalence isSheaf_of_type). -/

theorem presheafHom_isSheaf_of_isSheaf (F G : Cᵒᵖ ⥤ A)
    (hG : Presheaf.IsSheaf J G) :
    Presheaf.IsSheaf J (presheafHom F G) :=
  Presheaf.IsSheaf.hom F G hG

/-!
## Hom interne au niveau faisceau

Le hom interne faisceau `sheafHom F G` est la version prête pour la faisceautisation
vivant dans Sheaf J (Type _). Ses sections s'identifient aux morphismes de faisceaux
F ⟶ G.
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
## Le hom interne préserve la condition de faisceau

La construction du hom interne préserve la condition de faisceau, rendant la
catégorie des faisceaux enrichie sur elle-même. C'est la première étape vers
la structure cartésienne fermée de Sheaf J (Type _).
-/

/-- Pont de construction : à partir d'un morphisme de faisceaux F ⟶ G,
    obtenir une section du hom interne faisceau. C'est la direction inverse de
    sheafHomSectionsEquiv. -/

noncomputable def sheafHomSectionOfHom (F G : Sheaf J A) (φ : F ⟶ G) :
    (sheafHom F G).1.sections :=
  (sheafHomSectionsEquiv F G).symm φ

/-- Pont de construction : à partir d'une section du hom interne faisceau,
    obtenir un morphisme de faisceaux F ⟶ G. C'est la direction avant de
    sheafHomSectionsEquiv. -/

noncomputable def sheafHomOfSection (F G : Sheaf J A)
    (s : (sheafHom F G).1.sections) : F ⟶ G :=
  (sheafHomSectionsEquiv F G) s

/-- Le hom interne faisceau sheafHom F G est bien un faisceau (par construction). -/

theorem sheafHom_isSheaf (F G : Sheaf J A) :
    Presheaf.IsSheaf J (sheafHom F G).1 :=
  (sheafHom F G).2

/-- Le préfaisceau sous-jacent de sheafHom est isomorphe à presheafHom. -/

theorem sheafHom'_iso_presheafHom (F G : Sheaf J A) :
    Nonempty (sheafHom' F G ≅ presheafHom F.1 G.1) :=
  ⟨sheafHom'Iso F G⟩

/-!
## Roundtrips sections-morphismes

L'équivalence entre sections et morphismes nous donne des lemmes de roundtrip
qui témoignent la bijection (sheafHom F G).sections ≃ (F ⟶ G).
-/

/-- Roundtrip : section → morphisme → section est l'identité. -/

theorem sheafHomSectionsEquiv_roundtrip (F G : Sheaf J A)
    (s : (sheafHom F G).1.sections) :
    sheafHomSectionOfHom F G (sheafHomOfSection F G s) = s := by
  dsimp [sheafHomSectionOfHom, sheafHomOfSection]
  exact (sheafHomSectionsEquiv F G).left_inv s

/-- Roundtrip : morphisme → section → morphisme est l'identité. -/

theorem sheafHomSectionsEquiv_roundtrip_symm (F G : Sheaf J A)
    (φ : F ⟶ G) :
    sheafHomOfSection F G (sheafHomSectionOfHom F G φ) = φ := by
  dsimp [sheafHomSectionOfHom, sheafHomOfSection]
  exact (sheafHomSectionsEquiv F G).right_inv φ

end Grothendieck.SheafHom
