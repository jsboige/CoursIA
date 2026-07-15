/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## `Grothendieck.MathlibMap` — Cartographie Mathlib

Un index vivant de ce que Mathlib 4 fournit depuis le langage mathématique
de Grothendieck. Chaque `#check` vérifie que la définition existe et est
accessible depuis les imports courants.

Epic #1646. Tous les `sorry`s éliminés à la création.

### i18n — convention #4980 ratifiée 2026-07-04

Ce module est jumelé avec sa version anglaise canonique dans le fichier
sibling `MathlibMap_en.lean` (modèle sibling pair, voir PR #6154 pour le
pilote sur `Utility.lean`). Les énoncés `#check @...` restent en anglais
(Mathlib 4, tactic DSL standard) ; seules les **docstrings `/-- ... -/`** et
les **commentaires `-- ...`** diffèrent entre les deux fichiers. Anti-§D
byte-identity garanti : le namespace body est préservé bit-pour-bit (les
énoncés `#check` sont identiques entre `MathlibMap.lean` et `MathlibMap_en.lean`,
seuls les commentaires diffèrent).
-/

import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Topology.Sheaves.Sheaf

namespace Grothendieck

/-!
## Fondements de la théorie des catégories (l'héritage de Grothendieck)

Grothendieck a fait de la théorie des catégories le langage de la géométrie
algébrique. Mathlib 4 dispose d'une riche bibliothèque de théorie des
catégories construite sur ces idées.
-/

-- Le lemme de Yoneda (fondamental pour les cribles et les faisceaux)
#check @CategoryTheory.yoneda            -- C ⥤ (Cᵒᵖ ⥤ Type v)
#check @CategoryTheory.coyoneda          -- (Cᵒᵖ ⥤ Type v) ⥤ C

/-!
## Cribles et précaractères (Sieves et Presieves)
-/

#check @CategoryTheory.Presieve          -- Presieve X
#check @CategoryTheory.Sieve             -- Sieve X (sous-foncteur de yoneda.obj X)
#check @CategoryTheory.Sieve.pullback    -- pullback d'un crible le long d'un morphisme
#check @CategoryTheory.Sieve.arrows      -- le précaractère sous-jacent

/-!
## Topologies de Grothendieck
-/

#check @CategoryTheory.GrothendieckTopology          -- la structure de topologie
#check @CategoryTheory.GrothendieckTopology.trivial  -- topologie la plus grossière
#check @CategoryTheory.GrothendieckTopology.discrete -- topologie la plus fine
#check @CategoryTheory.GrothendieckTopology.dense    -- topologie dense

/-!
## Faisceaux
-/

-- Faisceaux de types sur un site
#check @CategoryTheory.Presieve.IsSheaf  -- condition de faisceau pour préfaisceaux en Type
#check @CategoryTheory.Presieve.IsSeparated  -- préfaisceau séparé

-- Faisceaux sur un espace topologique
#check @TopCat.Sheaf                     -- faisceau bundle sur un espace topologique

/-!
## Géométrie algébrique : Schémas et Spec
-/

open AlgebraicGeometry CategoryTheory

-- Le type des schémas
#check Scheme                   -- le type des schémas

-- La construction Spec : des anneaux vers les espaces
#check Scheme.Spec              -- CommRingCatᵒᵖ ⥤ Scheme

-- Sections globales : des espaces vers les anneaux
#check Scheme.Γ                 -- Schemeᵒᵖ ⥤ CommRingCat

-- Foncteurs d'oubli
#check Scheme.forgetToTop       -- Scheme ⥤ TopCat
#check Scheme.forgetToLocallyRingedSpace  -- Scheme ⥤ LocallyRingedSpace

/-!
## Ce que Mathlib n'a PAS ENCORE (état 2026-05)

Les concepts fondamentaux de Grothendieck qui ne sont PAS encore dans Mathlib :
  - Cohomologie étale (site étale, cohomologie l-adique)
  - Motifs (motifs purs, catégorie DM de Voevodsky)
  - Six opérations (formalisme de Grothendieck)
  - Grothendieck-Riemann-Roch
  - Dualité de Grothendieck
  - Cohomologie cristalline
  - Géométrie anabélienne
  - Résultats profonds EGA/SGA (EGA II-IV, SGA 1-7)

Ces cibles restent au niveau recherche en formalisation.
-/

end Grothendieck