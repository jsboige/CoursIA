/-
Hommage à Grothendieck — Partie 3 : Le site de Zariski
Alexandre Grothendieck (1928-2014).

La topologie de Zariski sur la catégorie des schémas est l'exemple fondateur
d'une topologie de Grothendieck issue de la géométrie algébrique. Une famille
de morphismes {U_i → X} est un recouvrement de Zariski ssi les U_i sont des
immersions ouvertes qui recouvrent X conjointement.

Mathlib 4 formalise cela via `Scheme.zariskiTopology`, dérivé de la
prétopologie des immersions ouvertes. Le théorème-pont clé est
`zariskiTopology_eq` : la topologie de Grothendieck engendrée par la
prétopologie de Zariski égale la topologie de Zariski.

Epic #1646. Tous les `sorry` ont été éliminés à la création.

Convention i18n (EPIC #4980, décision user ratifiée 2026-07-04) : ce fichier
est **FR canonique**, avec son miroir anglais dans le fichier sibling
`ZariskiSite_en.lean` (modèle sibling pair, cf `code-style.md` §Lean i18n).
Les énoncés de théorèmes/exemples, les tactiques Lean et les références
Mathlib restent en anglais (compat Mathlib 4) ; seules les docstrings et ce
bloc d'en-tête diffèrent entre les deux fichiers.
-/

import Mathlib.AlgebraicGeometry.Sites.BigZariski

universe v u

namespace Grothendieck

open AlgebraicGeometry CategoryTheory

/-!
## La prétopologie de Zariski

Une prétopologie spécifie directement les familles de recouvrement (collections
de morphismes). La prétopologie de Zariski recouvre X par des familles
d'immersions ouvertes conjointement surjectives sur l'espace topologique sous-jacent.
-/

/-- La prétopologie de Zariski sur la catégorie des schémas. -/
example : Pretopology Scheme :=
  Scheme.zariskiPretopology

/-!
## De la prétopologie à la topologie de Grothendieck

Toute prétopologie engendre une topologie de Grothendieck. La topologie de
Zariski est précisément la topologie de Grothendieck engendrée par la
prétopologie de Zariski.
-/

/-- La topologie de Zariski vue comme topologie de Grothendieck. -/
example : GrothendieckTopology Scheme :=
  Scheme.zariskiTopology

/-- Le théorème-pont : la topologie de Zariski égale la topologie de Grothendieck
    engendrée par la prétopologie de Zariski. C'est le lien clé entre les points
    de vue concret (prétopologie) et abstrait (topologie de Grothendieck). -/
theorem zariski_topology_eq :
    (Scheme.zariskiTopology : GrothendieckTopology Scheme) =
    Scheme.zariskiPretopology.toGrothendieck :=
  Scheme.zariskiTopology_eq

/-!
## La topologie de Zariski est sous-canonique

Une topologie de Grothendieck est *sous-canonique* si tout préfaisceau
représentable est déjà un faisceau. La topologie de Zariski sur les schémas
est sous-canonique.

Cela signifie : pour tout schéma X, le préfaisceau `Hom(-, X)` satisfait la
condition de faisceau vis-à-vis des recouvrements de Zariski. Intuitivement,
un morphisme vers X est déterminé par ses restrictions à un recouvrement ouvert.
-/

/-- La topologie de Zariski est sous-canonique. -/
example : Scheme.zariskiTopology.Subcanonical :=
  inferInstance

/-!
## Continuité du foncteur d'oubli

Le foncteur d'oubli des schémas vers les espaces topologiques est continu
vis-à-vis de la topologie de Zariski et de la topologie de Grothendieck
usuelle sur TopCat. Cela signifie : l'image réciproque d'un crible de
recouvrement de Zariski par forget est un crible de recouvrement dans TopCat.
-/

/-- Le foncteur d'oubli est continu vis-à-vis de la topologie de Zariski. -/
example : Scheme.forgetToTop.IsContinuous
    Scheme.zariskiTopology TopCat.grothendieckTopology :=
  inferInstance

/-! ## 5. Bridges Mathlib canoniques (hommage Grothendieck)

Ponts vers les 5 constructeurs canoniques de `Mathlib/AlgebraicGeometry/Sites/BigZariski.lean`
qui étendent le namespace `Grothendieck` avec les opérateurs fondamentaux du site de Zariski :
(5.1) la prétopologie et la topologie, (5.2) les instances Subcanonical et continuité du foncteur
d'oubli, (5.3) l'hypercover affine. -/

/-! ### 5.1 Pont-def : la prétopologie et la topologie de Zariski

Le bridge-lemma expose `zariskiPretopology` (la prétopologie sous-jacente) et `zariskiTopology`
(la topologie de Grothendieck dérivée) directement sous `Grothendieck.Scheme`. -/

/-- Pont-def : re-export de la prétopologie de Zariski sur la catégorie des schémas. -/
def zariskiPretopology_field : Pretopology Scheme.{u} :=
  Scheme.zariskiPretopology

/-- Pont-def : re-export de la topologie de Zariski (topologie de Grothendieck dérivée). -/
abbrev zariskiTopology_field : GrothendieckTopology Scheme.{u} :=
  Scheme.zariskiTopology

/-! ### 5.2 Pont-instance : Zariski sous-canonique et foncteur d'oubli continu

L'instance Subcanonical sur la topologie de Zariski (cf. Subcanonical.lean Partie 16) et
l'instance de continuité du foncteur d'oubli vers TopCat. -/

/-- Pont-instance : la topologie de Zariski est sous-canonique. -/
instance subcanonical_zariskiTopology_field : Scheme.zariskiTopology.Subcanonical :=
  Scheme.subcanonical_zariskiTopology

/-- Pont-instance : le foncteur d'oubli vers TopCat est continu vis-à-vis de Zariski. -/
instance forgetToTop_continuous_zariskiTopology :
    Scheme.forgetToTop.IsContinuous Scheme.zariskiTopology TopCat.grothendieckTopology :=
  inferInstance

/-! ### 5.3 Pont-def : hypercover affine (1-hypercover)

Pour tout schéma X, le 1-hypercover de Zariski dont tous les composantes sont affines.
C'est l'outil de base pour la cohomologie de Zariski. -/

/-- Pont-def : 1-hypercover de Zariski dont toutes les composantes sont affines. -/
noncomputable def affineOneHypercover_field (X : Scheme.{u}) :
    Scheme.zariskiTopology.OneHypercover X :=
  Scheme.affineOneHypercover X

end Grothendieck
