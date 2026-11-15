/-
Grothendieck Partie 28 — Limites et colimites (au-delà de Yoneda)

Alexandre Grothendieck (1928-2014).

Extension Phase 2+ (#2159, Epic #1646).

Les limites et colimites sont la syntaxe universelle qui transforme une
catégorie en un espace où des problèmes d'existence se résolvent « par
propriété universelle ». Grothendieck en fait le pilier de la géométrie
algébrique : le produit fibré de schémas (limite d'un diagramme en V), le
produit de schémas au-dessus d'une base, les noyaux et conoyaux de morphismes
de faisceaux, les limites projectives de groupes fondamentaux étales, et —
surtout — la cohomologie comme foncteur dérivé du foncteur « sections
globales » Γ, lui-même adjoint à droite et donc continu (préserve les
limites, cf module `Grothendieck.Adjunction`).

Une **limite** d'un foncteur `F : J ⥤ C` (un « diagramme ») est un objet qui
représente les « familles compatibles » d'éléments de `F`. C'est la solution
universelle au problème : « donner un objet `L` et des projections vers chaque
`F j` compatibles avec les flèches du diagramme, par lequel passe tout autre
tel cône, de manière unique ». La **colimite** est la notion duale (factorisation
universelle des cocônes). Produits, produits fibrés, égaliseurs sont des
limites ; sommes amalgamées, coproduits, conoyaux sont des colimites.

Mathlib 4 formalise toute cette infrastructure dans `Mathlib.CategoryTheory.Limits` :
  - `CategoryTheory.Limits.Cone` / `Cocone` — cônes et cocônes sur un diagramme
  - `CategoryTheory.Limits.IsLimit` / `IsColimit` — la propriété universelle
  - `CategoryTheory.Limits.HasLimit` / `HasColimit` — existence d'une (co)limite choisie
  - `CategoryTheory.Limits.limit` / `colimit` — l'objet (co)limite
  - `CategoryTheory.Limits.limit.cone` / `colimit.cocone` — le cône/cocône limite
  - `CategoryTheory.Limits.limit.π` / `colimit.ι` — projections / injections
  - `CategoryTheory.Limits.limit.lift` / `colimit.desc` — factorisation universelle
  - `CategoryTheory.Limits.HasLimitsOfSize` / `HasColimitsOfSize` — catégorie (co)complète
  - `CategoryTheory.Limits.PreservesLimitsOfSize` / `PreservesColimitsOfSize` — foncteur continu/cocontinu
  - `CategoryTheory.Limits.HasProducts` / `HasBinaryProducts` / `HasEqualizers` — formes classiques

Ce module ré-expose ces faits comme un parcours pédagogique organisé, pour
des apprenants découvrant les (co)limites pour la première fois, en miroir du
module `Grothendieck.Adjunction` (où l'on voit que préserver les limites est
précisément la propriété des adjoints à droite).

Epic #1646, See #2159. Tous les `sorry` éliminés à la création.

### i18n — convention #4980 ratifiée 2026-07-04

Ce module est jumelé avec sa version anglaise canonique dans le fichier
sibling `Limits_en.lean`. Les énoncés de théorèmes, les noms de lemmes,
les tactiques Lean et les références Mathlib restent en anglais. Seules les
**docstrings `/-- ... -/`** et les **commentaires `-- ...`** diffèrent entre
les deux fichiers. Anti-§D byte-identity garanti.
-/

import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

universe v v' u u'

namespace Grothendieck.Limits

open CategoryTheory Limits

variable {J : Type u} [Category.{v} J]
variable {C : Type u'} [Category.{v'} C]

/-!
## 1. Cônes et propriété universelle de la limite

Un **cône** `c : Cone F` sur un diagramme `F : J ⥤ C` est la donnée d'un
sommet `c.pt : C` et d'une famille de flèches `c.π.app j : c.pt ⟶ F j`
compatible avec les morphismes du diagramme (une transformation naturelle du
foncteur constant en `c.pt` vers `F`). La limite est le cône universel :
tout autre cône s'en factorise de manière unique.
-/

-- La structure d'un cône sur un diagramme F : J ⥤ C.
#check @Cone

-- La structure duale : un cocône (famelle sortante compatible).
#check @Cocone

-- La propriété universelle : un cône t est limite si tout cône se factorise
-- de manière unique à travers t.
#check @IsLimit

-- La propriété universelle duale : un cocône est colimite.
#check @IsColimit

/-!
## 2. Existence et choix d'une limite

`HasLimit F` asserte qu'il existe une limite de `F` (proposition classique) ;
`limit F` est alors l'objet limite choisi, `limit.cone F` le cône limite,
`limit.π F j` sa projection vers `F j`, et `limit.lift F c` la factorisation
universelle d'un cône arbitraire `c` à travers le cône limite.
-/

-- La proposition d'existence d'une limite de F.
#check @HasLimit

-- La proposition d'existence d'une colimite de F (duale).
#check @HasColimit

-- L'objet limite choisi (sous HasLimit F).
#check @limit

-- L'objet colimite choisi (sous HasColimit F).
#check @colimit

-- Le cône limite limite universel.
#check @limit.cone

-- La projection du cône limite vers la composante j du diagramme.
#check @limit.π

-- Le témoignage que `limit.cone F` satisfait la propriété universelle.
#check @limit.isLimit

-- La factorisation universelle : tout cône c se factorise par le cône limite.
#check @limit.lift

/-!
## 3. Colimites duales

Par dualité, `colimit.cocone F` est le cocône colimite, `colimit.ι F j` son
injection depuis `F j`, et `colimit.desc F c` la factorisation universelle
d'un cocône arbitraire à travers le cocône colimite.
-/

-- Le cocône colimite universel.
#check @colimit.cocone

-- L'injection de la composante j vers l'objet colimite.
#check @colimit.ι

-- Le témoignage que `colimit.cocone F` satisfait la propriété universelle.
#check @colimit.isColimit

-- La factorisation universelle : tout cocône c se factorise par le cocône colimite.
#check @colimit.desc

/-!
## 4. Catégories complètes et cocomplètes

Une catégorie est **complète** (`HasLimitsOfSize.{w} C`) si tout diagramme
indexé par une petite catégorie de taille adéquate admet une limite ;
**cocomplète** est la duale. Ces propriétés sont stables par la plupart des
constructions catégoriques utiles (catégorie de faisceaux, catégorie de
foncteurs).
-/

-- Une catégorie qui a toutes les limites de la taille indiquée.
#check @HasLimitsOfSize

-- Une catégorie qui a toutes les colimites de la taille indiquée.
#check @HasColimitsOfSize

/-!
## 5. Formes classiques de limites

Les limites les plus utiles en géométrie algébrique sont les produits
(`HasProducts`, `HasBinaryProducts`) et les égaliseurs (`HasEqualizers`).
Un théorème de Freyd affirme qu'une catégorie a toutes les limites (petites)
si et seulement si elle a produits et égaliseurs — d'où leur centralité.
-/

-- La catégorie a tous les produits (limites sur types discrétisés).
#check @HasProducts

-- La catégorie a tous les produits binaires.
#check @HasBinaryProducts

-- La catégorie a tous les égaliseurs.
#check @HasEqualizers

/-!
## 6. Préservation des limites

Un foncteur `G : C ⥤ D` **préserve les limites** (`PreservesLimitsOfSize G`)
si l'image par `G` d'un cône limite en est encore une. C'est précisément la
propriété des adjoints à droite (cf module `Grothendieck.Adjunction`) :
le foncteur « sections globales » Γ préserve ainsi les limites de faisceaux,
ce qui under-grit la continuité des foncteurs cohomologiques.
-/

-- Un foncteur qui préserve toutes les limites de la taille indiquée.
#check @PreservesLimitsOfSize

-- Un foncteur qui préserve toutes les colimites de la taille indiquée.
#check @PreservesColimitsOfSize

/-!
## 7. Théorèmes ponts

Reformulations dans l'espace de noms du projet, pontant les faits Mathlib.
-/

/-- Pont : l'objet limite d'un diagramme F, comme représentant choisi.
    C'est l'objet universel vers lequel tout cône compatible se factorise. -/
noncomputable def limit_object (F : J ⥤ C) [HasLimit F] : C :=
  limit F

/-- Pont : l'objet colimite d'un diagramme F, comme représentant choisi.
    C'est l'objet universel depuis lequel tout cocône compatible se factorise. -/
noncomputable def colimit_object (F : J ⥤ C) [HasColimit F] : C :=
  colimit F

/-- Pont : la propriété universelle de la limite — le cône `limit.cone F`
    est bien limite, i.e. tout cône se factorise de manière unique à travers lui. -/
noncomputable def limit_is_universal (F : J ⥤ C) [HasLimit F] : IsLimit (limit.cone F) :=
  limit.isLimit F

/-- Pont : la propriété universelle duale des colimites. -/
noncomputable def colimit_is_universal (F : J ⥤ C) [HasColimit F] : IsColimit (colimit.cocone F) :=
  colimit.isColimit F

/-- Pont : la projection du cône limite vers la composante j. C'est l'analogue
    catégorique d'une « coordonnée » dans un produit. -/
noncomputable def limit_projection (F : J ⥤ C) [HasLimit F] (j : J) : limit F ⟶ F.obj j :=
  limit.π F j

/-- Pont : l'injection du cocône colimite depuis la composante j. C'est
    l'analogue catégorique d'une « inclusion » dans une somme. -/
noncomputable def colimit_injection (F : J ⥤ C) [HasColimit F] (j : J) : F.obj j ⟶ colimit F :=
  colimit.ι F j

/-- Pont : la factorisation universelle de la limite — tout cône `c` sur `F`
    se factorise de manière unique par le cône limite. C'est le morphisme
    « médiateur » qui incarne la propriété universelle. -/
noncomputable def cone_factorisation (F : J ⥤ C) [HasLimit F] (c : Cone F) : c.pt ⟶ limit F :=
  limit.lift F c

/-- Pont : la factorisation universelle duale des colimites — tout cocône `c`
    sur `F` se factorise de manière unique par le cocône colimite. -/
noncomputable def cocone_factorisation (F : J ⥤ C) [HasColimit F] (c : Cocone F) : colimit F ⟶ c.pt :=
  colimit.desc F c

/-!
## 8. Théorèmes ponts : naturalité des projections et injections

Les projections `limit.π F j` et injections `colimit.ι F j` ne sont pas de simples
familles de morphismes : ce sont des **transformations naturelles** en l'indice
`j`. La naturalité est certifiée par les théorèmes Mathlib 4 `limit.w` et
`colimit.w` (chacun `@[simp]`). On les ré-expose ici comme bridges vers le
namespace du projet, avec application de leurs arguments explicites (L902 ★★
ÉTENDUE c.8228 : un théorème Mathlib à arguments explicites doit être APPLIQUÉ
dans le corps, sinon c'est un `∀` qui produit `Type mismatch`).
-/

/-- Pont : la factorisation universelle `cone_factorisation` est une reformulation
    directe du `limit.lift` Mathlib 4. Cast par application de l'argument `F`. -/
noncomputable def limit_lift_eq (F : J ⥤ C) [HasLimit F] (c : Cone F) :
    c.pt ⟶ limit F :=
  CategoryTheory.Limits.limit.lift F c

/-- Pont : la naturalité des projections du cône limite — pour toute flèche
    `f : j ⟶ j'` du diagramme, `limit.π F j ≫ F.map f = limit.π F j'`. C'est
    l'**égalité de naturalité** de la transformation naturelle `limit.π`, prouvée
    par le théorème `@[simp] lemma CategoryTheory.Limits.limit.w F j j' f`. -/
theorem limit_w_natural (F : J ⥤ C) [HasLimit F] {j j' : J} (f : j ⟶ j') :
    limit.π F j ≫ F.map f = limit.π F j' := by
  rw [CategoryTheory.Limits.limit.w]

/-- Pont : la factorisation universelle `cocone_factorisation` est une reformulation
    directe du `colimit.desc` Mathlib 4. Cast par application de l'argument `F`. -/
noncomputable def colimit_desc_eq (F : J ⥤ C) [HasColimit F] (c : Cocone F) :
    colimit F ⟶ c.pt :=
  CategoryTheory.Limits.colimit.desc F c

/-- Pont : la naturalité des injections du cocône colimite — pour toute flèche
    `f : j' ⟶ j` du diagramme, `F.map f ≫ colimit.ι F j = colimit.ι F j'`. C'est
    l'**égalité de naturalité** de la transformation naturelle `colimit.ι`,
    prouvée par le théorème `@[simp] lemma CategoryTheory.Limits.colimit.w
    F j j' f` (note : la flèche va de `j'` vers `j`, duale de `limit.w`). -/
theorem colimit_w_natural (F : J ⥤ C) [HasColimit F] {j j' : J} (f : j' ⟶ j) :
    F.map f ≫ colimit.ι F j = colimit.ι F j' := by
  rw [CategoryTheory.Limits.colimit.w]

/-!
## 9. Ponts additionnels : factorisation des cônes, extension, et cônes limites

Les 4 ponts suivants complètent le tableau des lemmes Mathlib 4 fondamentaux
sur les limites et colimites :
  - `limit_lift_π` : la projection `limit.π F j` après « lift » d'un cône
    arbitraire redonne exactement la composante du cône — tige que fournit
    tout cône sur `F`.
  - `limit_hom_ext_apply` : critère d'extension « **deux morphismes dans la
    limite qui coïncident sur chaque projection sont égaux** », application
    du `@[ext] lemma limit.hom_ext`.
  - `limit_lift_cone` : le « lift » du cône limite est l'identité — la limite
    est **point fixe** de sa propre opération de factorisation.
  - `colimit_ι_desc` : dual côté colimites — l'« desc » suivi de `colimit.ι F j`
    d'un cocône arbitraire redonne la composante du cocône.

Pattern winner (L902 ★★ c.8261) : univers explicites, alias directs Mathlib,
signatures alignées sur le lemme source. Pour `limit.hom_ext` (`@[ext]`),
l'application donne le lemme d'égalité, pas une fonction — on l'écrit
explicitement avec ses args pointwise.
-/

/-- Pont : pour tout cône `c` sur `F`, la projection `limit.π F j` composée
    avec le `limit.lift F c` redonne la `j`-ème composante du cône. C'est la
    **tige que fournit tout cône** sur le diagramme, démontré par le lemme
    Mathlib `@[reassoc, simp] lemma CategoryTheory.Limits.limit.lift_π F c j`.
    Namespace theorem (L902 ★★ Tier 4) — alias direct. -/
theorem limit_lift_π (F : J ⥤ C) [HasLimit F] (c : Cone F) (j : J) :
    limit.lift F c ≫ limit.π F j = c.π.app j :=
  CategoryTheory.Limits.limit.lift_π c j

/-- Pont : critère d'extension entre la limite et le cône — étant donné
    deux morphismes `f, f' : X ⟶ limit F`, s'ils coïncident sur chaque
    projection `limit.π F j`, alors `f = f'`. C'est le lemme
    `@[ext] lemma CategoryTheory.Limits.limit.hom_ext F {X} (w : ∀ j, ...) :
    f = f'`. Namespace theorem (L902 ★★ Tier 4) — alias direct. -/
theorem limit_hom_ext_apply (F : J ⥤ C) [HasLimit F] {X : C} {f f' : X ⟶ limit F}
    (w : ∀ j, f ≫ limit.π F j = f' ≫ limit.π F j) : f = f' :=
  CategoryTheory.Limits.limit.hom_ext w

/-- Pont : le `limit.lift` du cône limite est l'identité — la limite est
    point fixe de sa propre factorisation. Démontré par le lemme Mathlib
    `@[simp] lemma CategoryTheory.Limits.limit.lift_cone {F : J ⥤ C}
    [HasLimit F] : limit.lift F (limit.cone F) = 𝟙 (limit F)`. Le `F` est
    implicite — on omet l'argument explicite pour laisser Lean l'unifier. -/
theorem limit_lift_cone (F : J ⥤ C) [HasLimit F] :
    limit.lift F (limit.cone F) = 𝟙 (limit F) :=
  CategoryTheory.Limits.limit.lift_cone

/-- Pont : dual côté colimites — pour tout cocône `c` sur `F`, l'injection
    `colimit.ι F j` composée avec le `colimit.desc F c` redonne la `j`-ème
    composante du cocône. C'est la **tige que fournit tout cocône** sur le
    diagramme, démontré par le lemme Mathlib
    `@[reassoc, simp] lemma CategoryTheory.Limits.colimit.ι_desc F c j`.
    Namespace theorem (L902 ★★ Tier 4) — alias direct. -/
theorem colimit_ι_desc (F : J ⥤ C) [HasColimit F] (c : Cocone F) (j : J) :
    colimit.ι F j ≫ colimit.desc F c = c.ι.app j :=
  CategoryTheory.Limits.colimit.ι_desc c j

/-!
## 10. Ponts sur les classes de complétude et de préservation

Les 7 bridges suivants ferment les sections 4-6 du répertoire documentaire
(`#check`) : les classes de **complétude** (`HasLimitsOfSize`/
`HasColimitsOfSize`), les **formes classiques** (`HasProducts`/
`HasBinaryProducts`/`HasEqualizers`) et la **préservation** des limites
(`PreservesLimitsOfSize`/`PreservesColimitsOfSize`). Chacun est un re-export
type-sig de la classe Prop Mathlib (pattern winner L902 ★★ Tier 5) : args
résidents (les univers du diagramme `v v' u u'`), instances structurelles
uniquement, pas de constructeur polymorphe d'univers.

Note univers (leçon c.1301+141-L1) : `HasLimitsOfSize.{u, v} C` prend **deux**
univers explicites — l'univers du Shape (`J : Type u`) et l'univers des
morphismes du Shape (`[Category.{v} J]`) — et couvre exactement nos diagrammes.
`HasProducts.{u} C` prend **un** univers explicite (l'univers des types
d'indices du produit, `HasProducts := ∀ J : Type w, HasLimitsOfShape
(Discrete J) C`), aligné sur notre Shape univers ; l'omettre produit
`universe level metavariables`. `HasBinaryProducts`/`HasEqualizers` ont des
shapes fixes (`Discrete WalkingPair`/`WalkingParallelPair`) — aucun univers
explicite.
-/

/-- Pont : la catégorie `C` est **complete** — tout diagramme indexé par une
    petite catégorie de notre Shape univers (`J : Type u` avec
    `[Category.{v} J]`) admet une limite. C'est l'assertion de complétude des
    catégories de diagrammes de taille `(u, v)`, re-export type-sig de la
    classe Mathlib `HasLimitsOfSize.{u, v} C`. Les limites y sont stables par
    les constructions catégoriques utiles (catégories de faisceaux, catégories
    de foncteurs). -/
def has_limits_of_size_field : Prop :=
  HasLimitsOfSize.{u, v} C

/-- Pont : la catégorie `C` est **cocomplete** — tout diagramme indexé par une
    petite catégorie de notre Shape univers admet une colimite. Duale de
    `has_limits_of_size_field`, re-export type-sig de la classe Mathlib
    `HasColimitsOfSize.{u, v} C`. -/
def has_colimits_of_size_field : Prop :=
  HasColimitsOfSize.{u, v} C

/-- Pont : la catégorie `C` a tous les **produits** indexés par des types de
    notre Shape univers — les limites sur les types discrétisés `Discrete J`
    avec `J : Type u`. Un théorème de Freyd ramène la complétude (petite) à
    l'existence des produits et des égaliseurs — d'où leur centralité.
    Re-export type-sig de la classe Mathlib `HasProducts.{u} C`. -/
def has_products_field : Prop :=
  HasProducts.{u} C

/-- Pont : la catégorie `C` a tous les **produits binaires** — les limites
    sur le shape fixe `Discrete WalkingPair` (la paire à deux objets).
    Re-export type-sig de la classe Mathlib `HasBinaryProducts C` (aucun
    univers explicite : le shape est fixe). -/
def has_binary_products_field : Prop :=
  HasBinaryProducts C

/-- Pont : la catégorie `C` a tous les **égaliseurs** — les limites sur le
    shape fixe `WalkingParallelPair` (la paire de flèches parallèles), la
    seconde brique du théorème de Freyd avec les produits. Re-export type-sig
    de la classe Mathlib `HasEqualizers C` (aucun univers explicite). -/
def has_equalizers_field : Prop :=
  HasEqualizers C

/-- Pont : un endofoncteur `F : C ⥤ C` **préserve les limites** de taille
    `(u, v)` — l'image par `F` d'un cône limite en est encore une. C'est
    précisément la propriété des adjoints à droite (cf module
    `Grothendieck.Adjunction`) : le foncteur « sections globales » Γ préserve
    ainsi les limites de faisceaux. Re-export type-sig de la classe Mathlib
    `PreservesLimitsOfSize.{u, v} F`. -/
def preserves_limits_of_size_field (F : C ⥤ C) : Prop :=
  PreservesLimitsOfSize.{u, v} F

/-- Pont : un endofoncteur `F : C ⥤ C` **préserve les colimites** de taille
    `(u, v)` — l'image par `F` d'un cocône colimite en est encore une. C'est
    la propriété des adjoints à gauche. Duale de
    `preserves_limits_of_size_field`, re-export type-sig de la classe Mathlib
    `PreservesColimitsOfSize.{u, v} F`. -/
def preserves_colimits_of_size_field (F : C ⥤ C) : Prop :=
  PreservesColimitsOfSize.{u, v} F

end Grothendieck.Limits
