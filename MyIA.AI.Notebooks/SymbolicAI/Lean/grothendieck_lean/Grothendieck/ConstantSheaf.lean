/-
Grothendieck Partie 18 — Le faisceau constant

La Partie 17 (SheafHom.lean) a introduit le hom interne des faisceaux,
première étape vers une structure cartésienne fermée sur Sheaf J (Type _).

Ce module introduit le **foncteur faisceau constant** `constantSheaf J D`,
défini comme la faisceautisation du préfaisceau constant. Il est adjoint à
gauche de l'évaluation en un objet terminal (constantSheafAdj), établissant
une adjonction fondamentale en théorie des topos de Grothendieck.

Constructions clés pontées depuis Mathlib (`CategoryTheory.Sites.ConstantSheaf`) :

  - `constantPresheafAdj` : préfaisceau constant ⊣ évaluation en objet terminal
  - `constantSheaf J D` : le foncteur faisceau constant D ⥤ Sheaf J D
  - `constantSheafAdj` : constantSheaf ⊣ sheafSections en objet terminal
  - `Sheaf.IsConstant` : prédicat pour les faisceaux dans l'image essentielle
  - `Sheaf.isConstant_iff_isIso_counit_app` : constance ↔ counit est iso
  - `Sheaf.isConstant_iff_of_equivalence` : constance invariante par équivalence
  - `Sheaf.isConstant_iff_forget` : constance à travers les foncteurs d'oubli

C'est un ingrédient clé pour comprendre la nature « localement constante » des
faisceaux et pour connecter la théorie des faisceaux à la cohomologie (SGA 4 II, IV).

Epic #1646, See #2159. Tous les `sorry` éliminés à la création.
-/

import Mathlib.CategoryTheory.Sites.ConstantSheaf

universe v v' u u'

namespace Grothendieck.ConstantSheaf

open CategoryTheory Category Opposite Limits Functor Sheaf Adjunction

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {D : Type u'} [Category.{v'} D]

/-! ## 1. L'adjonction du préfaisceau constant

Le foncteur préfaisceau constant `Functor.const Cᵒᵖ` envoie un objet X : D sur
le préfaisceau constant en X. Lorsque C possède un objet terminal T, ce foncteur
est adjoint à gauche de l'évaluation en T (c.-à-d. prendre les sections globales).

Cette adjonction se relève aux faisceaux via la faisceautisation.
-/

-- Le foncteur préfaisceau constant est adjoint à gauche de l'évaluation en un objet terminal.
-- constantPresheafAdj : Functor.const Cᵒᵖ ⊣ (evaluation Cᵒᵖ D).obj (op T)
#check @constantPresheafAdj

/-! ## 2. Le foncteur faisceau constant

Le foncteur faisceau constant `constantSheaf J D` est défini comme la composition
du foncteur préfaisceau constant avec la faisceautisation :

  constantSheaf J D = Functor.const Cᵒᵖ ⋙ presheafToSheaf J D

Il envoie un objet X : D sur la faisceautisation du préfaisceau constant en X.
Cela requiert `HasWeakSheafify J D` (existence de la faisceautisation).
-/

-- Le foncteur faisceau constant : faisceautisation du préfaisceau constant.
#check @constantSheaf

/-- Construction pont : le faisceau constant en un objet X : D, défini comme la
    faisceautisation du préfaisceau constant en X. -/
noncomputable def constantSheafObj (X : D) [HasWeakSheafify J D] :
    Sheaf J D :=
  (constantSheaf J D).obj X

/-! ## 3. L'adjonction du faisceau constant

Lorsque C possède un objet terminal T, le foncteur faisceau constant est adjoint
à gauche du foncteur « sections globales » `sheafSections J D`.obj (op T) :

  constantSheaf J D ⊣ (sheafSections J D).obj (op T)

Cela signifie : les morphismes du faisceau constant en X vers un faisceau F
correspondent naturellement à des morphismes X ⟶ F.obj.obj (op T) dans D.
-/

-- L'adjonction du faisceau constant : constantSheaf ⊣ évaluation en l'objet terminal.
#check @constantSheafAdj

/-- Théorème pont : étant donné un objet terminal T, le foncteur faisceau constant
    est adjoint à gauche de l'évaluation des sections de faisceau en T. C'est
    l'adjonction fondamentale sous-jacente à la théorie du faisceau constant. -/
noncomputable def constantSheafAdjBridge {T : C} (hT : IsTerminal T)
    [HasWeakSheafify J D] :
    constantSheaf J D ⊣ (sheafSections J D).obj (op T) :=
  constantSheafAdj J D hT

/-! ## 4. Le prédicat IsConstant

Un faisceau F est « constant » s'il se trouve dans l'image essentielle du
foncteur faisceau constant : il existe X : D tel que F ≅ constantSheaf J D.obj X.

C'est une propriété, non une structure — la constance est une proposition.
-/

-- Un faisceau est constant s'il est dans l'image essentielle de constantSheaf.
#check @Sheaf.IsConstant

-- Si F est constant, il se trouve dans l'image essentielle de constantSheaf.
#check @Sheaf.mem_essImage_of_isConstant

-- Les isomorphismes préservent la constance.
#check @Sheaf.isConstant_congr

-- Un iso avec un faisceau constant témoigne de la constance.
#check @Sheaf.isConstant_of_iso

/-! ## 5. Caractérisation via la coünité

Lorsque le foncteur faisceau constant est pleinement fidèle, un faisceau F est
constant si et seulement si la coünité de l'adjonction du faisceau constant
appliquée à F est un isomorphisme. Cela donne un critère pratique de constance.
-/

-- Lorsque constantSheaf est pleinement fidèle, constance ↔ counit est iso.
#check @Sheaf.isConstant_iff_isIso_counit_app

/-- Théorème pont : lorsque le foncteur faisceau constant est pleinement fidèle
    et que C possède un objet terminal T, un faisceau est constant si et seulement
    si la coünité de l'adjonction qui lui est appliquée est un isomorphisme. -/
theorem isConstant_iff_counit_iso [HasWeakSheafify J D]
    [(constantSheaf J D).Faithful] [(constantSheaf J D).Full]
    (F : Sheaf J D) {T : C} (hT : IsTerminal T) :
    Sheaf.IsConstant J F ↔
      IsIso ((constantSheafAdj J D hT).counit.app F) :=
  CategoryTheory.Sheaf.isConstant_iff_isIso_counit_app J F hT

/-! ## 6. Invariance par équivalence

La propriété d'être constant est invariante par équivalences de catégories de
faisceaux induites par des sous-sites denses. Si G : C ⥤ C' est un morphisme de
sous-site dense, alors un faisceau sur (C', K) est constant si et seulement si
son image réciproque sur (C, J) est constant.
-/

-- La constance est invariante par équivalence de catégories de faisceaux.
#check @Sheaf.isConstant_iff_of_equivalence

/-! ## 7. Constance à travers les foncteurs d'oubli

Étant donné un foncteur d'« oubli » U : D ⥤ B, la propriété d'être constant est
détectée par post-composition avec U (lorsque U préserve la faisceautisation et
que sheafCompose reflète les isomorphismes).
-/

-- Constance détectée à travers les foncteurs d'oubli.
#check @Sheaf.isConstant_iff_forget

/-! ## 8. Commutation avec sheafCompose

Le foncteur faisceau constant commute avec `sheafCompose J U` à isomorphisme
près, pourvu que U préserve la faisceautisation.
-/

-- constantSheaf commute avec sheafCompose à iso près.
#check @constantCommuteCompose

/-! ## 9. Théorèmes pont : image essentielle et allers-retours

La caractérisation par image essentielle donne des propriétés d'aller-retour
connectant le prédicat IsConstant à des témoins explicites.
-/

/-- Construction pont : à partir d'un isomorphisme avec un faisceau constant,
    obtenir un témoin que le faisceau est constant. Utilise `Sheaf.isConstant_of_iso`. -/
theorem isConstant_of_iso_bridge [HasWeakSheafify J D]
    {F : Sheaf J D} {X : D}
    (i : F ≅ (constantSheaf J D).obj X) :
    Sheaf.IsConstant J F := by
  exact CategoryTheory.Sheaf.isConstant_of_iso J i

/-- Construction pont : la constance est préservée par isomorphisme.
    Utilise `Sheaf.isConstant_congr`. -/
theorem isConstant_congr_bridge [HasWeakSheafify J D]
    {F G : Sheaf J D} (i : F ≅ G) [Sheaf.IsConstant J F] :
    Sheaf.IsConstant J G := by
  exact CategoryTheory.Sheaf.isConstant_congr J i

end Grothendieck.ConstantSheaf
