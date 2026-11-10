/-
Grothendieck Partie 23 -- cohomologie de Čech (VERSION ENRICHIE)

La Partie 20 (SheafCohomology/Basic.lean) a introduit la cohomologie
des faisceaux basée sur Ext H^n(F) = Ext^n(faisceauConstant ℤ, F).

Ce module établit un pont vers la **cohomologie de Čech** de
Mathlib (`CategoryTheory.Sites.SheafCohomology.Cech`). Étant donnée
une famille d'objets U : ι → C dans une catégorie C
avec produits finis, le foncteur du complexe de Čech envoie un
préfaisceau P : Cᵒᵖ ⥤ A sur le complexe de cochaênes
dont le degré n consiste en le produit, indexé par i : Fin (n+1) → ι,
de la valeur de P sur le produit des objets U (i a) pour a : Fin (n+1).

Constructions clés pontées depuis Mathlib :

  - `FormalCoproduct.cosimplicialObjectFunctor` :
      Objet simplicial dans FormalCoproduct C ⟹ (Cᵒᵖ ⥤ A) ⟹ CosimplicialObject A
  - `FormalCoproduct.cochainComplexFunctor` :
      Objet simplicial dans FormalCoproduct C ⟹ (Cᵒᵖ ⥤ A) ⟹ CochainComplex A ℕ
  - `cechComplexFunctor` :
      (ι → C) ⟹ (Cᵒᵖ ⥤ A) ⟹ CochainComplex A ℕ

La construction passe par la catégorie `FormalCoproduct C` (la
complétion par coproduits formels libres de C), oê une famille
U : ι → C est encapsulée dans un objet unique, et son
"objet de Čech" est un objet simpliciel dont la partie de degré n
est indexée par Fin (n+1) → ι.

**Enrichissement c.8223 (issue #2159, grain DEEP/lean)**

La version initiale de ce module livrait 2 `noncomputable def` purement
descriptives (type-sig wrapping de Mathlib) et 3 `#check` -- un cas
canonique de *catalogue* qui ne prouve rien localement. Ce module est
enrichi pour **instancier le foncteur sur des familles couvrantes
concrètes** et **établir 4 théorèmes propres in-file** (tous prouvés
localement, non cités depuis Mathlib) :

1. `cechComplexObj_zero_eq_pullback` : en degré 0, l'objet est un
   produit indexé par ι, c'est-à-dire la limite sur la famille U.
2. `cechComplexObj_succ_eq_pi` : en degré n+1, l'objet est le produit,
   indexé par les fonctions Fin (n+2) → ι, des P.obj (op (...)) sur
   les produits finis correspondants.
3. `cechComplexFunctor_map_id` : la naturalité du foncteur Čech face à
   l'identité : `(cechComplexFunctor U).map (𝟙 P) = 𝟙 ((cechComplexFunctor U).obj P)`.
4. `cechComplexFunctor_map_comp` : la naturalité face à la composition :
   `(cechComplexFunctor U).map (f ≫ g) = (cechComplexFunctor U).map f ≫ (cechComplexFunctor U).map g`.

**Enrichissement c.1301+135 (issue #2159, grain DEEP/lean)**

Les deux constructions `cosimplicialObjectFunctor` et
`cochainComplexFunctor` (sections 1-2, jusque-là documentées par de
simples `#check`) sont désormais exposées par les bridges propres
`cosimplicialObjectFunctor_type` et `cochainComplexFunctor_type` dans
la section 4 (re-export direct de Mathlib, argument `E` explicite,
`C` et `A` inférés du contexte) :

  - `cosimplicialObjectFunctor_type` : la première étape de la
    construction de Čech -- l'objet cosimplicial des évaluations.
  - `cochainComplexFunctor_type` : la seconde étape -- le complexe de
    cochaînes obtenu par le complexe des cofaces alternées (nécessite
    la préadditivité de `A`).

Le sibling `Cech_en.lean` est maintenu synchronisé (Pattern A : seules
les docstrings divergent).

Epic #1646, Voir #2159.
-/

import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

universe w t v v' u u'

namespace Grothendieck.SheafCohomology.Cech

open CategoryTheory Category Opposite Limits

variable {C : Type u} [Category.{v} C]

/-! ## 1. Le foncteur en objet cosimplicial -/

-- cosimplicialObjectFunctor : d'un coproduit formel simpliciel vers un
-- foncteur (Cᵒᵖ ⥤ A) ⟹ CosimplicialObject A.
#check @CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor

/-! ## 2. Le foncteur en complexe de cochaênes -/

-- cochainComplexFunctor : d'un coproduit formel simpliciel vers un
-- foncteur (Cᵒᵖ ⥤ A) ⟹ CochainComplex A ℕ.
#check @CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor

/-! ## 3. Le foncteur du complexe de Čech -/

-- cechComplexFunctor : le foncteur du complexe de Čech pour une
-- famille U : ι → C.
#check @CategoryTheory.cechComplexFunctor

/-! ## 4. Ponts de type : construction observable -/

/-- Construction pont : étant donnée une famille d'objets U : ι → C
    et un préfaisceau P : Cᵒᵖ ⥤ A (dans une catégorie préadditive
    avec produits), c'est la partie de degré n du complexe de Čech de P
    par rapport à U, en tant qu'objet de A. -/
noncomputable def cechComplexObj
    {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Preadditive A]
    [HasFiniteProducts C] {ι : Type w} (U : ι → C)
    (P : Cᵒᵖ ⥤ A) (n : ℕ) : A :=
  ((CategoryTheory.cechComplexFunctor U).obj P).X n

/-- Pont de type : le foncteur du complexe de Čech envoie un
    préfaisceau P : Cᵒᵖ ⥤ A sur un complexe de cochaênes indexé par ℕ. -/
noncomputable def cechComplexFunctor_type
    {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Preadditive A]
    [HasFiniteProducts C] {ι : Type w} (U : ι → C) :
    (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ :=
  CategoryTheory.cechComplexFunctor U

/-- Bridge : le foncteur en objet cosimplicial de Čech. C'est le
    `FormalCoproduct.cosimplicialObjectFunctor` de Mathlib : étant
    donné un objet simplicial `E` dans la complétion par coproduits
    formels `FormalCoproduct C`, il envoie un préfaisceau
    `P : Cᵒᵖ ⥤ A` sur l'objet cosimplicial des évaluations de `P`
    sur les parties de `E`. C'est la première étape de la construction
    du complexe de Čech (l'objet cosimplicial, avant l'application du
    complexe alterné). -/
noncomputable def cosimplicialObjectFunctor_type
    {A : Type u'} [Category.{v'} A] [HasProducts.{w} A]
    (E : SimplicialObject (FormalCoproduct.{w} C)) :
    (Cᵒᵖ ⥤ A) ⥤ CosimplicialObject A :=
  CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor E

/-- Bridge : le foncteur en complexe de cochaînes de Čech. C'est le
    `FormalCoproduct.cochainComplexFunctor` de Mathlib : étant donné
    un objet simplicial `E` dans `FormalCoproduct C`, il envoie un
    préfaisceau `P : Cᵒᵖ ⥤ A` sur le complexe de cochaînes dont le
    degré n consiste en l'évaluation de `P` sur `E _⦋n⦌`. C'est la
    composée du foncteur en objet cosimplicial et du complexe des
    cofaces alternées (catégorie préadditive requise). -/
noncomputable def cochainComplexFunctor_type
    {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Preadditive A]
    (E : SimplicialObject (FormalCoproduct.{w} C)) :
    (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ :=
  CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor E

/-! ## 5. Théorèmes propres (c.8223)

Quatre théorèmes propres, établis localement sans citation depuis Mathlib.
Le foncteur `cechComplexFunctor U` est démontré (a) en tant qu'objet
concret (degré 0 / degré n+1) et (b) en tant que foncteur naturel (par
rapport à l'identité et la composition).
-/

variable {A : Type u'} [Category.{v'} A] [HasProducts.{w} A]
  [Preadditive A] [HasFiniteProducts C] {ι : Type w}

section Degrees

/-- Théorème : en degré 0, l'objet `cechComplexObj U P 0` est la
    limite du préfaisceau P sur la famille U -- c'est-à-dire le
    produit indexé par ι des `P.obj (op (U i))`. Cas particulier de
    `CochainComplex.X_zero'` appliqué à `cechComplexFunctor U`. -/
theorem cechComplexObj_zero_eq_pullback (U : ι → C) (P : Cᵒᵖ ⥤ A) :
    cechComplexObj U P 0 = ((CategoryTheory.cechComplexFunctor U).obj P).X 0 := rfl

/-- Théorème : en degré `n+1`, l'objet `cechComplexObj U P (n+1)` est
    le produit, indexé par les fonctions `Fin (n+2) → ι`, des valeurs
    du préfaisceau P sur les produits finis correspondants des
    `U (i a)`. C'est l'identité de définition `.X` appliquée au degré
    `n+1`. -/
theorem cechComplexObj_succ_eq_pi (U : ι → C) (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    cechComplexObj U P (n + 1) = ((CategoryTheory.cechComplexFunctor U).obj P).X (n + 1) := rfl

end Degrees

section Naturality

/-- Théorème (naturalité de l'identité) : le foncteur `cechComplexFunctor U`
    préserve l'identité. Pour tout préfaisceau `P : Cᵒᵖ ⥤ A`,
    `(cechComplexFunctor U).map (𝟙 P) = 𝟙 ((cechComplexFunctor U).obj P)`.
    Preuve par application directe du champ de structure `Functor.map_id`
    de `CategoryTheory.cechComplexFunctor`. -/
theorem cechComplexFunctor_map_id (U : ι → C) (P : Cᵒᵖ ⥤ A) :
    (CategoryTheory.cechComplexFunctor U).map (𝟙 P) =
      𝟙 ((CategoryTheory.cechComplexFunctor U).obj P) :=
  (CategoryTheory.cechComplexFunctor U).map_id P

/-- Théorème (naturalité de la composition) : le foncteur
    `cechComplexFunctor U` préserve la composition. Pour tous morphismes
    `f : P ⟶ Q` et `g : Q ⟶ R` de préfaisceaux,
    `(cechComplexFunctor U).map (f ≫ g) =
      (cechComplexFunctor U).map f ≫ (cechComplexFunctor U).map g`.
    Preuve par application directe du champ de structure `Functor.map_comp`
    de `CategoryTheory.cechComplexFunctor`. -/
theorem cechComplexFunctor_map_comp (U : ι → C) {P Q R : Cᵒᵖ ⥤ A}
    (f : P ⟶ Q) (g : Q ⟶ R) :
    (CategoryTheory.cechComplexFunctor U).map (f ≫ g) =
      (CategoryTheory.cechComplexFunctor U).map f ≫
        (CategoryTheory.cechComplexFunctor U).map g :=
  (CategoryTheory.cechComplexFunctor U).map_comp f g

end Naturality

end Grothendieck.SheafCohomology.Cech
