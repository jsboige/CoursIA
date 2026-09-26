/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grothendieck.Godement

/-!
# Fonctorialite du faisceau de Godement : `C⁰` est un endofoncteur

Suite de la Partie 84 [God58, Chap. II §4.1]. La construction `C⁰F : U ↦ ∏_{x ∈ U} Fₓ`
y est definie **objet par objet**, avec ses trois proprietes (flasque, faisceau,
unite injective sur les faisceaux). Pour la resolution canonique — iterer `C⁰` sur les
noyaux — il manque un prerequis : que `C⁰` soit un **foncteur**. C'est l'objet de
cette Partie, et rien d'autre.

Trois faits, dans l'ordre du recit :

1. `godementHomApp` : un morphisme `φ : F ⟶ G` de prefaisceaux de groupes abeliens
   agit sur les sections de Godement **point par point dans les tiges**, via
   `Presheaf.stalkFunctor`. Aucune condition de compatibilite a verifier : une
   section de Godement est une fonction choisie librement, et l'action est celle,
   induite, sur les valeurs.
2. `godementFunctor` : `C⁰` est un **endofoncteur** de `X.Presheaf AddCommGrpCat`.
   L'identite et la composition sont celles des tiges — la fonctorialite de `C⁰`
   est gratuite, comme sa flasquitude : tout vient de ce que `C⁰` est un produit
   d'evaluations.
3. `toGodementNatTrans` : l'unite `F → C⁰F` est **naturelle** en `F` — c'est une
   transformation naturelle `𝟭 ⟶ C⁰`. La naturalite est un cas de
   `Presheaf.stalkFunctor_map_germ_apply` : le germe du morphisme est le morphisme
   des germes.

Ce qui est acquis est ce qui est prouve : un endofoncteur, et une unite naturelle.
Le lac ne revendique rien de plus — en particulier, la preservation des
monomorphismes par `C⁰` n'est **pas** etablie ici.

## References

  - R. Godement, *Topologie algebrique et theorie des faisceaux* [God58],
    Chap. II §4.1. La construction `C⁰(F)` des sections discontinues.
-/

universe u

open CategoryTheory Category Limits TopCat TopologicalSpace Opposite

namespace Grothendieck

variable {X : TopCat.{u}}

/-- L'action des tiges, point par point : `C⁰` agit sur une section de Godement en
transportant chaque germe par le foncteur des tiges. -/
noncomputable def godementHomApp {F G : X.Presheaf AddCommGrpCat.{u}} (φ : F ⟶ G)
    (U : Opens X) (s : godementSection F U) : godementSection G U :=
  fun x => (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (x : X)).map φ (s x)

/-- `C⁰` est additive : le transport dans les tiges l'est. -/
theorem godementHomApp_add {F G : X.Presheaf AddCommGrpCat.{u}} (φ : F ⟶ G)
    (U : Opens X) (s t : godementSection F U) :
    godementHomApp φ U (s + t) = godementHomApp φ U s + godementHomApp φ U t := by
  funext x
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (x : X)).map φ (s x + t x)
      = (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (x : X)).map φ (s x)
        + (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (x : X)).map φ (t x)
  exact map_add
    (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (x : X)).map φ))
    (s x) (t x)

/-- `C⁰` preserve le zero. -/
theorem godementHomApp_zero {F G : X.Presheaf AddCommGrpCat.{u}} (φ : F ⟶ G)
    (U : Opens X) : godementHomApp φ U (0 : godementSection F U) = 0 := by
  funext x
  exact map_zero
    (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (x : X)).map φ))

/-- `C⁰(𝟙 F) = 𝟙 (C⁰F)` : `stalkFunctor` est un foncteur, son `map_id` suffit. -/
theorem godementHomApp_id (F : X.Presheaf AddCommGrpCat.{u}) (U : Opens X)
    (s : godementSection F U) : godementHomApp (𝟙 F) U s = s := by
  funext x
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (x : X)).map (𝟙 F) (s x) = s x
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- `C⁰(φ ≫ ψ) = C⁰ψ ∘ C⁰φ` : meme raison, `Functor.map_comp`. -/
theorem godementHomApp_comp {F G H : X.Presheaf AddCommGrpCat.{u}} (φ : F ⟶ G)
    (ψ : G ⟶ H) (U : Opens X) (s : godementSection F U) :
    godementHomApp (φ ≫ ψ) U s = godementHomApp ψ U (godementHomApp φ U s) := by
  funext x
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (x : X)).map (φ ≫ ψ) (s x)
      = (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (x : X)).map ψ
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (x : X)).map φ (s x))
  rw [CategoryTheory.Functor.map_comp]
  rfl

/-- `C⁰φ` est un morphisme de prefaisceaux. La naturalite est **definitionnelle** :
restreindre puis transporter dans les tiges, ou transporter puis restreindre, sont
la meme fonction — les deux membres restreignent avant d'appliquer `stalkFunctor`. -/
noncomputable def godementMapHom {F G : X.Presheaf AddCommGrpCat.{u}} (φ : F ⟶ G) :
    godementPresheaf F ⟶ godementPresheaf G where
  app U :=
    AddCommGrpCat.ofHom
      { toFun := godementHomApp φ U.unop
        map_zero' := godementHomApp_zero φ U.unop
        map_add' := godementHomApp_add φ U.unop }
  naturality U V f := by
    ext s
    rfl

/-- `C⁰` preserve l'identite. -/
theorem godementMapHom_id (F : X.Presheaf AddCommGrpCat.{u}) :
    godementMapHom (𝟙 F) = 𝟙 (godementPresheaf F) := by
  ext U s
  funext x
  exact congrFun (godementHomApp_id F U s) x

/-- `C⁰` preserve la composition. -/
theorem godementMapHom_comp {F G H : X.Presheaf AddCommGrpCat.{u}} (φ : F ⟶ G)
    (ψ : G ⟶ H) :
    godementMapHom (φ ≫ ψ) = godementMapHom φ ≫ godementMapHom ψ := by
  ext U s
  funext x
  exact congrFun (godementHomApp_comp φ ψ U s) x

/-- **`C⁰` est un endofoncteur** de la categorie des prefaisceaux de groupes abeliens
sur `X`. C'est le prerequis qui manquait pour iterer la construction sur les noyaux
et former le complexe de Godement. [God58] Chap. II §4.1. -/
noncomputable def godementFunctor :
    X.Presheaf AddCommGrpCat.{u} ⥤ X.Presheaf AddCommGrpCat.{u} where
  obj F := godementPresheaf F
  map φ := godementMapHom φ
  map_id F := godementMapHom_id F
  map_comp φ ψ := godementMapHom_comp φ ψ

/-- La naturalite de l'unite de Godement : prendre le germe de chaque point commute
a l'action d'un morphisme. C'est `Presheaf.stalkFunctor_map_germ_apply` — le germe du
morphisme est le morphisme des germes. -/
theorem toGodement_naturality {F G : X.Presheaf AddCommGrpCat.{u}} (φ : F ⟶ G) :
    toGodement F ≫ godementMapHom φ = φ ≫ toGodement G := by
  ext U s
  funext x
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply U (x : X) x.2 φ s

/-- **L'unite de Godement est naturelle** : `toGodement` est une transformation
naturelle de l'identite vers l'endofoncteur `C⁰`. Avec `C⁰` fonctoriel, l'unite
naturelle `𝟭 ⟶ C⁰` est exactement ce qui permet d'ecrire le premier pas du complexe
de Godement `0 → F → C⁰F → C⁰(K) → ⋯`. -/
noncomputable def toGodementNatTrans :
    𝟭 (X.Presheaf AddCommGrpCat.{u}) ⟶ godementFunctor (X := X) where
  app F := toGodement F
  naturality F G φ := by
    exact (toGodement_naturality φ).symm

end Grothendieck
