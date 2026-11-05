/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Sites.IsSheafFor
import Mathlib.Topology.Sheaves.Flasque
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Topology.Sheaves.Stalks

/-!
# Le faisceau de Godement : sections discontinues

Suite du fil God58 après la clôture de la veine flasque (P79-P83) : la
construction de Godement [God58, Chap. II §4.1], l'application directe des
tiges (P73) et des critères de flasquité. Pour un préfaisceau `F` de groupes
abéliens sur `X`, la section de Godement sur `U` est la famille de germes
`C⁰(U) = ∏_{x ∈ U} Fₓ` — toute fonction choisissant un germe à chaque point,
sans aucune condition de continuité. D'où le nom : sections discontinues.

Trois faits, dans l'ordre du récit :

1. `isFlasque_godementPresheaf` : `C⁰F` est **flasque** — une section sur `U`
   s'étend à tout `V ⊇ U` en prolongeant par zéro hors de `U` (les germes
   vivent dans des groupes abéliens, le zéro est toujours disponible). C'est
   l'extension la plus brutale qui soit : aucune donnée à préserver.
2. `isSheaf_godementPresheaf` : `C⁰F` est un **faisceau** — une famille
   compatible sur un recouvrement se recolle point par point : deux valeurs
   coïncident sur les intersections parce que la compatibilité, pour des
   sections qui SONT des fonctions, est une égalité pointwise.
3. `injective_toGodement_of_isSheaf` : l'unité `F → C⁰F` (prendre le germe de
   chaque point) est **injective quand `F` est un faisceau** — deux sections
   aux germes égaux partout coïncident sur un voisinage de chaque point
   (`Presheaf.germ_eq`), et le recollement unique les identifie. C'est la
   localité, l'autre moitié de la condition de faisceau.

La construction est absente de Mathlib (vérifié v4.33.0) ; elle ouvre la voie
à la résolution canonique de Godement (itérer `C⁰` sur les noyaux), fil
prochain du lac.

## Références

  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §4.1. Le faisceau `C⁰(F)` des sections discontinues.
-/

universe u

open CategoryTheory Category Limits TopCat TopologicalSpace Opposite

namespace Grothendieck

variable {X : TopCat.{u}} (F : X.Presheaf AddCommGrpCat.{u})

/-- Une section de Godement sur `U` : un germe en chaque point de `U`.
Le `AddCommGroup` est ponctuel (produit de groupes). -/
noncomputable def godementSection (U : Opens X) : Type u :=
  ∀ x : U, ↥(F.stalk (x : X))

noncomputable instance (U : Opens X) : AddCommGroup (godementSection F U) :=
  Pi.addCommGroup

/-- Le faisceau de Godement, objet par objet : `AddCommGrp.of` du produit. -/
noncomputable def godementObj (U : Opens X) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of (godementSection F U)

/-- Restriction d'une section de Godement le long de `i : V ⟶ U` :
précomposition — la fonction se restreint. -/
noncomputable def godementMap {V U : Opens X} (i : V ⟶ U) :
    godementObj F U ⟶ godementObj F V :=
  AddCommGrpCat.ofHom
    { toFun := fun f x => f ⟨x.1, leOfHom i x.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

/-- Le préfaisceau de Godement `C⁰F : U ↦ ∏_{x ∈ U} Fₓ`. -/
noncomputable def godementPresheaf : X.Presheaf AddCommGrpCat where
  obj U := godementObj F U.unop
  map f := godementMap F f.unop
  map_id U := by
    ext f
    funext x
    rfl
  map_comp f g := by
    ext s
    funext x
    rfl

/-- La restriction d'une section de Godement est l'évaluation sur le point
transporté : compte tenu de la définition de `godementMap`, c'est une
réduction définitionnelle. C'est la clé de calcul de tout le module. -/
theorem godementPresheaf_map_apply {V U : Opens X} (i : V ⟶ U)
    (s : godementSection F U) (x : V) :
    (godementPresheaf F).map i.op s x = s ⟨(x : X), leOfHom i x.2⟩ :=
  rfl

open scoped Classical in
/-- Extension par zéro : une section de Godement sur `U` se prolonge à
tout `V ⊇ U` en choisissant le germe nul hors de `U`. C'est l'ingrédient
de flasquité — le zéro des tiges rend le prolongement toujours possible. -/
noncomputable def godementExtend {U V : Opens X}
    (s : godementSection F U) : godementSection F V :=
  fun x => if h : (x : X) ∈ U then s ⟨x, h⟩ else 0

/-- **Le faisceau de Godement est flasque** : toute section sur `U` se
prolonge à tout `V ⊇ U` (par zéro hors de `U`) — la restriction est
surjective, donc épimorphe. Aucune hypothèse sur `F` : la flasquité de
`C⁰F` est gratuite, c'est tout l'intérêt de la construction.
[God58] Chap. II §4.1. -/
theorem isFlasque_godementPresheaf : godementPresheaf F |>.IsFlasque where
  epi i := by
    refine (AddCommGrpCat.epi_iff_surjective _).mpr fun s => ⟨?_, ?_⟩
    · exact godementExtend F s
    · funext x
      exact dif_pos x.2

/-- L'unité de Godement : une section devient la famille de ses germes.
Naturelle par `Presheaf.germ_res` — prendre le germe commute aux
restrictions. -/
noncomputable def toGodement : F ⟶ godementPresheaf F where
  app U :=
    AddCommGrpCat.ofHom
      { toFun := fun s x => F.germ U.unop (x : X) x.2 s
        map_zero' := by funext x; rw [map_zero]; rfl
        map_add' := fun a b => by funext x; rw [map_add]; rfl }
  naturality U V f := by
    ext s
    funext x
    exact F.germ_res_apply' f (x : X) x.2 s

/-- **Le faisceau de Godement est un faisceau** : toute famille compatible
de sections sur une famille d'ouverts `U i` se recolle en une unique section
sur `⋃ U i`. Le recollement est littéralement pointwise : chaque point `z` de
la réunion vit dans un certain `U i` (choisi par `Classical.choice`), et la
compatibilité — pour des sections qui SONT des fonctions — garantit que le
choix de l'indice n'affecte pas la valeur en `z`. L'unicité est de même
entièrement ponctuelle : deux recollements coïncident sur chaque `U i`,
donc en chaque point de la réunion. La preuve passe par la caractérisation
`isSheaf_iff_isSheafUniqueGluing` de la condition de faisceau, disponible
pour `AddCommGrpCat` (catégorie concrète complète). -/
theorem isSheaf_godementPresheaf : TopCat.Presheaf.IsSheaf (godementPresheaf F) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hcomp
  have hcover : ∀ z : ((iSup U : Opens X)), ∃ i, (z : X) ∈ U i :=
    fun z => Opens.mem_iSup.mp z.2
  choose f hf using hcover
  have hglue : TopCat.Presheaf.IsGluing (godementPresheaf F) U sf
      (fun z => sf (f z) ⟨(z : X), hf z⟩) := by
    intro i
    funext x
    have hW := congrFun (hcomp i (f ⟨(x : X), leOfHom (Opens.leSupr U i) x.2⟩))
      ⟨(x : X), ⟨x.2, hf ⟨(x : X), leOfHom (Opens.leSupr U i) x.2⟩⟩⟩
    exact hW.symm
  refine ⟨_, hglue, fun s hs => ?_⟩
  funext z
  exact congrFun (hs (f z)) ⟨(z : X), hf z⟩

/-- **L'unité de Godement est injective sur les faisceaux** : si `F` est un
faisceau, deux sections dont les germes coïncident en chaque point de `U`
sont égales. La preuve est la localité : `Presheaf.germ_eq` (P73) fournit
pour chaque point un voisinage `W z ⊆ U` où les restrictions coïncident ;
les `W z` recouvrent `U` (donc `⨆ W = U`), et `s` comme `t` recollent la
même famille — l'unicité du recollement (`isSheaf_iff_isSheafUniqueGluing`)
les identifie. Toutes les égalités de morphismes d'ouverts passent par
`Subsingleton` : deux inclusions `V ⟶ U` sont égales.
C'est la réciproque attendue : le faisceau de Godement contient `F`
entièrement dès que `F` est un faisceau. [God58] Chap. II §4.1. -/
theorem injective_toGodement_of_isSheaf (hF : TopCat.Presheaf.IsSheaf F)
    (U : Opens X) : Function.Injective ((toGodement F).app (op U)) := by
  intro s t hst
  have hgerm : ∀ z : U, F.germ U (z : X) z.2 s = F.germ U (z : X) z.2 t :=
    fun z => congrFun hst ⟨(z : X), z.2⟩
  have hloc : ∀ z : U, ∃ W : Opens X, (z : X) ∈ W ∧ ∃ iWU : W ⟶ U,
      F.map iWU.op s = F.map iWU.op t := by
    intro z
    obtain ⟨W, hxW, iU', iV', heq⟩ := F.germ_eq (z : X) z.2 z.2 s t (hgerm z)
    refine ⟨W, hxW, iU', ?_⟩
    rw [Subsingleton.elim iV' iU'] at heq
    exact heq
  choose W hW iWU hagree using hloc
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing] at hF
  have hcompf : TopCat.Presheaf.IsCompatible F W (fun z => F.map (iWU z).op s) := by
    intro i j
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp,
      Subsingleton.elim (Opens.infLELeft (W i) (W j) ≫ iWU i)
        (Opens.infLERight (W i) (W j) ≫ iWU j)]
  obtain ⟨t₀, _, huniq⟩ := hF W (fun z => F.map (iWU z).op s) hcompf
  have hsupU : (iSup W : Opens X) = U := by
    refine le_antisymm (iSup_le fun z => leOfHom (iWU z)) ?_
    intro x hxU
    exact Opens.mem_iSup.mpr ⟨⟨x, hxU⟩, hW ⟨x, hxU⟩⟩
  have hsG : TopCat.Presheaf.IsGluing F W (fun z => F.map (iWU z).op s)
      (F.map (homOfLE (le_of_eq hsupU)).op s) := by
    intro z
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      Subsingleton.elim (Opens.leSupr W z ≫ homOfLE (le_of_eq hsupU)) (iWU z)]
  have htG : TopCat.Presheaf.IsGluing F W (fun z => F.map (iWU z).op s)
      (F.map (homOfLE (le_of_eq hsupU)).op t) := by
    intro z
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      Subsingleton.elim (Opens.leSupr W z ≫ homOfLE (le_of_eq hsupU)) (iWU z)]
    exact (hagree z).symm
  have hd : F.map (homOfLE (le_of_eq hsupU)).op s
      = F.map (homOfLE (le_of_eq hsupU)).op t :=
    (huniq _ hsG).trans (huniq _ htG).symm
  have key : ∀ u : ToType (F.obj (op U)),
      F.map (homOfLE (le_of_eq hsupU.symm)).op
        (F.map (homOfLE (le_of_eq hsupU)).op u) = u := by
    intro u
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      Subsingleton.elim (homOfLE (le_of_eq hsupU.symm)
        ≫ homOfLE (le_of_eq hsupU)) (𝟙 U)]
    rw [show (𝟙 U).op = 𝟙 (op U) from rfl, F.map_id]
    rfl
  exact (key s).symm.trans ((congrArg _ hd).trans (key t))

end Grothendieck
