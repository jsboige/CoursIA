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
# The Godement sheaf: discontinuous sections

English canonical sibling of `Grothendieck/Godement.lean` (Partie 84).

Continuation of the God58 thread after the flasque vein closed (P79-P83):
Godement's construction [God58, Chap. II §4.1], with direct use of stalks
(P73) and of the flasqueness criteria. For a presheaf `F` of abelian groups
on `X`, the Godement section over `U` is the family of germs
`C⁰(U) = ∏_{x ∈ U} Fₓ` — any function choosing a germ at each point, with
no continuity condition whatsoever. Hence the name: discontinuous sections.

Three facts, in the narrative order:

1. `isFlasque_godementPresheaf`: `C⁰F` is **flasque** — a section over `U`
   extends to any `V ⊇ U` by zero outside `U` (germs live in abelian
   groups, zero is always available). This is the most brutal extension
   possible: no data to preserve.
2. `isSheaf_godementPresheaf`: `C⁰F` is a **sheaf** — a compatible family
   over a cover glues point by point: two values agree on intersections
   because compatibility, for sections that ARE functions, is a pointwise
   equality.
3. `injective_toGodement_of_isSheaf`: the unit `F → C⁰F` (take the germ at
   each point) is **injective when `F` is a sheaf** — two sections with
   equal germs everywhere agree on a neighbourhood of each point
   (`Presheaf.germ_eq`), and unique gluing identifies them. This is
   locality, the other half of the sheaf condition.

The construction is absent from Mathlib (checked v4.33.0); it opens the way
to Godement's canonical resolution (iterating `C⁰` on kernels), the next
thread of this lake.

i18n convention (EPIC #4980 ratified 2026-07-04): `_en` suffix on the
namespace (`Grothendieck.Godement_en`), mirror imports, translated
docstrings and comments. Theorem statements, Lean tactics, lemma names and
Mathlib references remain in English. Anti-§D byte-identity guaranteed:
the namespace body is preserved bit for bit (statements and proofs
byte-identical between `Godement.lean` and `Godement_en.lean`).

## References

  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §4.1. The sheaf `C⁰(F)` of discontinuous sections.
-/

universe u

open CategoryTheory Category Limits TopCat TopologicalSpace Opposite

namespace Grothendieck.Godement_en

variable {X : TopCat.{u}} (F : X.Presheaf AddCommGrpCat.{u})

/-- A Godement section over `U`: a germ at each point of `U`.
The `AddCommGroup` is pointwise (product of groups).
Stacks correspondence — **PARTIAL**: Stacks does not formalise the "product of
stalks" presheaf on a topological space; its degree-0 term is `f_* f^*` on the
modules of a ringed space
(`Topology/Sheaves/Cohomology/GodementResolution/Basic.lean:416`,
`godementComonad`, tag 0FKS). The gap of setting is explicit; the inequality is
not.
-/
noncomputable def godementSection (U : Opens X) : Type u :=
  ∀ x : U, ↥(F.stalk (x : X))

noncomputable instance (U : Opens X) : AddCommGroup (godementSection F U) :=
  Pi.addCommGroup

/-- The Godement sheaf, objectwise: `AddCommGrp.of` the product.
Stacks correspondence — **PARTIAL**: the categorical object is, in Stacks, that of
`f_* f^*` on `Mod(𝒪_X)` (`Basic.lean:416`); ours is an `AddCommGrpCat.of` of the
product of stalks. Same gap of setting: abelian groups on a topological space on one
side, modules on a ringed space on the other.
-/
noncomputable def godementObj (U : Opens X) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of (godementSection F U)

/-- Restriction of a Godement section along `i : V ⟶ U`:
precomposition — the function restricts.
Stacks correspondence — **PARTIAL**: in Stacks the restriction is the one of
`f_*` (`Basic.lean:416`); ours is the precomposition on germs. No named statement
of Stacks describes this transport point by point.
-/
noncomputable def godementMap {V U : Opens X} (i : V ⟶ U) :
    godementObj F U ⟶ godementObj F V :=
  AddCommGrpCat.ofHom
    { toFun := fun f x => f ⟨x.1, leOfHom i x.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

/-- The Godement presheaf `C⁰F : U ↦ ∏_{x ∈ U} Fₓ`.
Stacks correspondence — **PARTIAL**: the degree-0 term of the Stacks Godement
complex is the iterate `(f_* f^*)^{n+1}` (`Basic.lean:466` `godementComplex`,
`Basic.lean:482` `godementComplexEvalIso`); the equality between `f_* f^*` and the
product of stalks is not established in Stacks. What our version adds: the
construction of the product of stalks as a **presheaf** (Stacks builds a sheaf of
modules).
-/
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

/-- Restricting a Godement section is evaluation at the transported
point: given the definition of `godementMap`, this is a definitional
reduction. This is the computation key of the whole module.
Stacks correspondence — **ABSENT**: no named statement in the Stacks files read
(`Basic.lean`, `Stalk.lean`, `StalkHomotopy.lean`, `Sheaf/Abelian.lean`) describes
this transport; it is a definitional-reduction lemma proper to our definition of
`godementMap`.
-/
theorem godementPresheaf_map_apply {V U : Opens X} (i : V ⟶ U)
    (s : godementSection F U) (x : V) :
    (godementPresheaf F).map i.op s x = s ⟨(x : X), leOfHom i x.2⟩ :=
  rfl

open scoped Classical in
/-- Zero extension: a Godement section over `U` extends to any `V ⊇ U`
by choosing the zero germ outside `U`. This is the flasqueness ingredient
— the zero of stalks makes the extension always possible.
Stacks correspondence — **PARTIAL**: Stacks establishes the flasqueness of every
term of the complex (`Basic.lean:499` `isFlasque_godementComplex`, tag 0FKS;
`Basic.lean:276` `isFlasque_iterate_modulePullbackPushforward`) but does not name
the extension by zero; what our version adds is to write it, and that is what makes
the "no hypothesis on `F`" case readable.
-/
noncomputable def godementExtend {U V : Opens X}
    (s : godementSection F U) : godementSection F V :=
  fun x => if h : (x : X) ∈ U then s ⟨x, h⟩ else 0

/-- **The Godement sheaf is flasque**: every section over `U` extends to
any `V ⊇ U` (by zero outside `U`) — the restriction is surjective, hence
epimorphic. No hypothesis on `F`: the flasqueness of `C⁰F` is free, which
is the whole point of the construction. [God58] Chap. II §4.1.
Stacks correspondence — **COVERED**:
`Topology/Sheaves/Cohomology/GodementResolution/Basic.lean:499`
(`isFlasque_godementComplex`, tag 0FKS) and `Basic.lean:276`
(`isFlasque_iterate_modulePullbackPushforward`) establish the flasqueness of the
terms of the Godement complex. Gap of setting: Stacks works with sheaves of
modules on a ringed space, we work with the **presheaf** `C⁰F` of a presheaf of
abelian groups, without any sheaf hypothesis. What our version adds: the extension
by zero as a construction.
-/
theorem isFlasque_godementPresheaf : godementPresheaf F |>.IsFlasque where
  epi i := by
    refine (AddCommGrpCat.epi_iff_surjective _).mpr fun s => ⟨?_, ?_⟩
    · exact godementExtend F s
    · funext x
      exact dif_pos x.2

/-- The Godement unit: a section becomes the family of its germs.
Natural by `Presheaf.germ_res` — taking germs commutes with
restrictions.
Stacks correspondence — **PARTIAL**: Stacks has two distinct units — the unit of
the adjunction at degree 0 (`Basic.lean:475` `godementAugmentation`) and the
"Godement on opens"
(`Cohomology/CechDerivedEffaceability/GodementResolution.lean:181` `godUnit`,
whose sections `GodSections` l.99 are families of sections, not germs). Ours — the
germ at every point — has no named statement.
-/
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

/-- **The Godement sheaf is a sheaf**: every compatible family of sections
over a family of opens `U i` glues to a unique section over `⋃ U i`. The
gluing is literally pointwise: each point `z` of the union lives in some
`U i` (chosen by `Classical.choice`), and compatibility — for sections
that ARE functions — guarantees that the choice of index does not affect
the value at `z`. Uniqueness is likewise entirely punctual: two gluings
agree on each `U i`, hence at every point of the union. The proof goes
through the `isSheaf_iff_isSheafUniqueGluing` characterisation of the
sheaf condition, available for `AddCommGrpCat` (concrete complete
category).
Stacks correspondence — **PARTIAL**: in Stacks, the sheaf property of the degree-0
term comes from `f_*` (direct image of a sheaf); no named statement says that the
product of stalks of a sheaf of abelian groups is a sheaf — that is Godement's
theorem, which our statement proves.
-/
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

/-- **The Godement unit is injective on sheaves**: if `F` is a sheaf, two
sections whose germs coincide at every point of `U` are equal. The proof
is locality: `Presheaf.germ_eq` (P73) provides, for each point, a
neighbourhood `W z ⊆ U` where the restrictions coincide; the `W z` cover
`U` (so `⨆ W = U`), and both `s` and `t` glue the same family — unique
gluing (`isSheaf_iff_isSheafUniqueGluing`) identifies them. All equalities
of morphisms of opens go through `Subsingleton`: two inclusions
`V ⟶ U` are equal. This is the expected converse: the Godement sheaf
contains `F` entirely as soon as `F` is a sheaf. [God58] Chap. II §4.1.
Stacks correspondence — **COVERED**: `Topology/Sheaves/Sheaf/Abelian.lean:149`
(`restrict_eq_zero_of_germ_eq_zero`) states that a section of a sheaf of abelian
groups whose germs are all zero is zero — its contrapositive is exactly our
converse of the unit. What our version adds: the phrasing "two sections with the
same germs are equal" and the route through unique gluing.
-/
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

end Grothendieck.Godement_en
