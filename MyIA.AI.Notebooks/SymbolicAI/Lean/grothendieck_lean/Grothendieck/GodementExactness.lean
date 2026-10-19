/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grothendieck.GodementCanonicalDiff
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.Stalks

/-!
# Le complexe augmenté de Godement : d¹, le mono de l'unité, la séparéité du conoyau

Partie 90 — la suite annoncée de la Partie 89. Cette dernière avait posé le pas
canonique `godementStep f := cokernel.π f ≫ toGodement (coker f)` et la
différentielle `d⁰ := godementCanonicalDZero` avec sa null-composition
`μ ≫ d⁰ = 0`. Cette Partie fait deux pas de plus sur le même fil (le troisième
— la **réduction de l'exactitude** — a été retiré : voir note de l'auteur à
la fin du namespace). La **Partie 91 y ouvre son pas A** (la séparéité du
conoyau de l'unité) **et livre son pas B** (le mono de l'unité du conoyau,
puis l'exactitude `μ ≫ d⁰`), tous deux prouvés en clôture de module.

## Deux faits, dans l'ordre du récit

1. `godementCanonicalDOne` : la **différentielle de degré 1** — le pas canonique
   appliqué à `d⁰`. Le terme suivant `C²F := C⁰(coker d⁰)` est le préfaisceau de
   Godement du conoyau de `d⁰`, et `d¹ : C¹F ⟶ C²F` en est la flèche. La
   null-composition `d⁰ ≫ d¹ = 0` (`godementCanonicalDZero_comp_godementCanonicalDOne`)
   est une instance de `comp_godementStep_zero` (P89) : **la résolution canonique
   est un complexe au-delà du degré 0** — chaque degré s'obtient en appliquant le
   pas canonique à la différentielle précédente, et la null-composition est
   gratuite à chaque étape.
2. `mono_toGodement_of_isSheaf` : **l'unité de Godement est un monomorphisme
   catégorique sur les faisceaux**. La Partie 84 avait prouvé l'injectivité
   section par section (`godementUnit_injective_of_isSheaf`) ; ce fait en est la
   montée catégorique : mono dans la catégorie des préfaisceaux, via
   `NatTrans.mono_iff_mono_app` (le mono d'une transformation naturelle entre
   préfaisceaux de groupes abéliens est exactement le mono section par section).
   C'est l'exactitude de `0 → F → C⁰F` **en F**, désormais énoncée dans le
   langage des complexes.

## Ce que cette Partie pose vs. ce qu'elle laisse ouvert

**Posé** : le complexe aux degrés 0 et 1 (et le motif d'itération qui prolonge à
tous les degrés), et le mono catégorique de l'unité sur les faisceaux.

**Non posé** — frontière nommée de la Partie 91 : la **réduction de l'exactitude
en `C⁰F` au mono de l'unité du conoyau** (`exact_toGodement_godementCanonicalDZero`),
dont les deux montées — le **pas A** (séparéité du conoyau `coker μ` pour `F`
faisceau : recollement des sections locales du quotient par séparéité de `F`
et injectivité de `μ`) et le **pas B** (mono de `toGodement (coker μ)` par
localité P84 + pas A, puis transfert de l'exactitude du conoyau à `d⁰` par
`ShortComplex.exact_iff_of_epi_of_isIso_of_mono`) — sont **prouvées dans ce
module**. Restent l'**itération complète** de la réduction aux degrés
supérieurs, et l'**acyclicité** `H^n(C⁰F) = 0` pour `n ≥ 1` ([God58] II.5).

## Références

  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §4.1. La résolution canonique `0 → F → C⁰F → C¹F → ⋯` : complexe
    (d⁰ ≫ d¹ = 0) et exactitude en `C⁰F` — réduite ici au mono de l'unité du
    conoyau.
  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §5. Acyclicité — frontière nommée de la Partie 91.
-/

universe u

open CategoryTheory Category Limits TopCat TopologicalSpace Opposite

namespace Grothendieck

variable {X : TopCat.{u}}

/-- **La différentielle de degré 1 de la résolution canonique** : le pas
canonique de la Partie 89 appliqué à `d⁰`. Le terme `C¹F = C⁰(coker μ)` (posé en
P89 comme codomaine de `d⁰`) engendre à son tour `C²F = C⁰(coker d⁰)`, et `d¹`
est la flèche `C¹F ⟶ C²F`. Le motif est uniforme : `d^{n+1} := godementStep d^n`,
chaque terme étant le préfaisceau de Godement du conoyau de la différentielle
précédente ([God58] II §4.1). -/
noncomputable def godementCanonicalDOne (F : X.Presheaf AddCommGrpCat.{u}) :
    godementPresheaf (cokernel (toGodement F)) ⟶
    godementPresheaf (cokernel (godementCanonicalDZero F)) :=
  godementStep (godementCanonicalDZero F)

/-- **La null-composition en degré 1** : `d⁰ ≫ d¹ = 0`. Instance immédiate de
`comp_godementStep_zero` (P89) — la résolution canonique est un complexe au-delà
du degré 0, et le restera à chaque degré suivant par le même argument : chaque
différentielle composée avec son pas canonique s'annule par la condition
universelle du conoyau. -/
theorem godementCanonicalDZero_comp_godementCanonicalDOne
    (F : X.Presheaf AddCommGrpCat.{u}) :
    godementCanonicalDZero F ≫ godementCanonicalDOne F = 0 :=
  comp_godementStep_zero _

/-- **L'unité de Godement est un monomorphisme catégorique sur les faisceaux** :
la montée catégorique de l'injectivité section par section de la Partie 84
(`godementUnit_injective_of_isSheaf`). Dans la catégorie des préfaisceaux de
groupes abéliens, un morphisme est mono exactement quand chaque composante
l'est (`NatTrans.mono_iff_mono_app`), et dans `AddCommGrpCat` un morphisme est
mono exactement quand il est injectif (`AddCommGrpCat.mono_iff_injective`).
C'est l'exactitude de `0 → F → C⁰F` **en F**, énoncée dans le langage des
catégories. -/
theorem mono_toGodement_of_isSheaf (F : X.Presheaf AddCommGrpCat.{u})
    (hF : TopCat.Presheaf.IsSheaf F) :
    Mono (toGodement F) := by
  rw [NatTrans.mono_iff_mono_app]
  intro U
  exact (AddCommGrpCat.mono_iff_injective _).mpr
    (godementUnit_injective_of_isSheaf F hF U.unop)

/- Note de l'auteur : la **réduction de l'exactitude en `C⁰F` au mono de
l'unité du conoyau** ([God58] II.4.1) — énoncé 3 du draft r65
(`exact_toGodement_godementCanonicalDZero_of_mono`) — avait été **retirée de
la Partie 90** : le draft portait un `sorry` tactique sur cette preuve (defeq
de X₂ non réconcilié, instance `IsIso` non inférée), et le gate
`proof-integrity` du caller workflow a élevé ce `sorry` en `sorryAx`
transitif à l'import — classe `forbidden` (pr-review-discipline §B).
L'option honnête était le **retrait**. La Partie 91 reprend ce fil en deux
pas, **tous deux clos dans ce module** : le pas A (séparéité du conoyau
`coker μ` pour `F` faisceau) est prouvé intégralement, par le même argument
de recollement que la Partie 84 ; le pas B — monter de la séparéité au mono
de `toGodement (coker μ)`, puis à l'exactitude de `μ ≫ d⁰` — est clos en
clôture de module. Aucun énoncé-stub `True.intro` ni `False` n'est laissé
dans le module. -/

/-! ## Le pas A de la Partie 91 : la séparéité du conoyau

`eq_zero_of_locally_zero_cokernel_toGodement` : pour `F` faisceau, une
section `s` du conoyau `coker μ` qui s'annule sur chaque ouvert d'une
famille couvrante `V` de `U` est nulle. Le conoyau n'est pas un faisceau en
général — mais il reste **séparé**, et c'est tout ce que le pas B exigera.
La preuve transpose le schéma de la Partie 84 au quotient. -/

/-- **La composante en un ouvert du morphisme nul de préfaisceaux est nulle** :
bribe technique utilisée deux fois (condition de descente et conclusion) pour
réécrire `(0 : G ⟶ H).app W` en la flèche nulle de groupes abéliens — vraie
par défaut, la structure nulle des transformations naturelles étant posée
composante par composante. -/
private theorem zero_app (G H : X.Presheaf AddCommGrpCat.{u}) (W : (Opens X)ᵒᵖ) :
    (0 : G ⟶ H).app W = 0 := rfl

/-- **L'image de l'unité se restreint en l'image de l'unité** : la condition de
compatibilité du préfaisceau quotient — la naturalité de `μ` fait passer le
range de `μ_W` dans le range de `μ_{W'}` par la restriction. -/
private theorem toGodement_range_le_comap
    (F : X.Presheaf AddCommGrpCat.{u}) {W W' : (Opens X)ᵒᵖ} (f : W ⟶ W') :
    AddMonoidHom.range ((toGodement F).app W).hom ≤
      AddSubgroup.comap ((godementPresheaf F).map f).hom
        (AddMonoidHom.range ((toGodement F).app W').hom) := by
  intro y hy
  rw [AddSubgroup.mem_comap, AddMonoidHom.mem_range]
  obtain ⟨t, rfl⟩ := hy
  refine ⟨F.map f t, ?_⟩
  rw [← ConcreteCategory.comp_apply, (toGodement F).naturality,
    ConcreteCategory.comp_apply]

/-- **Le préfaisceau quotient de `C⁰F` par l'image de l'unité** : à chaque
ouvert `W`, le groupe `C⁰F(W) ⧸ μ_W(F(W))`, muni des restrictions induites —
la naturalité de `μ` garantit que l'image de `μ_W` se restreint en l'image de
`μ_{W'}`. C'est le réceptacle de la descente qui relie la projection du
conoyau (au niveau des préfaisceaux) au quotient algébrique section par
section. -/
private noncomputable def unitImageQuotientPresheaf (F : X.Presheaf AddCommGrpCat.{u}) :
    X.Presheaf AddCommGrpCat.{u} where
  obj W := AddCommGrpCat.of (((godementPresheaf F).obj W) ⧸
    AddMonoidHom.range ((toGodement F).app W).hom)
  map {W W' : (Opens X)ᵒᵖ} (f : W ⟶ W') :=
    AddCommGrpCat.ofHom <|
      QuotientAddGroup.map _ _ ((godementPresheaf F).map f).hom
        (toGodement_range_le_comap F f)
  map_id W := by
    ext x
    simp
  map_comp {W W' W'' : (Opens X)ᵒᵖ} (f : W ⟶ W') (g : W' ⟶ W'') := by
    ext x
    simp

/-- **La projection section par section sur le quotient par l'image** : la
transformation naturelle `C⁰F ⟶ C⁰F/im μ` dont chaque composante est
`QuotientAddGroup.mk'`. -/
private noncomputable def unitImageQuotientπ (F : X.Presheaf AddCommGrpCat.{u}) :
    godementPresheaf F ⟶ unitImageQuotientPresheaf F where
  app W := AddCommGrpCat.ofHom
    (QuotientAddGroup.mk' (AddMonoidHom.range ((toGodement F).app W).hom))
  naturality W W' f := by
    ext x
    exact QuotientAddGroup.map_mk'
      (N := AddMonoidHom.range ((toGodement F).app W).hom)
      (M := AddMonoidHom.range ((toGodement F).app W').hom)
      (f := ((godementPresheaf F).map f).hom)
      (toGodement_range_le_comap F f) _

/-- **L'unité composée avec la projection quotient est nulle** : la condition
de descente — chaque `μ_W t` est nul dans le quotient par l'image. -/
private theorem toGodement_comp_unitImageQuotientπ
    (F : X.Presheaf AddCommGrpCat.{u}) :
    toGodement F ≫ unitImageQuotientπ F = 0 := by
  refine NatTrans.ext (funext fun W => ?_)
  rw [NatTrans.comp_app, zero_app]
  ext x
  exact (QuotientAddGroup.eq_zero_iff ((toGodement F).app W x)).mpr
    ((AddMonoidHom.mem_range).mpr ⟨x, rfl⟩)

/-- **La projection du conoyau d'une flèche de préfaisceaux est surjective
section par section** : la composante en `U` de `cokernel.π f` couvre tout le
conoyau. Trois montées enchaînées : la projection d'un conoyau est
épimorphe (`coequalizer.π_epi`, via `coequalizer_as_cokernel`), l'épi d'une
transformation naturelle se lit section par section
(`NatTrans.epi_iff_epi_app`), et l'épi des groupes abéliens est la
surjectivité (`AddCommGrpCat.epi_iff_surjective`). -/
private theorem surjective_cokernel_app {A B : X.Presheaf AddCommGrpCat.{u}}
    (f : A ⟶ B) (U : Opens X) :
    Function.Surjective ((cokernel.π f).app (op U)) := by
  rw [← AddCommGrpCat.epi_iff_surjective, ← coequalizer_as_cokernel]
  exact (NatTrans.epi_iff_epi_app _).mp coequalizer.π_epi (op U)

/-- **Une section de Godement nulle dans le conoyau se relève** : si `x` se
projette sur `0` dans `coker μ`, alors `x` est dans l'image de `μ`. La
preuve fait parler la propriété universelle du conoyau au niveau des
préfaisceaux : la projection quotient `C⁰F ⟶ C⁰F/im μ` (naturelle, nulle
après `μ`) se factorise par la projection `π : C⁰F ⟶ coker μ`, et la nullité
de `π x` descend au quotient algébrique, où `eq_zero_iff` extrait un
antécédent. C'est la brique « relèvement local » que le pas A applique à
chaque ouvert du recouvrement. -/
private theorem exists_of_cokernelπ_app_eq_zero
    (F : X.Presheaf AddCommGrpCat.{u}) (W : Opens X)
    (x : (godementPresheaf F).obj (op W))
    (hx : (cokernel.π (toGodement F)).app (op W) x = 0) :
    ∃ t : F.obj (op W), (toGodement F).app (op W) t = x := by
  classical
  have hfacW : (cokernel.π (toGodement F)).app (op W) ≫
      (cokernel.desc (toGodement F) (unitImageQuotientπ F)
        (toGodement_comp_unitImageQuotientπ F)).app (op W)
      = (unitImageQuotientπ F).app (op W) := by
    rw [← NatTrans.comp_app, cokernel.π_desc]
  have h1 : QuotientAddGroup.mk'
      (AddMonoidHom.range ((toGodement F).app (op W)).hom) x
      = (cokernel.desc (toGodement F) (unitImageQuotientπ F)
          (toGodement_comp_unitImageQuotientπ F)).app (op W)
        ((cokernel.π (toGodement F)).app (op W) x) := by
    rw [← ConcreteCategory.comp_apply, hfacW]
    rfl
  have hqx0 : (cokernel.desc (toGodement F) (unitImageQuotientπ F)
      (toGodement_comp_unitImageQuotientπ F)).app (op W)
      ((cokernel.π (toGodement F)).app (op W) x) = 0 := by
    simp [hx]
  obtain ⟨t, rfl⟩ := (AddMonoidHom.mem_range).mp
    ((QuotientAddGroup.eq_zero_iff x).mp (h1.trans hqx0))
  exact ⟨t, rfl⟩

/-- **La séparéité du conoyau de l'unité — pas A de la Partie 91** : pour
`F` faisceau, une section `s` du conoyau `coker μ` (μ = `toGodement F`)
dont la restriction à chaque ouvert d'une famille couvrante `V` de `U` est
nulle, est nulle. Le conoyau n'est pas un faisceau en général — mais il
reste séparé, et c'est tout ce que le pas B (réduction de l'exactitude en
`C⁰F` au mono de l'unité du conoyau) exigera. La preuve transpose le
recollement de la Partie 84 au quotient :

1. **Relèvement** — `s` se relève en `σ : C⁰F(U)` (surjectivité
   sectionwise de la projection) ;
2. **Nullité locale remontée** — par naturalité, `σ` se projette sur `0`
   sur chaque `V i`, et la descente par le préfaisceau quotient
   `C⁰F/im μ` (propriété universelle du conoyau, section par section)
   fournit des relèvements locaux `t i : F(V i)` avec `μ (t i) = σ|` ;
3. **Compatibilité** — sur les intersections, les `t i` ont même image par
   `μ`, donc coïncident : injectivité de l'unité sur les faisceaux (P84) ;
4. **Recollement** — les `t i` se recollent en `t' : F(⨆ V)` par la
   condition de faisceau ; dans `C⁰F` (faisceau), `μ t'` recolle la même
   famille que `σ`, et l'unicité du recollement identifie les deux ;
5. **Conclusion** — `s = π σ = π (μ t') = 0` par la condition du conoyau.

[God58] Chap. II §4.1. -/
theorem eq_zero_of_locally_zero_cokernel_toGodement
    (F : X.Presheaf AddCommGrpCat.{u}) (hF : TopCat.Presheaf.IsSheaf F)
    {U : Opens X} {ι : Type u} (V : ι → Opens X) (iVU : ∀ i, V i ⟶ U)
    (hcover : ∀ x : X, x ∈ U → ∃ i, x ∈ V i)
    (s : (cokernel (toGodement F)).obj (op U))
    (hV : ∀ i, (cokernel (toGodement F)).map (iVU i).op s = 0) :
    s = 0 := by
  classical
  -- (1) Relèvement de `s` en une section de Godement `σ`.
  obtain ⟨σ, hσ⟩ := surjective_cokernel_app (toGodement F) U s
  -- (2) Nullité locale remontée au relèvement, puis relèvements locaux `t i`.
  have hrestrict : ∀ i : ι, (cokernel.π (toGodement F)).app (op (V i))
      ((godementPresheaf F).map (iVU i).op σ) = 0 := by
    intro i
    have hn : (cokernel.π (toGodement F)).app (op (V i))
        ((godementPresheaf F).map (iVU i).op σ)
        = (cokernel (toGodement F)).map (iVU i).op
          ((cokernel.π (toGodement F)).app (op U) σ) := by
      rw [← ConcreteCategory.comp_apply, NatTrans.naturality,
        ConcreteCategory.comp_apply]
    rw [hn, hσ, hV i]
  have hlift : ∀ i : ι, ∃ t : F.obj (op (V i)),
      (toGodement F).app (op (V i)) t
        = (godementPresheaf F).map (iVU i).op σ :=
    fun i => exists_of_cokernelπ_app_eq_zero F (V i)
      ((godementPresheaf F).map (iVU i).op σ) (hrestrict i)
  choose t ht using hlift
  -- (3) Compatibilité : les `t i` coïncident sur les intersections, par
  -- injectivité de `μ` sur les faisceaux (Partie 84).
  have hcomp : TopCat.Presheaf.IsCompatible F V t := by
    intro i j
    refine (godementUnit_injective_of_isSheaf F hF (V i ⊓ V j)).eq_iff.mp ?_
    have hLi : (toGodement F).app (op (V i ⊓ V j))
        (F.map (Opens.infLELeft (V i) (V j)).op (t i))
        = (godementPresheaf F).map
          ((Opens.infLELeft (V i) (V j) ≫ iVU i).op) σ := by
      rw [← ConcreteCategory.comp_apply, (toGodement F).naturality,
        ConcreteCategory.comp_apply, ht i, ← ConcreteCategory.comp_apply,
        ← Functor.map_comp, ← op_comp]
    have hRi : (toGodement F).app (op (V i ⊓ V j))
        (F.map (Opens.infLERight (V i) (V j)).op (t j))
        = (godementPresheaf F).map
          ((Opens.infLERight (V i) (V j) ≫ iVU j).op) σ := by
      rw [← ConcreteCategory.comp_apply, (toGodement F).naturality,
        ConcreteCategory.comp_apply, ht j, ← ConcreteCategory.comp_apply,
        ← Functor.map_comp, ← op_comp]
    rw [hLi, hRi, Subsingleton.elim (Opens.infLELeft (V i) (V j) ≫ iVU i)
      (Opens.infLERight (V i) (V j) ≫ iVU j)]
  -- (4) Recollement : les `t i` se recollent (`hF`), et dans `C⁰F` (faisceau)
  -- `μ t'` recolle la même famille que `σ` — unicité : `μ t' = σ` sur `iSup V`.
  have hsupU : (iSup V : Opens X) = U := by
    refine le_antisymm (iSup_le fun i => leOfHom (iVU i)) ?_
    intro x hxU
    obtain ⟨i, hxV⟩ := hcover x hxU
    exact Opens.mem_iSup.mpr ⟨i, hxV⟩
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing] at hF
  obtain ⟨t', ht'g, _⟩ := hF V t hcomp
  have hcompC : TopCat.Presheaf.IsCompatible (godementPresheaf F) V
      (fun i => (godementPresheaf F).map (iVU i).op σ) := by
    intro i j
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      Subsingleton.elim (Opens.infLELeft (V i) (V j) ≫ iVU i)
        (Opens.infLERight (V i) (V j) ≫ iVU j)]
  have hF0 := (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing
    (godementPresheaf F)).mp (isSheaf_godementPresheaf F)
  obtain ⟨g₀, _, huniq₀⟩ :=
    hF0 V (fun i => (godementPresheaf F).map (iVU i).op σ) hcompC
  have hglσ : TopCat.Presheaf.IsGluing (godementPresheaf F) V
      (fun i => (godementPresheaf F).map (iVU i).op σ)
      ((godementPresheaf F).map (homOfLE (le_of_eq hsupU)).op σ) := by
    intro i
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      Subsingleton.elim (Opens.leSupr V i ≫ homOfLE (le_of_eq hsupU)) (iVU i)]
  have hglμ : TopCat.Presheaf.IsGluing (godementPresheaf F) V
      (fun i => (godementPresheaf F).map (iVU i).op σ)
      ((toGodement F).app (op (iSup V)) t') := by
    intro i
    rw [← ConcreteCategory.comp_apply, ← (toGodement F).naturality,
      ConcreteCategory.comp_apply, ht'g i, ht i]
  have hμt' : (toGodement F).app (op (iSup V)) t'
      = (godementPresheaf F).map (homOfLE (le_of_eq hsupU)).op σ :=
    (huniq₀ _ hglμ).trans (huniq₀ _ hglσ).symm
  -- (5) `s = π σ = π (μ (t'|_U)) = 0` par la condition du conoyau.
  have hfinal : (toGodement F).app (op U)
      (F.map (homOfLE (le_of_eq hsupU.symm)).op t') = σ := by
    rw [← ConcreteCategory.comp_apply, (toGodement F).naturality,
      ConcreteCategory.comp_apply, hμt', ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← op_comp,
      Subsingleton.elim (homOfLE (le_of_eq hsupU.symm) ≫ homOfLE (le_of_eq hsupU))
        (𝟙 U),
      show (𝟙 U).op = 𝟙 (op U) from rfl]
    simp
  rw [← hσ, ← hfinal, ← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
    cokernel.condition, zero_app]
  rfl

/-! ## Le pas B de la Partie 91 : du séparé au mono, puis à l'exactitude en `C⁰F`

Le pas A (`eq_zero_of_locally_zero_cokernel_toGodement`) établissait que le
conoyau de l'unité reste **séparé** pour `F` faisceau. Cette section en livre
la conséquence — l'énoncé retiré du draft r65, frontière nommée depuis la
Partie 90, désormais **prouvé** :

1. `injective_toGodement_cokernel_of_isSheaf` puis
   `mono_toGodement_cokernel_of_isSheaf` : l'unité de Godement du conoyau,
   `toGodement (coker μ)`, est un **monomorphisme catégorique**. La preuve
   est la localité de la Partie 84 (`Presheaf.germ_eq` : des germes égaux en
   un point donnent un voisinage où les restrictions coïncident), dont la
   conclusion — la différence des deux sections est localement nulle dans le
   conoyau — est confiée au pas A au lieu du recollement : la séparéité du
   conoyau suffit, aucun gluing n'est requis.
2. `exact_toGodement_godementCanonicalDZero` : la suite `F → C⁰F → C¹F` est
   **exacte en `C⁰F`**. La différentielle est le pas canonique
   `d⁰ = cokernel.π μ ≫ toGodement (coker μ)` (P89) ; l'exactitude de
   `μ ≫ cokernel.π μ` est celle du conoyau (`ShortComplex.exact_cokernel`),
   et le transfert `ShortComplex.exact_iff_of_epi_of_isIso_of_mono` —
   τ₁ = 𝟙, τ₂ = 𝟙, τ₃ = `toGodement (coker μ)`, mono par 1 — la porte de
   `π` à `π ≫ τ₃ = d⁰`.

Restent l'**itération complète** de la réduction aux degrés supérieurs et
l'**acyclicité** `H^n(C⁰F) = 0` pour `n ≥ 1` ([God58] II.5).
-/

/-- **L'unité de Godement du conoyau est injective section par section —
pas B de la Partie 91 (montée 1/2)** : pour `F` faisceau, deux sections du
conoyau `coker μ` dont les germes-images par l'unité `toGodement (coker μ)`
coïncident, sont égales. La preuve transpose la localité de la Partie 84 :
des germes égaux en chaque point (`Presheaf.germ_eq`) fournissent un
voisinage par point où les restrictions des deux sections coïncident ; la
différence, localement nulle dans le conoyau, est nulle par le pas A
(`eq_zero_of_locally_zero_cokernel_toGodement`) — la séparéité du conoyau
tient exactement le rôle que le recollement jouait pour l'injectivité de
l'unité elle-même. -/
theorem injective_toGodement_cokernel_of_isSheaf (F : X.Presheaf AddCommGrpCat.{u})
    (hF : TopCat.Presheaf.IsSheaf F) (U : Opens X) :
    Function.Injective ((toGodement (cokernel (toGodement F))).app (op U)) := by
  intro s t hst
  have hgerm : ∀ z : ↥U, (cokernel (toGodement F)).germ U (z : X) z.2 s
      = (cokernel (toGodement F)).germ U (z : X) z.2 t :=
    fun z => congrFun hst ⟨(z : X), z.2⟩
  have hloc : ∀ z : ↥U, ∃ N : Opens X, (z : X) ∈ N ∧ ∃ iNU : N ⟶ U,
      (cokernel (toGodement F)).map iNU.op s
        = (cokernel (toGodement F)).map iNU.op t := by
    intro z
    obtain ⟨N, hxN, iU', iN', heq⟩ := (cokernel (toGodement F)).germ_eq
      (z : X) z.2 z.2 s t (hgerm z)
    refine ⟨N, hxN, iU', ?_⟩
    rw [Subsingleton.elim iN' iU'] at heq
    exact heq
  choose N hN iNU hagree using hloc
  have hzero : ∀ z : ↥U,
      (cokernel (toGodement F)).map (iNU z).op (s - t) = 0 := by
    intro z
    rw [map_sub, sub_eq_zero]
    exact hagree z
  have hcover : ∀ x : X, x ∈ U → ∃ z : ↥U, x ∈ N z :=
    fun x hxU => ⟨⟨x, hxU⟩, hN ⟨x, hxU⟩⟩
  have hst0 : s - t = 0 :=
    eq_zero_of_locally_zero_cokernel_toGodement F hF N iNU hcover _ hzero
  exact sub_eq_zero.mp hst0

/-- **L'unité de Godement du conoyau est un monomorphisme catégorique —
pas B de la Partie 91 (montée 2/2)** : la montée catégorique de
l'injectivité section par section ci-dessus, par `NatTrans.mono_iff_mono_app`
puis `AddCommGrpCat.mono_iff_injective` — le même geste que
`mono_toGodement_of_isSheaf` (P90) pour l'unité elle-même. -/
theorem mono_toGodement_cokernel_of_isSheaf (F : X.Presheaf AddCommGrpCat.{u})
    (hF : TopCat.Presheaf.IsSheaf F) :
    Mono (toGodement (cokernel (toGodement F))) := by
  rw [NatTrans.mono_iff_mono_app]
  intro W
  exact (AddCommGrpCat.mono_iff_injective _).mpr
    (injective_toGodement_cokernel_of_isSheaf F hF W.unop)

/-- **La réduction de l'exactitude en `C⁰F` — l'énoncé retiré du draft r65,
prouvé (pas B de la Partie 91)** : pour `F` faisceau, la suite
`F → C⁰F → C¹F` est exacte en `C⁰F`. La preuve est un transfert de complexes
courts : l'exactitude de `μ ≫ cokernel.π μ` est celle du conoyau
(`ShortComplex.exact_cokernel`), et le morphisme de complexes
τ = (𝟙, 𝟙, `toGodement (coker μ)`) — dont la composante τ₃ est mono par
`mono_toGodement_cokernel_of_isSheaf` — porte cette exactitude de `π` à
`π ≫ τ₃ = d⁰` par `ShortComplex.exact_iff_of_epi_of_isIso_of_mono`
([God58] II §4.1). -/
theorem exact_toGodement_godementCanonicalDZero (F : X.Presheaf AddCommGrpCat.{u})
    (hF : TopCat.Presheaf.IsSheaf F) :
    (ShortComplex.mk (toGodement F) (godementCanonicalDZero F)
      (toGodement_comp_godementCanonicalDZero F)).Exact := by
  have hmono : Mono (toGodement (cokernel (toGodement F))) :=
    mono_toGodement_cokernel_of_isSheaf F hF
  have key : (ShortComplex.mk (toGodement F) (cokernel.π (toGodement F))
        (cokernel.condition (toGodement F))).Exact ↔
      (ShortComplex.mk (toGodement F) (godementCanonicalDZero F)
        (toGodement_comp_godementCanonicalDZero F)).Exact :=
    ShortComplex.exact_iff_of_epi_of_isIso_of_mono
      { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := toGodement (cokernel (toGodement F)),
        comm₁₂ := by simp, comm₂₃ := by simp [godementCanonicalDZero, godementStep] }
  exact key.mp (ShortComplex.exact_cokernel (toGodement F))

end Grothendieck
