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


## Correspondance Stacks (groupe « l'exactitude » — #28788)

Lecture de `AxiomMath/Stacks` sur l'**arborescence locale**
`StacksFrontier/Topology/Sheaves/` (clone sparse du dossier entier). Le
critère de classement est le **contenu**, jamais le seul nom : une recherche
par identifiant qui ne renvoie rien n'établit pas une absence, elle établit
qu'un énoncé n'est pas *nommé* ainsi. Un verdict « absent » signifie donc :
aucun contenu équivalent dans l'ensemble de `Topology/Sheaves/`, à aucun
endroit — les sept énoncés de la colonne « absent » ci-dessous ont été
relu dans le **contenu** des fichiers qui les portent, pas comptés.

Les **23 énoncés publics** du module sont classés un par un ; les sept
helpers `private` (`zero_app`, `toGodement_range_le_comap`,
`unitImageQuotientPresheaf`, `unitImageQuotientπ`,
`toGodement_comp_unitImageQuotientπ`, `surjective_cokernel_app`,
`exists_of_cokernelπ_app_eq_zero`) sont des briques d'implémentation, sans
contrepartie à classer chez Stacks.

| Énoncé | Classe | Référent Stacks | Ce que notre version ajoute |
|---|---|---|---|
| `godementCanonicalDOne` | partiel | `Cohomology/GodementResolution/Basic.lean:466` `godementComplex` ; `:482` `godementComplexEvalIso` | la récurrence `d^{n+1} := godementStep d^n` entre les degrés, sur le site des ouverts |
| `godementCanonicalDZero_comp_godementCanonicalDOne` | partiel | `Basic.lean:466` `godementComplex` (la null-composition est portée par le type `CochainComplex`) | la null-composition **prouvée** à chaque degré |
| `mono_toGodement_of_isSheaf` | partiel | `Basic.lean:475` `godementAugmentation` ; `StalkHomotopy.lean:558` `quasiIso_godementAugmentation` | le **mono** de l'unité, en catégories de préfaisceaux (Stacks : quasi-isomorphisme de complexes) |
| `eq_zero_of_locally_zero_cokernel_toGodement` | partiel | `Stalk/Separated.lean:78` `IsSeparated'` ; `:86` `isSeparated'_iff` ; `Sheafify/Separated.lean:71` `IsSeparated` ; `:88` `toSheafify_app_eq_iff_germ_eq` | le critère de séparéité appliqué au **conoyau** de l'unité, qui n'est pas un faisceau |
| `injective_toGodement_cokernel_of_isSheaf` | partiel | `Stalk/Separated.lean:86` `isSeparated'_iff` (007A) | l'injectivité de l'unité du conoyau, par **localité** puis séparéité — sans recollement |
| `mono_toGodement_cokernel_of_isSheaf` | partiel | `Stalk/Separated.lean:86` `isSeparated'_iff` | la **montée catégorique** (mono), que Stacks ne fait pas |
| `exact_toGodement_godementCanonicalDZero` | **couvert** | `StalkHomotopy.lean:558` `quasiIso_godementAugmentation` (0FKS clause (3)) | l'exactitude au **degré 0**, en complexe court de préfaisceaux |
| `epi_stalkFunctor_map_of_epi` | partiel | `Modules/Exactness.lean:52` `stalkAddCommGroupFunctor` ; `:77` `exact_iff_stalkShortComplex_exact` ; `Sheaf/Abelian.lean:75` `shortExact_of_stalk` | l'isolat « le foncteur tige préserve les épis », hors d'un énoncé d'exactitude |
| `stalkEvalLeg` | absent | — (le germe de Stacks est un quotient : `Basis/Germs.lean:132` `Stalk`, `:136` `germ`) | l'évaluation d'une section de Godement **en un point**, possible parce que la section est une fonction |
| `stalkEvalCocone` | absent | — (idem) | le cône sur le diagramme des voisinages |
| `stalkEval` | partiel | `StalkHomotopy.lean:520` `homotopyEquivalences_stalk_godementAugmentation` ; `:95` `godementStalkPullbackIso` | une **application** (l'évaluation), dont la section fera la rétraction |
| `germ_stalkEval` | absent | — (le pendant du contenu : `Basis/Germs.lean:124` `StalkDatum.Rel`, `:132`, `:136`) | la propriété universelle de la colimite, déployée |
| `toGodement_app_stalkEvalLeg` | absent | — (le pendant le plus proche : `Basic.lean:475` `godementAugmentation`) | la lisibilité de l'évaluation avec l'unité |
| `toGodement_stalkEval` | partiel | `StalkHomotopy.lean:520` `homotopyEquivalences_stalk_godementAugmentation` ; `:558` `quasiIso_godementAugmentation` | un **scindage** (rétraction `ev_x₀`), inconditionnel |
| `stalkEval_stalkFunctor_map_toGodement_apply` | absent | — (le pendant du scindage : `StalkHomotopy.lean:520`) | la forme appliquée du scindage |
| `mono_stalkFunctor_map_toGodement` | partiel | `Sheaf/Abelian.lean:88` (usage de `TopCat.Presheaf.mono_iff_stalk_mono`) ; `:75` | l'instance « l'unité de Godement est mono **en tige** », inconditionnelle |
| `stalkFunctor_preservesMono` | partiel | `Sheaf/Abelian.lean:88` | l'instance, que Stacks utilise sans l'énoncer |
| `stalkFunctor_preservesHomology` | partiel | `Modules/Exactness.lean:77` `exact_iff_stalkShortComplex_exact` (01AG) | la forme **locale** (préservation par un foncteur) |
| `stalkFunctor_preservesFiniteLimits` | absent | — (aucune mention d'AB5 ni de `PreservesFiniteLimits` **pour le foncteur tige** dans `Topology/Sheaves/`) | l'axiome AB5 explicitement, dont `Modules/Exactness.lean:77` n'est qu'une conséquence |
| `stalkFunctor_map_exact` | **couvert** | `Modules/Exactness.lean:77` `exact_iff_stalkShortComplex_exact` (01AG) ; `Sheaf/Abelian.lean:75` `shortExact_of_stalk` | la conservation de l'exactitude **sans hypothèse de faisceau**, sur des préfaisceaux de groupes abéliens |
| `stalk_exact_godementStep` | partiel | `StalkHomotopy.lean:558` `quasiIso_godementAugmentation` ; `:127` `quasiIso_of_forall_stalk_quasiIso_nat` | la version **générique** (toute flèche `f`), qui rend la récurrence entre degrés uniforme |
| `stalk_exact_toGodement_godementCanonicalDZero` | **couvert** | `StalkHomotopy.lean:558` `quasiIso_godementAugmentation` (0FKS clause (3)) | le degré 0 **inconditionnel** (aucune hypothèse de faisceau) |
| `stalk_exact_godementCanonicalDZero_godementCanonicalDOne` | **couvert** | `StalkHomotopy.lean:558` `quasiIso_godementAugmentation` | le **degré 1** isolé, la récurrence rendue visible |

**Décompte** : 4 couverts, 13 partiels, 6 absents — sur 23 énoncés publics.

**Écarts de cadre, énoncés.** Stacks travaille en **faisceaux de modules** sur
espace annelé (`SheafOfModules`, topologie de Grothendieck) et en
`TopCat.Sheaf` ; le lac travaille en **préfaisceaux de groupes abéliens** sur
la topologie des ouverts. Les deux « complexes de Godement » ne sont pas le
même objet : chez Stacks, le terme de degré `n` est l'itérée `(f_* f^*)^{n+1}`
le long de `X_discret ⟶ X` (`Basic.lean:482`), chez nous le terme est construit
par un pas canonique `godementStep` sur le site des ouverts. Le verdict dit
« couvert / partiel / absent » **avec cette ligne** ; il ne dit pas
« équivalent importable » — l'import de `StacksFrontier` reste hors périmètre.
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

**Renvoi Stacks** — *partiel* : `Cohomology/GodementResolution/Basic.lean:466`
`godementComplex` (le complexe de Godement de 0FKS) et `:482`
`godementComplexEvalIso` (le terme de degré `n` est l'itérée `(f_* f^*)^{n+1} F`).
Stacks pose le terme de chaque degré d'un seul trait ; notre version pose une
**récurrence** entre les degrés (`d^{n+1} := godementStep d^n`) sur le site des
ouverts, en préfaisceaux de groupes abéliens, et identifie `d¹` au pas
canonique appliqué à `d⁰`. L'écart de cadre est écrit dans l'en-tête du
module.
précédente ([God58] II §4.1). -/
noncomputable def godementCanonicalDOne (F : X.Presheaf AddCommGrpCat.{u}) :
    godementPresheaf (cokernel (toGodement F)) ⟶
    godementPresheaf (cokernel (godementCanonicalDZero F)) :=
  godementStep (godementCanonicalDZero F)

/-- **La null-composition en degré 1** : `d⁰ ≫ d¹ = 0`. Instance immédiate de
`comp_godementStep_zero` (P89) — la résolution canonique est un complexe au-delà
du degré 0, et le restera à chaque degré suivant par le même argument : chaque
différentielle composée avec son pas canonique s'annule par la condition

**Renvoi Stacks** — *partiel* : chez Stacks la null-composition est **portée par
le type** : `godementComplex` (`Cohomology/GodementResolution/Basic.lean:466`)
est un `CochainComplex`, dont la null-composition fait partie de la structure.
Stacks n'énonce donc aucun lemme de null-composition ; notre version la
**prouve** à chaque degré, pour le pas `d^{n+1} := godementStep d^n`, par
l'instance de `comp_godementStep_zero`.
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

**Renvoi Stacks** — *partiel* : la même flèche est chez Stacks
l'augmentation `F[0] ⟶ godementComplex` (`Cohomology/GodementResolution/Basic.lean:475`
`godementAugmentation`), et Stacks en dit **plus** sur elle, mais dans un autre
langage : `Cohomology/GodementResolution/StalkHomotopy.lean:558`
`quasiIso_godementAugmentation` (clause (3) de 0FKS) fait de l'augmentation un
**quasi-isomorphisme** de complexes de cochaînes. Le **monomorphisme** de
l'unité, lui, n'est pas énoncé chez Stacks ; notre version l'énonce en
catégories de préfaisceaux, comme mono — et non comme quasi-isomorphisme.
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


**Renvoi Stacks** — *partiel* : le **critère** de séparéité est chez Stacks
`Stalk/Separated.lean:78` `IsSeparated'` et `:86` `isSeparated'_iff` (007A),
puis, sous forme de recollement, `Sheafify/Separated.lean:71` `IsSeparated` et
`:88` `toSheafify_app_eq_iff_germ_eq` (« deux sections ont la même image par
`toSheafify` si et seulement si leurs germes coïncident »). Stacks énonce ce
critère pour un **faisceau** ; notre énoncé l'applique au **conoyau** de
l'unité, qui n'est pas un faisceau — d'où l'écart : Stacks ne peut pas
l'énoncer dans ce cadre, et le passage du recollement à la séparéité est chez
nous un lemme à part entière.
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

**Renvoi Stacks** — *partiel* : pendant de `Stalk/Separated.lean:86`
`isSeparated'_iff` (007A), Stacks énonce l'injectivité de la famille des
germes pour un **faisceau**. Notre version l'énonce pour l'unité du conoyau
`toGodement (coker μ)`, par **localité** (deux germes égaux en un point
donnent un voisinage) puis **séparéité du conoyau** (pas A ci-dessus) — le
recollement des sections, que Stacks utilise, n'est pas requis ici.
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

**Renvoi Stacks** — *partiel* : c'est la **montée catégorique** du renvoi
précédent (`Stalk/Separated.lean:86` `isSeparated'_iff`), que Stacks ne fait
pas : leur formulation est l'équivalence **pointwise** (deux sections dont les
germes coïncident sont égales), la nôtre est un morphisme de catégories
(`NatTrans.mono_iff_mono_app` puis `AddCommGrpCat.mono_iff_injective`). Le
contenu est chez Stacks ; la formulation mono ne l'est pas.
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

**Renvoi Stacks** — *couvert* : `Cohomology/GodementResolution/StalkHomotopy.lean:558`
`quasiIso_godementAugmentation`, clause (3) de 0FKS — « l'exactitude de
`0 → F → f_* f^* F → f_* f^* f_* f^* F → ⋯` » (SGA 4 XVII 4.2.3 (ii)). Stacks
établit donc l'exactitude du complexe **augmenté de l'unité de Godement**, ce
que notre énoncé établit au **degré 0**. Ce que notre version ajoute : la
formulation en **complexe court** de préfaisceaux de groupes abéliens (le
transfert `ShortComplex.exact_iff_of_epi_of_isIso_of_mono`, τ₁ = τ₂ = 𝟙,
τ₃ = l'unité du conoyau, mono par le pas B), là où Stacks détecte l'exactitude
sur les tiges.
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

/-! ## La Partie 93(a) : les ingrédients locaux du transport vers les tiges

La Partie 93(a) (exactitude du complexe canonique **en les tiges**,
ingrédient de l'isomorphisme d'homologie de la Partie 93(b)) demande de
transporter en les tiges les deux faces de l'exactitude du niveau
préfaisceaux : l'épi de la projection de conoyau et le mono de l'unité.
Cette section en livre les deux ingrédients locaux, valables pour **tout
préfaisceau** — aucune hypothèse de faisceau :

1. `epi_stalkFunctor_map_of_epi` : le foncteur tige préserve les
   épimorphismes — gratuit par l'adjonction tige ⊣ gratte-ciel
   (`skyscraperPresheafStalkAdjunction`, instance
   `Presheaf.stalkFunctor.IsLeftAdjoint`), un adjoint à gauche préservant
   les épis (`preservesEpimorphisms_of_isLeftAdjoint`).
2. `stalkEval` puis `toGodement_stalkEval` : **l'unité de Godement est un
   monomorphisme scindé en chaque tige**. La rétraction est l'évaluation
   `ev_x₀ : (C⁰F)ₓ₀ ⟶ Fₓ₀`, `σ ↦ σ(x₀)` — bien définie car une section de
   Godement est une fonction et les restrictions (`godementMap`) ne font
   que la restreindre : la composante en `x₀` ne dépend pas du voisinage
   choisi. C'est l'ingrédient qui **remplace l'argument de
   faisceification** : pour transporter l'exactitude vers les tiges, on
   n'a pas besoin que `μ` soit mono en préfaisceaux (cela exigerait `F`
   séparé — Partie 91), seulement que chaque `μₓ₀` le soit — et le
   scindage par `ev_x₀` l'établit pour tout préfaisceau.

**Frontière nommée** : reste la brique de transport elle-même — le foncteur
tige, composé syntaxique `whiskering ⋙ colim` sur la catégorie filtrante
des voisinages (`Presheaf.stalkFunctor`), préserve aussi les limites finies
par exactitude des colimites filtrantes de `AddCommGrpCat` (AB5,
`Mathlib.Algebra.Category.Grp.AB`). Elle est reportée à la livraison
suivante de la Partie 93(a). -/

/-- **Le foncteur tige préserve les épimorphismes** : le foncteur tige est
un adjoint à gauche (adjonction tige ⊣ gratte-ciel de
`skyscraperPresheafStalkAdjunction`), donc préserve les épimorphismes.
Appliqué à la projection `cokernel.π f` — épimorphe par construction —
ceci fournit l'ingrédient « épi » du transport d'exactitude vers les

**Renvoi Stacks** — *partiel* : le foncteur tige est chez Stacks
`Modules/Exactness.lean:52` `stalkAddCommGroupFunctor`, et la **combinaison**
est énoncée : `Modules/Exactness.lean:77` `exact_iff_stalkShortComplex_exact`
(01AG) et `Sheaf/Abelian.lean:75` `shortExact_of_stalk`. Stacks énonce donc
la conservation des épis **à l'intérieur** d'un énoncé d'exactitude ; l'isolat
« le foncteur tige préserve les épimorphismes » n'y est pas, et notre version
se place dans une autre catégorie (préfaisceaux de groupes abéliens, non
faisceaux de modules).
tiges : `(coker f)ₓ₀` reçoit surjectivement `(C⁰...)ₓ₀`. -/
theorem epi_stalkFunctor_map_of_epi {A B : X.Presheaf AddCommGrpCat.{u}}
    (f : A ⟶ B) [Epi f] (x₀ : X) :
    Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map f) :=
  inferInstance

/-- **La jambe d'évaluation en `x₀`** : pour `V` un ouvert voisinage de
`x₀` (objet de `(OpenNhds x₀)ᵒᵖ`), l'application « évaluer la section de
Godement en `x₀` » : une section de `C⁰F` sur `V` est une fonction
`σ : ∀ y ∈ V, Fₓ`, on prend sa valeur en `x₀`. Morphisme de groupes

**Renvoi Stacks** — *absent* : aucun pendant dans
`StacksFrontier/Topology/Sheaves/`. Stacks n'a pas de mécanisme d'**évaluation
d'une section en un point** : son germe est un **quotient** par la relation
d'équivalence des germes (`Basis/Germs.lean:132` `Stalk`, `:136` `germ`), non
une colimite dotée d'une application d'évaluation. La construction n'est pas
transposable parce que son origine est **propre au lac** : une section de
`C⁰F` est une *fonction* `σ : ∀ y ∈ V, Fₓ`, et l'évaluation est la
restriction de cette fonction à `x₀`. Le plus proche chez Stacks :
`Cohomology/GodementResolution/StalkHomotopy.lean:95`
`godementStalkPullbackIso` (le foncteur tige factorise par `f^*` au point).
abstraits : la structure de `C⁰F(V)` est ponctuelle. -/
noncomputable def stalkEvalLeg (F : X.Presheaf AddCommGrpCat.{u}) (x₀ : X)
    (V : (OpenNhds x₀)ᵒᵖ) :
    (godementPresheaf F).obj ((OpenNhds.inclusion x₀).op.obj V) ⟶ F.stalk x₀ :=
  AddCommGrpCat.ofHom
    { toFun := fun s => s ⟨x₀, V.unop.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

/-- **Le cocone d'évaluation** : les jambes `stalkEvalLeg` forment un
cocone sur le diagramme des voisinages `(OpenNhds x₀)ᵒᵖ ⥤ AddCommGrpCat` —
c'est la bien-définition de l'évaluation : restreindre la section puis
évaluer en `x₀`, ou l'évaluer directement, donne le même germe, car

**Renvoi Stacks** — *absent* : idem `stalkEvalLeg`. Le cône sur le
diagramme des voisinages, dont l'universalité est la condition de
bien-définition de l'évaluation, n'a pas de pendant chez Stacks : le germe y
est un quotient (`Basis/Germs.lean:132`, `:136`), non une colimite.
`godementMap` ne fait que restreindre la fonction. -/
noncomputable def stalkEvalCocone (F : X.Presheaf AddCommGrpCat.{u}) (x₀ : X) :
    Cocone ((OpenNhds.inclusion x₀).op ⋙ godementPresheaf F) where
  pt := F.stalk x₀
  ι :=
    { app := fun V => stalkEvalLeg F x₀ V
      naturality := by
        intro V W f
        ext s
        rfl }

/-- **L'évaluation `ev_x₀ : (C⁰F)ₓ₀ ⟶ Fₓ₀`** : le morphisme de tiges
induit par le cocone d'évaluation — à un germe de section de Godement
(représentée par `σ` sur un voisinage `V ∋ x₀`), on associe sa valeur
`σ(x₀)`. La condition de cocone ci-dessus est exactement la
bien-définition : la valeur en `x₀` ne dépend pas du représentant. C'est
la rétraction qui scinde l'unité de Godement en chaque tige.

Le domaine est déclaré en forme **dépliée** (`(stalkFunctor x₀).obj (C⁰F)`
plutôt que `(C⁰F).stalk x₀`) : les deux sont définitionnellement égales,
mais la forme dépliée est celle du codomaine de `stalkFunctor.map` —
elle rend les compositions `map ≫ ev` correctes à la transparence des

**Renvoi Stacks** — *partiel* : Stacks dispose d'une **équivalence** entre
le stalk de `F` et le terme de degré 0 du complexe de Godement —
`Cohomology/GodementResolution/StalkHomotopy.lean:520`
`homotopyEquivalences_stalk_godementAugmentation`, et `:95`
`godementStalkPullbackIso` pour le foncteur tige lui-même. Notre version
construit une **application** (l'évaluation par universalité de la colimite),
dont la section fera la **rétraction** `ev_x₀` : le scindage, lui, n'est pas
énoncé chez Stacks.
instances, que la réécriture exige. -/
noncomputable def stalkEval (F : X.Presheaf AddCommGrpCat.{u}) (x₀ : X) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).obj (godementPresheaf F) ⟶
      F.stalk x₀ :=
  colimit.desc _ (stalkEvalCocone F x₀)

/-- **L'évaluation d'un germe est la valeur en `x₀`** : sur un germe
représenté par une section de Godement `σ` sur `U ∋ x₀`, l'évaluation
donne `σ(x₀)` — la propriété universelle du cocone (`colimit.ι_desc`),

**Renvoi Stacks** — *absent* : lemme de la construction de l'évaluation
(la propriété universelle de la colimite, déployée en forme appliquée) ; aucun
pendant, Stacks n'ayant pas d'évaluation en un point (`Basis/Germs.lean:132`,
`:136`). Le pendant le plus proche du **contenu** — l'indépendance du germe
quant au représentant — est chez Stacks la définition même du germe comme
quotient (`Basis/Germs.lean:124` `StalkDatum.Rel`, `:132` `Stalk`, `:136`
`germ`).
dépliée en forme appliquée par l'attribut `elementwise`. -/
@[reassoc, elementwise nosimp]
theorem germ_stalkEval (F : X.Presheaf AddCommGrpCat.{u}) (x₀ : X)
    (U : Opens X) (hx : x₀ ∈ U) :
    (godementPresheaf F).germ U x₀ hx ≫ stalkEval F x₀ =
      stalkEvalLeg F x₀ (op ⟨U, hx⟩) :=
  colimit.ι_desc _ _

/-- **Le lemme composant du scindage** : composer l'unité avec la jambe
d'évaluation redonne le germe — sur `s ∈ F(U)`, prendre la section de
Godement de `s` puis l'évaluer en `x₀` rend le germe de `s` en `x₀`.
Les deux membres sont la même fonction de `F(U)` : l'égalité est
définitionnelle (`ext` puis `rfl`), comme la naturalité du cocone

**Renvoi Stacks** — *absent* : composant du scindage, sans pendant (voir
`stalkEvalLeg`). C'est la legende qui relie l'unité de Godement à
l'évaluation ; chez Stacks, le pendant le plus proche est la naturalité de
l'augmentation `F[0] ⟶ godementComplex`
(`Cohomology/GodementResolution/Basic.lean:475`), qui ne dit rien de
l'évaluation.
d'évaluation. -/
theorem toGodement_app_stalkEvalLeg (F : X.Presheaf AddCommGrpCat.{u}) (x₀ : X)
    (U : Opens X) (hx : x₀ ∈ U) :
    (toGodement F).app (op U) ≫ stalkEvalLeg F x₀ (op ⟨U, hx⟩) = F.germ U x₀ hx := by
  ext s
  rfl

/-- **L'unité de Godement est scindée en chaque tige** — le cœur local de
la Partie 93(a) : pour **tout préfaisceau** `F` (aucune hypothèse de
faisceau), le morphisme de tiges `Fₓ₀ ⟶ (C⁰F)ₓ₀` induit par l'unité admet
`ev_x₀` pour rétraction : prendre les germes de `s` puis évaluer en `x₀`
redonne le germe de `s` en `x₀`. La preuve reste au niveau des morphismes
— l'idiome `stalk_hom_ext` de Mathlib : deux flèches sortant d'une tige
sont égales dès que leurs composées avec chaque germe le sont. Chaque
jambe se réduit par `stalkFunctor_map_germ` (la tige d'un morphisme
envoie germe sur germe) puis `germ_stalkEval` (propriété universelle de
la colimite) au lemme composant ci-dessus. On évite ainsi les formes
appliquées, dont l'unification entre formes repliée (`F.stalk x₀`) et
dépliée (`(stalkFunctor x₀).obj F`) échoue à la transparence des
instances. La chaîne est un `calc` dont chaque étape est un **terme**
(`assoc`, `congrArg` sur les lemmes de Mathlib), élaboré à transparence

**Renvoi Stacks** — *partiel* : Stacks établit sur les tiges un fait
**plus fort en genre** et **différent en nature** :
`Cohomology/GodementResolution/StalkHomotopy.lean:520`
`homotopyEquivalences_stalk_godementAugmentation` donne l'équivalence
d'homotopie entre le stalk de `F` et celui du terme de degré 0, d'où
`:558` `quasiIso_godementAugmentation`. Notre version construit un
**scindage** — une rétraction `ev_x₀` de l'unité de tiges — que Stacks
n'énonce pas, et qui est inconditionnel (aucune hypothèse de faisceau).
par défaut, où formes repliée et dépliée s'unifient librement. -/
theorem toGodement_stalkEval (F : X.Presheaf AddCommGrpCat.{u}) (x₀ : X) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map (toGodement F) ≫
      stalkEval F x₀ = 𝟙 (F.stalk x₀) := by
  apply TopCat.Presheaf.stalk_hom_ext F
  intro U hx
  rw [Category.comp_id]
  calc F.germ U x₀ hx ≫ ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map
        (toGodement F) ≫ stalkEval F x₀) =
      (F.germ U x₀ hx ≫ (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map
        (toGodement F)) ≫ stalkEval F x₀ :=
        (Category.assoc _ _ _).symm
    _ = ((toGodement F).app (op U) ≫ (godementPresheaf F).germ U x₀ hx) ≫
        stalkEval F x₀ :=
        congrArg (· ≫ stalkEval F x₀)
          (Presheaf.stalkFunctor_map_germ U x₀ hx (toGodement F))
    _ = (toGodement F).app (op U) ≫
        ((godementPresheaf F).germ U x₀ hx ≫ stalkEval F x₀) :=
        Category.assoc _ _ _
    _ = (toGodement F).app (op U) ≫ stalkEvalLeg F x₀ (op ⟨U, hx⟩) :=
        congrArg ((toGodement F).app (op U) ≫ ·) (germ_stalkEval F x₀ U hx)
    _ = F.germ U x₀ hx := toGodement_app_stalkEvalLeg F x₀ U hx

/-- Forme appliquée du scindage : l'évaluation est inverse à gauche du
morphisme de tiges de l'unité. La preuve applique l'égalité hom-niveau
ci-dessus à l'élément `t` (`congrArg` sur `ConcreteCategory.hom`),
élaborée à transparence par défaut, où les formes repliée et dépliée du
domaine de `stalkEval` sont interchangeables ; les deux réductions

**Renvoi Stacks** — *absent* : forme appliquée du renvoi précédent (le
pendant du scindage reste
`Cohomology/GodementResolution/StalkHomotopy.lean:520`
`homotopyEquivalences_stalk_godementAugmentation`, qui n'est pas une
rétraction).
restantes (`comp_apply`, `id_apply`) sont définitionnelles. -/
theorem stalkEval_stalkFunctor_map_toGodement_apply
    (F : X.Presheaf AddCommGrpCat.{u}) (x₀ : X)
    (t : ToType ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).obj F)) :
    stalkEval F x₀
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map (toGodement F) t) = t := by
  have key : (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map (toGodement F) ≫
        stalkEval F x₀)) t = (ConcreteCategory.hom (𝟙 (F.stalk x₀))) t :=
    congrArg (fun g : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).obj F ⟶
      F.stalk x₀ => ConcreteCategory.hom g t) (toGodement_stalkEval F x₀)
  exact key

/-- **Le morphisme de tiges de l'unité est un monomorphisme, pour tout
préfaisceau** : un morphisme scindé à gauche est injectif — la rétraction
est `stalkEval`. À comparer avec `mono_toGodement_of_isSheaf` (Partie 90) :
au niveau préfaisceaux, le mono de l'unité exige `F` faisceau ; au niveau
des tiges, il est **inconditionnel** — c'est ce qui permet au transport
d'exactitude de la Partie 93(a) de s'affranchir de toute hypothèse de

**Renvoi Stacks** — *partiel* : le **contenu** — « le mono se détecte sur les
tiges » — est chez Stacks, `Sheaf/Abelian.lean:88` (usage de
`TopCat.Presheaf.mono_iff_stalk_mono` dans `shortExact_of_stalk`, `:75`) ;
l'instance « l'unité de Godement est mono **en tige** » n'y est pas, et
Stacks travaille en faisceaux de modules sur espace annelé
(`Modules/Exactness.lean:52`), non en préfaisceaux de groupes abéliens sur le
site des ouverts. C'est cette instance qui autorise le transport d'exactitude
sans hypothèse de séparéité.
séparéité sur les conoyaux intermédiaires. -/
theorem mono_stalkFunctor_map_toGodement (F : X.Presheaf AddCommGrpCat.{u})
    (x₀ : X) :
    Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map (toGodement F)) := by
  rw [AddCommGrpCat.mono_iff_injective]
  intro a b h
  have h2 := congrArg (stalkEval F x₀) h
  rw [stalkEval_stalkFunctor_map_toGodement_apply,
    stalkEval_stalkFunctor_map_toGodement_apply] at h2
  exact h2

/-! ### Partie 93(a), brique (i) — AB5 : le foncteur tige préserve les limites finies

Face « transport d'exactitude » du re-scopage de la Partie 93. Le foncteur
tige est un adjoint à gauche (`skyscraperPresheafStalkAdjunction`) : il
préserve les colimites — épimorphismes (`epi_stalkFunctor_map_of_epi`
ci-dessus) et conoyaux. La préservation des **limites finies** n'est pas
gratuite : c'est l'axiome AB5 — les colimites filtrantes de groupes
abéliens sont exactes. Conceptuellement, `Presheaf.stalkFunctor` est le
composé `whiskering ⋙ colim` sur la catégorie des voisinages (filtrante :
`OpenNhds x₀` est un demi-treillis pour l'intersection, donc cofiltrante,
donc d'opposée filtrante), et `colim` préserve les limites finies dans
`AddCommGrpCat` (`Mathlib.Algebra.Category.Grp.AB`). La voie empruntée
suit Mathlib (`TopCat.Sheaf` dans `Mathlib.Topology.Sheaves.Abelian`) : la
face concrète d'AB5 — un morphisme de préfaisceaux injectif composante par
composante reste injectif sur les tiges
(`Presheaf.stalkFunctor_map_injective_of_app_injective`) — donne la
préservation des monomorphismes, et additif + colimites + monos ⇒
préservation de l'homologie ⇒ des limites finies. -/

/-- Le foncteur tige préserve les monomorphismes : un mono de préfaisceaux
de groupes abéliens est injectif composante par composante, et cette

**Renvoi Stacks** — *partiel* : Stacks utilise la même détection que nous
(`Sheaf/Abelian.lean:88`, à l'intérieur de `shortExact_of_stalk`), mais
n'énonce pas l'instance « le foncteur tige préserve les monomorphismes ».
injectivité passe aux tiges — la face concrète d'AB5. -/
instance stalkFunctor_preservesMono (x₀ : X) :
    Functor.PreservesMonomorphisms
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀) := by
  constructor
  intro F G f hf
  refine (AddCommGrpCat.mono_iff_injective _).mpr ?_
  refine TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective
    (fun U => ?_) x₀
  exact (AddCommGrpCat.mono_iff_injective (f.app (op U))).mp
    ((NatTrans.mono_iff_mono_app f).mp hf (op U))

/-- **AB5 pour les tiges, forme homologie** : le foncteur tige préserve
l'homologie — un mono de préfaisceaux reste mono sur les tiges (face
concrète d'AB5), un épi reste épi (adjonction tige ⊣ gratte-ciel), et la
préservation des conoyaux vient de celle des colimites (adjoint à

**Renvoi Stacks** — *partiel* : l'énoncé voisin est chez Stacks
`Modules/Exactness.lean:77` `exact_iff_stalkShortComplex_exact` (01AG) et
`Sheaf/Abelian.lean:75` `shortExact_of_stalk` — l'exactitude d'un court
complexe se détecte sur les tiges. Notre instance en est la forme **locale**
(la préservation de l'homologie par un foncteur) ; Stacks énonce le fait
global, non l'instance.
gauche). -/
noncomputable instance stalkFunctor_preservesHomology (x₀ : X) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).PreservesHomology := by
  simp only [(TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).exact_tfae.out 2 0]
  intro S hS
  have hcolim :=
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).preservesFiniteColimits_tfae.out 3 0).mp
      (inferInstance : Limits.PreservesFiniteColimits _)
  refine ShortComplex.ShortExact.mk' (hcolim S hS).left ?_ (hcolim S hS).right
  have := hS.2
  exact Functor.map_mono (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀) _

/-- **AB5 pour les tiges** : le foncteur tige d'un préfaisceau de groupes

**Renvoi Stacks** — *absent* : aucun énoncé de `Topology/Sheaves/` ne
mentionne AB5 ni la préservation des limites finies **par le foncteur tige**
(les occurrences de `PreservesFiniteLimits` de l'arborescence lue portent sur
d'autres foncteurs : `ClosedImmersion/AbelianCohomology.lean`,
`AlgebraicStructure/`). Le contenu le plus proche est
`Modules/Exactness.lean:77` `exact_iff_stalkShortComplex_exact`, qui en est
une **conséquence**, non l'axiome. Notre instance est donc la forme **la plus
forte** de ce que l'on trouve chez Stacks sur ce point.
abéliens préserve les limites finies. -/
noncomputable instance stalkFunctor_preservesFiniteLimits (x₀ : X) :
    Limits.PreservesFiniteLimits
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀) :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).preservesFiniteLimits_of_preservesHomology

/-- Transport d'exactitude vers les tiges : une suite courte exacte de
préfaisceaux de groupes abéliens reste exacte en chaque tige. Brique (i)
du re-scopage de la Partie 93 — combinée aux tiges des conoyaux (brique
ii) et au splicing (brique iii), elle ferme l'exactitude du complexe

**Renvoi Stacks** — *couvert* : `Modules/Exactness.lean:77`
`exact_iff_stalkShortComplex_exact` (01AG) et `Sheaf/Abelian.lean:75`
`shortExact_of_stalk` énoncent le **sens direct** que nous prouvons —
l'exactitude d'une suite se transporte aux tiges (Stacks l'énonce comme une
équivalence, nous comme la conservation de l'exactitude par le foncteur
tige). Ce que notre version ajoute : le foncteurPreservesExactness sur des
**préfaisceaux** de groupes abéliens, sans hypothèse de faisceau, là où Stacks
travaille en faisceaux de modules sur espace annelé.
canonique en chaque point. -/
theorem stalkFunctor_map_exact {S : ShortComplex (X.Presheaf AddCommGrpCat.{u})}
    (hS : S.Exact) (x₀ : X) :
    (S.map (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀)).Exact := by
  have h :=
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).exact_tfae.out 2 1
  exact h.mp inferInstance S hS

/-! ### Partie 93(a), briques (ii)+(iii) — le splicing en chaque tige, inconditionnel

Les deux briques restantes du re-scopage de la Partie 93 se combinent en un
seul énoncé générique plutôt qu'en deux lemmes séparés.

**Brique (ii) — tiges des conoyaux.** La suite `A ⟶ B ⟶ coker f` est exacte
en `B` (`ShortComplex.exact_cokernel`), et la brique (i)
(`stalkFunctor_map_exact`) transporte cette exactitude en chaque tige. La
préservation des conoyaux par le foncteur tige (adjoint à gauche, donc
colimites) est consommée sous cette forme : aucun isomorphisme explicite
`(coker f)ₓ₀ ≅ coker (fₓ₀)` n'a besoin d'être construit — l'exactitude de la
tige de la projection est exactement ce dont le splicing a besoin.

**Brique (iii) — récurrence splicing.** Composer à droite la tige de la
projection avec la tige de l'unité du conoyau ne change pas le noyau, dès
que cette dernière est mono — et elle l'est **inconditionnellement**
(`mono_stalkFunctor_map_toGodement`, valable pour tout préfaisceau, donc
pour `coker f`). Le transfert `ShortComplex.exact_iff_of_epi_of_isIso_of_mono`
est le même geste que `exact_toGodement_godementCanonicalDZero` côté
préfaisceaux (Partie 91 pas B), avec les mêmes τ₁ = τ₂ = 𝟙 et τ₃ = tige de
l'unité — mais ici τ₃ est mono pour **tout** préfaisceau, là où la version
préfaisceaux exigeait `F` faisceau (séparéité du conoyau, pas A de la
Partie 91).

Résultat : pour **toute** flèche `f` de préfaisceaux, sans aucune hypothèse
de faisceau, la suite de tiges `Aₓ₀ ⟶ Bₓ₀ ⟶ (C⁰(coker f))ₓ₀` est exacte en
`Bₓ₀`. La récurrence est ce lemme même : chaque degré du complexe canonique
en est une instance — degré 0 en `f = μ`, degré 1 en `f = d⁰`, chaque degré
suivant en `f = dⁿ` par le motif uniforme `d^{n+1} = godementStep dⁿ` (P89)
— sans que rien de nouveau n'apparaisse à aucun degré. -/

/-- **Le pas canonique est exact en chaque tige, pour toute flèche —
l'énoncé central des briques (ii)+(iii) de la Partie 93(a)** : pour tout
`f : A ⟶ B` de préfaisceaux de groupes abéliens et tout point `x₀`, la suite
de tiges `Aₓ₀ ⟶ Bₓ₀ ⟶ (C⁰(coker f))ₓ₀` est exacte en `Bₓ₀`. La preuve
transfère l'exactitude de la tige de `f ≫ π_f` — brique (i) appliquée à
`ShortComplex.exact_cokernel` — le long du morphisme de complexes courts
`(𝟙, 𝟙, tige de l'unité de coker f)` : la composante τ₃ est mono par
`mono_stalkFunctor_map_toGodement`, **sans aucune hypothèse de faisceau**.
C'est la brique de récurrence du complexe canonique : chaque degré en est

**Renvoi Stacks** — *partiel* : Stacks établit l'exactitude de la
construction **de Godement** — `Cohomology/GodementResolution/StalkHomotopy.lean:558`
`quasiIso_godementAugmentation`, clause (3) de 0FKS, détectée sur les tiges
(`StalkHomotopy.lean:127` `quasiIso_of_forall_stalk_quasiIso_nat`). Notre
énoncé est la version **générique** : il vaut pour **toute** flèche `f` de
préfaisceaux, et pas seulement pour les différentielles du complexe canonique
— c'est ce qui rend la récurrence `d^{n+1} = godementStep d^n` uniforme d'un
degré à l'autre.
une instance. -/
theorem stalk_exact_godementStep {A B : X.Presheaf AddCommGrpCat.{u}}
    (f : A ⟶ B) (x₀ : X) :
    (ShortComplex.mk
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map f)
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map (godementStep f))
      (by rw [show ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map f ≫
            (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map
              (godementStep f)) =
            (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map
              (f ≫ godementStep f) from
              (Functor.map_comp _ _ _).symm, comp_godementStep_zero,
        Functor.map_zero])).Exact := by
  have hmono : Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map
      (toGodement (cokernel f))) :=
    mono_stalkFunctor_map_toGodement (cokernel f) x₀
  have key : (ShortComplex.mk
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map f)
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map (cokernel.π f))
        (by rw [show ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map f ≫
              (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map
                (cokernel.π f)) =
              (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map
                (f ≫ cokernel.π f) from
              (Functor.map_comp _ _ _).symm, cokernel.condition,
          Functor.map_zero])).Exact ↔
      (ShortComplex.mk
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map f)
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map (godementStep f))
        (by rw [show ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map f ≫
              (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map
                (godementStep f)) =
              (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map
                (f ≫ godementStep f) from
              (Functor.map_comp _ _ _).symm, comp_godementStep_zero,
          Functor.map_zero])).Exact :=
    ShortComplex.exact_iff_of_epi_of_isIso_of_mono
      { τ₁ := 𝟙 _, τ₂ := 𝟙 _,
        τ₃ := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map
          (toGodement (cokernel f)),
        comm₁₂ := by rw [Category.id_comp, Category.comp_id],
        comm₂₃ := by simp [godementStep] }
  exact key.mp
    (stalkFunctor_map_exact (ShortComplex.exact_cokernel f) x₀)

/-- **Exactitude en tige du degré 0, inconditionnelle** : la suite
`Fₓ₀ ⟶ (C⁰F)ₓ₀ ⟶ (C¹F)ₓ₀` est exacte en `(C⁰F)ₓ₀` pour **tout** préfaisceau
`F` — là où la version préfaisceaux
(`exact_toGodement_godementCanonicalDZero`, Partie 91 pas B) exige `F`
faisceau. Le mono de l'unité, coûteux en préfaisceaux (il fallait la
séparéité du conoyau, pas A), est gratuit en tige
(`mono_stalkFunctor_map_toGodement`). Instance du lemme générique en

**Renvoi Stacks** — *couvert* : `Cohomology/GodementResolution/StalkHomotopy.lean:558`
`quasiIso_godementAugmentation` (clause (3) de 0FKS) — l'exactitude de
`0 → F → f_* f^* F → ⋯` détectée sur les tiges ; notre énoncé est le degré 0
de cette exactitude, énoncé en complexe court et **inconditionnel** (aucune
hypothèse de faisceau, là où la version préfaisceaux exigeait `F` faisceau).
`f = μ` : `d⁰ = godementStep μ` par définition. -/
theorem stalk_exact_toGodement_godementCanonicalDZero
    (F : X.Presheaf AddCommGrpCat.{u}) (x₀ : X) :
    (ShortComplex.mk
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map (toGodement F))
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map
        (godementCanonicalDZero F))
      (by rw [show ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map
              (toGodement F) ≫
            (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map
              (godementCanonicalDZero F)) =
            (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map
              (toGodement F ≫ godementCanonicalDZero F) from
              (Functor.map_comp _ _ _).symm,
        toGodement_comp_godementCanonicalDZero, Functor.map_zero])).Exact :=
  stalk_exact_godementStep (toGodement F) x₀

/-- **Exactitude en tige du degré 1 — la récurrence en acte** : la suite
`(C⁰F)ₓ₀ ⟶ (C¹F)ₓ₀ ⟶ (C²F)ₓ₀` est exacte en `(C¹F)ₓ₀`, pour tout préfaisceau
`F`. C'est le même lemme générique appliqué à `f = d⁰` : chaque degré
suivant du complexe canonique en est une instance identique, le motif
`d^{n+1} = godementStep dⁿ` (P89) rendant la récurrence uniforme — la

**Renvoi Stacks** — *couvert* : même référent que ci-dessus
(`Cohomology/GodementResolution/StalkHomotopy.lean:558`
`quasiIso_godementAugmentation`) : Stacks établit l'exactitude du complexe
augmenté **en un seul énoncé**, donc de chaque degré ; notre version isole le
**degré 1** et rend visible la récurrence (chaque degré suivant en est une
instance identique).
preuve ne change pas d'un degré à l'autre. -/
theorem stalk_exact_godementCanonicalDZero_godementCanonicalDOne
    (F : X.Presheaf AddCommGrpCat.{u}) (x₀ : X) :
    (ShortComplex.mk
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map
        (godementCanonicalDZero F))
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map
        (godementCanonicalDOne F))
      (by rw [show ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map
              (godementCanonicalDZero F) ≫
            (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map
              (godementCanonicalDOne F)) =
            (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map
              (godementCanonicalDZero F ≫ godementCanonicalDOne F) from
              (Functor.map_comp _ _ _).symm,
        godementCanonicalDZero_comp_godementCanonicalDOne,
        Functor.map_zero])).Exact :=
  stalk_exact_godementStep (godementCanonicalDZero F) x₀

end Grothendieck
