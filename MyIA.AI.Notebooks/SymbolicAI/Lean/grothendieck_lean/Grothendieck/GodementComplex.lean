/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grothendieck.GodementExactness
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Le complexe de Godement : l'itération du pas canonique à tous les degrés

Partie 92 — la frontière nommée par les Parties 90 et 91. La Partie 89 a posé
le **pas canonique** `godementStep f = cokernel.π f ≫ toGodement (coker f)` et
sa null-composition `f ≫ godementStep f = 0` ; les Parties 89-90 en ont tiré
les différentielles `d⁰` et `d¹` avec `d⁰ ≫ d¹ = 0` ; la Partie 91 a établi
l'exactitude du début (`exact_toGodement_godementCanonicalDZero`). Ce module
itére le pas **à tous les degrés** et assemble le résultat en un objet
`CochainComplex` [God58, Chap. II §4.1].

## La chaîne des différentielles

1. `godementDChain F` : la chaîne des différentielles comme suite de flèches
   (`Arrow`), par récursion sur le degré — le degré `n + 1` est le pas
   canonique de la flèche de degré `n` : `d^{n+1} := godementStep dⁿ`. C'est
   l'itération exacte de la construction de [God58], chaque flèche passant par
   le conoyau de la précédente — le contraste avec la Partie 87 : la suite des
   unités itérées n'est **pas** un complexe, celle des pas canoniques l'est.
2. `godementCanonicalObj F n` et `godementCanonicalD F n` : le terme de degré
   `n` et la différentielle `X n ⟶ X (n+1)` extraits de la chaîne, avec les
   lemmes `rfl` de recalage sur les notations des Parties 89-90
   (`godementCanonicalD_zero`, `godementCanonicalD_one`, `godementCanonicalD_succ`).
3. `godementCanonicalD_comp_zero` : **la null-composition à tout degré** —
   `dⁿ ≫ d^{n+1} = 0` pour tout `n`, instance immédiate de
   `comp_godementStep_zero` (Partie 89) appliquée au degré `n`.
4. `godementCanonicalComplex F` : l'assemblage en `CochainComplex` indexé par
   `ℕ`, via le constructeur canonique `CochainComplex.of` de Mathlib, avec les
   lemmes d'interface `godementCanonicalComplex_X_zero`,
   `godementCanonicalComplex_d_zero`, `godementCanonicalComplex_d_one`.
5. `toGodement_comp_godementCanonicalD` : le début du complexe augmenté —
   `μ ≫ d⁰ = 0`, réénoncé de la Partie 89 dans les notations itérées.

## Ce que cette Partie pose vs. ce qu'elle laisse ouvert

**Posé** : la récursion `d^{n+1} = godementStep dⁿ` à tous les degrés, la
null-composition `dⁿ ≫ d^{n+1} = 0` pour tout `n`, et l'objet
`godementCanonicalComplex : CochainComplex … ℕ` — la résolution canonique de
Godement existe maintenant **comme objet complexe**, pas seulement comme suite
de flèches épinglées degré par degré.

**Non posé** — frontière nommée de la Partie 93 : l'**acyclicité**
`Hⁿ(C⁰) = 0` pour `n ≥ 1` ([God58] II Th. 5.2.1). Elle exigera l'exactitude en
chaque degré — c'est-à-dire l'itération de `exact_toGodement_godementCanonicalDZero`
(P91, non encore mergée) le long de la chaîne — puis le passage à l'homologie.
Le complexe augmenté `F ⟶ C⁰F ⟶ C⁰(coker μ) ⟶ ⋯` comme **résolution** de `F`
(la quasi-isomorphisme) suit l'acyclicité et n'est pas abordé ici.

## Références

* [God58] R. Godement, *Topologie algébrique et théorie des faisceaux*,
  Hermann, 1958, chap. II §4.1.
-/

universe u

open CategoryTheory Category Limits TopCat TopologicalSpace Opposite

namespace Grothendieck

variable {X : TopCat.{u}}

/-- La chaîne des différentielles de la résolution canonique, comme suite de
flèches : le degré 0 est la différentielle `d⁰` de la Partie 89, et chaque
degré suivant est le **pas canonique** (Partie 89) de la flèche précédente —
`d^{n+1} = godementStep dⁿ`, chaque flèche passant par le conoyau de la
précédente. -/
noncomputable def godementDChain (F : X.Presheaf AddCommGrpCat.{u}) :
    ℕ → Arrow (X.Presheaf AddCommGrpCat.{u})
  | 0 => Arrow.mk (godementCanonicalDZero F)
  | n + 1 => Arrow.mk (godementStep (godementDChain F n).hom)

/-- Le terme de degré `n` de la résolution canonique : le but de la flèche de
degré `n - 1`, c'est-à-dire `C⁰` du conoyau de la différentielle précédente. -/
noncomputable def godementCanonicalObj (F : X.Presheaf AddCommGrpCat.{u}) (n : ℕ) :
    X.Presheaf AddCommGrpCat.{u} :=
  (godementDChain F n).left

/-- La différentielle de degré `n` de la résolution canonique, du terme `n` au
terme `n + 1` — par construction le pas canonique de la différentielle de
degré `n - 1`. -/
noncomputable def godementCanonicalD (F : X.Presheaf AddCommGrpCat.{u}) (n : ℕ) :
    godementCanonicalObj F n ⟶ godementCanonicalObj F (n + 1) :=
  (godementDChain F n).hom

@[simp]
theorem godementCanonicalObj_zero (F : X.Presheaf AddCommGrpCat.{u}) :
    godementCanonicalObj F 0 = godementPresheaf F :=
  rfl

theorem godementCanonicalObj_succ (F : X.Presheaf AddCommGrpCat.{u}) (n : ℕ) :
    godementCanonicalObj F (n + 2) =
      godementPresheaf (cokernel (godementCanonicalD F n)) :=
  rfl

@[simp]
theorem godementCanonicalD_zero (F : X.Presheaf AddCommGrpCat.{u}) :
    godementCanonicalD F 0 = godementCanonicalDZero F :=
  rfl

@[simp]
theorem godementCanonicalD_one (F : X.Presheaf AddCommGrpCat.{u}) :
    godementCanonicalD F 1 = godementCanonicalDOne F :=
  rfl

@[simp]
theorem godementCanonicalD_succ (F : X.Presheaf AddCommGrpCat.{u}) (n : ℕ) :
    godementCanonicalD F (n + 1) = godementStep (godementCanonicalD F n) :=
  rfl

/-- **La null-composition à tout degré** : chaque différentielle composée avec
la suivante est nulle, par la null-composition du pas canonique (Partie 89)
appliquée à la différentielle de degré `n`. C'est ce qui fait de la suite des
pas canoniques un complexe — là où la suite des unités itérées de la Partie 87
échouait (témoin injectif). -/
theorem godementCanonicalD_comp_zero (F : X.Presheaf AddCommGrpCat.{u}) (n : ℕ) :
    godementCanonicalD F n ≫ godementCanonicalD F (n + 1) = 0 :=
  comp_godementStep_zero _

/-- Le début du complexe augmenté est un complexe : l'unité de Godement
composée avec la différentielle de degré 0 est nulle (réénoncé itératif de la
Partie 89). -/
theorem toGodement_comp_godementCanonicalD (F : X.Presheaf AddCommGrpCat.{u}) :
    toGodement F ≫ godementCanonicalD F 0 = 0 :=
  toGodement_comp_godementCanonicalDZero F

/-- **Le complexe de Godement canonique** : la résolution canonique assemblée
en objet `CochainComplex` indexé par `ℕ` — termes `C⁰` des conoyaux
successifs, différentielles données par la récursion
`d^{n+1} = godementStep dⁿ`, null-composition à tout degré. -/
noncomputable def godementCanonicalComplex (F : X.Presheaf AddCommGrpCat.{u}) :
    CochainComplex (X.Presheaf AddCommGrpCat.{u}) ℕ :=
  CochainComplex.of (godementCanonicalObj F) (godementCanonicalD F)
    (godementCanonicalD_comp_zero F)

theorem godementCanonicalComplex_X (F : X.Presheaf AddCommGrpCat.{u}) :
    (godementCanonicalComplex F).X = godementCanonicalObj F :=
  rfl

theorem godementCanonicalComplex_X_zero (F : X.Presheaf AddCommGrpCat.{u}) :
    (godementCanonicalComplex F).X 0 = godementPresheaf F :=
  rfl

@[simp]
theorem godementCanonicalComplex_d (F : X.Presheaf AddCommGrpCat.{u}) (n : ℕ) :
    (godementCanonicalComplex F).d n (n + 1) = godementCanonicalD F n :=
  CochainComplex.of_d _ _ _

theorem godementCanonicalComplex_d_zero (F : X.Presheaf AddCommGrpCat.{u}) :
    (godementCanonicalComplex F).d 0 1 = godementCanonicalDZero F := by
  rw [godementCanonicalComplex_d, godementCanonicalD_zero]

theorem godementCanonicalComplex_d_one (F : X.Presheaf AddCommGrpCat.{u}) :
    (godementCanonicalComplex F).d 1 2 = godementCanonicalDOne F := by
  rw [godementCanonicalComplex_d, godementCanonicalD_one]

/-- **Partie 93(b) — l'assemblage : le complexe canonique est exact en
chaque tige, à tout degré, sans aucune hypothèse de faisceau** : pour tout
`n`, la suite de tiges `CⁿFₓ₀ ⟶ C^{n+1}Fₓ₀ ⟶ C^{n+2}Fₓ₀` est exacte en
`C^{n+1}Fₓ₀`. La récurrence promise par la Partie 93(a) est le lemme
générique lui-même : chaque degré est `stalk_exact_godementStep` en
`f = dⁿ`, les deux motifs d'assemblage — `d^{n+1} = godementStep dⁿ`
(P89) et `C^{n+2} = C⁰(coker dⁿ)` (P92) — étant **définitionnels**
(`rfl`), aucune récurrence sur `n` n'est à écrire. Les degrés explicités
en 93(a) sont les instances `n = 0` du présent énoncé
(`stalk_exact_godementCanonicalDZero_godementCanonicalDOne`) et le degré
augmenté `Fₓ₀ ⟶ (C⁰F)ₓ₀ ⟶ (C¹F)ₓ₀` en `f = μ`
(`stalk_exact_toGodement_godementCanonicalDZero`). La lecture homologique —
l'acyclicité `Hⁿ(C⁰F) = 0` pour `n ≥ 1` — est livrée ci-dessous
(`isZero_stalk_homology_godementCanonicalComplex`). -/
theorem stalk_exact_godementCanonicalD (F : X.Presheaf AddCommGrpCat.{u})
    (x₀ : X) (n : ℕ) :
    (ShortComplex.mk
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map
        (godementCanonicalD F n))
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map
        (godementCanonicalD F (n + 1)))
      (by rw [show ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map
              (godementCanonicalD F n) ≫
            (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map
              (godementCanonicalD F (n + 1))) =
            (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).map
              (godementCanonicalD F n ≫ godementCanonicalD F (n + 1)) from
              (Functor.map_comp _ _ _).symm,
        godementCanonicalD_comp_zero,
        Functor.map_zero])).Exact :=
  stalk_exact_godementStep (godementCanonicalD F n) x₀

/-- **Partie 93(b) — la lecture homologique : l'homologie du complexe
canonique est nulle en chaque tige, pour tout degré `n ≥ 1`** : pour tout
point `x₀`, `IsZero` de la tige en `x₀` de `Hⁿ(C⁰F)` — **sans aucune
hypothèse de faisceau**.

C'est la lecture homologique de `stalk_exact_godementCanonicalD`, en trois
gestes : le complexe court de tiges centré en `n` est exact (c'est ce
théorème en `n - 1`) ; une suite courte exacte a une homologie nulle
(`ShortComplex.exact_iff_isZero_homology`) ; et l'instance
`stalkFunctor_preservesHomology` (Partie 93(a), AB5) transporte ce `IsZero`
le long de l'isomorphisme canonique `ShortComplex.mapHomologyIso` :
l'homologie de la tige est la tige de l'homologie.

**Pourquoi les tiges et non le préfaisceau** : l'énoncé de [God58]
(II Th. 5.2.1) est `Hⁿ(C⁰F) = 0` dans la catégorie des faisceaux. Un
préfaisceau dont toutes les tiges sont nulles n'est pas nul en général
(non séparé) : la nullité en chaque tige est la forme inconditionnelle —
le corollaire « faisceau » (nullité de `Hⁿ` dans la catégorie des
faisceaux) est le front suivant.

Le degré `n = 0` est exclu : `H⁰(C⁰F) = ker d⁰` n'a aucune raison d'être
nul — l'exactitude en `C⁰F` est celle du complexe augmenté
`F ⟶ C⁰F ⟶ ⋯` (flèche entrante `μ`), déjà établie en chaque tige par
`stalk_exact_toGodement_godementCanonicalDZero` (Partie 93(a)). -/
theorem isZero_stalk_homology_godementCanonicalComplex
    (F : X.Presheaf AddCommGrpCat.{u}) (x₀ : X) {n : ℕ} (hn : 1 ≤ n) :
    IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).obj
      ((godementCanonicalComplex F).homology n)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- `ComplexShape.next`/`prev` sont choisis via `Exists.choose` : opaques en
  -- defeq, leurs équations se prouvent à la main (split sur le dite).
  have hprev : (ComplexShape.up ℕ).prev (m + 1) = m := by
    unfold ComplexShape.prev
    split
    case isTrue h =>
      have h2 : h.choose + 1 = m + 1 := h.choose_spec
      omega
    case isFalse h =>
      exact (h (Exists.intro m rfl : ∃ j, (ComplexShape.up ℕ).Rel j (m + 1))).elim
  have hnext : (ComplexShape.up ℕ).next (m + 1) = m + 1 + 1 := by
    unfold ComplexShape.next
    split
    case isTrue h =>
      have h2 : m + 1 + 1 = h.choose := h.choose_spec
      exact h2.symm
    case isFalse h =>
      exact (h (Exists.intro (m + 1 + 1) rfl : ∃ j, (ComplexShape.up ℕ).Rel (m + 1) j)).elim
  -- Les différentielles de `sc'` sont les `d` exacts du complexe ; `simp only`
  -- (et non `rw`) réécrit `d` dans le champ autoParam `zero` dépendant :
  have hex : (((godementCanonicalComplex F).sc' m (m + 1) (m + 1 + 1)).map
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀)).Exact := by
    show ((ShortComplex.mk ((godementCanonicalComplex F).d m (m + 1))
        ((godementCanonicalComplex F).d (m + 1) (m + 1 + 1))
        ((godementCanonicalComplex F).d_comp_d m (m + 1) (m + 1 + 1))).map
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀)).Exact
    simp only [godementCanonicalComplex_d]
    exact stalk_exact_godementCanonicalD F x₀ m
  have h0 : IsZero (((godementCanonicalComplex F).sc' m (m + 1) (m + 1 + 1)).map
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀)).homology :=
    (ShortComplex.exact_iff_isZero_homology _).mp hex
  have h1 : IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).obj
      ((godementCanonicalComplex F).sc' m (m + 1) (m + 1 + 1)).homology) :=
    IsZero.of_iso h0 (((godementCanonicalComplex F).sc' m (m + 1) (m + 1 + 1)).mapHomologyIso
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀)).symm
  -- Raccord sc' ≅ sc (isoSc' + prev/next manuels) puis homologie du complexe
  -- (`homologyMapIso` est une fonction de namespace, pas une projection) :
  have e := (godementCanonicalComplex F).isoSc' (i := m) (j := m + 1) (k := m + 1 + 1)
    hprev hnext
  exact IsZero.of_iso h1
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x₀).mapIso
      (ShortComplex.homologyMapIso e))

/-- **Partie 94 — flascuité de la tour canonique** : chaque étage du complexe
canonique de Godement est flasque, sans aucune hypothèse sur `F`. C'est
l'étape 1 de la lecture « résolution flasque » de [God58] II Th. 5.2.1 :
tous les étages sont des préfaisceaux de Godement (`C⁰F` en degré 0,
`C⁰(coker dⁿ)` en degré `n+1` via `godementStep`), et la flascuité
générique de `godementPresheaf` — `isFlasque_godementPresheaf`,
prolongement par zéro des familles de germes : une famille de germes sur
`V` se relève sur tout ouvert `U ⊇ V` en prolongeant par `0` hors de `V` —
transporte à la tour entière.

Les trois cas de la récursion `godementCanonicalObj` sont chacun
définitionnels : degré 0 (`godementCanonicalObj_zero` : l'étage est
`godementPresheaf F`), degré 1 (l'étage est `godementPresheaf (coker μ)`,
définition du chaînon `godementDChain` en 1), degré `n+2`
(`godementCanonicalObj_succ` : l'étage est `godementPresheaf (coker dⁿ)`).
L'assemblage est un tri-cas `exact` — aucune récurrence à écrire, la
flascuité de chaque étage est celle du préfaisceau de Godement qu'il est.

Note de cadrage (2026-10-18) : `TopCat.Presheaf.IsFlasque` existe bien dans
Mathlib (Topology/Sheaves/Flasque.lean) — l'addendum c.6242821964 sur #2159
le disait à tort « faisceau-only » ; le fichier porte les deux versions,
préfaisceau et faisceau. Le corollaire faisceau de [God58] II Th. 5.2.1
(nullité de `Hⁿ` dans la catégorie des faisceaux) reste derrière la
faisceification abélienne, absente de Mathlib au pin du lake :
`sheafify`/`sheafifyStalkIso` Type-valued seulement, `HasSheafify`/
`HasSheafCompose (forget A)` hypothèses sans instance pour
`(AddCommGrpCat, TopCat)`. La voie préfaisceau — acyclicité en tige
(Partie 93(b)), flascuité des étages (cette Partie) — avance sans elle ;
la résolution flasque (suite exacte longue, Partie 95+) consommera la
brique livrée ici. -/
theorem isFlasque_godementCanonicalComplex
    (F : X.Presheaf AddCommGrpCat.{u}) (n : ℕ) :
    ((godementCanonicalComplex F).X n).IsFlasque := by
  match n with
  | 0 => exact isFlasque_godementPresheaf F
  | 1 => exact isFlasque_godementPresheaf (cokernel (toGodement F))
  | (n + 2) => exact isFlasque_godementPresheaf (cokernel (godementCanonicalD F n))

end Grothendieck
