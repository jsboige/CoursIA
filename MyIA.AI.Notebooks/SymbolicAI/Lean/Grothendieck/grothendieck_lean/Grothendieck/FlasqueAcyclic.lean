/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Grothendieck hommage — Partie 94 : l'acyclicité des faisceaux flasques —
degré 1 inconditionnel, décalage, et la frontière `injectif => flasque`.

Alexandre Grothendieck (1928-2014).

Extension Phase 2 (#2159, Epic #1646).

Cette partie corrige une glose et livre le théorème qu'elle masquait. La
Partie 80 créditait Godement II.5.2 d'un « flasque => injectif par Zorn » :
**cet énoncé est faux** — sur un espace discret à deux points, tous les
faisceaux sont flasques (tout crible principal amalgamate), et le faisceau
constant (Z, Z) n'est pas injectif dans Ab x Ab. L'énoncé vrai de Godement
est **flasque => Γ-acyclique** (II.5.1) : H^{n+1}(F) = 0 pour tout n. Le
prolongement par Zorn de la Partie 82 n'est pas un passage à l'injectif,
c'est la **surjectivité des sections globales** — le cas de base de
l'acyclicité.

Trois théorèmes et un capstone :

  - `shortExact_of_injectivePresentation` : toute présentation injective
    F ↪ J (EnoughInjectives) engendre une suite exacte courte
    0 → F → J → coker → 0. Pure algèbre homologique
    (`CategoryTheory.ShortComplex.exact_cokernel`),
    mais Mathlib ne fournit pas ce constructeur : la suite exacte longue
    covariante d'Ext s'applique à des `ShortComplex.ShortExact`, pas à des
    mono bruts. Ce pont est le premier maillon.

  - `subsingleton_H_one_of_flasque` : **le degré 1, inconditionnel**. Sur une
    suite exacte courte 0 → X₁ → X₂ → X₃ → 0 de faisceaux abéliens avec X₁
    flasque (cribles) et X₂ injectif, H¹(X₁) = 0. La preuve assemble :
    (a) la suite exacte longue covariante d'Ext de Mathlib
    (`Abelian.Ext.covariant_sequence_exact₁`) — un élément de H¹(X₁) dont
    l'image dans H¹(X₂) est nulle (injectif : instance Mathlib) provient
    d'un élément de H⁰(X₃) ; (b) l'identification H⁰ ≃ Γ sur l'ouvert
    terminal (`Sheaf.H.equiv₀`), qui fait de cet élément une section globale
    de X₃ ; (c) la surjectivité Γ de la Partie 82
    (`epi_of_shortExact_of_isFlasqueSieves` — c'est là que Zorn travaille) :
    la section se relève en une section de X₂, c'est-à-dire que l'élément
    de H⁰(X₃) est dans l'image du morphisme de degré 0 ; (d) la nullité de
    son image par la classe d'extension (`comp_extClass`), qui remonte à
    l'élément original et le tue. Aucune hypothèse sur X₃ : le quotient
    n'a pas besoin d'être flasque au degré 1.

  - `subsingleton_H_succ_of_flasque_decalage` : **le décalage**. Même suite
    exacte courte, X₂ injectif ; si Hⁿ(X₃) est trivial alors H^{n+1}(X₁)
    est trivial. Le pas inductif de l'acyclicité : chaque degré se paie en
    un degré du quotient.

  - `subsingleton_H_succ_of_flasque_all` : **le capstone conditionnel**.
    Si de plus tout faisceau injectif est flasque (hypothèse `hInjFlasque`,
    Godement II.4), alors tout faisceau flasque est Γ-acyclique :
    H^{n+1}(F) = 0 pour tout n. L'induction est complète : la présentation
    injective fournit 0 → F → J → Q, la Partie 83
    (`isFlasqueSieves_of_shortExact_of_isFlasque₁₂`) rend Q flasque (F l'est,
    J l'est par l'hypothèse), le degré 1 ou l'induction appliquée à Q fournit
    l'hypothèse du décalage.

**Frontière explicitement nommée** : `injectif => flasque` ([God58] II.4).
C'est le seul maillon manquant pour décharger l'hypothèse du capstone en
un théorème inconditionnel ∀n. La preuve classique prolonge la section 1
de ℤ_U le long de l'inclusion mono ℤ_U ↪ ℤ_V, ce qui exige
l'extension par zéro `j_!` des faisceaux ouverts — absents de Mathlib à
ce jour. Tant que `j_!` n'existe pas, le degré 1 (inconditionnel, ci-dessus)
et le décalage sont les briques livrables ; le capstone attend son hypothèse.

La lecture conceptuelle : l'acyclicité des flasques n'est pas un théorème
d'injectivité, c'est un théorème de **surjectivité des sections** — la
partie facile de la suite exacte longue, celle qui vit dans Γ et non dans
Ext. La difficulté de Godement n'est pas de tuer H¹, mais de faire tourner
la récursion : le quotient d'un flasque par un flasque est flasque, et
c'est l'injectif qui doit être flasque pour amorcer. C'est exactement la
ligne de partage que cette partie enregistre.

Références :
  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §4 (injectif => flasque) et §5 (th. 5.1 : flasque => Γ-acyclique).
  - Mathlib, `Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences`
    (suite exacte longue covariante d'Ext, Joel Riou).
  - Mathlib, `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`
    (`Sheaf.H`, `Sheaf.H.equiv₀`, identification H⁰ = Γ).
  - Partie 20 (`Grothendieck.SheafCohomology.Basic`) : le pont cohomologie.
  - Partie 79 (`Grothendieck.Flasque`) : `IsFlasqueSieves`.
  - Partie 80 (`Grothendieck.FlasqueStability`) : stabilite, croisement
    flasque-injectif (corrigee : la glose « flasque => injectif » y est
    remplacee par un renvoi a la presente partie).
  - Partie 82 (`Grothendieck.FlasqueExact`) : la surjectivité Γ par Zorn.
  - Partie 83 (`Grothendieck.FlasqueQuotient`) : quotient de flasques.

Convention i18n (EPIC #4980 ratifiée 2026-07-04) : ce module est jumelé avec
sa version anglaise canonique dans le fichier sibling
`Grothendieck/FlasqueAcyclic_en.lean` — suffixe `_en` sur le namespace et les
imports, byte-identity du reste (signatures, preuves, tactiques).
-/

import Grothendieck.FlasqueExact
import Grothendieck.FlasqueQuotient
import Grothendieck.FlasqueStability
import Grothendieck.SheafCohomology.Basic

universe r w u

namespace Grothendieck

open CategoryTheory Category Limits Opposite

/-!
## 1. Le constructeur : présentation injective => suite exacte courte

Mathlib définit `InjectivePresentation` (champs J injectif, f mono) mais ne
fournit pas la suite exacte courte `0 → F → J → coker f → 0` sous la forme
`ShortComplex.ShortExact` que consomme la suite exacte longue covariante
d'Ext. Ce constructeur est la colle :
`CategoryTheory.ShortComplex.exact_cokernel` fournit
l'exactitude, les champs mono/épi de la présentation et du conoyau les
deux autres composantes.
-/

section Constructeur

variable {A : Type r} [Category.{w} A] [Abelian A]

/-- Toute présentation injective `P : InjectivePresentation F` engendre une
suite exacte courte `0 → F → P.J → coker P.f → 0` au sens
`ShortComplex.ShortExact`. Les trois composantes : l'exactitude en le
conoyau (`CategoryTheory.ShortComplex.exact_cokernel`), le mono de la présentation (champ
`P.mono`), l'épi du conoyau (instance). C'est la forme que consomme la
suite exacte longue covariante d'Ext (`Abelian.Ext.covariant_sequence_exact₁`). -/
theorem shortExact_of_injectivePresentation {F : A} (P : InjectivePresentation F) :
    (ShortComplex.mk P.f (cokernel.π P.f) (cokernel.condition P.f)).ShortExact where
  exact := CategoryTheory.ShortComplex.exact_cokernel P.f
  mono_f := P.mono
  epi_g := inferInstance

end Constructeur

/-!
## 2. Le degré 1 : flasque => H¹ = 0, inconditionnel

Sur `0 → X₁ → X₂ → X₃ → 0` avec X₁ flasque et X₂ injectif, le groupe
H¹(X₁) est trivial. C'est le théorème de Godement II.5.1 au degré 1 : la
surjectivité Γ de la Partie 82 (Zorn) suffit, aucune hypothèse sur X₃.
-/

section DegreUn

variable {X : TopCat.{u}}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

open TopCat TopCat.Presheaf TopologicalSpace

/-- **Degré 1 de l'acyclicité des flasques** (Godement II.5.1, cas n = 0).
Sur une suite exacte courte `0 → X₁ → X₂ → X₃ → 0` de faisceaux abéliens
sur un espace topologique X, avec X₁ flasque (au sens cribles, Partie 79)
et X₂ injectif, le groupe `H¹(X₁)` est trivial.

La preuve : un élément x₁ de H¹(X₁) a une image nulle dans H¹(X₂)
(injectif), donc par la suite exacte longue covariante d'Ext il provient
d'un x₃ : H⁰(X₃) ; via `Sheaf.H.equiv₀` sur l'ouvert terminal, x₃ est une
section globale de X₃ ; la surjectivité Γ de la Partie 82 la relève en une
section de X₂, c'est-à-dire x₃ = image de x₂ : H⁰(X₂) ; alors x₃ ∘ δ = 0
par `comp_extClass` et l'associativité d'Ext, donc x₁ = 0. -/
theorem subsingleton_H_one_of_flasque
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) [Injective S.X₂]
    [IsFlasqueSieves (S.X₁.obj ⋙ CategoryTheory.forget AddCommGrpCat)] :
    Subsingleton (CategoryTheory.Sheaf.H S.X₁ 1) := by
  refine subsingleton_of_forall_eq 0 fun x₁ => ?_
  -- l'image de x₁ dans H¹(X₂) est nulle : X₂ est injectif
  have hx₁ : x₁.comp (CategoryTheory.Abelian.Ext.mk₀ S.f) (add_zero 1) = 0 :=
    Subsingleton.elim _ _
  -- donc x₁ provient d'un x₃ : H⁰(X₃) (suite exacte longue covariante)
  obtain ⟨x₃, hx₃⟩ :=
    CategoryTheory.Abelian.Ext.covariant_sequence_exact₁ _ hS x₁ hx₁ rfl
  -- x₃ est une section globale de X₃ (identification H⁰ = Γ, ouvert terminal)
  have hT : IsTerminal (⊤ : Opens X) := Limits.isTerminalTop
  obtain ⟨i, hi⟩ := (AddCommGrpCat.epi_iff_surjective _).mp
    (epi_of_shortExact_of_isFlasqueSieves hS)
    (CategoryTheory.Sheaf.H.equiv₀ S.X₃ hT x₃)
  -- cette section se relève en une section de X₂ (Partie 82, Zorn)
  set x₂ : CategoryTheory.Sheaf.H S.X₂ 0 :=
    (CategoryTheory.Sheaf.H.equiv₀ S.X₂ hT).symm i with hx₂def
  have hcomp : x₂.comp (CategoryTheory.Abelian.Ext.mk₀ S.g) (add_zero 0) = x₃ := by
    refine (CategoryTheory.Sheaf.H.equiv₀ S.X₃ hT).injective ?_
    rw [← CategoryTheory.Sheaf.H.map_apply]
    rw [← CategoryTheory.Sheaf.H.equiv₀_naturality hT S.g x₂]
    rw [hx₂def, AddEquiv.apply_symm_apply]
    exact hi
  -- alors x₃ ∘ δ = 0 : l'élément est dans l'image du morphisme de degré 0
  have hδ : x₃.comp hS.extClass (rfl : (0 : ℕ) + 1 = 1) = 0 := by
    rw [← hcomp, CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero,
      hS.comp_extClass, CategoryTheory.Abelian.Ext.comp_zero]
  exact hx₃.symm.trans hδ

/-- **Corollaire inconditionnel du degré 1** : tout faisceau flasque (cribles)
sur un espace topologique à faisceaux abéliens, dans un catégorie à assez
d'injectifs, a un H¹ trivial. La présentation injective de F fournit la
suite exacte courte du théorème précédent. -/
theorem subsingleton_H_one_of_flasque_presentation
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [IsFlasqueSieves (F.obj ⋙ CategoryTheory.forget AddCommGrpCat)]
    [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] :
    Subsingleton (CategoryTheory.Sheaf.H F 1) := by
  obtain ⟨P⟩ := ‹EnoughInjectives _›.presentation F
  exact subsingleton_H_one_of_flasque (shortExact_of_injectivePresentation P)

end DegreUn

/-!
## 3. Le décalage : Hⁿ(X₃) = 0 => H^{n+1}(X₁) = 0

Le pas inductif. Aucune hypothèse de flasquie ici : le décalage est une
propriété de la suite exacte longue seule, X₂ injectif tuant le morphisme
de X₁ vers X₂ en tout degré.
-/

section Decalage

variable {X : TopCat.{u}}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

open TopCat TopCat.Presheaf TopologicalSpace

/-- **Décalage** : sur une suite exacte courte `0 → X₁ → X₂ → X₃ → 0` avec
X₂ injectif, la trivialité de `Hⁿ(X₃)` entraîne celle de `H^{n+1}(X₁)`.
L'élément de `H^{n+1}(X₁)` a une image nulle dans X₂ (injectif), provient
d'un `Hⁿ(X₃)` trivial, donc est nul. C'est le pas inductif de l'acyclicité :
chaque degré de X₁ se paie en un degré du quotient. -/
theorem subsingleton_H_succ_of_flasque_decalage
    {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) [Injective S.X₂] {n : ℕ}
    (hQ : Subsingleton (CategoryTheory.Sheaf.H S.X₃ n)) :
    Subsingleton (CategoryTheory.Sheaf.H S.X₁ (n + 1)) := by
  refine subsingleton_of_forall_eq 0 fun x₁ => ?_
  have hx₁ : x₁.comp (CategoryTheory.Abelian.Ext.mk₀ S.f) (add_zero (n + 1)) = 0 :=
    Subsingleton.elim _ _
  have hex : ∃ x₃ : CategoryTheory.Sheaf.H S.X₃ n,
      x₃.comp hS.extClass (rfl : n + 1 = n + 1) = x₁ :=
    CategoryTheory.Abelian.Ext.covariant_sequence_exact₁ _ hS x₁ hx₁ rfl
  obtain ⟨x₃, hx₃⟩ := hex
  rw [← hx₃, Subsingleton.elim (α := CategoryTheory.Sheaf.H S.X₃ n) x₃ 0]
  simp

end Decalage

/-!
## 4. Capstone conditionnel : flasque => Γ-acyclique, sous `injectif => flasque`

L'induction complète. L'hypothèse `hInjFlasque` (Godement II.4) est le seul
maillon manquant : elle rend le terme du milieu flasque, la Partie 83 rend
le quotient flasque, et la récursion tourne. Frontière nommée pour la
Partie 95 : la preuve classique exige l'extension par zéro `j_!` des
faisceaux ouverts, absente de Mathlib.
-/

section Capstone

variable {X : TopCat.{u}}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

open TopCat TopCat.Presheaf TopologicalSpace

/-- **Capstone conditionnel** (Godement II.5.1 complet) : si tout faisceau
injectif est flasque — hypothèse `hInjFlasque`, Godement II.4, frontière
nommée pour la Partie 95 (`j_!` absent de Mathlib) — alors tout faisceau
flasque est Γ-acyclique : `H^{n+1}(F)` est trivial pour tout n.

L'induction : au degré 0, le théorème du degré 1 ; au degré n+1, la
présentation injective `0 → F → J → Q`, la Partie 83 rend Q flasque
(F l'est, J l'est par l'hypothèse), l'hypothèse d'induction appliquée à Q
fournit `H^{n+1}(Q)` trivial, le décalage conclut. -/
theorem subsingleton_H_succ_of_flasque_all
    (hInjFlasque : ∀ I : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u},
      Injective I → IsFlasqueSieves (I.obj ⋙ CategoryTheory.forget AddCommGrpCat))
    [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (n : ℕ) (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [IsFlasqueSieves (F.obj ⋙ CategoryTheory.forget AddCommGrpCat)] :
    Subsingleton (CategoryTheory.Sheaf.H F (n + 1)) := by
  induction n generalizing F with
  | zero =>
    exact subsingleton_H_one_of_flasque_presentation F
  | succ n ih =>
    obtain ⟨P⟩ := ‹EnoughInjectives _›.presentation F
    have hS : (ShortComplex.mk P.f (cokernel.π P.f) (cokernel.condition P.f)).ShortExact :=
      shortExact_of_injectivePresentation P
    haveI hI₁ : IsFlasqueSieves
        ((ShortComplex.mk P.f (cokernel.π P.f) (cokernel.condition P.f)).X₁.obj ⋙
          CategoryTheory.forget AddCommGrpCat) := ‹_›
    haveI hI₂ : IsFlasqueSieves
        ((ShortComplex.mk P.f (cokernel.π P.f) (cokernel.condition P.f)).X₂.obj ⋙
          CategoryTheory.forget AddCommGrpCat) := hInjFlasque P.J P.injective
    haveI hQflasque : IsFlasqueSieves
        ((ShortComplex.mk P.f (cokernel.π P.f) (cokernel.condition P.f)).X₃.obj ⋙
          CategoryTheory.forget AddCommGrpCat) :=
      isFlasqueSieves_of_shortExact_of_isFlasque₁₂ hS
    exact subsingleton_H_succ_of_flasque_decalage hS (ih (cokernel P.f))

end Capstone

end Grothendieck
