/-
# Hommage Grothendieck — Partie 20 : Cohomologie des faisceaux (Ext)

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Les parties 1-19 ont etabli les fondamentaux : categories, cribles, topologies,
lois de treillis, identites de pullback, bases de faisceaux, cloture couvrante,
calibration, sous-canonicalite, topologies denses, generation de couvertures,
coherence conservative, points de site, schemas, schemas de Zariski, faisceaux
constants, exactitude a gauche, cohomologie de Cech, carres de Mayer-Vietoris,
hom interne des faisceaux.

Ce module introduit la **cohomologie des faisceaux** pour des faisceaux abeliens
sur un site (C, J), selon la definition Ext de Mathlib (SGA 4 II, Grothendieck 1957).
La cohomologie H^n(F) est definie comme le groupe Ext depuis le faisceau constant
a valeurs ULift Z vers F, conformement a la definition de Joel Riou (2024) qui
realise la cohomologie classique de SGA 4 II dans Mathlib.

Constructions clefs pontées depuis Mathlib (`CategoryTheory.Sites.SheafCohomology.Basic`) :

  - `Sheaf.H F n` : le n-ieme groupe de cohomologie d'un faisceau abelien F
  - `Sheaf.cohomologyPresheaf F n` : le prefaisceau U ↦ Ext^n(free(yoneda U), F)
  - `Sheaf.H' F n X` : cohomologie de degre n en un objet X
  - `Sheaf.H.equiv₀` : H^0(F) ≃+ F(T) quand T est terminal (sections globales)
  - `Sheaf.H.map` : l'application induite sur la cohomologie par un morphisme de faisceaux
  - `Sheaf.functorH J n` : le foncteur cohomologie Sheaf J AddCommGrp ⥤ AddCommGrp
  - Lemmes de fonctorialite : map_id, map_comp, map_add
  - Annulation : faisceau injectif -> Subsingleton H^{n+1}, faisceau nul -> Subsingleton

C'est le fondement de la machinerie cohomologique des topos de Grothendieck :
foncteurs derives, suites spectrales, et leurs applications (theorie de Hodge,
theorie des nombres, geometrie algebrique).

EPIC #1646, Phase 5 (#2159), voir #2159. Tous les `sorry`s elimines a la creation.

### Note d'accessibilite (Epics #1452/#1453)

Ce module expose **2 noncomputable def + 3 theorem** sur la cohomologie des
faisceaux (H^0 = sections globales, fonctorialite, annulation), accessibilite
progressive par 8 sections thematiques : (1) groupes de cohomologie,
(2) prefaisceau de cohomologie, (3) cohomologie de degre n en un objet,
(4) cohomologie de degre zero et sections globales, (5) application induite sur
la cohomologie, (6) foncteur cohomologie, (7) resultats d'annulation,
(8) theoremes ponts.

### Convention i18n (EPIC #4980 ratifiee par user 2026-07-04)

Ce module substantiel est apparie avec son jumeau anglais dans le fichier sibling
`Basic_en.lean` (modele sibling pair, voir PR #6154 pour le pilote sur
`Utility.lean` et #6275/#6277/#6280/#6284/#6291 pour la continuite du rollout
Phase 2+). Namespace suffix `_en` applique au fichier EN (anti-collision,
conforme code-style.md #4980).
-/

import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

universe w' w v u

namespace Grothendieck.SheafCohomology

open CategoryTheory Category Opposite Limits
/-!
## 1. Groupes de cohomologie des faisceaux

Le groupe de cohomologie `Sheaf.H F n` d'un faisceau abelien F en degre n est
defini comme le groupe Ext depuis le faisceau constant a valeurs ULift Z vers F :

  H^n(F) = Ext^n(constantSheaf J AddCommGrp (ULift Z), F)

Cela suit la definition de Mathlib (Joel Riou, 2024) et correspond a la
cohomologie classique des faisceaux dans SGA 4 II.

Necessite `HasSheafify J AddCommGrp` et `HasExt (Sheaf J AddCommGrp)`.
-/

-- The nth cohomology group of an abelian sheaf F (Ext-based).
#check @CategoryTheory.Sheaf.H

/-!
## 2. Le prefaisceau de cohomologie

Etant donne un faisceau abelien F, `cohomologyPresheaf F n` est le prefaisceau
qui envoie U : C^op vers le groupe Ext depuis le faisceau abelien libre engendre
par yoneda.obj U vers F. C'est un prefaisceau de groupes abeliens.

Evalue en un objet terminal T, ceci recupere H^n(F) (a equivalence `H.equiv_0` pres).
-/

-- The cohomology presheaf functor (bifunctor variant).
#check @CategoryTheory.Sheaf.cohomologyPresheafFunctor

-- The cohomology presheaf: U ↦ Ext^n(free(yoneda U), F).
#check @CategoryTheory.Sheaf.cohomologyPresheaf

/-!
## 3. Cohomologie de degre n en un objet

`Sheaf.H' F n X` est la cohomologie de degre n du faisceau F sur X, definie
comme `(F.cohomologyPresheaf n).obj (op X)`.

C'est la version « locale » de la cohomologie -- elle varie fonctoriellement en X.
-/

-- Degree-n cohomology of X with values in F.
#check @CategoryTheory.Sheaf.H'

/-!
## 4. Cohomologie de degre zero et sections globales

Quand C a un objet terminal T, la cohomologie de degre zero H^0(F) est
additivement equivalente au groupe des sections globales F(T) :

  H^0(F) =+ F(T)

via `H.equiv_0`. C'est la version faisceautique de l'identification classique
H^0(X, F) = Gamma(X, F) en cohomologie des faisceaux classique.

L'equivalence est naturelle : un morphisme f : F --> G induit un carre commutatif
reliant H.map f 0 et f.app (op T).
-/

-- The additive equivalence H^0(F) =+ F(T) for terminal T.
#check @CategoryTheory.Sheaf.H.equiv₀

-- H.equiv_0 is natural in the sheaf argument.
#check @CategoryTheory.Sheaf.H.equiv₀_naturality

-- The symmetry of naturality for equiv_0.
#check @CategoryTheory.Sheaf.H.equiv₀_symm_naturality

/-!
## 5. L'application induite sur la cohomologie

Etant donne un morphisme f : F --> G de faisceaux abeliens, `H.map f n` est
l'application additive induite H^n(F) ->+ H^n(G). Cela fait de H^n un foncteur
de Sheaf J AddCommGrp vers AddCommGrp.

Proprietes cles :
  - H.map (1 F) n = id  (fonctorialite : identite)
  - H.map (f >> g) n = H.map g n . H.map f n  (fonctorialite : composition)
  - H.map (f + g) n x = H.map f n x + H.map g n x  (additivite)
-/

-- The induced map on cohomology by a sheaf morphism.
#check @CategoryTheory.Sheaf.H.map

-- Functoriality: H.map (1 F) n x = x.
#check @CategoryTheory.Sheaf.H.map_id_apply

-- Functoriality: H.map (f >> g) n x = H.map g n (H.map f n x).
#check @CategoryTheory.Sheaf.H.map_comp_apply

-- Additivity: H.map (f + g) n x = H.map f n x + H.map g n x.
#check @CategoryTheory.Sheaf.H.map_add_apply

-- Explicit unfolding: H.map f n x = x.comp (Ext.mk_0 f) (add_zero n).
#check @CategoryTheory.Sheaf.H.map_apply

/-!
## 6. Le foncteur cohomologie

`functorH J n` empaquette les groupes de cohomologie en un foncteur :

  functorH J n : Sheaf J AddCommGrp ⥤ AddCommGrp

Il envoie F vers H^n(F) et f vers H.map f n. Ce foncteur est additif
(instance `(functorH J n).Additive`).
-/

-- The cohomology functor Sheaf J AddCommGrp >> AddCommGrp.
#check @CategoryTheory.Sheaf.functorH

-- Simps lemma: (functorH J n).map f = ofHom (H.map f n).
#check @CategoryTheory.Sheaf.functorH_map

/-!
## 7. Resultats d'annulation

Deux resultats d'annulation cles :

1. **Faisceau injectif** : si F est injectif, alors H^{n+1}(F) est un subsingleton
   (au plus un element) pour tout n. Cela reflete le fait classique que les
   objets injectifs n'ont pas de cohomologie superieure.
   (Instance dans Mathlib : instance anonyme `[Injective F] : Subsingleton (H F (n + 1))`)

2. **Faisceau nul** : si F est l'objet zero, alors H^n(F) est un subsingleton
   pour tout n. La cohomologie du faisceau nul s'annule en tous les degres.
-/

-- Zero sheaf -> Subsingleton H^n(F).
#check @CategoryTheory.Sheaf.subsingleton_H_of_isZero

/-!
## 8. Theoremes ponts

Theoremes ponts connectant la cohomologie Ext de Mathlib a la verification concrete.
-/

/-- Theoreme pont : la cohomologie de degre zero H^0(F) est additivement
    equivalente aux sections globales F(T) quand T est terminal. C'est
    l'identification fondamentale H^0 = Gamma en cohomologie des faisceaux. -/

noncomputable def H0_equiv_global_sections
    (F : Sheaf J AddCommGrpCat.{w}) {T : C} (hT : IsTerminal T)
    [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})] :
    CategoryTheory.Sheaf.H F 0 ≃+ F.obj.obj (op T) :=
  CategoryTheory.Sheaf.H.equiv₀ F hT

/-- Theoreme pont : le foncteur cohomologie est additif. Pour tous f : F --> G
    et g : F --> G, l'application induite sur la cohomologie verifie
    H.map (f + g) n x = H.map f n x + H.map g n x. -/

theorem H_map_add {F G : Sheaf J AddCommGrpCat.{w}} (f g : F ⟶ G)
    [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    {n : ℕ} (x : CategoryTheory.Sheaf.H F n) :
    CategoryTheory.Sheaf.H.map (f + g) n x =
      CategoryTheory.Sheaf.H.map f n x + CategoryTheory.Sheaf.H.map g n x :=
  CategoryTheory.Sheaf.H.map_add_apply f g x

/-- Theoreme pont : le foncteur cohomologie respecte la composition.
    H.map (f >> g) n = H.map g n . H.map f n. -/

theorem H_map_comp {F G G' : Sheaf J AddCommGrpCat.{w}} (f : F ⟶ G) (g : G ⟶ G')
    [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    {n : ℕ} (x : CategoryTheory.Sheaf.H F n) :
    CategoryTheory.Sheaf.H.map (f ≫ g) n x =
      CategoryTheory.Sheaf.H.map g n (CategoryTheory.Sheaf.H.map f n x) :=
  CategoryTheory.Sheaf.H.map_comp_apply f g x

/-- Theoreme pont : le foncteur cohomologie respecte les identites.
    H.map (1 F) n x = x. -/

theorem H_map_id (F : Sheaf J AddCommGrpCat.{w})
    [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    {n : ℕ} (x : CategoryTheory.Sheaf.H F n) :
    CategoryTheory.Sheaf.H.map (𝟙 F) n x = x :=
  CategoryTheory.Sheaf.H.map_id_apply x

/-- Construction pont : la cohomologie prefaisceautique en un objet X.
    C'est `(F.cohomologyPresheaf n).obj (op X)`, la cohomologie de degre n
    de X a valeurs dans F. -/

noncomputable def cohomologyAt
    (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) (X : C)
    [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})] :
    AddCommGrpCat.{w'} :=
  CategoryTheory.Sheaf.H' F n X

end Grothendieck.SheafCohomology
