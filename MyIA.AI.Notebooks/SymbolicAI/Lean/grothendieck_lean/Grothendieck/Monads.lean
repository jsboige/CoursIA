/-
Grothendieck Partie 26 — Monades et adjonctions monadiques

Alexander Grothendieck (1928-2014).

Extension Phase 2+ (#2159, Epic #1646).

Toute adjonction L ⊣ R (Partie 25) engendre une monade T = R ⋙ L sur la
catégorie de base C. Inversement, toute monade T provient d'une adjonction
(deux factorisations canoniques : Eilenberg-Moore via les algèbres, Kleisli
via les coextensions libres). Grothendieck utilise cette correspondance
dans la théorie des topos (un topos est la catégorie des faisceaux, qui est
monadique sur la catégorie des préfaisceaux via la faisceautisation ⊣
inclusion) et dans la descente (les morphismes de descente effective sont
caractérisés par une propriété monadique du foncteur fibre).

Une monade sur C est un endofoncteur T : C ⥤ C muni d'une unité
η : 𝟭 C ⟶ T et d'une multiplication μ : T ⋙ T ⟶ T satisfaisant les
identités d'unité et d'associativité. C'est « un monoïde dans la catégorie
des endofoncteurs » (formulation de Godement, qui les introduisit en 1958
sous le nom de « constructions standard »).

Mathlib 4 formalise toute cette infrastructure dans
`Mathlib.CategoryTheory.Monad` :
  - `CategoryTheory.Monad : Type*` — la structure T = (T, η, μ)
  - `CategoryTheory.Adjunction.toMonad : (L ⊣ R) → Monad C` — la monade induite
  - `CategoryTheory.Adjunction.adjToMonadIso` — toute monade provient d'une adjonction (à iso près)
  - `CategoryTheory.Monad.Algebra` — la catégorie d'Eilenberg-Moore des algèbres
  - `CategoryTheory.Monad.forget` / `CategoryTheory.Monad.free` — oubli ⊣ libre
  - `CategoryTheory.Monad.Kleisli` — la catégorie de Kleisli
  - `CategoryTheory.Monad.comparison` — le foncteur de comparaison d'Eilenberg-Moore
  - `CategoryTheory.MonadicRightAdjoint` — foncteur monadique (théorème de Beck)

Ce module ré-expose ces faits comme un parcours pédagogique organisé, pour
des apprenants découvrant les monades catégoriques pour la première fois.

Epic #1646, See #2159. Tous les `sorry` éliminés à la création.

### i18n — convention #4980 ratifiée 2026-07-04

Ce module est jumelé avec sa version anglaise canonique dans le fichier
sibling `Monads_en.lean`. Les énoncés de théorèmes, les noms de lemmes,
les tactiques Lean et les références Mathlib restent en anglais. Seules les
**docstrings `/-- ... -/`** et les **commentaires `-- ...`** diffèrent entre
les deux fichiers. Anti-§D byte-identity garanti.
-/

import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Monad.Algebra
import Mathlib.CategoryTheory.Monad.Kleisli

universe v₁ u₁

namespace Grothendieck.Monads

open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

/-!
## 1. La structure de monade

Une monade sur C est un endofoncteur `T : C ⥤ C` muni de l'unité
`η : 𝟭 C ⟶ T` et de la multiplication `μ : T ⋙ T ⟶ T` satisfaisant les
trois axiomes (unité gauche, unité droite, associativité). C'est un monoïde
dans la catégorie monoïdale des endofoncteurs.
-/

-- La structure de monade (T, η, μ) sur une catégorie. On la qualifie
-- pleinement car `Monad` est aussi un typeclass Lean core.
#check @CategoryTheory.Monad

-- L'unité η : 𝟭 C ⟶ T d'une monade (champ `η`).
#check @CategoryTheory.Monad.η

-- La multiplication μ : T ⋙ T ⟶ T d'une monade (champ `μ`).
#check @CategoryTheory.Monad.μ

/-!
## 2. Toute adjonction engendre une monade

Le théorème fondateur : une adjonction `L ⊣ R` (Partie 25) induit une monade
`R ⋙ L` sur C. Réciproquement, toute monade provient d'une adjonction — la
correspondance est essentielle (à isomorphisme près), bouclant le pont
adjonction ↔ monade.
-/

-- La monade R ⋙ L induite par une adjonction L ⊣ R (ici sur une catégorie
-- unique C via la catégorie de Kleisli/Eilenberg-Moore).
#check @CategoryTheory.Adjunction.toMonad

-- Réciproque : toute monade T provient de son adjonction libre ⊣ oubli,
-- et `T.adj.toMonad ≅ T`.
#check @CategoryTheory.Adjunction.adjToMonadIso

/-!
## 3. La catégorie d'Eilenberg-Moore (algèbres)

La catégorie des algèbres d'une monade T est la « solution universelle » au
problème de factoriser T à travers une adjonction. Une T-algèbre est un
objet A muni d'une action `a : T A ⟶ A` compatible avec η (unité) et μ
(associativité). Le foncteur d'oubli oublie l'action ; son adjoint à gauche
construit l'algèbre libre.
-/

-- La structure de T-algèbre (objet sous-jacent A + action a : T A ⟶ A).
#check @CategoryTheory.Monad.Algebra

-- La catégorie d'Eilenberg-Moore des T-algèbres (instance de catégorie),
-- exhibée comme instance `Category` pour toute monade T.
#check fun (T : CategoryTheory.Monad C) ↦ (inferInstance : Category (T.Algebra))

-- Le foncteur d'oubli Algebra T ⥤ C (oublie l'action de la monade).
#check @CategoryTheory.Monad.forget

-- Le foncteur algèbre libre C ⥤ Algebra T (adjoint à gauche de l'oubli).
#check @CategoryTheory.Monad.free

/-!
## 4. L'adjonction libre ⊣ oubli (Eilenberg-Moore)

Le foncteur algèbre libre `free` et le foncteur d'oubli `forget` forment une
adjonction `free ⊣ forget` dont la monade induite est exactement T — c'est
la factorisation canonique d'Eilenberg-Moore.
-/

-- L'adjonction libre ⊣ oubli pour les algèbres d'Eilenberg-Moore.
#check @CategoryTheory.Monad.adj

/-!
## 5. La catégorie de Kleisli

Symétrique d'Eilenberg-Moore : la catégorie de Kleisli est l'autre solution
universelle (les morphismes A ⟶ B dans Kleisli T sont les flèches
A ⟶ T B dans C). Les adjonctions de Kleisli et d'Eilenberg-Moore sont les
deux factorisations extrêmes de la monade T (Kleisli = initiale, Eilenberg-
Moore = terminale parmi les adjonctions qui engendrent T).
-/

-- La catégorie de Kleisli de la monade T (sous `CategoryTheory`, pas `Monad`).
#check @CategoryTheory.Kleisli

/-!
## 6. Théorèmes ponts

Reformulations dans l'espace de noms du projet, pontant les faits Mathlib.
-/

/-- Pont : la monade induite par une adjonction L ⊣ R, vue comme endofoncteur
    de C. C'est l'objet de la monade (sans sa structure η, μ), i.e. le
    composé R ⋙ L vu fonctoriellement. -/
def toMonad_underlying {D : Type u₁} [Category.{v₁} D] {L : C ⥤ D} {R : D ⥤ C}
    (h : L ⊣ R) : C ⥤ C :=
  (h : CategoryTheory.Adjunction L R).toMonad

/-- Pont : le foncteur d'oubli d'Eilenberg-Moore, de la catégorie des
    algèbres vers la catégorie de base. C'est le « bon » foncteur oublieux
    dont la monadicité (théorème de Beck) détecte les catégories de structures
    algébriques (groupes, anneaux, faisceaux). -/
def forget_family (T : CategoryTheory.Monad C) :
    CategoryTheory.Monad.Algebra T ⥤ C :=
  T.forget

/-- Pont : le foncteur algèbre libre, adjoint à gauche du foncteur d'oubli.
    Il incarne la construction « libre » (groupe libre, anneau libre, faisceau
    libre) centrale en algèbre et en géométrie algébrique. -/
def free_family (T : CategoryTheory.Monad C) :
    C ⥤ CategoryTheory.Monad.Algebra T :=
  T.free

end Grothendieck.Monads
