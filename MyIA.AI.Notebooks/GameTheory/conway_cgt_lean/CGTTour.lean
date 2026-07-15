/-
  Tour des résultats de vihdzp/combinatorial-games
  =================================================

  Ce fichier propose une visite guidée des principaux résultats formalisés dans
  vihdzp/combinatorial-games, importé comme dépendance Lake.

  Dépôt : https://github.com/vihdzp/combinatorial-games
  Auteurs : Violeta Hernandez Palacios (vihdzp)
  Licence : Apache-2.0

  Note historique :
  Ce dépôt a remplacé les modules CGT de Mathlib (SetTheory.Surreal,
  SetTheory.PGame, SetTheory.Game, SetTheory.Nimber), dépréciés dans la PR
  #28063 (août 2025) puis retirés dans la PR #35550 (février 2026). L'autrice
  (vihdzp) est la même personne qui maintenait le code CGT de Mathlib.

  Principales contributions formalisées ici :
  1. Jeux combinatoires (IGame, Game, anniversaire, équivalence, ordre)
  2. Nombres surréels (LinearOrder, théorème de simplicité, multiplication, division)
  3. Nimbers (corps de caractéristique 2, connexion Sprague-Grundy)
  4. Jeux dyadiques et plongements ordinaux

  Convention i18n #4980 (sibling pair) : cette racine est FR-seule canonique,
  le jumeau anglais agrégateur est `CGTTour_en.lean`.
-/

-- Théorie des jeux de base
import CombinatorialGames.Game.Basic
import CombinatorialGames.Game.Birthday
import CombinatorialGames.Game.Order
import CombinatorialGames.Game.Canonical
import CombinatorialGames.Game.Player

-- Nombres surréels
import CombinatorialGames.Surreal.Basic
import CombinatorialGames.Surreal.Multiplication
import CombinatorialGames.Surreal.Division
import CombinatorialGames.Surreal.Dyadic
import CombinatorialGames.Surreal.Ordinal

-- Nimbers
import CombinatorialGames.Nimber.Basic
import CombinatorialGames.Nimber.Field

namespace CGTTour

open IGame Game Surreal Nimber

/-! ## 1. Jeux combinatoires

La formalisation repose sur deux couches :

### IGame (pré-jeux)
Un `IGame` est un jeu combinatoire défini par ses ensembles d'options gauches et
droites :
```
structure IGame : Type (u+1) where
  left : Set IGame
  right : Set IGame
  [small_left : Small left]
  [small_right : Small right]
```
C'est la représentation concrète, où l'on peut inspecter les coups individuels.

### Game (jeux à équivalence près)
Deux jeux `x` et `y` sont équivalents (`x ≈ y`) quand aucun joueur n'a de
préférence — formellement `x ≤ y ∧ y ≤ x`. Le type quotient :
```
def Game := Antisymmetrization IGame (· ≤ ·)
```

`Game` forme un `OrderedAddCommGroup` :
-/
#check @Game.mk                               -- IGame → Game (application du quotient)
#check (inferInstance : AddCommGroupWithOne Game)
#check (inferInstance : PartialOrder Game)

/-! ## 2. Nombres surréels

Un nombre surréel est un jeu numérique quotienté par équivalence :
```
def Surreal := Antisymmetrization (Subtype Numeric) (· ≤ ·)
```

Les surréels héritent de `≤` et `<` des jeux, formant un **ordre linéaire**.
Ils forment un corps ordonné complet contenant tout corps ordonné comme sous-corps.

### Théorème de simplicité
Si un jeu numérique `x` tient dans `y` (se situe entre les options gauches et
droites de y) mais qu'aucune de ses options n'y tient, alors `x ≈ y`. C'est
l'outil clé pour calculer les valeurs surréelles :
```
theorem IGame.Fits.equiv_of_forall_not_fits :
    Numeric x → x.Fits y → (∀ p z ∈ x.moves p, ¬ z.Fits y) → x ≈ y
```
-/
#check @Surreal.mk                            -- IGame → [Numeric] → Surreal
#check (inferInstance : LinearOrder Surreal)   -- Ordre total sur les surréels
#check @IGame.Fits.equiv_of_forall_not_fits   -- Théorème de simplicité

/-! ### Arithmétique des surréels

Les surréels portent les opérations complètes d'un corps :
- Addition (héritée du AddCommGroup de Game)
- Multiplication (définie dans Surreal.Multiplication)
- Division (définie dans Surreal.Division)
-/
#check (inferInstance : CommRing Surreal)
#check (inferInstance : LinearOrder Surreal)

/-! ### Surréels dyadiques

Tout rationnel dyadique se plonge dans les surréels via `Dyadic.toIGame`.
Les surréels dyadiques sont exactement ceux d'anniversaire fini.
-/
#check @Dyadic.toIGame    -- Plongement Rationnel dyadique → IGame

/-! ### Plongement ordinal

Tout ordinal se plonge dans les surréels via `NatOrdinal.toSurreal` :
-/
#check @NatOrdinal.toSurreal  -- NatOrdinal ↪o Surreal

/-! ## 3. Nimbers

Les nimbers sont des ordinaux munis de l'arithmétique de nim. Ils proviennent des
jeux impartiaux via le théorème de Sprague-Grundy : tout jeu impartial est
équivalent à une partie de nim.

### Définition
```
Nimber = Ordinal (synonyme de type avec addition et multiplication nimber)
```
Notation : `∗o` pour `Nimber.of o` (conversion depuis Ordinal).

### Addition de nim
`a + b` est la valeur minimale exclue (mex) de `{a' + b, a + b'}` :
```
theorem add_def (a b : Nimber) :
    a + b = sInf {x | (∃ a' < a, a' + b = x) ∨ ∃ b' < b, a + b' = x}ᶜ
```
-/
#check @Nimber.add_def          -- Définition de l'addition de nim par mex
#check @Nimber.exists_of_lt_add -- Réciproque : toute valeur plus petite est atteinte

/-! ### Corps des nimbers

Les nimbers avec addition et multiplication de nim forment un **corps de
caractéristique 2** (chaque élément est son propre opposé pour l'addition).

L'objectif à long terme du projet est de prouver que les nimbers sont
algébriquement clos.
-/
#check (inferInstance : Field Nimber)

/-! ## 4. Différences clés avec l'ancien CGT de Mathlib

Le dépôt `combinatorial-games` représente une expansion substantielle :

| Aspect | Mathlib (retiré) | combinatorial-games (actuel) |
|--------|------------------|------------------------------|
| Jeux | `PGame` (basique) | `IGame` (concret) + `Game` (quotient) |
| Surréels | `Surreal.Basic/Dyadic/Mul` | + Division, séries de Hahn, Anniversaire, Pow |
| Nimbers | `Nimber.Basic/Field` | + Nat, SimplestExtension |
| Ordre | `PGame.Order` | `LinearOrder` complet sur les surréels |
| Bibliothèque de jeux | 8 modules | 15+ modules (Impartial, Loopy, Specific...) |
| Toolchain | v4.x (ancien) | v4.31.0-rc1 (actuel) |

Référence : Conway, J.H. - *On Numbers and Games* (2001)
-/

end CGTTour
