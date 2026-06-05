/-
  Tour of vihdzp/combinatorial-games Results
  ===========================================

  This file provides a curated tour of the main results formalized in
  vihdzp/combinatorial-games, imported as a Lake dependency.

  Repository: https://github.com/vihdzp/combinatorial-games
  Authors: Violeta Hernandez Palacios (vihdzp)
  License: Apache-2.0

  Historical note:
  This repository superseded Mathlib's CGT modules (SetTheory.Surreal,
  SetTheory.PGame, SetTheory.Game, SetTheory.Nimber), which were deprecated
  in PR #28063 (Aug 2025) and removed in PR #35550 (Feb 2026). The author
  (vihdzp) is the same person who maintained the Mathlib CGT code.

  Key contributions formalized here:
  1. Combinatorial games (IGame, Game, birthday, equivalence, ordering)
  2. Surreal numbers (LinearOrder, simplicity theorem, multiplication, division)
  3. Nimbers (characteristic 2 field, Sprague-Grundy connection)
  4. Dyadic games and ordinal embeddings
-/

-- Core game theory
import CombinatorialGames.Game.Basic
import CombinatorialGames.Game.Birthday
import CombinatorialGames.Game.Order
import CombinatorialGames.Game.Canonical
import CombinatorialGames.Game.Player

-- Surreal numbers
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

/-! ## 1. Combinatorial Games

The formalization is built on two layers:

### IGame (pre-games)
An `IGame` is a combinatorial game defined by its left and right option sets:
```
structure IGame : Type (u+1) where
  left : Set IGame
  right : Set IGame
  [small_left : Small left]
  [small_right : Small right]
```
This is the concrete representation where you can inspect individual moves.

### Game (games up to equivalence)
Two games `x` and `y` are equivalent (`x ≈ y`) when neither player has a
preference -- formally `x ≤ y ∧ y ≤ x`. The quotient type:
```
def Game := Antisymmetrization IGame (· ≤ ·)
```

`Game` forms an `OrderedAddCommGroup`:
-/
#check @Game.mk                               -- IGame → Game (quotient map)
#check (inferInstance : AddCommGroupWithOne Game)
#check (inferInstance : PartialOrder Game)

/-! ## 2. Surreal Numbers

A surreal number is a numeric game quotiented by equivalence:
```
def Surreal := Antisymmetrization (Subtype Numeric) (· ≤ ·)
```

The surreals inherit `≤` and `<` from games, forming a **linear order**.
They form a complete ordered field containing every ordered field as a subfield.

### Simplicity Theorem
If a numeric game `x` fits within `y` (lies between y's left and right options)
but none of its options do, then `x ≈ y`. This is the key tool for computing
surreal values:
```
theorem IGame.Fits.equiv_of_forall_not_fits :
    Numeric x → x.Fits y → (∀ p z ∈ x.moves p, ¬ z.Fits y) → x ≈ y
```
-/
#check @Surreal.mk                            -- IGame → [Numeric] → Surreal
#check (inferInstance : LinearOrder Surreal)   -- Total order on surreals
#check @IGame.Fits.equiv_of_forall_not_fits   -- Simplicity theorem

/-! ### Surreal Arithmetic

The surreals carry full field operations:
- Addition (inherited from Game's AddCommGroup)
- Multiplication (defined in Surreal.Multiplication)
- Division (defined in Surreal.Division)
-/
#check (inferInstance : CommRing Surreal)
#check (inferInstance : LinearOrder Surreal)

/-! ### Dyadic Surreals

Every dyadic rational embeds into the surreals via `Dyadic.toIGame`.
The dyadic surreals are precisely those with finite birthday.
-/
#check @Dyadic.toIGame    -- Dyadic rational → IGame embedding

/-! ### Ordinal Embedding

Every ordinal embeds into the surreals via `NatOrdinal.toSurreal`:
-/
#check @NatOrdinal.toSurreal  -- NatOrdinal ↪o Surreal

/-! ## 3. Nimbers

Nimbers are ordinals equipped with nim arithmetic. They arise from impartial
games via the Sprague-Grundy theorem: every impartial game is equivalent to
some game of nim.

### Definition
```
Nimber = Ordinal (type synonym with nimber addition and multiplication)
```
Notation: `∗o` for `Nimber.of o` (cast from Ordinal).

### Nim Addition
`a + b` is the minimum excluded value (mex) from `{a' + b, a + b'}`:
```
theorem add_def (a b : Nimber) :
    a + b = sInf {x | (∃ a' < a, a' + b = x) ∨ ∃ b' < b, a + b' = x}ᶜ
```
-/
#check @Nimber.add_def          -- mex definition of nim addition
#check @Nimber.exists_of_lt_add -- converse: every smaller value is reached

/-! ### Nimber Field

Nimbers with nim addition and nim multiplication form a **field of
characteristic 2** (every element is its own additive inverse).

The long-term goal of the project is to prove nimbers are algebraically closed.
-/
#check (inferInstance : Field Nimber)

/-! ## 4. Key Differences with the Former Mathlib CGT

The `combinatorial-games` repo represents a substantial expansion:

| Aspect | Mathlib (removed) | combinatorial-games (current) |
|--------|-------------------|-------------------------------|
| Games | `PGame` (basic) | `IGame` (concrete) + `Game` (quotient) |
| Surreals | `Surreal.Basic/Dyadic/Mul` | + Division, Hahn series, Birthday, Pow |
| Nimbers | `Nimber.Basic/Field` | + Nat, SimplestExtension |
| Order | `PGame.Order` | Full `LinearOrder` on surreals |
| Games lib | 8 modules | 15+ modules (Impartial, Loopy, Specific...) |
| Toolchain | v4.x (old) | v4.31.0-rc1 (current) |

Reference: Conway, J.H. - *On Numbers and Games* (2001)

-/

end CGTTour
