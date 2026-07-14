/-
  Tour of vihdzp/combinatorial-games results (EN sibling)
  ========================================================

  English mirror of `CGTTour.lean` (FR-first canonical, cible PR pilote #1
  de l'inventaire I18N Lean, tranche 2 EPIC #4980, PR pilote Option A ratifiée
  2026-07-04 + supersede c.429).

  Convention i18n Lean ratifiée par ai-01 (2026-07-04, issue #4980
  comment-4881909354) : pour chaque `Foo.lean` FR canonique, un sibling
  `Foo_en.lean` préserve le verbatim EN dans le namespace `_en` pour
  (a) permettre la compilation des deux dans le même lake (anti-collision
      namespace `_en` suffix),
  (b) détecter le drift CI entre FR et EN sur le contenu non-docstring
      (code byte-identique obligatoire),
  (c) conserver la version historique EN comme référence pédagogique.

  Scope PR c.429 : 1 sibling créé + 1 ligne lakefile (globs pour
  auto-discovery). Atomicité G.4 respectée (1 sujet = i18n Lean conway_cgt_lean).

  Original FR: https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/conway_cgt_lean/CGTTour.lean
  Issue parente: https://github.com/jsboige/CoursIA/issues/4980
  Inventaire I18N: MyIA.AI.Notebooks/SymbolicAI/Lean/I18N_INVENTORY.md (PR #6090 MERGED)
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

namespace CGTTour_en

open IGame Game Surreal Nimber

/-! ## 1. Combinatorial games

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

`Game` forms an `OrderedAddCommGroup`.
-/
#check @Game.mk
#check (inferInstance : AddCommGroupWithOne Game)
#check (inferInstance : PartialOrder Game)

/-! ## 2. Surreal numbers

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
#check @Surreal.mk
#check (inferInstance : LinearOrder Surreal)
#check @IGame.Fits.equiv_of_forall_not_fits

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
#check @Dyadic.toIGame

/-! ### Ordinal Embedding

Every ordinal embeds into the surreals via `NatOrdinal.toSurreal`.
-/
#check @NatOrdinal.toSurreal

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
#check @Nimber.add_def
#check @Nimber.exists_of_lt_add

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

end CGTTour_en