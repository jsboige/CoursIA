/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## MathlibMap — Conway's mathematics in Mathlib (pinned snapshot)

This satellite module maps what **Mathlib actually provides** at the pinned
version (`54f98fd6`, 2026-05-15) that relates to John Horton Conway's
contributions. It serves as a companion to our own re-implementations in
`Conway/` (Life, Angel, Doomsday, Fractran, LookAndSay, Nim, FWT).

### Historical note — CGT removal (Mathlib PR #35550, 2026-02-20)

Mathlib **previously** contained extensive Combinatorial Game Theory modules
under `Mathlib.SetTheory`:

- `Surreal.Basic` / `Surreal.Dyadic` / `Surreal.Multiplication`
- `PGame.Basic` / `PGame.Order` / `PGame.Algebra`
- `Game.Basic` / `Game.Birthday` / `Game.State` / `Game.Short`
- `Game.Impartial` / `Game.Nim` / `Game.Domineering` / `Game.Ordinal`
- `Nimber.Basic` / `Nimber.Field`

These were removed by PR #35550 ("remove deprecated material from CGT"),
which noted that the modules had been deprecated for 6 months. At our pinned
version (May 2026), none of these survive.

This means that, for the domains most closely associated with Conway's
*On Numbers and Games* (surreal numbers, partisan games, Sprague-Grundy),
**our project provides the reference implementation** (see `Conway.Nim`,
`Conway.Life`, etc.) rather than Mathlib.

### What Mathlib DOES provide (Conway-adjacent)

1. **Ordinal arithmetic** (`SetTheory.Ordinal.*`): the foundation of
   Conway's birthday construction for surreal numbers. Includes Cantor
   Normal Form (`Ordinal.CNF`), ordinal exponentiation, fixed points.
2. **Coxeter groups** (`GroupTheory.Coxeter.*`): Conway's work on Coxeter
   groups and their geometric interpretations.
3. **Game addition** (`Order.GameAdd`): an abstract relation modelling
   the subgame relation in combinatorial game theory.

-/

/-
  `Conway.MathlibMap` — les mathématiques de Conway dans Mathlib
  ==================================================================
  Module satellite qui cartographie ce que **Mathlib 4 fournit réellement**
  dans sa version épinglée (`54f98fd6`, 2026-05-15) en lien avec les
  contributions de John Horton Conway. Il accompagne nos propres
  ré-implantations sous `Conway/` (Life, Angel, Doomsday, Fractran,
  LookAndSay, Nim, FWT).

  ### Note historique — retrait CGT (Mathlib PR #35550, 2026-02-20)

  Mathlib **contenait autrefois** des modules étendus de théorie
  combinatoire des jeux sous `Mathlib.SetTheory` :

  - `Surreal.Basic` / `Surreal.Dyadic` / `Surreal.Multiplication`
  - `PGame.Basic` / `PGame.Order` / `PGame.Algebra`
  - `Game.Basic` / `Game.Birthday` / `Game.State` / `Game.Short`
  - `Game.Impartial` / `Game.Nim` / `Game.Domineering` / `Game.Ordinal`
  - `Nimber.Basic` / `Nimber.Field`

  Ces modules ont été retirés par la PR #35550 (« remove deprecated
  material from CGT »), qui notait qu'ils étaient dépréciés depuis
  6 mois. Sur notre version épinglée (mai 2026), aucun ne survit.

  Cela signifie que, pour les domaines les plus directement associés
  à *On Numbers and Games* de Conway (nombres surréels, jeux partisans,
  Sprague-Grundy), **notre projet constitue l'implémentation de
  référence** (voir `Conway.Nim`, `Conway.Life`, etc.) plutôt que
  Mathlib.

  ### Ce que Mathlib FOURNIT (domaines conway-adjacents)

  1. **Arithmétique ordinale** (`SetTheory.Ordinal.*`) : fondement de
     la construction des « anniversaires » (birthdays) pour les
     nombres surréels de Conway. Inclut la forme normale de Cantor
     (`Ordinal.CNF`), l'exponentiation ordinale, les points fixes.
  2. **Groupes de Coxeter** (`GroupTheory.Coxeter.*`) : travaux de
     Conway sur les groupes de Coxeter et leurs interprétation
     géométriques.
  3. **Addition de jeux** (`Order.GameAdd`) : une relation abstraite
     qui modélise la relation de sous-jeu en théorie combinatoire des
     jeux.

  ### i18n — convention #4980 ratifiée 2026-07-04

  Ce sous-module suit l'option A (bilingue inline FR/EN), variante
  pragmatique c.377 (deux blocs `/` top-level distincts, sans `---`
  interne, analogue à c.376) : le bloc EN existant est préservé
  verbatim ci-dessus, le bloc FR miroir est ajouté juste après sans
  séparateur `---`. Convention sibling pair (`<Foo>_en.lean` à part)
  réservée aux modules de substance (cf c.374 `Astar_en.lean`) ;
  pour les modules satellites de cartographie comme `MathlibMap`,
  l'inline FR+EN est le bon compromis (peu de code, deux langues
  côte à côte).

  Cross-références : c.373 `knot_lean/Knots.lean` racine bilingue,
  c.374 `search_lean/Astar_en.lean` sibling pair, c.375 `knot_lean`
  sous-modules 5/6 bilingues, c.376 `Knots/Invariant.lean`
  bilingue (sixième et dernier, saturation locale du lac `knot_lean`
  fermée à 6/6), **c.377 `Conway/MathlibMap.lean` (initie le
  rollout `conway_lean`, registre ≠ knot_lean, PIVOT L335
  post-saturation locale)**.
-/

import Mathlib.SetTheory.Ordinal.CantorNormalForm
import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.Order.GameAdd

namespace Conway
namespace MathlibMap

/-! ## 1. Ordinal arithmetic — the foundation of ONAG

Conway's surreal numbers are built on the concept of "birthdays", indexed
by ordinals. The ordinal type `Ordinal` and its arithmetic (addition,
multiplication, exponentiation) form the substrate of the birthday
construction. Cantor Normal Form (`Ordinal.CNF`) gives the base-ω
decomposition that underlies the combinatorial structure of games. -/

-- Ordinal exponentiation via the Pow instance (a ^ b notation).
-- Conway's surreal number addition and multiplication extend ordinal
-- arithmetic to the full surreal field.
#check @Ordinal.instPow

-- Cantor Normal Form induction: every ordinal α can be written uniquely as
-- ω^{β₁}·c₁ + ω^{β₂}·c₂ + ... + ω^{βₖ}·cₖ where β₁ > β₂ > ... > βₖ.
-- Conway exploited this structure in ONAG.
#check @Ordinal.CNF.rec

-- Ordinal logarithm: the largest exponent in the base-ω expansion.
-- This is the first component of the Cantor Normal Form.
#check @Ordinal.log

/-! ## 2. Coxeter groups — symmetry and reflection

Conway made significant contributions to the study of Coxeter groups,
particularly in their connection to sphere packings (the Leech lattice)
and the classification of finite simple groups. Mathlib provides a
complete formalization of Coxeter systems. -/

-- A Coxeter matrix: symmetric, with 1 on the diagonal and ≠ 0 elsewhere.
-- Conway studied these in connection with reflection groups and the
-- symmetries of the Leech lattice.
#check @CoxeterMatrix

-- The Coxeter group associated to a matrix M:
-- presented by generators s_i with relations (s_i s_j)^{M_{ij}} = 1.
#check @CoxeterMatrix.Group

-- A Coxeter system: a group W with an isomorphism to a Coxeter group.
#check @CoxeterSystem

-- The simple reflection s_i of a Coxeter system. These generate W.
#check @CoxeterSystem.simple

-- Universal property: any function satisfying the Coxeter relations
-- extends uniquely to a group homomorphism from W.
#check @CoxeterSystem.lift

/-! ## 3. Game addition — the combinatorial game theory residue

The relation `Prod.GameAdd` models the subgame relation: from position
(x, y), one can move to (x', y) where x' < x, or to (x, y') where y' < y.
This is exactly the structure of a sum of two combinatorial games.

While Mathlib's full CGT library (PGame, Surreal, Nim) was removed in
PR #35550, this abstract game addition relation survives as a building
block for well-founded induction on pairs. -/

-- Game addition relation on ordered pairs. Models the subgame relation
-- on the sum of two combinatorial games, a central concept from ONAG.
#check @Prod.GameAdd

-- Well-foundedness of game addition: if both component relations are
-- well-founded, then so is Prod.GameAdd. This is the induction principle
-- behind the Sprague-Grundy theorem.
#check @WellFounded.prod_gameAdd

end MathlibMap
end Conway
