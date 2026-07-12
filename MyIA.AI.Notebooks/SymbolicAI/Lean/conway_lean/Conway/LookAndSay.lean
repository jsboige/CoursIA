/-
Conway's Look-and-Say Sequence
John Horton Conway (1937-2020)

The look-and-say sequence starts with "1". Each subsequent term describes the
previous term by reading off consecutive digit groups:
  1 → 11 → 21 → 1211 → 111221 → 312211 → 13112221 → ...

Conway proved remarkable properties:
- The ratio |a(n+1)| / |a(n)| converges to Conway's constant λ ≈ 1.303577...
- λ is the unique positive real root of a degree-71 polynomial
- The sequence splits into exactly 92 "atomic elements" (named after chemical elements)

This file formalizes the sequence generation and verifies the first terms.
-/

/-
  `Conway.LookAndSay` — La suite look-and-say de Conway
  ======================================================
  La suite look-and-say démarre avec « 1 ». Chaque terme suivant décrit le
  terme précédent en lisant à voix haute les groupes de chiffres consécutifs :
    1 → 11 → 21 → 1211 → 111221 → 312211 → 13112221 → ...

  Conway a démontré des propriétés remarquables :
  - Le rapport |a(n+1)| / |a(n)| converge vers la constante de Conway
    λ ≈ 1.303577...
  - λ est l'unique racine réelle positive d'un polynôme de degré 71
  - La suite se décompose en exactement 92 « éléments atomiques » (nommés
    d'après les éléments chimiques)

  Ce fichier formalise la génération de la suite et vérifie les premiers
  termes.

  ### i18n — convention #4980 ratifiée 2026-07-04

  Ce sous-module suit l'option A (bilingue inline FR/EN), variante pragmatique
  c.378 (deux blocs `/` top-level distincts, sans `---` interne, analogue
  c.376/c.377) : le bloc EN existant est préservé verbatim ci-dessus, le bloc
  FR miroir est ajouté juste après sans séparateur `---`. Convention sibling
  pair (`<Foo>_en.lean` à part) réservée aux modules de substance (cf c.374
  `Astar_en.lean`) ; pour les modules de formalisation comme `LookAndSay`,
  l'inline FR+EN est le bon compromis (peu de code, deux langues côte à côte).

  Cross-références : c.366 `Conway.lean` racine bilingue (MERGED), c.373
  `Knots.lean` racine bilingue, c.374 `Astar.lean` sibling pair, c.375
  `Knots` sub-modules bilingues, c.376 `Knots/Invariant` bilingue (saturation
  locale du lac `knot_lean` à 6/6), c.377 `Conway/MathlibMap` bilingue
  (premier sous-module rollout `conway_lean`, PIVOT L335 strict), **c.378
  `Conway/LookAndSay` bilingue (suite rollout `conway_lean` Phase 1+)**.
-/

import Mathlib.Data.List.Basic

namespace Conway

/-- Split a number into its decimal digits (most significant first).
  1211 → [1, 2, 1, 1]  -/
def natToDigits (n : Nat) : List Nat :=
  if n = 0 then []
  else natToDigits (n / 10) ++ [n % 10]
  termination_by n
  decreasing_by omega

/-- Convert a list of digits (most significant first) to a Nat.
  [1, 2, 1, 1] → 1211 -/
def digitsToNat : List Nat → Nat
  | [] => 0
  | d :: ds => d * 10 ^ ds.length + digitsToNat ds

/-- Run-length encode a list: group consecutive equal elements.
  [1, 1, 2, 2, 2, 1] → [(2, 1), (3, 2), (1, 1)]
  Uses fuel to satisfy the termination checker. -/
def runLengthAux : Nat → List Nat → List (Nat × Nat)
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, a :: as =>
    match as.span (· = a) with
    | (eqs, rest) => (eqs.length + 1, a) :: runLengthAux fuel rest

/-- Run-length encode a list (wrapper with sufficient fuel). -/
def runLength (l : List Nat) : List (Nat × Nat) :=
  runLengthAux (l.length + 1) l

/-- Flatten (count, digit) pairs into a digit list: [(2,1), (3,2)] → [2,1,3,2] -/
def flattenPairs : List (Nat × Nat) → List Nat
  | [] => []
  | (count, digit) :: rest =>
    natToDigits count ++ [digit] ++ flattenPairs rest

/-- One step of the look-and-say transformation.
  Read digits left-to-right, output run-length encoding as a number. -/
def lookAndSayStep (n : Nat) : Nat :=
  if n = 0 then 0
  else digitsToNat (flattenPairs (runLength (natToDigits n)))

/-- Generate the n-th look-and-say number (0-indexed, seed = 1) -/
def lookAndSay : Nat → Nat
  | 0 => 1
  | n + 1 => lookAndSayStep (lookAndSay n)

-- Verify the first 6 terms of the look-and-say sequence
#eval! lookAndSay 0  -- 1
#eval! lookAndSay 1  -- 11
#eval! lookAndSay 2  -- 21
#eval! lookAndSay 3  -- 1211
#eval! lookAndSay 4  -- 111221
#eval! lookAndSay 5  -- 312211

end Conway
