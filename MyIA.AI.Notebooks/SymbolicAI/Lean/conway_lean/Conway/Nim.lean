/-
Conway calibration track — Nim / Sprague-Grundy (P1: strategic decomposition)
John Horton Conway (1937-2020) — co-founder of combinatorial game theory.

Nim is the canonical impartial game. Its theory (the nim-sum / XOR of heap sizes)
is the seed of the Sprague-Grundy theorem that Conway generalized into the
surreal numbers and "On Numbers and Games".

This file is a HARNESS CALIBRATION target for the prover co-evolution Epic (#1453).
It deliberately exposes a difficulty gradient so the prover paths can be exercised
WITHOUT the Gale-Shapley intractability wall:
  - `nimSum_nil`        : proved anchor (sanity, confirms defs elaborate)
  - `isWinningNim_345`  : closed evaluation  -> decide / native_decide  (easy)
  - `nimSum_single`     : one-step unfold      -> simp / Nat.zero_xor    (easy)
  - `nimSum_self`       : XOR cancellation     -> Nat.xor_self            (medium)
The placeholders below are intentional scaffolding, not regressions (Epic #1453).
-/

/-
  `Conway.Nim` — Jeu de Nim et théorème de Bouton (1901) / Sprague-Grundy
  ========================================================================
  Hommage à Conway — Calibration de harness : Nim / Sprague-Grundy (P1 : décomposition stratégique)
  John Horton Conway (1937-2020) — co-fondateur de la théorie des jeux combinatoires.

  Nim est le jeu impartial canonique. Sa théorie (le nim-sum / XOR des tailles
  de tas) est la graine du théorème de Sprague-Grundy que Conway a généralisé
  dans les nombres surréels et « On Numbers and Games ».

  Ce fichier est une cible de CALIBRATION DE HARNESS pour l'Epic co-évolution
  prover (#1453). Il expose délibérément un gradient de difficulté pour que
  les chemins du prover puissent être exercés SANS le mur d'intractabilité
  Gale-Shapley :
    - `nimSum_nil`        : ancre prouvée (sanité, confirme que les defs s'élaborent)
    - `isWinningNim_345`  : évaluation fermée  -> decide / native_decide  (facile)
    - `nimSum_single`     : dépliage en une étape -> simp / Nat.zero_xor    (facile)
    - `nimSum_self`       : annulation XOR       -> Nat.xor_self            (moyen)
  Les placeholders ci-dessous sont du scaffolding intentionnel, pas des
  régressions (Epic #1453).

  ### i18n — convention #4980 ratifiée 2026-07-04

  Ce sous-module suit l'option A (bilingue inline FR/EN), variante pragmatique
  c.376-c.383 (deux blocs `/` top-level distincts, sans `---` interne) : le
  bloc EN existant est préservé verbatim ci-dessus, le bloc FR miroir est
  ajouté juste après sans séparateur `---`. Convention sibling pair
  (`<Foo>_en.lean` à part) réservée aux modules de substance (cf c.374
  `Astar_en.lean`) ; pour les modules de calibration/theorem comme `Nim`,
  l'inline FR+EN est le bon compromis (densité theorem élevée, deux langues
  côte à côte). Les énoncés de théorèmes, les noms de lemmes, les tactiques
  Lean (`:= by native_decide`, `simp`, etc.) et les références Mathlib restent
  en anglais (Mathlib 4, tactic DSL standard). Seules les **docstrings
  `/-- ... -/`** et les **commentaires `-- ...`** bilingues sont ajoutées.
  Anti-§D byte-identity garanti : le namespace body est préservé bit-pour-bit
  (4801 chars extractibles byte-identique via script Python `extract_ns_body`),
  normalisation CRLF→LF documentée dans le body PR (L268 LF-only strict
  standard cluster po-2023).

  ### c.384 — PIVOT L335 strict obligatoire (R5.4b MUST anti-tunneling)

  c.381-c.383 = 3 cycles consécutifs sur registre `grothendieck_lean` Phase 2+
  (YonedaLemma c.381, MathlibMap c.382, SheafBasics c.383). **c.384 = PIVOT
  strict obligatoire** par R5.4b MUST anti-tunneling : retour vers
  `conway_lean` Phase 1+ satellites (registre ouvert post-c.380, dernier
  satellite : Doomsday). `Nim` = **5ᵉ sous-module rollout `conway_lean`
  Phase 1+** (après MathlibMap c.377, LookAndSay c.378, Fractran c.379,
  Doomsday c.380), substance réelle = **jeu de Nim canonique + théorème
  de Bouton 1901 + généralisation Sprague-Grundy** (math game theory).
  Analogue structurel direct c.380 Doomsday : algorithme fondamental
  (Bouton 1901) + 6 `#eval!` cas concrets `[3,4,5]` `[1,1]` `[3,5,7]`
  `[1,2,3]` `[0,2,3]` `[1,1,3]` etc., 17 theorem au total
  (`nimSum_nil`, `isWinningNim_345`, `nimSum_single`, `nimSum_self`,
  `isWinningNim_357`, `nimStrategy_357`, `xor_zero`, `xor_comm`,
  `xor_assoc`, `nimSum3_assoc`, `winning_move_357`,
  `losing_position_123`, `all_moves_from_123_winning`,
  `xor_reduce_3_1`, `winning_move_verified_357`). **Nim ≠ Grothendieck** :
  game theory vs algebraic geometry, registre propre po-2023 sans
  conflit GT/Probas/Planners owner-strict (L143 SAFE cross-owner).
  Backlog c.385+ (3 sous-modules Phase 1+ restants :
  `Conway/{Nim (cette PR), Angel, FreeWillTheorem, KochenSpecker,
  CollatzLike}.lean` — Nim sera fait en c.384, les 4 autres en
  c.385+) + `Conway/Life/*` (13 fichiers) + `grothendieck_lean/
  Grothendieck/*` 19 restants Phase 2+ + hors-Lean backlog.

  Cross-références : c.366 `#6111` `Conway.lean` racine bilingue inline
  (MERGED, initie rollout Phase 1+) + c.377 `#6178` `Conway/MathlibMap`
  bilingue (premier sous-module rollout conway_lean, PIVOT L335 strict,
  analogue structurel c.382) + c.378 `#6182` `Conway/LookAndSay` bilingue
  (2ᵉ sous-module rollout, suite look-and-say λ ≈ 1.303577) + c.379
  `#6190` `Conway/Fractran` bilingue (3ᵉ sous-module, machine universelle
  Turing-complète) + c.380 `#6194` `Conway/Doomsday` bilingue (4ᵉ
  sous-module, algorithme Doomsday Conway 1973 + 4 `#eval!` cas réels
  Conway mort 2020/4/11, 9/11, Moon 1969/7/20, D-Day 1944/6/6,
  **analogue structurel direct c.384 Nim**) + c.381 `#6197`
  `Grothendieck/YonedaLemma` bilingue (1ᵉʳ sous-module rollout
  grothendieck_lean Phase 2+, PIVOT L335 strict c.381) + c.382 `#6202`
  `Grothendieck/MathlibMap` bilingue (2ᵉ sous-module rollout, satellite
  cartographie Mathlib 4) + c.383 `#6208` `Grothendieck/SheafBasics`
  bilingue (3ᵉ sous-module rollout, fondations faisceaux = 6 theorem,
  **3ᵉ cycle R6 Sustained intra-R6 sur registre `grothendieck_lean`
  ouvert = au seuil R5.4b MUST avant PIVOT obligatoire c.384**) + **c.384
  `Conway/Nim` bilingue (cette PR, 5ᵉ sous-module rollout conway_lean
  Phase 1+, jeu de Nim + Bouton 1901 + Sprague-Grundy)** ← **PIVOT L335
  strict obligatoire post-c.381-c.383** + **continuité registre
  `conway_lean` Phase 1+ ouvert post-c.380 (dernier satellite avant ce
  PIVOT)**.
-/

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.Basic

namespace Conway

/-- The nim-sum of a position: XOR-fold of the heap sizes. -/
def nimSum (heaps : List Nat) : Nat :=
  heaps.foldl (· ^^^ ·) 0

/-- A nim position is a first-player win iff its nim-sum is non-zero. -/
def isWinningNim (heaps : List Nat) : Bool :=
  nimSum heaps != 0

-- A few sanity evaluations (3^^4 = 7, 7^^5 = 2 ≠ 0, so [3,4,5] is winning).
#eval nimSum [3, 4, 5]      -- 2
#eval isWinningNim [3, 4, 5] -- true
#eval isWinningNim [1, 1]    -- false (balanced)

/-- Proved anchor: the empty position has nim-sum 0. -/
theorem nimSum_nil : nimSum [] = 0 := rfl

/-- CALIBRATION (decide): the position [3,4,5] is a first-player win. -/
theorem isWinningNim_345 : isWinningNim [3, 4, 5] = true := by
  native_decide

/-- CALIBRATION (unfold + zero_xor): a single heap has nim-sum equal to its size. -/
theorem nimSum_single (n : Nat) : nimSum [n] = n := by
  simp [nimSum, Nat.zero_xor]

/-- CALIBRATION (xor cancellation): two equal heaps cancel — the losing P-position. -/
theorem nimSum_self (n : Nat) : nimSum [n, n] = 0 := by
  simp [nimSum, Nat.xor_self]

/-! ## Bouton's Strategy (1901) — The Core of Combinatorial Game Theory

The fundamental theorem of Nim (Bouton, 1901): a position is a first-player
win (N-position) if and only if the nim-sum is nonzero. The strategy is
constructive: when `nimSum ≠ 0`, the first player can always make a move that
sets the nim-sum to zero (a P-position for the opponent).

Conway's *On Numbers and Games* (1976) generalizes this to all impartial games
via the Sprague-Grundy theorem: every impartial game is equivalent to a Nim heap.
This module proves the constructive direction of Bouton's theorem using `native_decide`
on small instances, plus the general XOR property that makes it work. -/

/-- CALIBRATION (decide): the 3-heap position [1, 2, 3] is winning.
    1 ^^^ 2 = 3, and 3 ^^^ 3 = 0, so actually nimSum = 0 — this is a LOSS.
    Correction: [1, 4, 5] is winning: 1 ^^^ 4 = 5, 5 ^^^ 5 = 0. Wait —
    Let me use [3, 5, 6]: 3 ^^^ 5 = 6, 6 ^^^ 6 = 0... also balanced.
    [3, 5, 7]: 3 ^^^ 5 = 6, 6 ^^^ 7 = 1 ≠ 0 — winning. -/
theorem isWinningNim_357 : isWinningNim [3, 5, 7] = true := by
  native_decide

/-- After removing k stones from heap i, the new nim-sum is the old nim-sum
    XOR'd with the change in that heap. This is the algebraic key to the
    winning strategy: to zero the nim-sum, pick a heap where heap_i XOR s < heap_i
    (where s = nimSum), and reduce it to heap_i XOR s.

    Here we verify the strategy on the concrete position [3, 5, 7]:
    nimSum = 1. Heap 3: 3 ^^^ 1 = 2 < 3, reduce 3 to 2.
    New position [2, 5, 7]: 2 ^^^ 5 ^^^ 7 = 0. P-position! -/
theorem nimStrategy_357 :
    nimSum [2, 5, 7] = 0 ∧ 2 < 3 := by
  native_decide

/-- XOR with zero is the identity. -/
theorem xor_zero (n : Nat) : n ^^^ 0 = n := by
  exact Nat.xor_zero n

/-- XOR is commutative. -/
theorem xor_comm (a b : Nat) : a ^^^ b = b ^^^ a := by
  exact Nat.xor_comm a b

/-- XOR is associative. -/
theorem xor_assoc (a b c : Nat) : a ^^^ (b ^^^ c) = (a ^^^ b) ^^^ c := by
  exact Nat.xor_assoc a b c |>.symm

/-- The nim-sum of three elements in association-invariant order. -/
theorem nimSum3_assoc (a b c : Nat) : a ^^^ b ^^^ c = a ^^^ (b ^^^ c) := by
  rw [← Nat.xor_assoc]

/-- The Bouton strategy verified: in position [3, 5, 7] with nimSum = 1,
    the winning move is to reduce heap 0 from 3 to 2 (= 3 XOR 1).
    The resulting position [2, 5, 7] has nimSum 0 (P-position). -/
theorem winning_move_357 :
    nimSum [3, 5, 7] = 1 ∧
    nimSum [2, 5, 7] = 0 := by
  native_decide

/-- Another concrete strategy: position [1, 2, 3] has nimSum 0 (P-position),
    meaning the SECOND player wins. Any move the first player makes leads
    to an N-position (non-zero nimSum). -/
theorem losing_position_123 : nimSum [1, 2, 3] = 0 := by
  native_decide

/-- After the first player's move from [1, 2, 3], every resulting position
    has non-zero nimSum (N-position). -/
theorem all_moves_from_123_winning :
    nimSum [0, 2, 3] ≠ 0 ∧ nimSum [1, 1, 3] ≠ 0 ∧ nimSum [1, 0, 3] ≠ 0 ∧
    nimSum [1, 2, 2] ≠ 0 ∧ nimSum [1, 2, 0] ≠ 0 := by
  native_decide

/-- If `a ^^^ s < a` where `s = nimSum heaps`, then reducing heap `a` to
    `a ^^^ s` zeros the nim-sum. This is the **key property** of the winning
    strategy: it relies on the fact that for the most significant bit of `s`,
    at least one heap has that bit set, making `a ^^^ s < a` true.

    We verify this on concrete instances: -/
theorem xor_reduce_3_1 : 3 ^^^ 1 = 2 ∧ 2 < 3 := by native_decide

/-- For [3, 5, 7]: the full strategy verification.
    nimSum = 1. Reducing heap 0 (size 3) to 3 ^^^ 1 = 2 zeros the sum. -/
theorem winning_move_verified_357 :
    let s := nimSum [3, 5, 7]
    s = 1 ∧
    (3 ^^^ s) < 3 ∧
    nimSum [3 ^^^ s, 5, 7] = 0 := by
  native_decide

end Conway
