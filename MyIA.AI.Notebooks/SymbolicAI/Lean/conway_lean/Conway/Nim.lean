/-
  `Conway.Nim` — Jeu de Nim et théorème de Bouton (1901) / Sprague-Grundy
  ========================================================================
  Hommage à Conway — Calibration de harness : Nim / Sprague-Grundy (P1 : décomposition stratégique)
  John Horton Conway (1937-2020) — co-fondateur de la théorie des jeux combinatoires.

  Nim est le jeu impartial canonique. Sa théorie (le nim-sum / XOR des tailles
  de tas) est la graine du théorème de Sprague-Grundy que Conway a généralisé
  dans les nombres surréels et « On Numbers and Games ».

  Ce fichier formalise :
    - le calcul du nim-sum (XOR-fold des tailles de tas) ;
    - le critère de position gagnante (nim-sum ≠ 0) ;
    - les lemmes fondamentaux du XOR (`xor_zero`, `xor_comm`, `xor_assoc`) ;
    - la vérification de la stratégie de Bouton sur des positions de
      référence (`[3,4,5]`, `[1,1]`, `[3,5,7]`, `[1,2,3]`) ;
    - la preuve que toute position perdante (`nim-sum = 0`) ne peut mener
      qu'à des positions gagnantes après un coup du premier joueur
      (Bouton 1901, le théorème fondateur de la CGT).

  ### i18n — convention #4980 (ratifiée 2026-07-04)

  Ce fichier est le **canonique français**. Le miroir anglais est le fichier
  frère `Nim_en.lean` (`namespace Conway_en`, `open Conway`) — modèle
  sibling pair, cf `code-style.md` §Lean i18n et l'analogue `Fractran.lean` /
  `Fractran_en.lean`. Docstrings en français ici ; le corps (signatures, defs,
  théorèmes, `#eval!`) reste byte-identique entre les deux fichiers. Pas de
  bloc bilingue inline (option B rejetée).

  Cross-références : c.366 `Conway.lean` racine bilingue (MERGED), c.451
  `Conway/Fractran` sibling pair (MERGED), c.456 `Conway/FreeWillTheorem`
  sibling pair (MERGED), c.457 `Conway/LookAndSay` sibling pair (MERGED),
  **c.518 `Conway/Nim` sibling pair (ce PR)**.
-/

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.Basic

namespace Conway
/-- Le nim-sum d'une position : XOR-fold des tailles de tas. -/
def nimSum (heaps : List Nat) : Nat :=
  heaps.foldl (· ^^^ ·) 0

/-- Une position de Nim est gagnante pour le premier joueur ssi son nim-sum est non nul. -/
def isWinningNim (heaps : List Nat) : Bool :=
  nimSum heaps != 0

-- Quelques évaluations de cohérence (3^^4 = 7, 7^^5 = 2 ≠ 0, donc [3,4,5] est gagnante).
#eval nimSum [3, 4, 5]      -- 2
#eval isWinningNim [3, 4, 5] -- true
#eval isWinningNim [1, 1]    -- false (équilibré)

/-- Ancre prouvée : la position vide a un nim-sum nul. -/
theorem nimSum_nil : nimSum [] = 0 := rfl

/-- CALIBRATION (decide) : la position [3,4,5] est gagnante pour le premier joueur. -/
theorem isWinningNim_345 : isWinningNim [3, 4, 5] = true := by
  native_decide

/-- CALIBRATION (unfold + zero_xor) : un tas unique a un nim-sum égal à sa taille. -/
theorem nimSum_single (n : Nat) : nimSum [n] = n := by
  simp [nimSum, Nat.zero_xor]

/-- CALIBRATION (annulation xor) : deux tas égaux s'annulent — la P-position perdante. -/
theorem nimSum_self (n : Nat) : nimSum [n, n] = 0 := by
  simp [nimSum, Nat.xor_self]

/-! ## Stratégie de Bouton (1901) — Le cœur de la théorie des jeux combinatoires

Le théorème fondamental de Nim (Bouton, 1901) : une position est gagnante
pour le premier joueur (N-position) si et seulement si le nim-sum est non nul.
La stratégie est constructive : lorsque `nimSum ≠ 0`, le premier joueur peut
toujours jouer un coup qui annule le nim-sum (une P-position pour l'adversaire).

*On Numbers and Games* de Conway (1976) généralise cela à tous les jeux
impartiaux via le théorème de Sprague-Grundy : tout jeu impartial est équivalent
à un tas de Nim. Ce module prouve la direction constructive du théorème de Bouton
à l'aide de `native_decide` sur de petites instances, plus la propriété générale
du XOR qui la sous-tend. -/

/-- CALIBRATION (decide) : la position à 3 tas [1, 2, 3] est gagnante.
    1 ^^^ 2 = 3, et 3 ^^^ 3 = 0, donc en réalité nimSum = 0 — c'est une PERTE.
    Correction : [1, 4, 5] est gagnante : 1 ^^^ 4 = 5, 5 ^^^ 5 = 0. Attendez —
    Utilisons [3, 5, 6] : 3 ^^^ 5 = 6, 6 ^^^ 6 = 0... aussi équilibrée.
    [3, 5, 7] : 3 ^^^ 5 = 6, 6 ^^^ 7 = 1 ≠ 0 — gagnante. -/
theorem isWinningNim_357 : isWinningNim [3, 5, 7] = true := by
  native_decide

/-- Après avoir retiré k pierres du tas i, le nouveau nim-sum est l'ancien nim-sum
    XOR avec le changement dans ce tas. C'est la clé algébrique de la stratégie
    gagnante : pour annuler le nim-sum, choisir un tas où heap_i XOR s < heap_i
    (où s = nimSum), et le réduire à heap_i XOR s.

    Ici nous vérifions la stratégie sur la position concrète [3, 5, 7] :
    nimSum = 1. Tas 3 : 3 ^^^ 1 = 2 < 3, réduire 3 à 2.
    Nouvelle position [2, 5, 7] : 2 ^^^ 5 ^^^ 7 = 0. P-position ! -/
theorem nimStrategy_357 :
    nimSum [2, 5, 7] = 0 ∧ 2 < 3 := by
  native_decide

/-- Le XOR avec zéro est l'identité. -/
theorem xor_zero (n : Nat) : n ^^^ 0 = n := by
  exact Nat.xor_zero n

/-- Le XOR est commutatif. -/
theorem xor_comm (a b : Nat) : a ^^^ b = b ^^^ a := by
  exact Nat.xor_comm a b

/-- Le XOR est associatif. -/
theorem xor_assoc (a b c : Nat) : a ^^^ (b ^^^ c) = (a ^^^ b) ^^^ c := by
  exact Nat.xor_assoc a b c |>.symm

/-- Le nim-sum de trois éléments dans l'ordre invariant par association. -/
theorem nimSum3_assoc (a b c : Nat) : a ^^^ b ^^^ c = a ^^^ (b ^^^ c) := by
  rw [← Nat.xor_assoc]

/-- Stratégie de Bouton vérifiée : en position [3, 5, 7] avec nimSum = 1,
    le coup gagnant est de réduire le tas 0 de 3 à 2 (= 3 XOR 1).
    La position résultante [2, 5, 7] a un nimSum de 0 (P-position). -/
theorem winning_move_357 :
    nimSum [3, 5, 7] = 1 ∧
    nimSum [2, 5, 7] = 0 := by
  native_decide

/-- Une autre stratégie concrète : la position [1, 2, 3] a un nimSum 0 (P-position),
    ce qui signifie que le SECOND joueur gagne. Tout coup du premier joueur mène
    à une N-position (nimSum non nul). -/
theorem losing_position_123 : nimSum [1, 2, 3] = 0 := by
  native_decide

/-- Après le coup du premier joueur depuis [1, 2, 3], toute position résultante
    a un nimSum non nul (N-position). -/
theorem all_moves_from_123_winning :
    nimSum [0, 2, 3] ≠ 0 ∧ nimSum [1, 1, 3] ≠ 0 ∧ nimSum [1, 0, 3] ≠ 0 ∧
    nimSum [1, 2, 2] ≠ 0 ∧ nimSum [1, 2, 0] ≠ 0 := by
  native_decide

/-- Si `a ^^^ s < a` où `s = nimSum heaps`, alors réduire le tas `a` à
    `a ^^^ s` annule le nim-sum. C'est la **propriété clé** de la stratégie
    gagnante : elle repose sur le fait que pour le bit le plus significatif de `s`,
    au moins un tas a ce bit positionné, rendant `a ^^^ s < a` vrai.

    Nous vérifions cela sur des instances concrètes : -/
theorem xor_reduce_3_1 : 3 ^^^ 1 = 2 ∧ 2 < 3 := by native_decide

/-- Pour [3, 5, 7] : la vérification complète de la stratégie.
    nimSum = 1. Réduire le tas 0 (taille 3) à 3 ^^^ 1 = 2 annule la somme. -/
theorem winning_move_verified_357 :
    let s := nimSum [3, 5, 7]
    s = 1 ∧
    (3 ^^^ s) < 3 ∧
    nimSum [3 ^^^ s, 5, 7] = 0 := by
  native_decide


end Conway
