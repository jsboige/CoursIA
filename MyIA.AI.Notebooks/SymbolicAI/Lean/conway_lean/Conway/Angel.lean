/-
Conway hommage — Le probleme de l'Ange (jeu de poursuite)
John Horton Conway (1937-2020).

Le probleme de l'Ange (Conway, 1996) : sur la grille entiere infinie
ℤ², un Ange de pouvoir `k` peut, a son tour, sauter sur n'importe
quelle case a distance de Chebyshev (coup de roi) `k` ; le Diable mange
une case par tour. L'Ange de pouvoir k donne-t-il la chasse
indefiniment ? Conway a pose les resultats initiaux et le probleme a
ouvert tout un champ ; il fut finalement resolu en 2006 (Bowditch :
pouvoir 4 ; Kloster et Mathe : pouvoir 2 ; Gacs) -- l'Ange de pouvoir
≥ 2 gagne.

NOTE D'ACCESSIBILITE (Epic #1452/#1453) : le THEOREME complet de
victoire est un enonce de jeu infini / non-terminaison sans precedent
Lean -- niveau recherche, PAS une cible prouveur tractable (classe
intractable comme les sorries Gale-Shapley). Ce qui EST accessible,
et fidele a l'hommage, c'est le SETUP : la combinatoire du mouvement
de l'Ange (une boule de Chebyshev), ou l'Ange de pouvoir 1 est
exactement un roi des echecs. Hommage a une contribution MathOverflow
sur les resultats de poursuite de Conway (post 357433).

Tous les `sorry` ont ete elimines (Epic #1453, #1651).
-/

/-
  Convention i18n (EPIC #4980, decision user 2026-07-04) : ce fichier est **FR canonique**,
  avec son miroir anglais dans le fichier sibling `Angel_en.lean` (modele sibling pair
  ratifie 2026-07-04, cf `code-style.md` §Lean i18n). Les enonces de theoremes, les
  tactiques Lean, les noms de lemmes et les references Mathlib restent en anglais (compat
  Mathlib 4) ; seules les docstrings de theoreme et ce bloc d'en-tete different entre
  les deux fichiers.
-/

import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Prod

namespace Conway

/-- Chebyshev (king-move) distance on the integer lattice. -/
def chebyshev (a b : ℤ × ℤ) : ℤ :=
  max (|a.1 - b.1|) (|a.2 - b.2|)

/-- Squares an Angel of power `k` can reach from `p`: the (2k+1)×(2k+1) Chebyshev
    box around `p`, excluding `p` itself (the Angel must move). -/
def angelMoves (k : ℕ) (p : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (p.1 - (k : ℤ)) (p.1 + (k : ℤ))) ×ˢ
   (Finset.Icc (p.2 - (k : ℤ)) (p.2 + (k : ℤ)))).erase p

-- The power-1 Angel is exactly a chess king (8 moves); power-2 has 24.
#eval (angelMoves 1 (0, 0)).card   -- 8
#eval (angelMoves 2 (0, 0)).card   -- 24

/-- Proved anchor: the Chebyshev distance from a square to itself is 0. -/
theorem chebyshev_self (a : ℤ × ℤ) : chebyshev a a = 0 := by
  simp [chebyshev]

/-- CALIBRATION (decide / native_decide): Conway's power-1 Angel is a king — 8 moves. -/
theorem kingMoves_card : (angelMoves 1 (0, 0)).card = 8 := by
  decide

/-- CALIBRATION (decide / native_decide): the power-2 Angel has 24 moves. -/
theorem angelMoves2_card : (angelMoves 2 (0, 0)).card = 24 := by
  decide

/-- CALIBRATION (Finset.card arithmetic, medium): an Angel of power `k` from any
    square has exactly `(2k+1)^2 - 1` moves — the combinatorial heart of the Angel
    problem setup (`card_erase_of_mem` + `card_product` + `Int.card_Icc`). -/
theorem angelMoves_card (k : ℕ) (p : ℤ × ℤ) :
    (angelMoves k p).card = (2 * k + 1) ^ 2 - 1 := by
  simp [angelMoves, Finset.card_product, Int.card_Icc]
  have hx : (p.1 + (k : ℤ) + 1 - (p.1 - (k : ℤ))).toNat = 2 * k + 1 := by omega
  have hy : (p.2 + (k : ℤ) + 1 - (p.2 - (k : ℤ))).toNat = 2 * k + 1 := by omega
  rw [hx, hy]
  rw [pow_two]

end Conway
