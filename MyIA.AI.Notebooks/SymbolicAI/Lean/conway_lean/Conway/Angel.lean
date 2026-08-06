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

/-- Distance de Chebyshev (coup de roi) sur le reseau entier. -/
def chebyshev (a b : ℤ × ℤ) : ℤ :=
  max (|a.1 - b.1|) (|a.2 - b.2|)

/-- Cases qu'un Ange de pouvoir `k` peut atteindre depuis `p` : le carre Chebyshev
    (2k+1)×(2k+1) autour de `p`, `p` lui-meme exclu (l'Ange doit bouger). -/
def angelMoves (k : ℕ) (p : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (p.1 - (k : ℤ)) (p.1 + (k : ℤ))) ×ˢ
   (Finset.Icc (p.2 - (k : ℤ)) (p.2 + (k : ℤ)))).erase p

-- L'Ange de pouvoir 1 est exactement un roi d'echecs (8 coups) ; le pouvoir 2 en a 24.
#eval (angelMoves 1 (0, 0)).card   -- 8
#eval (angelMoves 2 (0, 0)).card   -- 24

/-- Ancre prouvee : la distance de Chebyshev d'une case a elle-meme vaut 0. -/
theorem chebyshev_self (a : ℤ × ℤ) : chebyshev a a = 0 := by
  simp [chebyshev]

/-- CALIBRATION (decide / native_decide) : l'Ange de pouvoir 1 de Conway est un roi — 8 coups. -/
theorem kingMoves_card : (angelMoves 1 (0, 0)).card = 8 := by
  decide

/-- CALIBRATION (decide / native_decide) : l'Ange de pouvoir 2 a 24 coups. -/
theorem angelMoves2_card : (angelMoves 2 (0, 0)).card = 24 := by
  decide

/-- CALIBRATION (arithmetique Finset.card, moyen) : un Ange de pouvoir `k` depuis
    n'importe quelle case a exactement `(2k+1)^2 - 1` coups — le cœur combinatoire du
    setup du probleme de l'Ange (`card_erase_of_mem` + `card_product` + `Int.card_Icc`). -/
theorem angelMoves_card (k : ℕ) (p : ℤ × ℤ) :
    (angelMoves k p).card = (2 * k + 1) ^ 2 - 1 := by
  simp [angelMoves, Finset.card_product, Int.card_Icc]
  have hx : (p.1 + (k : ℤ) + 1 - (p.1 - (k : ℤ))).toNat = 2 * k + 1 := by omega
  have hy : (p.2 + (k : ℤ) + 1 - (p.2 - (k : ℤ))).toNat = 2 * k + 1 := by omega
  rw [hx, hy]
  rw [pow_two]

end Conway
