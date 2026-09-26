/-
Conway hommage — Le probleme de l'Ange (jeu de poursuite)
John Horton Conway (1937-2020).

Le probleme de l'Ange (Conway, 1996) : sur la grille entiere infinie
ℤ², un Ange de pouvoir `k` peut, a son tour, sauter sur n'importe
quelle case a distance de Chebyshev (coup de roi) `k` ; le Diable mange
une case par tour. L'Ange de pouvoir k donne-t-il la chasse
indefiniment ? Conway a pose les resultats initiaux et le probleme a
ouvert tout un champ ; il fut resolu en 2007 par trois articles
complementaires : Bowditch (pouvoir 4), Mathe (pouvoir 2), Kloster
(pouvoir 2, preuve alternative). Gacs demontre qu'un Ange de pouvoir
**fini suffisamment grand** gagne (theoreme 1 : « for sufficiently
large J, the angel has a strategy such that the devil will never
capture her », arXiv:0706.2817 p.1) -- formulation citee d'apres
l'archive `2007 - Gacs - The Angel Wins.pdf` du gisement partage.
Le papier ne donne pas de puissance numerique precise. -- l'Ange
de pouvoir ≥ 2 gagne.

Bibliographie archivee dans `G:\Mon Drive\MyIA\IA\Bibliographie IA\GameTheory\` :
- `2007 - Gacs - The Angel Wins.pdf` (arXiv:0706.2817v1, verifie)
- MathOverflow 357433 archive en HTML dans `Technical Web Docs/`
Les papiers paywalles (Bowditch/Mathe/Kloster, Cambridge Core +
Elsevier ScienceDirect) n'ont pas pu etre archives en local faute
d'acces auth ; leurs DOI sont references dans le bloc litteraire
ci-dessous (`## LITTERATURE DE REFERENCE` du module doc).

NOTE D'ACCESSIBILITE (Epic #1452/#1453) : le THEOREME complet de
victoire est un enonce de jeu infini / non-terminaison sans precedent
Lean -- niveau recherche, PAS une cible prouveur tractable (classe
intractable comme les sorries Gale-Shapley). Ce qui EST accessible,
et fidele a l'hommage, c'est le SETUP : la combinatoire du mouvement
de l'Ange (une boule de Chebyshev), ou l'Ange de pouvoir 1 est
exactement un roi des echecs. Hommage a une contribution MathOverflow
sur les resultats de poursuite de Conway (post 357433).

Tous les sorries de ce fichier ont ete elimines (revue ai-01 du
2026-09-26, PR #17756). La pseudo-declaration `True` par `sorry`
qui portait l'enonce du theoreme de victoire (intractable en
Lean 4 v4.33.0 local, classe `INTRINSIC`) a ete retirees des deux
siblings ; son contenu (enonce, motifs du non-port, litterature)
est conserve dans le bloc doc ci-dessous pour traçabilite
documentaire. Les autres theoremes de ce fichier (setup
combinatoire) restent verifies (Epic #1453, #1651).
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

/-!
# Theoreme porte-drapeau INTRINSIC -- Ange k ≥ 2 vs Diable (EPIC #1453)

Ce bloc documente **l'impossibilite de port** Lean du theoreme de victoire de
l'Ange de pouvoir `k ≥ 2` contre le Diable. Il tient lieu de `theorem` sans le
produire : pas d'enonce dans le lac (la section `Conway` reste formellement
vide sur ce point), pas de `sorry` reel.

## ENONCE INTENTIONNEL

`∀ k ≥ 2, ∀ stateInit, l'Ange a une strategie gagnante sur la grille ℤ².`

## MOTIFS DU NON-PORT (sota-not-workaround §F, mandat user 2026-06-21)

Pas une etape tactique -- une impossibilite portee par le systeme :

1. **Modele de jeu** : `Stream' (GameState × ℕ)` (dynamique tour-par-tour infinie)
   n'a pas de representant Mathlib 4 (`Game` n'existe pas dans Mathlib standard).
2. **Strategie gagnante** : encoder la strategie de Mathe (pouvoir 2) ou Bowditch
   (pouvoir 4) necessite plusieurs pages de maths subtiles -- zones, envahissement
   progressif, bornitude de l'avancee du Diable. Pas de port Lean connu.
3. **Soundness du modele** : les mathematiciens ont pris 11 ans (1996-2007) pour la
   preuve papier ; la traduction en assistant de preuve reste recherche.

## LITTERATURE DE REFERENCE

Archivee dans `G:\Mon Drive\MyIA\IA\Bibliographie IA\` :

- **Bowditch (2007)** "The Angel Game in the Plane", Combinatorics, Probability and
  Computing 16(3):349-362, DOI:10.1017/s0963548306008297 -- paywall Cambridge Core,
  pas archive en local.
- **Mathe (2007)** "The Angel of Power 2 Wins", Combinatorics, Probability and
  Computing 16(3):363-374, DOI:10.1017/s0963548306008303 -- paywall Cambridge Core,
  pas archive en local.
- **Kloster (2007)** "A solution to the Angel Problem", Theoretical Computer Science
  389(1-2):266-277, DOI:10.1016/j.tcs.2007.08.006 -- paywall Elsevier, pas archive.
- **Gacs (2007)** "The Angel Wins", arXiv:0706.2817v1, archive en local :
  `2007 - Gacs - The Angel Wins.pdf`. Verifie pypdf premiere page
  (28 pages, 362933 octets, arXiv:0706.2817v1, Peter Gacs).

## ISSUE DE SUIVI

`jsboige/CoursIA#17666` -- bibliographie canonique incomplete (3 papiers paywalles).
Reouverture possible si l'un des 3 papiers est obtenu en OA via une voie
institutionnelle. **Pas de `theorem` produit tant que l'enonce n'est pas
realisable dans Mathlib 4** (la pseudo-declaration `True` par `sorry` a ete
retiree a la revue ai-01 du 2026-09-26, voir PR #17756 ; le contenu est
conserve ici pour traçabilite documentaire).
-/

end Conway
