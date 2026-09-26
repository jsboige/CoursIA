/-
Conway hommage — Le problème de l'Ange (jeu de poursuite)
John Horton Conway (1937-2020).

Le problème de l'Ange (Conway, 1996) : sur la grille entière infinie
ℤ², un Ange de pouvoir `k` peut, à son tour, sauter sur n'importe
quelle case à distance de Chebyshev (coup de roi) `k` ; le Diable mange
une case par tour. L'Ange de pouvoir k donne-t-il la chasse
indéfiniment ? Conway a posé les résultats initiaux et le problème a
ouvert tout un champ ; il fut résolu en 2007 par trois articles
complémentaires : Bowditch (pouvoir 4), Máthé (pouvoir 2), Kloster
(pouvoir 2, preuve alternative). Gács démontre qu'un Ange de pouvoir
**fini suffisamment grand** gagne (résumé et introduction : « if J is
sufficiently large then the angel has a strategy such that the devil
will never capture her », arXiv:0706.2817 p.1) -- formulation citée
d'après l'archive `2007 - Gács - The Angel Wins.pdf` du gisement
partagé. Le papier ne donne pas de puissance numérique précise.

Bibliographie archivée dans `G:\Mon Drive\MyIA\IA\Bibliographie IA\GameTheory\` :
- `2007 - Gács - The Angel Wins.pdf` (arXiv:0706.2817v1, vérifié)
- MathOverflow 357433 archivé en HTML dans `Technical Web Docs/`
Les papiers paywallés (Bowditch/Máthé/Kloster, Cambridge Core +
Elsevier ScienceDirect) n'ont pas pu être archivés en local faute
d'accès auth ; leurs DOI sont référencés dans le bloc doc-module
(`## LITTERATURE DE REFERENCE`) en fin de fichier.

NOTE D'ACCESSIBILITE (Epic #1452/#1453) : le THEOREME complet de
victoire est un énoncé de jeu infini / non-terminaison sans précédent
Lean -- niveau recherche, PAS une cible prouveur tractable (classe
intraitable comme les sorries Gale-Shapley). Ce qui EST accessible,
et fidèle à l'hommage, c'est le SETUP : la combinatoire du mouvement
de l'Ange (une boule de Chebyshev), où l'Ange de pouvoir 1 est
exactement un roi des échecs. Hommage à une contribution MathOverflow
sur les résultats de poursuite de Conway (post 357433).

Tous les `sorry` de ce fichier ont été éliminés. Le **bloc doc-module** de
fin de fichier documente l'impossibilité du port du théorème de victoire
(EPIC #1452/#1453), la littérature de référence, et l'issue de suivi
#17666 ; le contenu est conservé pour traçabilité documentaire. Les
autres théorèmes (setup combinatoire) restent vérifiés (Epic #1453, #1651).
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

/-- Distance de Chebyshev (coup de roi) sur le réseau entier. -/
def chebyshev (a b : ℤ × ℤ) : ℤ :=
  max (|a.1 - b.1|) (|a.2 - b.2|)

/-- Cases qu'un Ange de pouvoir `k` peut atteindre depuis `p` : le carré Chebyshev
    (2k+1)×(2k+1) autour de `p`, `p` lui-même exclu (l'Ange doit bouger). -/
def angelMoves (k : ℕ) (p : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (p.1 - (k : ℤ)) (p.1 + (k : ℤ))) ×ˢ
   (Finset.Icc (p.2 - (k : ℤ)) (p.2 + (k : ℤ)))).erase p

-- L'Ange de pouvoir 1 est exactement un roi d'échecs (8 coups) ; le pouvoir 2 en a 24.
#eval (angelMoves 1 (0, 0)).card   -- 8
#eval (angelMoves 2 (0, 0)).card   -- 24

/-- Ancre prouvée : la distance de Chebyshev d'une case à elle-même vaut 0. -/
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
    setup du problème de l'Ange (`card_erase_of_mem` + `card_product` + `Int.card_Icc`). -/
theorem angelMoves_card (k : ℕ) (p : ℤ × ℤ) :
    (angelMoves k p).card = (2 * k + 1) ^ 2 - 1 := by
  simp [angelMoves, Finset.card_product, Int.card_Icc]
  have hx : (p.1 + (k : ℤ) + 1 - (p.1 - (k : ℤ))).toNat = 2 * k + 1 := by omega
  have hy : (p.2 + (k : ℤ) + 1 - (p.2 - (k : ℤ))).toNat = 2 * k + 1 := by omega
  rw [hx, hy]
  rw [pow_two]

/-!
# Théorème porte-drapeau INTRINSIC -- Ange k ≥ 2 vs Diable (EPIC #1453)

Ce bloc documente **l'impossibilité de port** Lean du théorème de victoire de
l'Ange de pouvoir `k ≥ 2` contre le Diable. Il tient lieu de `theorem` sans le
produire : pas d'énoncé dans le lac (la section `Conway` reste formellement
vide sur ce point), pas de `sorry` réel.

## ENONCE INTENTIONNEL

`∀ k ≥ 2, ∀ stateInit, l'Ange a une stratégie gagnante sur la grille ℤ².`

## MOTIFS DU NON-PORT (sota-not-workaround §F, mandat user 2026-06-21)

Pas une étape tactique -- une impossibilité portée par le système :

1. **Modèle de jeu** : `Stream' (GameState × ℕ)` (dynamique tour-par-tour infinie)
   n'a pas de représentant Mathlib 4 (`Game` n'existe pas dans Mathlib standard).
2. **Stratégie gagnante** : encoder la stratégie de Máthé (pouvoir 2) ou Bowditch
   (pouvoir 4) nécessite plusieurs pages de maths subtiles -- zones, envahissement
   progressif, bornitude de l'avancée du Diable. Pas de port Lean connu.
3. **Soundness du modèle** : les mathématiciens ont pris 11 ans (1996-2007) pour la
   preuve papier ; la traduction en assistant de preuve reste recherche.

## LITTERATURE DE REFERENCE

Archivée dans `G:\Mon Drive\MyIA\IA\Bibliographie IA\` :

- **Bowditch (2007)** "The Angel Game in the Plane", Combinatorics, Probability and
  Computing 16(3):349-362, DOI:10.1017/s0963548306008297 -- paywall Cambridge Core,
  pas archivé en local.
- **Máthé (2007)** "The Angel of Power 2 Wins", Combinatorics, Probability and
  Computing 16(3):363-374, DOI:10.1017/s0963548306008303 -- paywall Cambridge Core,
  pas archivé en local.
- **Kloster (2007)** "A solution to the Angel Problem", Theoretical Computer Science
  389(1-2):266-277, DOI:10.1016/j.tcs.2007.08.006 -- paywall Elsevier, pas archivé.
- **Gács (2007)** "The Angel Wins", arXiv:0706.2817v1, archivé en local :
  `2007 - Gács - The Angel Wins.pdf`. Vérifié pypdf première page
  (28 pages, 362933 octets, arXiv:0706.2817v1, Peter Gács).

## ISSUE DE SUIVI

`jsboige/CoursIA#17666` -- bibliographie canonique incomplète (3 papiers paywallés).
Réouverture possible si l'un des 3 papiers est obtenu en OA via une voie
institutionnelle. **Pas de `theorem` produit tant que l'énoncé n'est pas
réalisable dans Mathlib 4** (la pseudo-déclaration `True` par `sorry` a été
retirée à la revue ai-01 du 2026-09-26, voir PR #17756 ; le contenu est
conservé ici pour traçabilité documentaire).
-/

end Conway
