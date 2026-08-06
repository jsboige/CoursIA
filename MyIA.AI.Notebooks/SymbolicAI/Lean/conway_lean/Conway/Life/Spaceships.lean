/-
Copyright (c) 2026 CoursIA. Tous droits reserves.
Distribue sous licence Apache 2.0 comme decrit dans le fichier LICENSE.

## Jeu de la Vie de Conway — Vaisseaux spatiaux (spaceships)

Vaisseaux Leger, Moyen et Lourd (LWSS, MWSS, HWSS).
Vaisseaux de periode 4, chacun translatant de 2 cellules horizontalement par periode.

Decouverts au debut de l'histoire du Jeu de la Vie (Conway,
Guy, Berlekamp ; Cambridge 1970), ils sont parmi les vaisseaux
spatiaux les plus communs dans la nature. Avec le planeur (glider),
ils forment la famille des vaisseaux de periode 4 et deplacement 2
de la regle B3/S23.

Convention de coordonnees (heritee de `Conway.Life`) :
- Chaque cellule est une paire `(row, col) : Int × Int`.
- Les motifs sont stockes en `List (Int × Int)` dans l'ordre
  lexicographique trie (row d'abord, puis col) pour que `step`
  produise une liste dans le meme ordre, permettant a
  `decide` (kernel natif) de verifier l'egalite par comparaison structurelle.
- Un deplacement `(dr, dc)` translate chaque cellule de `dr` lignes
  et `dc` colonnes. Les vaisseaux ci-dessous vont vers l'est :
  `dr = 0`, `dc = 2`.

Ce module est entierement prouve (aucun gap).
-/

/-
  Convention i18n (EPIC #4980, decision user 2026-07-04) : ce fichier est **FR canonique**,
  avec son miroir anglais dans le fichier sibling `Spaceships_en.lean` (modele sibling
  pair ratifie 2026-07-04, cf `code-style.md` §Lean i18n). Les enonces de theoremes,
  les tactiques Lean, les noms de lemmes et les references Mathlib restent en anglais
  (compat Mathlib 4) ; seules les docstrings de theoreme et ce bloc d'en-tete different
  entre les deux fichiers.
-/

import Conway.Life

namespace Conway
namespace Life

/-! ## Vaisseau leger (LWSS)

Le plus petit vaisseau de periode 4 apres le planeur, avec 9 cellules vivantes.
Phase 1 (vers l'est) :

```
.OOOO
O...O
....O
O..O.
```

Apres 4 generations le motif reapparait, translate de `(0, 2)`.
-/

/-- The **LWSS** (Lightweight Spaceship), phase 1, east-bound. -/
def lwss : Grid :=
  [(0, 1), (0, 2), (0, 3), (0, 4),
   (1, 0), (1, 4),
   (2, 4),
   (3, 0), (3, 3)]

-- Sanity checks (computed by the elaborator, not part of the proof).
#eval lwss
#eval evolve 4 lwss
#eval shift (0, 2) lwss
#eval isSpaceship lwss 4 (0, 2)

/-- The LWSS is a spaceship of period 4 and displacement `(0, 2)`. -/
theorem lwss_spaceship : isSpaceship lwss 4 (0, 2) = true := by decide

/-! ## Vaisseau moyen (MWSS)

Un vaisseau de periode 4 avec 11 cellules vivantes : LWSS etendu d'une colonne
et couronne d'une cellule "chapeau". Phase 1 (vers l'est) :

```
.OOOOO
O....O
.....O
O...O.
..O...
```

Apres 4 generations le motif reapparait, translate de `(0, 2)`.
-/

/-- The **MWSS** (Middleweight Spaceship), phase 1, east-bound. -/
def mwss : Grid :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5),
   (1, 0), (1, 5),
   (2, 5),
   (3, 0), (3, 4),
   (4, 2)]

#eval mwss
#eval evolve 4 mwss
#eval shift (0, 2) mwss
#eval isSpaceship mwss 4 (0, 2)

/-- The MWSS is a spaceship of period 4 and displacement `(0, 2)`. -/
theorem mwss_spaceship : isSpaceship mwss 4 (0, 2) = true := by decide

/-! ## Vaisseau lourd (HWSS)

Un vaisseau de periode 4 avec 13 cellules vivantes : LWSS etendu de deux colonnes
et couronne d'un "chapeau" a deux cellules. Phase 1 (vers l'est) :

```
.OOOOOO
O.....O
......O
O....O.
..OO...
```

Apres 4 generations le motif reapparait, translate de `(0, 2)`.
-/

/-- The **HWSS** (Heavyweight Spaceship), phase 1, east-bound. -/
def hwss : Grid :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6),
   (1, 0), (1, 6),
   (2, 6),
   (3, 0), (3, 5),
   (4, 2), (4, 3)]

#eval hwss
#eval evolve 4 hwss
#eval shift (0, 2) hwss
#eval isSpaceship hwss 4 (0, 2)

/-- The HWSS is a spaceship of period 4 and displacement `(0, 2)`. -/
theorem hwss_spaceship : isSpaceship hwss 4 (0, 2) = true := by decide

end Life
end Conway
