/-
Copyright (c) 2026 CoursIA. Tous droits réservés.
Distribué sous licence Apache 2.0 tel que décrit dans le fichier LICENSE.

## Hashlife — la démo de marge n-aware du cadrage (P5 redesign, issue #3846)

Un compagnon exécutable de `Conway.Life.MacroCell` (`gridFrame`, `gridFrameN`)
et `Conway.Life.HashlifeCorrectness` (`box_assez_grand`, `box_assez_grandN`).
Il démontre **concrètement, à l'exécution**, le fait structurel qui motive
la porte de redesign N1 de P5 (PR #5890) : le padding fixe-2 de `gridFrame`
plafonne la marge du cône de lumière à 2, donc `box_assez_grand g n` est
*insatisfaisable* pour `n > 2` sur une grille non vide, alors que le
`gridFrameN n g` n-aware (padding `max 2 n`) rend `box_assez_grandN g n`
*satisfaisable par construction* pour tout `n`.

Ce module est entièrement prouvé (pas de trous) — chaque énoncé est déchargé
par `native_decide` dans `HashlifeCorrectness` (`box_assez_grandN_single_cell_3`,
`box_assez_grand_single_cell_3_false`) ; les appels `#eval` ci-dessous ne font
que reproduire les mêmes faits à l'exécution pour inspection pédagogique.

Voir Epic #3846 (correction Hashlife, P4/P5) et le verdict de redesign sur
cette issue pour le contexte de design-gate (N1 = cadrage, N2 = boucle sans
re-cadrage, N3 = reformulation invariante P5).
-/

import Conway.Life.MacroCell
import Conway.Life.HashlifeCorrectness

namespace Conway

namespace Life

/-! ## Le plafond fixe-2 face au cadre n-aware

`gridFrame` utilise un padding *fixe* de 2 cellules, donc la cellule vivante
la plus haute de toute grille non vide se trouve exactement à 2 cellules de
la frontière de MacroCell. Le prédicat de cône de lumière
`box_assez_grand g n` (marge `>= n` de chaque côté) ne tient donc que pour
`n <= 2` et échoue pour tout `n` plus grand. `gridFrameN n g` généralise le
padding à `max 2 n`, repoussant la frontière pour que la marge soit `>= n`
par construction. Le bloc `#eval` ci-dessous montre les deux cadres et les
valeurs de vérité des prédicats résultants côte à côte sur la grille
mono-cellulaire `[(0, 0)]`. -/

/-- La grille mono-cellulaire utilisée tout au long de cette démo. -/
def demoCell : Grid := [(0, 0)]

/- Le cadre choisi par le `gridFrame` fixe-2 pour `demoCell` :
   coin haut-gauche `(-2, -2)`, niveau `3` (côté `2^3 = 8`). -/
#eval gridFrame demoCell
-- => ((-2, -2), 3)

/- Le cadre choisi par le `gridFrameN 3` n-aware pour `demoCell` :
   padding `max 2 3 = 3`, donc le coin recule à `(-3, -3)` (toujours niveau 3). -/
#eval gridFrameN 3 demoCell
-- => ((-3, -3), 3)

/- Le coin n-aware recule d'autant plus que `n` grandit (padding = `max 2 n`) :
   `n = 0, 2, 4` donnent les coins haut-gauche `(-2,-2), (-2,-2), (-4,-4)`. -/
#eval (gridFrameN 0 demoCell).1
#eval (gridFrameN 2 demoCell).1
#eval (gridFrameN 4 demoCell).1

/-! ## Le prédicat de marge : où les deux cadres divergent

À `n = 2` les deux prédicats tiennent (le cadre fixe offre déjà 2 cellules
de marge). À `n = 3` et au-delà ils divergent : le prédicat `gridFrame` fixe
*échoue* (le plafond insat `boxAssezGrand_nonempty_le_two`), tandis que le
prédicat `gridFrameN` n-aware *tient*. C'est l'écho à l'exécution des témoins
anti-vacuité prouvés dans `HashlifeCorrectness`. -/

/- À `n = 2` les deux cadrages admettent la marge (le plafond du cadre fixe est `2`). -/
#eval box_assez_grand demoCell 2   -- => true
#eval box_assez_grandN demoCell 2  -- => true

/- À `n = 3` les cadrages divergent : fixe échoue (marge plafonnée à 2), n-aware
   tient (padding `max 2 3 = 3` donne marge 3). -/
#eval box_assez_grand demoCell 3   -- => false  (the unsat cap)
#eval box_assez_grandN demoCell 3  -- => true   (gridFrameN breaks the cap)

/- La divergence persiste à `n = 4` : fixe échoue toujours, n-aware tient toujours
   (padding `max 2 4 = 4`, le niveau croît à `4` donc le côté du domaine est `2^4`). -/
#eval box_assez_grand demoCell 4   -- => false
#eval box_assez_grandN demoCell 4  -- => true

/-! ## Pourquoi c'est important pour la correction Hashlife (P5)

Le cône de lumière du Jeu de la Vie a pour rayon `n` : sur `n` générations,
l'influence d'une cellule s'étend de `n` en distance de Manhattan. Le théorème
de saut grand-`n` de P5 nécessite que chaque cellule vivante se trouve à au
moins `n` cellules de la frontière MacroCell pour que rien dans son cône de
lumière en `n` étapes ne puisse fuir. Avec le `gridFrame` fixe-2, cette
hypothèse est *insatisfaisable de façon vacuous* pour `n > 2`, ce qui est
l'obstruction structurelle à P5. `gridFrameN` permet à l'hypothèse de porter
à nouveau une information réelle — le redesign (N2 fait passer ce cadre à
travers la boucle de saut sans re-cadrage ; N3 reformule l'invariante P5
comme « marge >= n restant ») s'appuie sur ce socle N1. -/

end Life
end Conway
