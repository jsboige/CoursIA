/-
Copyright (c) 2026 CoursIA. Tous droits reserves.
Distribue sous licence Apache 2.0 comme decrit dans le fichier LICENSE.

## Jeu de la Vie de Conway — Oscillateurs et structures stables (still lifes)

Structures stables additionnelles (loaf, boat, tub, pond, ship) et
oscillateurs (pulsar periode 3, pentadecathlon periode 15) etendant
le module fondateur `Conway.Life`.

Les structures stables sont verifiees via `isStillLife g = true`.
Les oscillateurs sont verifies via `isOscillator g n = true`.

Toutes les coordonnees sont listees dans l'ordre lexicographique
trie (ligne d'abord, puis colonne) pour que `step` produise une
liste dans le meme ordre et que le noyau puisse verifier l'egalite
par comparaison structurelle (`decide` pour les structures stables,
`native_decide` pour les oscillateurs — cf Section Oscillateurs).

Le pulsar (48 cellules, periode 3) et le pentadecathlon (12 cellules,
periode 15) depassent la limite de profondeur de recursion du reducteur
kernel (`maximum recursion depth reached` en `decide` pour le pulsar) ;
ils necessitent la compilation native (`native_decide`) pour etre
verifies. Leurs theoremes sont conserves non-commentes (prouves par
`native_decide`, un axiome natif par theoreme). Les cinq structures
stables (loaf, boat, tub, pond, ship), plus simples, sont prouvees par
`decide` dans le noyau (zero axiome). Les definitions elles-memes sont
exportees inconditionnellement.

Ce module est entierement prouve (aucun gap dans les theoremes non-commentes).
-/

/-
  Convention i18n (EPIC #4980, decision user 2026-07-04) : ce fichier est **FR canonique**,
  avec son miroir anglais dans le fichier sibling `Oscillators_en.lean` (modele sibling
  pair ratifie 2026-07-04, cf `code-style.md` §Lean i18n). Les enonces de theoremes,
  les tactiques Lean, les noms de lemmes et les references Mathlib restent en anglais
  (compat Mathlib 4) ; seules les docstrings de theoreme et ce bloc d'en-tete different
  entre les deux fichiers.
-/

import Conway.Life

namespace Conway
namespace Life

/-! ## Structures stables (still lifes)

Nous ajoutons cinq structures stables classiques pour completer `block`
et `beehive` de `Conway.Life` :

- **Loaf** : motif a 7 cellules, l'une des quatre structures stables les plus courantes
- **Boat** : motif a 5 cellules, la plus petite structure stable asymetrique
- **Tub** : motif a 4 cellules, la plus petite structure stable a symetrie rotationnelle
- **Pond** : motif a 8 cellules, une structure stable plus grande quasi carree
- **Ship** : motif a 6 cellules, apparente au boat (boat tourne avec une cellule supplementaire)
-/

/-- Le **Loaf** : une structure stable a 7 cellules.
    ```
    .XX.
    X..X
    .X.X
    ..X.
    ``` -/
def loaf : Grid :=
  [(0, 1), (0, 2), (1, 0), (1, 3), (2, 1), (2, 3), (3, 2)]

/-- Le **Boat** : une structure stable a 5 cellules. Plus petite structure stable asymetrique.
    ```
    XX.
    X.X
    .X.
    ``` -/
def boat : Grid :=
  [(0, 0), (0, 1), (1, 0), (1, 2), (2, 1)]

/-- Le **Tub** : une structure stable a 4 cellules a symetrie rotationnelle complete.
    ```
    .X.
    X.X
    .X.
    ``` -/
def tub : Grid :=
  [(0, 1), (1, 0), (1, 2), (2, 1)]

/-- Le **Pond** : une structure stable a 8 cellules.
    ```
    .XX.
    X..X
    X..X
    .XX.
    ``` -/
def pond : Grid :=
  [(0, 1), (0, 2), (1, 0), (1, 3), (2, 0), (2, 3), (3, 1), (3, 2)]

/-- Le **Ship** : une structure stable a 6 cellules.
    ```
    XX.
    X.X
    .XX
    ``` -/
def ship : Grid :=
  [(0, 0), (0, 1), (1, 0), (1, 2), (2, 1), (2, 2)]

/-! ## Verifications des structures stables

Chaque predicat est reduit a un `Bool` par le noyau. Les cinq structures
stables ci-dessous sont prouvees par `decide` dans le noyau (zero axiome
natif : la preuve est verifiee par le reducteur, pas deleguee au compilateur
natif). Le pulsar et le pentadecathlon, dont la reduction kernel depasse la
limite de profondeur de recursion (`maximum recursion depth reached` en
`decide` pour le pulsar), restent prouves par `native_decide` (Section
Oscillateurs ci-dessous). -/

-- Evaluations de verification (re-evaluees par `#eval` au moment de l'elaboration)
#eval isStillLife loaf
#eval isStillLife boat
#eval isStillLife tub
#eval isStillLife pond
#eval isStillLife ship

/-- Le Loaf est une structure stable. -/
theorem loaf_still_life : isStillLife loaf = true := by decide

/-- Le Boat est une structure stable. -/
theorem boat_still_life : isStillLife boat = true := by decide

/-- Le Tub est une structure stable. -/
theorem tub_still_life : isStillLife tub = true := by decide

/-- Le Pond est une structure stable. -/
theorem pond_still_life : isStillLife pond = true := by decide

/-- Le Ship est une structure stable. -/
theorem ship_still_life : isStillLife ship = true := by decide

/-! ## Oscillateurs (motifs a la limite)

Ces deux motifs sont les plus petits des « grands » oscillateurs du
Jeu de la Vie classique de Conway. Contrairement aux structures stables
ci-dessus (prouvees par `decide` dans le noyau, zero axiome), leur
reduction par le noyau atteint la limite de profondeur de recursion
(`maximum recursion depth reached` en `decide` pour le pulsar). Leurs
theoremes sont donc prouves par `native_decide` (compilation native),
qui n'est pas soumis a la limite `maxRecDepth` du reducteur kernel —
au prix d'un axiome `_native.native_decide.ax_1_1` ajoute a la TCB
pour chacun. Les temoins (`pulsar`, `pentadecathlon`) sont exportes
inconditionnellement comme definitions.

La disposition 13x13 du pulsar suit le positionnement standard de la
litterature. Le pentadecathlon est donne dans sa phase minimale
(12 cellules, 10 lignes par 5 colonnes) ; apres 15 etapes, il revient
a lui-meme modulo l'ordre de tri canonique.
-/

/-- Le **Pulsar** : un oscillateur de periode 3 a 48 cellules, decouvert par
    Conway en 1970. Le plus grand oscillateur apparaissant couramment dans les
    soupes aleatoires.
    ```
    ..XXX...XXX..   row 0
    .............   row 1
    X....X.X....X   row 2
    X....X.X....X   row 3
    X....X.X....X   row 4
    ..XXX...XXX..   row 5
    .............   row 6
    ..XXX...XXX..   row 7
    X....X.X....X   row 8
    X....X.X....X   row 9
    X....X.X....X   row 10
    .............   row 11
    ..XXX...XXX..   row 12
    ``` -/
def pulsar : Grid :=
  [(0, 2),  (0, 3),  (0, 4),  (0, 8),  (0, 9),  (0, 10),
   (2, 0),  (2, 5),  (2, 7),  (2, 12),
   (3, 0),  (3, 5),  (3, 7),  (3, 12),
   (4, 0),  (4, 5),  (4, 7),  (4, 12),
   (5, 2),  (5, 3),  (5, 4),  (5, 8),  (5, 9),  (5, 10),
   (7, 2),  (7, 3),  (7, 4),  (7, 8),  (7, 9),  (7, 10),
   (8, 0),  (8, 5),  (8, 7),  (8, 12),
   (9, 0),  (9, 5),  (9, 7),  (9, 12),
   (10, 0), (10, 5), (10, 7), (10, 12),
   (12, 2), (12, 3), (12, 4), (12, 8), (12, 9), (12, 10)]

-- Verifie le pulsar : evolution sur 3 etapes et verification d'egalite
#eval isOscillator pulsar 3
/-- Le Pulsar est de periode 3. -/
theorem pulsar_period_three : isOscillator pulsar 3 = true := by native_decide

/-- Le **Pentadecathlon** : un oscillateur de periode 15 a 12 cellules,
    decouvert par Conway en 1970. Ressemble a un blinker etire qui
    « respire » pendant 15 generations. Coordonnees en phase minimale :
    ```
    ..X..   row 0
    ..X..   row 1
    .X.X.   row 2
    ..X..   row 3
    ..X..   row 4
    ..X..   row 5
    ..X..   row 6
    .X.X.   row 7
    ..X..   row 8
    ..X..   row 9
    ``` -/
def pentadecathlon : Grid :=
  [(0, 2),
   (1, 2),
   (2, 1), (2, 3),
   (3, 2),
   (4, 2),
   (5, 2),
   (6, 2),
   (7, 1), (7, 3),
   (8, 2),
   (9, 2)]

-- Verifie le pentadecathlon : evolution sur 15 etapes et verification d'egalite
#eval isOscillator pentadecathlon 15
/-- Le Pentadecathlon est de periode 15. -/
theorem pentadecathlon_period_15 : isOscillator pentadecathlon 15 = true := by
  native_decide

end Life
end Conway
