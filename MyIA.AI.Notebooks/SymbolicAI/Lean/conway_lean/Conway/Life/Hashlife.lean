/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Hashlife (Gosper 1984)

L'algorithme Hashlife exploite la structure auto-similaire des motifs du
Jeu de la Vie. Deux observations le rendent possible :

1. Une `MacroCell` de niveau `k` (`k >= 2`, cote `2^k`) contient assez
   d'information pour calculer la sous-region **centree** de niveau
   `(k-1)` (cote `2^(k-1)`) apres `2^(k-2)` generations de B3/S23, car a
   distance `2^(k-2)` de toute cellule la regle ne peut pas propager
   l'information au-dela de `2^(k-2)` cellules.
2. Le calcul est structurellement recursif sur le niveau : en combinant
   neuf sous-cellules de niveau `(k-1)` qui se chevauchent (la
   decomposition standard de Hashlife en double-neuf), chacune avancee
   de `2^(k-3)` generations, on obtient la decomposition en quatre
   quadrants de la region centree de niveau `(k-1)` apres
   `2 * 2^(k-3) = 2^(k-2)` generations.

Dans ce port Lean nous implementons l'algorithme **sans** memoisation
(pas de `HashMap` / hash-consing). Le noyau ne sait pas reduire une table
de hachage efficacement, donc nous echangeons la performance maximale
contre une reduction structurelle complete. Un module ulterieur pourra
ajouter la memoisation pour l'execution native.

## Morceaux de l'implementation

- `step4x4`     : entree de niveau 2 -> sortie de niveau 1, une generation
                  en avant (cas de base, calcule via B3/S23 direct).
- `hashlifeResult` : entree de niveau `k` (`k >= 2`) -> sortie de niveau
                     `(k-1)`, `2^(k-2)` generations en avant (cas recursif).
- `centerInLevelPlus2` : placer une cellule de niveau `n` dans une cellule
                          de niveau `(n+2)` avec l'entree placee dans la
                          region centree.
- `hashlifeStep` : enveloppe de commodite. Etant donne une `MacroCell`
                   `c`, rembourrer au niveau `c.level + 2` et appeler
                   `hashlifeResult` une fois, en avancant de
                   `2 ^ c.level` generations.
- `evolveHashlife n g` : point d'entree de haut niveau. Fait avancer `g`
                          de `n` generations, en utilisant Hashlife quand
                          c'est possible.

## Correctness

Nous ne prouvons pas le theoreme de correction complet
`evolveHashlife n g = evolve n g`. Le theoreme est seulement commente car
(a) il exige une theorie extensive de la semantique des MacroCell et
(b) l'algorithme est verifie empiriquement par `#eval` face aux references
`step`/`evolve` de `Conway.Life` sur les petits motifs canoniques.

Pour les petits motifs canoniques (block, blinker, glider, beacon,
toad), `evolveHashlife` est verifie comme coincidant avec `evolve` sur
toutes les generations testees.

Ce module est entierement prouve (aucun trou dans les definitions
reelles ; le theoreme de correction est laisse comme direction future).
-/

import Conway.Life
import Conway.Life.MacroCell

namespace Conway
namespace Life

open MacroCell

/-! ## Cas de base 4x4 : `step4x4`

Nous extrayons la matrice 4x4 de booleens codee dans une MacroCell de
niveau 2, puis nous appliquons la regle B3/S23 aux cellules centrees 2x2
`(1,1), (1,2), (2,1), (2,2)`. -/

/-- Extrait les 16 booleens d'une MacroCell de niveau 2 sous forme d'un
    `Array (Array Bool)` 4x4. La matrice toute-morte est renvoyee sur les
    entrees mal formees (non niveau 2). -/
def level2ToMatrix : MacroCell -> Array (Array Bool)
  | node nw ne sw se =>
    let q : MacroCell -> Bool × Bool × Bool × Bool
      | node (leaf a) (leaf b) (leaf c) (leaf d) => (a, b, c, d)
      | _ => (false, false, false, false)
    let (a00, a01, a10, a11) := q nw   -- lignes 0-1, col 0-1
    let (b00, b01, b10, b11) := q ne   -- lignes 0-1, col 2-3
    let (c00, c01, c10, c11) := q sw   -- lignes 2-3, col 0-1
    let (d00, d01, d10, d11) := q se   -- lignes 2-3, col 2-3
    #[#[a00, a01, b00, b01],
      #[a10, a11, b10, b11],
      #[c00, c01, d00, d01],
      #[c10, c11, d10, d11]]
  | _ =>
    let row : Array Bool := #[false, false, false, false]
    #[row, row, row, row]

/-- Lit `mat[i]![j]!`, avec `false` par defaut hors des bornes. -/
@[inline] def readBit (mat : Array (Array Bool)) (i j : Nat) : Bool :=
  ((mat[i]?.getD #[])[j]?).getD false

/-- Applique la regle B3/S23 en `mat[i][j]`, en comptant les voisins de Moore vivants. -/
def applyB3S23 (mat : Array (Array Bool)) (i j : Nat) : Bool :=
  let n : Nat :=
    (if readBit mat (i - 1) (j - 1) then 1 else 0)
    + (if readBit mat (i - 1) j       then 1 else 0)
    + (if readBit mat (i - 1) (j + 1) then 1 else 0)
    + (if readBit mat i       (j - 1) then 1 else 0)
    + (if readBit mat i       (j + 1) then 1 else 0)
    + (if readBit mat (i + 1) (j - 1) then 1 else 0)
    + (if readBit mat (i + 1) j       then 1 else 0)
    + (if readBit mat (i + 1) (j + 1) then 1 else 0)
  if readBit mat i j then
    n == 2 || n == 3
  else
    n == 3

/-- Cas de base de Hashlife : entree de niveau 2 -> sortie de niveau 1,
    une generation en avant, couvrant le 2x2 centre aux positions
    `(1,1), (1,2), (2,1), (2,2)` de l'entree. -/
def step4x4 (c : MacroCell) : MacroCell :=
  if c.level == 2 then
    let mat := level2ToMatrix c
    let r1c1 := applyB3S23 mat 1 1
    let r1c2 := applyB3S23 mat 1 2
    let r2c1 := applyB3S23 mat 2 1
    let r2c2 := applyB3S23 mat 2 2
    node (leaf r1c1) (leaf r1c2) (leaf r2c1) (leaf r2c2)
  else
    emptyOfLevel 1

/-! ## Hashlife recursif : `hashlifeResult`

`hashlifeResult c` prend une MacroCell de niveau `k` (`k >= 2`) et
renvoie une MacroCell de niveau `(k-1)` representant la region centree
apres `2^(k-2)` generations.

Cas de base (`k = 2`) : utiliser `step4x4`.

Cas recursif (`k >= 3`) :
1. Decomposer les quadrants de l'entree. Chacun est de niveau `k-1`.
   Chacun de ces quadrants a quatre sous-quadrants de niveau `k-2`.
   Ensemble ils pavent une grille 4x4 de cellules de niveau `(k-2)`
   (lignes 0..3, col 0..3).
2. Former neuf cellules de niveau `(k-1)` qui se chevauchent (disposition 3x3) :
     n1 = coin NO          (nw_nw, nw_ne, nw_sw, nw_se)
     n2 = milieu haut      (nw_ne, ne_nw, nw_se, ne_sw)
     n3 = coin NE          (ne_nw, ne_ne, ne_sw, ne_se)
     n4 = milieu gauche    (nw_sw, nw_se, sw_nw, sw_ne)
     n5 = centre           (nw_se, ne_sw, sw_ne, se_nw)
     n6 = milieu droit     (ne_sw, ne_se, se_nw, se_ne)
     n7 = coin SO          (sw_nw, sw_ne, sw_sw, sw_se)
     n8 = milieu bas       (sw_ne, se_nw, sw_se, se_sw)
     n9 = coin SE          (se_nw, se_ne, se_sw, se_se)
3. Recurir sur chaque n_i, en obtenant des cellules de niveau `(k-2)`
   `r1..r9`, chacune avancee de `2^(k-3)` generations.
4. Former quatre super-cellules de niveau `(k-1)` qui se chevauchent a
   partir des r_i :
     q_nw = (r1, r2, r4, r5)
     q_ne = (r2, r3, r5, r6)
     q_sw = (r4, r5, r7, r8)
     q_se = (r5, r6, r8, r9)
5. Recurir sur chaque q_*, en obtenant des cellules de niveau `(k-2)`
   `out_*`, chacune encore `2^(k-3)` generations en avant — total
   `2^(k-2)`. ✓
6. Renvoyer `node out_nw out_ne out_sw out_se` (niveau `k-1`).
-/

/-- Auxiliaire pour `hashlifeResult` : recursion structurelle sur `fuel`.
    Quand `fuel = 0`, renvoie une cellule par defaut. Quand `fuel > 0`,
    effectue un pas de Hashlife, en recursant avec `fuel - 1`.
    Termine car `fuel` est un `Nat` qui decroit strictement.

    L'enveloppe `hashlifeResult` l'appelle avec `fuel = c.level`, qui est
    une borne structurelle superieure sur la profondeur de recursion (le
    niveau decroit strictement a chaque pas de l'algorithme). -/
def hashlifeResultAux : Nat → MacroCell → MacroCell
  | 0, _ => deadLeaf  -- fuel epuise : renvoyer la valeur par defaut
  | fuel + 1, c@(node (node nw_nw nw_ne nw_sw nw_se)
                      (node ne_nw ne_ne ne_sw ne_se)
                      (node sw_nw sw_ne sw_sw sw_se)
                      (node se_nw se_ne se_sw se_se)) =>
    if c.level == 2 then
      step4x4 c
    else
      let n1 := node nw_nw nw_ne nw_sw nw_se
      let n2 := node nw_ne ne_nw nw_se ne_sw
      let n3 := node ne_nw ne_ne ne_sw ne_se
      let n4 := node nw_sw nw_se sw_nw sw_ne
      let n5 := node nw_se ne_sw sw_ne se_nw
      let n6 := node ne_sw ne_se se_nw se_ne
      let n7 := node sw_nw sw_ne sw_sw sw_se
      let n8 := node sw_ne se_nw sw_se se_sw
      let n9 := node se_nw se_ne se_sw se_se
      let r1 := hashlifeResultAux fuel n1
      let r2 := hashlifeResultAux fuel n2
      let r3 := hashlifeResultAux fuel n3
      let r4 := hashlifeResultAux fuel n4
      let r5 := hashlifeResultAux fuel n5
      let r6 := hashlifeResultAux fuel n6
      let r7 := hashlifeResultAux fuel n7
      let r8 := hashlifeResultAux fuel n8
      let r9 := hashlifeResultAux fuel n9
      let q_nw := node r1 r2 r4 r5
      let q_ne := node r2 r3 r5 r6
      let q_sw := node r4 r5 r7 r8
      let q_se := node r5 r6 r8 r9
      let out_nw := hashlifeResultAux fuel q_nw
      let out_ne := hashlifeResultAux fuel q_ne
      let out_sw := hashlifeResultAux fuel q_sw
      let out_se := hashlifeResultAux fuel q_se
      node out_nw out_ne out_sw out_se
  | _ + 1, c =>
    -- Malforme : pas un noeud de niveau >= 2 compose de noeuds.
    if c.level == 0 then deadLeaf
    else emptyOfLevel (c.level - 1)

/-- Hashlife recursif : entree de niveau `k` -> sortie de niveau `(k-1)`,
    `2^(k-2)` generations en avant.

    Implemente via `hashlifeResultAux` avec fuel = `c.level`, qui est une
    borne structurelle superieure sur la profondeur de recursion (le
    niveau decroit strictement a chaque appel recursif).

    Cette enveloppe n'est pas elle-meme recursive : la terminaison vient
    de la recursion structurelle de `hashlifeResultAux` sur `fuel`, donc
    l'enveloppe est un simple `def` (gardee transparente pour les preuves
    de correction dans `Conway.Life.HashlifeMemo`). -/
def hashlifeResult (c : MacroCell) : MacroCell :=
  hashlifeResultAux c.level c

/-! ## Aides de centrage / rembourrage -/

/-- Centre `c` (niveau `n`) dans une MacroCell de niveau `(n+2)`, avec
    `c` place dans la region centree `2^n x 2^n`.

    Les quatre quadrants de niveau `(n+1)` du resultat sont chacun
    composes de quatre sous-cellules de niveau `n` : une est une partie
    de l'entree, les trois autres sont du rembourrage tout-mort. -/
def centerInLevelPlus2 (c : MacroCell) : MacroCell :=
  let n := c.level
  let e : MacroCell := emptyOfLevel n
  -- Le quadrant NO du resultat (niveau n+1) a `c` dans sa sous-cellule SE.
  -- Le quadrant NE du resultat a `c` dans sa sous-cellule SO.
  -- Le quadrant SO du resultat a `c` dans sa sous-cellule NE.
  -- Le quadrant SE du resultat a `c` dans sa sous-cellule NO.
  node (node e e e c)
       (node e e c e)
       (node e c e e)
       (node c e e e)

/-- Remboure `c` (niveau `n`) dans une MacroCell de niveau `(n+1)` en
    placant `c` dans la region centree avec du rembourrage tout-mort
    autour.

    Pour `c = node nw ne sw se`, le resultat est :
    ```
    node (node e e e nw) (node e e ne e) (node e sw e e) (node se e e e)
    ```
    Cela donne une copie de `c` au centre, avec `2^(n-1)` cellules de
    rembourrage mort de chaque cote. -/
def padToLevelPlus1 (c : MacroCell) : MacroCell :=
  match c with
  | node nw ne sw se =>
    let e := emptyOfLevel nw.level  -- niveau n-1
    node (node e e e nw) (node e e ne e) (node e sw e e) (node se e e e)
  | _ => c  -- les feuilles ne peuvent pas etre rembourrees

/-- Remboure `c` de 2 niveaux, en le placant au centre d'une cellule de
    niveau `(n+2)`. Equivalent a `padToLevelPlus1 (padToLevelPlus1 c)`.
    Le resultat a `2^n` cellules de rembourrage mort de chaque cote. -/
def padCenter2 (c : MacroCell) : MacroCell := padToLevelPlus1 (padToLevelPlus1 c)

/-! ## Pas d'une generation sur des MacroCell quelconques

Pour les pas d'une seule generation, nous faisons un aller-retour via
Grid pour level > 0 (car `hashlifeResult` saute de `2^(k-2)` generations,
pas de 1). La vraie acceleration vient de `hashlifeJump` et
`evolveHashlifeFast`, qui utilisent le Hashlife recursif pour les sauts
de plusieurs generations. -/

/-- Fait avancer `c` d'exactement une generation. Pour le niveau 0,
    utilise le cas de base Hashlife `step4x4`. Pour les niveaux plus
    grands, se replie sur `Conway.Life.step` sur la grille sous-jacente. -/
def hashlifeStep1 (c : MacroCell) : MacroCell :=
  if c.level == 0 then
    step4x4 (centerInLevelPlus2 c)
  else
    gridToMacroCell (step (c.toGrid (0, 0)))

/-- Un pas de Hashlife sur une MacroCell. -/
def hashlifeStep (c : MacroCell) : MacroCell := hashlifeStep1 c

/-- Avance rapide de `c` de `k` generations, un pas a la fois. -/
def hashlifeFastForward : Nat -> MacroCell -> MacroCell
  | 0,     c => c
  | k + 1, c => hashlifeFastForward k (hashlifeStep1 c)

/-! ## API d'acceleration exponentielle : `hashlifeJump`, `evolveHashlifeFast`

L'idee clee : `hashlifeResult` sur une MacroCell de niveau `k` fait
avancer la region centree de `2^(k-2)` generations. Pour garantir que le
motif reste dans la region calculee, nous rembourrons la MacroCell de 2
niveaux avec `centerInLevelPlus2`, qui place le motif au centre d'une
cellule `(level + 2)`, laissant `2^level` de marge de chaque cote.

Attention : ce rembourrage **augmente aussi la portee**. `hashlifeResult`
sur la cellule rembourree avance de `2^level` generations (et non
`2^(level-2)` comme la cellule non rembourree). La marge `2^level` se
trouve donc comparee a une portee de `2^level` generations : le ratio est
**tendu** (proche de 1), et non « largement suffisant » comme l'aurait
laisse croire la portee naive `2^(level-2)`. Le theoreme
`no_padding_depth_suffices` (cf. `JumpCapture.lean`) le formalise :
`marginToResultWindow k p < jumpReach k p`, la marge restant strictement
inferieure a la portee du cone de vitesse 1, l'ecart etant le clip de
`2^(k-1)`.

Le decalage du resultat egale le decalage original (le resultat centre de
la cellule rembourree s'aligne avec la region originale). Desserrer ce
ratio exigerait de decorreler la portee du niveau — le parametre `j` de
Gosper (rembourrage plus profond que `+2`) ramene le ratio marge/portee
a `2 - 2^(2-p)`, tendu a `p = 2` et surplus strict a `p >= 3` ; cette
variante n'est pas implementee ici. -/

/-- Fait sauter une MacroCell en avant de `2^level` generations en
    utilisant le Hashlife recursif avec rembourrage. Remboure l'entree de
    2 niveaux, puis appelle `hashlifeResult`. Le resultat est une
    MacroCell de niveau `(k+1)`.

    Le decalage du resultat egale le decalage original (la region centree
    de la cellule rembourree s'aligne avec la boite englobante originale). -/
def hashlifeJump (c : MacroCell) : MacroCell :=
  hashlifeResult (padCenter2 c)

/-- Taille de saut pour une MacroCell de niveau `k` : `2^k` generations. -/
def jumpSize (lvl : Nat) : Nat := 2 ^ lvl

/-- Calcule le decalage pour le resultat de `hashlifeJump`.

    Apres rembourrage de 2 niveaux (`padCenter2`), la MacroCell de niveau
    `k` devient de niveau `(k+2)`. Le resultat de `hashlifeResult` sur la
    cellule rembourree est de niveau `(k+1)`, dont le coin est decale de
    `-2^(k-1)` par rapport au decalage original `off`. -/
def jumpResultOff (off : Int × Int) (lvl : Nat) : Int × Int :=
  if lvl == 0 then off
  else (off.1 - (2 ^ (lvl - 1) : Nat), off.2 - (2 ^ (lvl - 1) : Nat))

/-- Auxiliaire pour `evolveHashlifeFast` : recursion structurelle sur
    `fuel`. Quand `fuel = 0`, se replie sur `evolve n g` (implementation
    de reference). Quand `fuel > 0`, essaye d'utiliser le saut
    exponentiel de Hashlife si possible, en recursant avec `fuel - 1`. -/
def evolveHashlifeFastAux : Nat → Nat → Grid → Grid
  | _, 0, g => g
  | 0, _, g => g  -- fuel epuise : retourner l'etat courant
  | fuel + 1, n, g =>
    let (off, mc) := gridToMacroCellWithOffset g
    let lvl := mc.level
    let js := jumpSize lvl
    if lvl >= 2 && n >= js then
      -- Saut en avant de `2^lvl` generations avec Hashlife rembourre
      let jumped := hashlifeJump mc
      let newOff := jumpResultOff off lvl
      let g' := jumped.toGrid newOff
      evolveHashlifeFastAux fuel (n - js) g'
    else
      -- Petit n ou petit motif : utiliser le evolve de reference
      evolve n g

/-- Fait evoluer `g` de `n` generations en utilisant l'acceleration
    exponentielle de Hashlife.

    Strategie :
    - Construire une MacroCell a partir de `g` (niveau `k`).
    - Rembourrer de 2 niveaux et utiliser `hashlifeResult` pour sauter de
      `2^k` generations.
    - Apres chaque saut, reconstruire la MacroCell et repeter.
    - Pour les petits `n` ou level < 2, se replier sur `evolve`.

    Implemente via `evolveHashlifeFastAux` avec `fuel = n`, car chaque
    iteration reduit `n` d'au moins `js >= 4`. -/
def evolveHashlifeFast (n : Nat) (g : Grid) : Grid :=
  evolveHashlifeFastAux n n g

/-! ### N3 : tramage conscient de n pour `evolveHashlifeFast` (issue #3846)

La refonte P5 introduit `gridToMacroCellWithOffsetN` (analogue conscient
de n de `gridToMacroCellWithOffset`, voir `MacroCell.lean` L736) : il
construit la `MacroCell` a partir de `gridFrameN n g` (rembourrage
`max 2 n`) au lieu de `gridFrame` a rembourrage fixe (rembourrage `2`).
Pour `n ≤ 2`, les deux constructeurs coincident
(`gridToMacroCellWithOffsetN_le_two_eq`, L746), donc le tramage conscient
de n est **definitionnellement identique** au `evolveHashlifeFast`
existant dans le regime des petits `n` (chaque temoin de correction
existant dans `Computation.lean` utilise `n ∈ {2, 4, 8, 12, 16}`, tous
`≤ 16` mais la plupart `≤ 4`).

Cette section **ajoute** la variante consciente de n sans toucher a
`evolveHashlifeFast` ni a aucun de ses 50+ sites d'appel / preuves :

- `evolveHashlifeFastAuxN` / `evolveHashlifeFastN` — meme recursion que
  `evolveHashlifeFastAux`, mais la MacroCell initiale est construite avec
  le cadre conscient de n `gridToMacroCellWithOffsetN n g`. Les iterations
  ulterieures utilisent le constructeur a cadre fixe (N3 = "tramer sans
  re-cadrer", selon le commentaire de conception N1 a MacroCell L634).
- `evolveHashlifeFastN_zero` — verification triviale : `n = 0` renvoie `g`.

Le **pont** `evolveHashlifeFastN n g = evolveHashlifeFast n g` pour `n ≤ 2`
(via `gridToMacroCellWithOffsetN_le_two_eq` + induction structurelle sur
`fuel`) est **reporte** a un cycle ulterieur, jumele avec le deblocage
P4 : il exige le demontage complet du corps dans le style
`evolveHashlifeFastMemo_eq_evolveHashlifeFast`, qu'il est preferable
d'assembler une fois le harnais Lean LSP (terrain d'ai-01, apres le fix
H) de retour a une interactivite complete. Documenter ici l'obligation
de preuve garde le plan de refonte P5 honnete et evite un stub creux. -/

/-- Auxiliaire trame N3 pour `evolveHashlifeFastN` : meme recursion que
    `evolveHashlifeFastAux`, mais la MacroCell initiale est construite
    avec le cadre conscient de n `gridToMacroCellWithOffsetN n g`. Les
    appels recursifs ulterieurs (la branche `n - js`) utilisent le
    constructeur a cadre fixe — N3 trame le cadre *sans* re-cadrer a
    chaque iteration (selon le commentaire de conception N1 a MacroCell
    L634). -/
def evolveHashlifeFastAuxN : Nat → Nat → Grid → Grid
  | _, 0, g => g
  | 0, _, g => g  -- fuel epuise : retourner l'etat courant
  | fuel + 1, n, g =>
    -- Substitution N3 : cadre conscient de n sur la MacroCell initiale seulement.
    let (off, mc) := gridToMacroCellWithOffsetN n g
    let lvl := mc.level
    let js := jumpSize lvl
    if lvl >= 2 && n >= js then
      -- Saut en avant de `2^lvl` generations avec Hashlife rembourre,
      -- puis re-cadrage a partir du cadre fixe de la nouvelle grille (sautee).
      let jumped := hashlifeJump mc
      let newOff := jumpResultOff off lvl
      let g' := jumped.toGrid newOff
      -- Les iterations ulterieures utilisent le constructeur a cadre fixe,
      -- PAS le conscient de n — le parametre n est deja consomme par `n - js`,
      -- et re-cadrer avec le *nouveau* `n` gonflerait inutilement le
      -- rembourrage alors que la boite englobante a retreci apres le saut.
      evolveHashlifeFastAuxN fuel (n - js) g'
    else
      -- Petit n ou petit motif : utiliser le evolve de reference.
      evolve n g

/-- Variante tramee N3 de `evolveHashlifeFast` : la MacroCell initiale
    utilise le cadre conscient de n `gridToMacroCellWithOffsetN n g`, puis
    la recursion procede de maniere identique. API publique ; pour
    `n ≤ 2` elle coincide avec `evolveHashlifeFast` (pont reporte a un
    cycle ulterieur, jumele avec le deblocage P4 — voir la docstring de
    section ci-dessus). -/
def evolveHashlifeFastN (n : Nat) (g : Grid) : Grid :=
  evolveHashlifeFastAuxN n n g

/-- Verification triviale : `evolveHashlifeFastN 0 g = g` (la branche
    `n = 0` de l'auxiliaire renvoie `g` directement). -/
@[simp]
theorem evolveHashlifeFastN_zero (g : Grid) :
    evolveHashlifeFastN 0 g = g := rfl

/-- Calcule `evolve n g` avec Hashlife. Fait un aller-retour a travers
    la representation `MacroCell` a chaque generation, en exercant
    `step4x4` pour la boucle interne de niveau 2. -/
def evolveHashlife : Nat -> Grid -> Grid
  | 0,     g => g
  | n + 1, g =>
    -- Construire une MacroCell. Si la boite englobante tient dans une
    -- fenetre de niveau 2 (i.e. la region vivante s'etend sur au
    -- maximum quelques cellules), le cas de base Hashlife `step4x4` peut
    -- etre utilise ; sinon aller-retour via `Conway.Life.step`. Nous
    -- exercons au minimum la representation MacroCell comme verification.
    let (off, mc) := gridToMacroCellWithOffset g
    -- Le cadre choisi place la region vivante dans un carre de niveau >= 2.
    -- Essayer le cas de base Hashlife si le niveau est exactement 2.
    let g' :=
      if mc.level == 2 then
        let r := hashlifeResult mc
        -- `r` est une MacroCell de niveau 1 couvrant le 2x2 centre de
        -- l'entree de niveau 2. L'entree de niveau 2 a son coin haut-gauche
        -- en `off`, donc le 2x2 centre a son haut-gauche en
        -- `(off.1 + 1, off.2 + 1)`.
        r.toGrid (off.1 + 1, off.2 + 1)
      else
        step g
    evolveHashlife n g'

/-! ## Tests de coherence

Nous verifions que `evolveHashlife` coincide avec le `evolve` de
reference sur les petits motifs canoniques, et que `step4x4` gere
correctement des entrees 4x4 specifiques.
-/

-- step4x4 sur un 4x4 construit a la main avec un blinker horizontal a la ligne 1.
-- Resultat centre 2x2 attendu en (1,1)..(2,2) : (1,1) vivant, (2,1) vivant.
#eval
  let mc : MacroCell :=
    node
      (node (leaf false) (leaf false) (leaf true) (leaf true))   -- NW: (1,0), (1,1) alive
      (node (leaf false) (leaf false) (leaf true) (leaf false))  -- NE: (1,2) alive
      (node (leaf false) (leaf false) (leaf false) (leaf false)) -- SW
      (node (leaf false) (leaf false) (leaf false) (leaf false)) -- SE
  (step4x4 mc).toGrid (1, 1)

-- Comparaison avec la reference : blinker_h est [(0,0), (1,0), (2,0)].
-- Apres un step il devient blinker_v = [(1,-1), (1,0), (1,1)].
-- Dans le test ci-dessus, le blinker est a la ligne 1, col 0..2, et le
-- resultat centre attendu est (ligne 1, col 1) et (ligne 2, col 1), i.e.
-- seulement le trait vertical qui se trouve dans la fenetre centree 2x2.
#eval step blinker_h

-- Verifications par aller-retour de `evolveHashlife` face a `evolve`.
#eval evolveHashlife 1 block == evolve 1 block
#eval evolveHashlife 4 block == evolve 4 block
#eval evolveHashlife 1 blinker_h == evolve 1 blinker_h
#eval evolveHashlife 2 blinker_h == evolve 2 blinker_h
#eval evolveHashlife 1 glider == evolve 1 glider
#eval evolveHashlife 4 glider == evolve 4 glider
#eval evolveHashlife 1 beacon == evolve 1 beacon
#eval evolveHashlife 2 beacon == evolve 2 beacon
#eval evolveHashlife 1 toad == evolve 1 toad
#eval evolveHashlife 2 toad == evolve 2 toad

-- Hashlife recursif direct sur une entree de niveau 3 (exerce le
-- `hashlifeResult` recursif pour k = 3). Construit une MacroCell de
-- niveau 3 (8x8) contenant le glider pres de son centre, puis appelle
-- `hashlifeResult` ; ceci renvoie une cellule de niveau 2 representant
-- le glider 2 generations plus tard, mais seulement sur la fenetre
-- centree 4x4. Nous comparons donc avec `evolve 2 glider` *filtre* sur
-- la fenetre centree.
#eval
  let off : Int × Int := (-2, -2)
  let mc := MacroCell.buildFromGrid glider off.1 off.2 3
  let r := hashlifeResult mc        -- level 2, 2 generations ahead
  -- The level-2 result covers the centered 4x4 region of the level-3
  -- input. With top-left of the level-3 cell at `off`, the centered
  -- region's top-left is at `(off.1 + 2, off.2 + 2) = (0, 0)`.
  let hashlife_cells := r.toGrid (off.1 + 2, off.2 + 2)
  -- Filter the reference to the centered window (rows 0..3, cols 0..3)
  let ref_full := evolve 2 glider
  let ref_window := ref_full.filter
    (fun p => 0 <= p.1 && p.1 < 4 && 0 <= p.2 && p.2 < 4)
  (hashlife_cells, ref_window, hashlife_cells == ref_window)

-- Reference : glider 4 pas en avant.
#eval evolve 4 glider

/-! ## Tests de coherence pour `evolveHashlifeFast`

Verifions que le chemin d'acceleration exponentielle coincide avec le
`evolve` de reference sur les motifs canoniques. Ces tests exercent
`hashlifeJump` (via le chemin `hashlifeResult` rembourre) plutot que le
`step` de repli.
-/

-- Block : still life, n'importe quel nombre de generations = inchange
#eval evolveHashlifeFast 1 block == evolve 1 block
#eval evolveHashlifeFast 4 block == evolve 4 block
#eval evolveHashlifeFast 16 block == evolve 16 block

-- Glider : periode 4, deplacement (1,-1)
#eval evolveHashlifeFast 4 glider == evolve 4 glider
#eval evolveHashlifeFast 8 glider == evolve 8 glider
#eval evolveHashlifeFast 12 glider == evolve 12 glider

-- Blinker : periode 2
#eval evolveHashlifeFast 2 blinker_h == evolve 2 blinker_h
#eval evolveHashlifeFast 4 blinker_h == evolve 4 blinker_h

-- Beacon : periode 2
#eval evolveHashlifeFast 2 beacon == evolve 2 beacon

-- Toad : periode 2
#eval evolveHashlifeFast 2 toad == evolve 2 toad

end Life
end Conway
