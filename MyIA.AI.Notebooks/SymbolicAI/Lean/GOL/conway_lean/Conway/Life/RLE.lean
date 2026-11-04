/-
Copyright (c) 2026 CoursIA. Tous droits réservés.
Distribué sous licence Apache 2.0 comme décrit dans le fichier LICENSE.

## Conway's Game of Life — Analyseur syntaxique RLE (Epic #1647 Phase 2)

Le format Run Length Encoded (RLE) est la représentation textuelle
standard des motifs de Conway's Game of Life, utilisée par l'archive
communautaire LifeWiki / conwaylife.com et par le simulateur `golly`.

Un exemple canonique : le **glider**.
```
#N Glider
#O Richard K. Guy
#C The smallest, most common, and first discovered spaceship.
x = 3, y = 3, rule = B3/S23
bob$2bo$3o!
```

Grammaire (informelle) :
- Les lignes commençant par `#` sont des commentaires et sont ignorées.
- Une ligne d'en-tête `x = W, y = H, rule = ...` déclare la boîte
  englobante. L'analyseur tolère et ignore l'en-tête (le corps est
  auto-délimité par `!`).
- Le corps est un flux run-length sur l'alphabet `b o $ !`
  (avec des compteurs décimaux optionnels) :
  * `<n>b` saute `n` cellules mortes (par défaut `n = 1`), avançant la colonne.
  * `<n>o` émet `n` cellules vivantes, avançant la colonne.
  * `<n>$` termine la ou les ligne(s) en cours : avance la ligne de `n`
    (par défaut 1) et remet la colonne à 0.
  * `!` termine le motif. Les caractères suivants sont ignorés.
  * Tous les espaces (espaces, retours à la ligne, tabulations,
    retours chariot) dans le corps sont ignorés. Cela permet aux motifs
    de s'enrouler sur plusieurs lignes.

L'analyseur retourne une `Grid` (liste lexicographique triée de
`(row, col) : Int × Int`). Il utilise `Except String` pour le
rapport d'erreurs.

Ce module est entièrement prouvé (pas de trou).

## Convention i18n (EPIC #4980, Option A)

Convention ratifiée par user 2026-07-04 (cf `code-style.md` §Lean i18n) :
fichier **FR canonique** + sibling **EN** dans `RLE_en.lean`. Seules
les **docstrings `/-- ... -/`** et les **commentaires `-- ...`**
diffèrent entre les deux fichiers. **Préservation byte-identity** sur
le reste (signatures, preuves, tactiques) — vérifiable par diff.
Pas de bloc bilingue inline dans un même fichier (Option B rejeté).
-/

import Conway.Life
import Conway.Life.Spaceships
import Conway.Life.Oscillators

namespace Conway
namespace Life
namespace RLE

/-! ## État interne de l'analyseur -/

/-- État de l'analyseur : ligne courante, colonne courante, cellules
    vivantes accumulées (en ordre inverse — on inverse + trie à la fin),
    compteur de run en attente. `done` devient `true` après le
    terminateur `!`. -/
structure ParseState where
  row     : Int
  col     : Int
  cells   : List (Int × Int)  -- accumulées en ordre d'insertion inverse
  runCnt  : Nat               -- 0 signifie « pas de compte explicite, défaut 1 »
  done    : Bool
  deriving Repr

/-- État initial de l'analyseur. -/
def initState : ParseState :=
  { row := 0, col := 0, cells := [], runCnt := 0, done := false }

/-- Compte de run effectif : le compte explicite, ou `1` si aucun n'a
    été donné. -/
def effRun (st : ParseState) : Nat :=
  if st.runCnt == 0 then 1 else st.runCnt

/-! ## Détection des commentaires et de l'en-tête

Le format RLE réserve le préfixe `#` aux commentaires et dédie une
ligne à l'en-tête `x = W, y = H, rule = ...`. Les deux sont ignorés par
le préprocesseur au niveau ligne ci-dessous. L'analyseur du corps
ignore lui-même les espaces, donc les corps multi-lignes sont traités
de manière transparente.
-/

/-- Supprime les espaces ASCII en tête d'une chaîne en récursant sur la
    liste de caractères. Évite `String.dropWhile` / `String.trim` qui
    retournent une `String.Slice` en Lean courant — on a besoin d'une
    simple `String` pour que le reste du pipeline (`startsWith`, `any`)
    typecheck de manière uniforme. -/
def lTrim (s : String) : String :=
  String.ofList (s.toList.dropWhile Char.isWhitespace)

/-- `true` si la ligne est un commentaire (commence par `#`) ou ne
    contient que des espaces. -/
def isCommentOrEmpty (line : String) : Bool :=
  let t := lTrim line
  t.isEmpty || t.startsWith "#"

/-- `true` si la ligne est l'en-tête RLE (commence par `x` suivi de
    `=`). Robuste aux espaces en tête. -/
def isHeaderLine (line : String) : Bool :=
  let t := lTrim line
  t.startsWith "x" && t.any (· = '=')

/-- Supprime les lignes de commentaires et l'en-tête d'une chaîne RLE
    brute, puis concatène le corps. -/
def stripCommentsAndHeader (s : String) : String :=
  let lines := s.splitOn "\n"
  let bodyLines := lines.filter (fun l => ¬ isCommentOrEmpty l && ¬ isHeaderLine l)
  String.join bodyLines

/-! ## Analyseur du corps

Le corps est consommé caractère par caractère. On traite les chiffres
décimaux comme accumulateurs pour le prochain compte de run, et les
quatre caractères de payload `b o $ !` comme actions qui consomment le
compte courant.

Note : `Int.ofNat` est utilisé pour élargir les compteurs Nat de ligne/
colonne vers les cellules `Int × Int` de `Grid`.
-/

/-- Ajoute `n` cellules vivantes démarrant à `(row, col)` à
    l'accumulateur (en ordre inverse). Les cellules sont insérées de
    gauche à droite pour qu'après le `List.reverse` final elles
    ressortent en ordre row-major. -/
def appendLiveRun (row : Int) (startCol : Int) (n : Nat)
    (acc : List (Int × Int)) : List (Int × Int) :=
  let rec go (k : Nat) (c : Int) (a : List (Int × Int)) : List (Int × Int) :=
    match k with
    | 0       => a
    | Nat.succ k' => go k' (c + 1) ((row, c) :: a)
  go n startCol acc

/-- Une étape de l'analyseur du corps RLE. Retourne l'état mis à jour
    ou un message d'erreur. -/
def stepChar (c : Char) (st : ParseState) : Except String ParseState :=
  if st.done then
    -- Après `!`, on ignore tous les caractères suivants (convention RLE).
    Except.ok st
  else if c.isWhitespace then
    Except.ok st
  else if c.isDigit then
    let d : Nat := c.toNat - '0'.toNat
    Except.ok { st with runCnt := st.runCnt * 10 + d }
  else if c == 'b' then
    -- Cellules mortes : avance la colonne de `effRun`, remet le compteur à 0.
    let n := effRun st
    Except.ok { st with col := st.col + Int.ofNat n, runCnt := 0 }
  else if c == 'o' then
    -- Cellules vivantes : émet `effRun` cellules vivantes, avance la colonne, remet le compteur à 0.
    let n := effRun st
    let cells' := appendLiveRun st.row st.col n st.cells
    Except.ok { st with
      cells := cells',
      col := st.col + Int.ofNat n,
      runCnt := 0 }
  else if c == '$' then
    -- Fin de ligne(s) : avance la ligne de `effRun`, remet la colonne à 0.
    let n := effRun st
    Except.ok { st with
      row := st.row + Int.ofNat n,
      col := 0,
      runCnt := 0 }
  else if c == '!' then
    Except.ok { st with done := true }
  else
    Except.error s!"RLE parse error: unexpected character {repr c}"

/-- Plie `stepChar` sur le corps, court-circuitant à la première erreur. -/
def runBody (body : String) : Except String ParseState :=
  body.toList.foldlM (fun st c => stepChar c st) initState

/-! ## Analyseur de niveau supérieur -/

/-- Analyse une chaîne de motif RLE en une `Grid`.

    La grille est retournée en ordre lexicographique trié (ligne
    d'abord, puis colonne) et dédupliquée, suivant la convention de
    `Conway.Life`. -/
def parseRLE (s : String) : Except String Grid := do
  let body := stripCommentsAndHeader s
  let st ← runBody body
  -- Inverse pour retrouver l'ordre d'insertion row-major, puis trie/dédoublonne.
  let cells := st.cells.reverse
  Except.ok (sortDedup cells)

/-- Une enveloppe de commodité totale : retourne `[]` en cas d'erreur
    d'analyse. Destinée aux vérifications `#eval` où l'on sait déjà que
    l'entrée est valide ; utiliser `parseRLE` directement quand le
    rapport d'erreur importe. -/
def parseRLE! (s : String) : Grid :=
  match parseRLE s with
  | Except.ok g => g
  | Except.error _ => []

/-! ## Constantes de motifs

Nous fournissons les chaînes RLE canoniques pour les quatre motifs
phares (`glider`, `lwss`, `pulsar`, `gosper_gun`) avec leurs valeurs
`Grid` analysées. Les trois premiers sont recoupés contre les
constantes écrites à la main exportées par `Conway.Life`,
`Conway.Life.Spaceships`, et `Conway.Life.Oscillators` via les
assertions `#eval` plus bas.

Le Gosper Glider Gun (Bill Gosper, 1970, MIT) est le premier motif fini
connu dans Conway's Life à croissance non bornée : il émet un glider
toutes les 30 générations indéfiniment. Avec 36 cellules vivantes dans
sa phase canonique, il a répondu au défi à 50 USD de Conway pour un
motif à croissance infinie et a déclenché la recherche de
constructions auto-réplicantes qui a culminé avec le Gemini (Wade, 2010).
-/

/-- RLE pour le Glider, le plus petit vaisseau (Conway, 1970). -/
def glider_RLE : String :=
"#N Glider
#O Richard K. Guy
#C The smallest, most common, and first discovered spaceship.
x = 3, y = 3, rule = B3/S23
bob$2bo$3o!"

/-- Grille Glider analysée. Doit correspondre à `Conway.Life.glider`
    (modulo un décalage de convention de coordonnées — voir les
    assertions `#eval`). -/
def glider_parsed : Grid := parseRLE! glider_RLE

/-- RLE pour le Lightweight Spaceship (Conway, 1970).
    Encode la même phase que `Conway.Life.Spaceships.lwss` :
    ```
    .OOOO
    O...O
    ....O
    O..O.
    ``` -/
def lwss_RLE : String :=
"#N Lightweight spaceship
#O John Conway
#C Smallest known c/2 orthogonal spaceship after the glider.
x = 5, y = 4, rule = B3/S23
b4o$o3bo$4bo$o2bo!"

/-- Grille LWSS analysée. Doit correspondre à `Conway.Life.lwss`. -/
def lwss_parsed : Grid := parseRLE! lwss_RLE

/-- RLE pour l'oscillateur Pulsar (Conway, 1970). 48 cellules vivantes,
    période 3, le grand oscillateur le plus courant dans les soups
    aléatoires. -/
def pulsar_RLE : String :=
"#N Pulsar
#O John Conway
#C Period 3 oscillator. The most common naturally occurring oscillator.
x = 13, y = 13, rule = B3/S23
2b3o3b3o2b$13b$o4bobo4bo$o4bobo4bo$o4bobo4bo$2b3o3b3o2b$13b$2b3o3b3o2b$o4bobo4bo$o4bobo4bo$o4bobo4bo$13b$2b3o3b3o2b!"

/-- Grille Pulsar analysée. Doit correspondre à `Conway.Life.pulsar`. -/
def pulsar_parsed : Grid := parseRLE! pulsar_RLE

/-- RLE pour le Gosper Glider Gun (Bill Gosper, 1970, MIT). 36 cellules
    vivantes, période 30 : le premier motif fini connu à croissance non
    bornée, émettant un glider toutes les 30 générations. -/
def gosper_gun_RLE : String :=
"#N Gosper glider gun
#O Bill Gosper
#C A true period 30 glider gun. The first known gun and the first known
#C finite pattern with unbounded growth. Found by Bill Gosper in November 1970.
x = 36, y = 9, rule = B3/S23
24bo11b$22bobo11b$12b2o6b2o12b2o$11bo3bo4b2o12b2o$2o8bo5bo3b2o14b$2o8bo3bob2o4bobo11b$10bo5bo7bo11b$11bo3bo20b$12b2o!"

/-- Grille Gosper Glider Gun analysée. 36 cellules vivantes. -/
def gosper_gun : Grid := parseRLE! gosper_gun_RLE

/-! ## Vérifications de cohérence

Nous utilisons `#eval` plutôt que `theorem` ici : l'analyseur est un
calcul pur, pas une propriété nécessitant réduction du noyau.
`native_decide` sur un `theorem` ré-exécuterait l'analyseur dans le
noyau, ce qui est notablement plus lent et n'offre aucune garantie
supplémentaire pour une fonction déterministe.

La première cellule de chaque grille analysée, le compte de cellules,
et l'égalité avec les constantes écrites à la main sont tous imprimés.
Toute discordance est visible dans la sortie d'élaboration.
-/

-- Glider : 5 cellules vivantes, boîte englobante 3x3.
#eval glider_parsed                              -- attendu : 5 cellules
#eval glider_parsed.length                       -- attendu : 5
#eval (parseRLE glider_RLE).toOption.isSome      -- attendu : true

-- LWSS : 9 cellules vivantes, boîte englobante 5x4. Recoupement avec `lwss`.
#eval lwss_parsed                                -- attendu : 9 cellules
#eval lwss_parsed.length                         -- attendu : 9
#eval lwss_parsed == lwss                        -- attendu : true

-- Pulsar : 48 cellules vivantes, boîte englobante 13x13. Recoupement avec `pulsar`.
#eval pulsar_parsed.length                       -- attendu : 48
#eval pulsar_parsed == pulsar                    -- attendu : true

-- Gosper Glider Gun : 36 cellules vivantes, boîte englobante 36x9.
#eval gosper_gun                                 -- attendu : 36 cellules
#eval gosper_gun.length                          -- attendu : 36

/-! ## Correction prouvée de l'analyse

L'analyseur est déterministe et total. `native_decide` vérifie que
l'analyse réussit (sans erreur) pour les quatre motifs phares et
confirme que les grilles LWSS et Pulsar analysées correspondent à
leurs contreparties écrites à la main dans `Conway.Life`. Le glider
utilise une phase différente de la constante écrite à la main (le RLE
encode la phase 1 allant vers le SE tandis que `Conway.Life.glider`
utilise une orientation différente), donc aucun théorème de
round-trip n'est énoncé pour lui.
-/

/-- L'analyse du RLE du glider réussit (pas d'erreur). -/
theorem glider_parse_ok : (parseRLE glider_RLE).toOption.isSome = true := by native_decide

/-- L'analyse du RLE du LWSS réussit. -/
theorem lwss_parse_ok : (parseRLE lwss_RLE).toOption.isSome = true := by native_decide

/-- L'analyse du RLE du pulsar réussit. -/
theorem pulsar_parse_ok : (parseRLE pulsar_RLE).toOption.isSome = true := by native_decide

/-- L'analyse du RLE du Gosper gun réussit. -/
theorem gosper_gun_parse_ok : (parseRLE gosper_gun_RLE).toOption.isSome = true := by native_decide

/-- La grille LWSS analysée correspond à la constante `lwss` écrite
    à la main. -/
theorem lwss_rle_roundtrip : lwss_parsed = lwss := by native_decide

/-- La grille Pulsar analysée correspond à la constante `pulsar`
    écrite à la main. -/
theorem pulsar_rle_roundtrip : pulsar_parsed = pulsar := by native_decide

/-- Le Gosper gun a exactement 36 cellules vivantes. -/
theorem gosper_gun_cell_count : gosper_gun.length = 36 := by native_decide

/-- La grille glider analysée a exactement 5 cellules vivantes. -/
theorem glider_parsed_cell_count : glider_parsed.length = 5 := by native_decide

/-! ## Vérifications comportementales de round-trip

Celles-ci confirment que les grilles analysées exhibent le
comportement dynamique documenté, en réutilisant les prédicats de
`Conway.Life`. Ce sont des évaluations pures (pas des théorèmes) :
`native_decide` sur les grilles dérivées de l'analyseur est un outil
trop grossier — l'analyseur est lui-même total et les comportements
sous-jacents sont déjà prouvés pour les constantes écrites à la main.
-/

-- Le LWSS analysé est un vaisseau de période 4, déplacement (0, 2).
#eval isSpaceship lwss_parsed 4 (0, 2)           -- attendu : true

-- Le Pulsar analysé oscille avec une période 3.
#eval isOscillator pulsar_parsed 3               -- attendu : true

end RLE
end Life
end Conway
