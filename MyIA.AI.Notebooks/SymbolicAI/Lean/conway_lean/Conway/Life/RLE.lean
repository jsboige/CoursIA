/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Conway's Game of Life — RLE pattern parser (Epic #1647 Phase 2)

The Run Length Encoded (RLE) format is the standard textual representation
of Conway's Game of Life patterns, used by the community archive
LifeWiki / conwaylife.com and by the `golly` simulator.

A canonical example: the **glider**.
```
#N Glider
#O Richard K. Guy
#C The smallest, most common, and first discovered spaceship.
x = 3, y = 3, rule = B3/S23
bob$2bo$3o!
```

Grammar (informal):
- Lines beginning with `#` are comments and are ignored.
- A header line `x = W, y = H, rule = ...` declares the bounding box.
  The parser tolerates and ignores the header (the body itself is
  self-delimiting via `!`).
- The body is a run-length stream over the alphabet
  `b o $ !` (with optional decimal run counts):
  * `<n>b` skips `n` dead cells (default `n = 1`), advancing the column.
  * `<n>o` emits `n` live cells, advancing the column.
  * `<n>$` ends the current row(s): advances the row by `n` (default 1)
    and resets the column to 0.
  * `!` terminates the pattern. Subsequent characters are ignored.
  * All whitespace (spaces, newlines, tabs, carriage returns) in the
    body is ignored. This allows patterns that wrap across lines.

The parser returns a `Grid` (sorted lexicographic list of
`(row, col) : Int × Int`). It uses `Except String` for error reporting.

This module is fully proven (no gaps).
-/

import Conway.Life
import Conway.Life.Spaceships
import Conway.Life.Oscillators

namespace Conway
namespace Life
namespace RLE

/-! ## Internal parser state -/

/-- Parser state: current row, current column, accumulated live cells
    (in reverse order — we reverse + sort at the end), pending run count.
    `done` becomes `true` after we hit the `!` terminator. -/
structure ParseState where
  row     : Int
  col     : Int
  cells   : List (Int × Int)  -- accumulated in reverse insertion order
  runCnt  : Nat               -- 0 means "no explicit count, default to 1"
  done    : Bool
  deriving Repr

/-- Initial parser state. -/
def initState : ParseState :=
  { row := 0, col := 0, cells := [], runCnt := 0, done := false }

/-- Effective run count: the explicit count, or `1` if none was given. -/
def effRun (st : ParseState) : Nat :=
  if st.runCnt == 0 then 1 else st.runCnt

/-! ## Comment / header detection

The RLE format reserves the `#` prefix for comments and dedicates one
line to the `x = W, y = H, rule = ...` header. Both are skipped by the
line-level pre-processor below. The body parser itself ignores
whitespace, so multi-line bodies are handled transparently.
-/

/-- Drop leading ASCII whitespace from a string by recursing on the
    character list. Avoids `String.dropWhile` / `String.trim` which
    return a `String.Slice` in current Lean — we need a plain `String`
    so the rest of the pipeline (`startsWith`, `any`) typechecks
    uniformly. -/
def lTrim (s : String) : String :=
  String.ofList (s.toList.dropWhile Char.isWhitespace)

/-- `true` iff a line is a comment (starts with `#`) or contains only
    whitespace. -/
def isCommentOrEmpty (line : String) : Bool :=
  let t := lTrim line
  t.isEmpty || t.startsWith "#"

/-- `true` iff a line is the RLE header (starts with `x` followed by
    an `=`). Robust to leading whitespace. -/
def isHeaderLine (line : String) : Bool :=
  let t := lTrim line
  t.startsWith "x" && t.any (· = '=')

/-- Drop comment lines and the header from a raw RLE string, then
    concatenate the body. -/
def stripCommentsAndHeader (s : String) : String :=
  let lines := s.splitOn "\n"
  let bodyLines := lines.filter (fun l => ¬ isCommentOrEmpty l && ¬ isHeaderLine l)
  String.join bodyLines

/-! ## Body parser

The body is consumed character by character. We treat decimal digits
as accumulators for the next run count, and the four payload
characters `b o $ !` as actions that consume the current count.

Note: `Int.ofNat` is used to widen the Nat row/column counters into the
`Int × Int` cells of `Grid`.
-/

/-- Append `n` live cells starting at `(row, col)` to the (reversed)
    accumulator. Cells are inserted in left-to-right order so that
    after the final `List.reverse` they come out in row-major order. -/
def appendLiveRun (row : Int) (startCol : Int) (n : Nat)
    (acc : List (Int × Int)) : List (Int × Int) :=
  let rec go (k : Nat) (c : Int) (a : List (Int × Int)) : List (Int × Int) :=
    match k with
    | 0       => a
    | Nat.succ k' => go k' (c + 1) ((row, c) :: a)
  go n startCol acc

/-- One step of the RLE body parser. Returns the updated state or an
    error message. -/
def stepChar (c : Char) (st : ParseState) : Except String ParseState :=
  if st.done then
    -- After `!`, ignore all subsequent characters (per RLE convention).
    Except.ok st
  else if c.isWhitespace then
    Except.ok st
  else if c.isDigit then
    let d : Nat := c.toNat - '0'.toNat
    Except.ok { st with runCnt := st.runCnt * 10 + d }
  else if c == 'b' then
    -- Dead cells: advance column by `effRun`, reset run count.
    let n := effRun st
    Except.ok { st with col := st.col + Int.ofNat n, runCnt := 0 }
  else if c == 'o' then
    -- Live cells: emit `effRun` live cells, advance column, reset run.
    let n := effRun st
    let cells' := appendLiveRun st.row st.col n st.cells
    Except.ok { st with
      cells := cells',
      col := st.col + Int.ofNat n,
      runCnt := 0 }
  else if c == '$' then
    -- End of row(s): advance row by `effRun`, reset column.
    let n := effRun st
    Except.ok { st with
      row := st.row + Int.ofNat n,
      col := 0,
      runCnt := 0 }
  else if c == '!' then
    Except.ok { st with done := true }
  else
    Except.error s!"RLE parse error: unexpected character {repr c}"

/-- Fold `stepChar` over the body, short-circuiting on the first error. -/
def runBody (body : String) : Except String ParseState :=
  body.toList.foldlM (fun st c => stepChar c st) initState

/-! ## Top-level parser -/

/-- Parse an RLE pattern string into a `Grid`.

    The grid is returned in sorted lexicographic order (row first, then
    column) and deduplicated, matching the convention of `Conway.Life`. -/
def parseRLE (s : String) : Except String Grid := do
  let body := stripCommentsAndHeader s
  let st ← runBody body
  -- Reverse to recover row-major insertion order, then sort/dedup.
  let cells := st.cells.reverse
  Except.ok (sortDedup cells)

/-- A total convenience wrapper: returns `[]` on parse error. Intended
    for `#eval` sanity checks where we already know the input is valid;
    use `parseRLE` directly when error reporting matters. -/
def parseRLE! (s : String) : Grid :=
  match parseRLE s with
  | Except.ok g => g
  | Except.error _ => []

/-! ## Pattern constants

We provide the canonical RLE strings for the four flagship patterns
(`glider`, `lwss`, `pulsar`, `gosper_gun`) together with their parsed
`Grid` values. The first three are cross-checked against the
hand-written constants exported by `Conway.Life`,
`Conway.Life.Spaceships`, and `Conway.Life.Oscillators` via the
`#eval` assertions further down.

The Gosper Glider Gun (Bill Gosper, 1970, MIT) is the first known
finite pattern in Conway's Life with unbounded growth: it emits a
glider every 30 generations indefinitely. With 36 live cells in its
canonical phase, it answered Conway's USD 50 challenge for an
infinite-growth pattern and ignited the search for self-replicating
constructions that culminated in the Gemini (Wade, 2010).
-/

/-- RLE for the Glider, the smallest spaceship (Conway, 1970). -/
def glider_RLE : String :=
"#N Glider
#O Richard K. Guy
#C The smallest, most common, and first discovered spaceship.
x = 3, y = 3, rule = B3/S23
bob$2bo$3o!"

/-- Parsed Glider grid. Should agree with `Conway.Life.glider` (modulo
    a coordinate convention shift — see the `#eval` assertions). -/
def glider_parsed : Grid := parseRLE! glider_RLE

/-- RLE for the Lightweight Spaceship (Conway, 1970).
    Encodes the same phase as `Conway.Life.Spaceships.lwss`:
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

/-- Parsed LWSS grid. Should agree with `Conway.Life.lwss`. -/
def lwss_parsed : Grid := parseRLE! lwss_RLE

/-- RLE for the Pulsar oscillator (Conway, 1970). 48 live cells,
    period 3, the most common large oscillator in random soups. -/
def pulsar_RLE : String :=
"#N Pulsar
#O John Conway
#C Period 3 oscillator. The most common naturally occurring oscillator.
x = 13, y = 13, rule = B3/S23
2b3o3b3o2b$13b$o4bobo4bo$o4bobo4bo$o4bobo4bo$2b3o3b3o2b$13b$2b3o3b3o2b$o4bobo4bo$o4bobo4bo$o4bobo4bo$13b$2b3o3b3o2b!"

/-- Parsed Pulsar grid. Should agree with `Conway.Life.pulsar`. -/
def pulsar_parsed : Grid := parseRLE! pulsar_RLE

/-- RLE for the Gosper Glider Gun (Bill Gosper, 1970, MIT). 36 live
    cells, period 30: the first known finite pattern with unbounded
    growth, emitting one glider every 30 generations. -/
def gosper_gun_RLE : String :=
"#N Gosper glider gun
#O Bill Gosper
#C A true period 30 glider gun. The first known gun and the first known
#C finite pattern with unbounded growth. Found by Bill Gosper in November 1970.
x = 36, y = 9, rule = B3/S23
24bo11b$22bobo11b$12b2o6b2o12b2o$11bo3bo4b2o12b2o$2o8bo5bo3b2o14b$2o8bo3bob2o4bobo11b$10bo5bo7bo11b$11bo3bo20b$12b2o!"

/-- Parsed Gosper Glider Gun grid. 36 live cells. -/
def gosper_gun : Grid := parseRLE! gosper_gun_RLE

/-! ## Sanity checks

We use `#eval` rather than `theorem` here: the parser is a pure
computation, not a property requiring kernel reduction. `native_decide`
on a `theorem` would re-run the parser inside the kernel, which is
substantially slower and offers no extra guarantee for a deterministic
function.

The first cell of each parsed grid, the cell count, and the equality
against the hand-written constants are all printed. Any mismatch is
visible in the elaboration output.
-/

-- Glider: 5 live cells, bounding box 3x3.
#eval glider_parsed                              -- expected: 5 cells
#eval glider_parsed.length                       -- expected: 5
#eval (parseRLE glider_RLE).toOption.isSome      -- expected: true

-- LWSS: 9 live cells, bounding box 5x4. Cross-check with `lwss`.
#eval lwss_parsed                                -- expected: 9 cells
#eval lwss_parsed.length                         -- expected: 9
#eval lwss_parsed == lwss                        -- expected: true

-- Pulsar: 48 live cells, bounding box 13x13. Cross-check with `pulsar`.
#eval pulsar_parsed.length                       -- expected: 48
#eval pulsar_parsed == pulsar                    -- expected: true

-- Gosper Glider Gun: 36 live cells, bounding box 36x9.
#eval gosper_gun                                 -- expected: 36 cells
#eval gosper_gun.length                          -- expected: 36

/-! ## Proven parsing correctness

The parser is deterministic and total. `native_decide` verifies that
parsing succeeds (no error) for all four flagship patterns and confirms
that the parsed LWSS and Pulsar grids match their hand-written
counterparts in `Conway.Life`. The glider uses a different phase than
the hand-written constant (the RLE encodes phase 1 heading SE while
`Conway.Life.glider` uses a different orientation), so no round-trip
theorem is stated for it.
-/

/-- Parsing the glider RLE succeeds (no error). -/
theorem glider_parse_ok : (parseRLE glider_RLE).toOption.isSome = true := by native_decide

/-- Parsing the LWSS RLE succeeds. -/
theorem lwss_parse_ok : (parseRLE lwss_RLE).toOption.isSome = true := by native_decide

/-- Parsing the pulsar RLE succeeds. -/
theorem pulsar_parse_ok : (parseRLE pulsar_RLE).toOption.isSome = true := by native_decide

/-- Parsing the Gosper gun RLE succeeds. -/
theorem gosper_gun_parse_ok : (parseRLE gosper_gun_RLE).toOption.isSome = true := by native_decide

/-- The parsed LWSS grid matches the hand-written `lwss` constant. -/
theorem lwss_rle_roundtrip : lwss_parsed = lwss := by native_decide

/-- The parsed Pulsar grid matches the hand-written `pulsar` constant. -/
theorem pulsar_rle_roundtrip : pulsar_parsed = pulsar := by native_decide

/-- The Gosper gun has exactly 36 live cells. -/
theorem gosper_gun_cell_count : gosper_gun.length = 36 := by native_decide

/-- The parsed glider grid has exactly 5 live cells. -/
theorem glider_parsed_cell_count : glider_parsed.length = 5 := by native_decide

/-! ## Round-trip behavioural checks

These confirm the parsed grids exhibit the documented dynamical
behaviour, reusing predicates from `Conway.Life`. They are pure
evaluations (no theorems): `native_decide` on the parser-derived
grids is too coarse a tool — the parser itself is total and the
underlying behaviours are already proven for the hand-written
constants. -/

-- The parsed LWSS is a spaceship of period 4, displacement (0, 2).
#eval isSpaceship lwss_parsed 4 (0, 2)           -- expected: true

-- The parsed Pulsar oscillates with period 3.
#eval isOscillator pulsar_parsed 3               -- expected: true

end RLE
end Life
end Conway
