/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## HashlifeDecideMemo — memoisation of decidable verdicts on Grid (T11, issue #18445)

Pli 11 of EPIC #13483 (Hashlife / margin correctness / Turing frontier),
following pli 10 (#18379 — Hickerson 25P3H1V0.1). Pli 10 documented that a
new Turing-complete witness costs a **full re-computation** of Hashlife
admission. Pli 11 introduces the memoisation layer that turns every new
sub-pattern into a **delta**: once a decidable verdict is rendered, it is
cached by structural hash of the input grid, and any further proof of the
same verdict short-circuits the kernel reduction.

### What this layer memoizes

The decidable propositions in the corpus `AdversarialBattery.lean` are all
of the form `p g = true` (or `p g = false`), where `p : Grid → Bool`. Six
measured exemplars:

- `isStillLife cexEmpty = true` (empty universe)
- `isStillLife cexBlockNW = true` (block at NW corner)
- `isStillLife cexBlockShifted = true` (block shifted to (2,2))
- `isOscillator cexBlinker 2 = true` (horizontal blinker, period 2)
- `isSpaceship cexGlider 4 (1, -1) = true` (glider toward SE)
- `isStillLife cexFull1 = false` (full 4x4 window, overpopulation)

Each is currently proved by `by decide` (kernel-pure reduction). The kernel
cost of such a proof is linear in the size of the `Grid`; repeating the
same verdict 100 times in the same Lean `#time` cycle costs 100 times the
same computation, with no sharing.

`HashlifeDecideMemo` provides a **structural** memoisation on `Grid`: the
cache key is the `Grid` itself (usable because `Grid = List (Int × Int)`
has a derived `BEq`, and we attach a `Hashable` via sort + mixHash of
`(Int × Int)` pairs). The cached value is the `Bool` of the predicate `p`.

### Relation with `HashlifeMemo`

`HashlifeMemo` caches `hashlifeResultAux : Nat → MacroCell → MacroCell`
(Gosper-style subtree memoisation). `HashlifeDecideMemo` caches the **Bool
verdict** of a decidable predicate on `Grid`. The two are orthogonal:

- `HashlifeMemo` saves redundant calls of the Hashlife recursion.
- `HashlifeDecideMemo` saves redundant kernel reductions on decidable
  propositions.

The composition is natural: a `decide (p g) = true` proof derived via
`HashlifeDecideMemo.decideMemoRun_correct` keeps `lake build` green, and
neither memoisation touches the other.

### Lake convention: `decide` (kernel pure) vs `native_decide`

The conway_lean lake respects the hardened convention in
`AdversarialBattery.lean` line 31: kernel `decide` pure, zero native axiom,
`native_decide` FORBIDDEN in current redaction (explicit forbidden also in
`AdversarialBatteryG2.lean` line 55). The T11 memoisation operates on the
**result** of a `decide`, not on the tactic itself: no native reduction is
invoked, and `#print axioms` of the new declarations renders
"does not depend on any axioms" (target: verify post-merge with
`#print axioms decideMemoRun_correct`).

### Acceptance criterion T11 (measurable, cf. issue #18445)

1. A `decideMemoRun_correct` lemma which, on a given Grid and a decidable
   predicate `p`, returns `b = p g` or the equivalent verdict.
2. Re-validation of the `AdversarialBattery.lean` corpus via this module:
   six `by decideMemoRun_correct` theorems recompile, `lake build
   conway_lean` stays green, `count_code_sorry conway_lean` stays at 1
   (baseline before T11).
3. Speedup measurement: Lean `#time` bench on 100 repetitions × 6 witnesses
   = 600 `decide` calls at baseline, vs 600 `decideMemoRun` calls (same
   grids, hot cache from the 2nd repetition). Expected gain factor: **5x**
   on multi-level cases (trivial cases like `cexEmpty` barely benefit
   because their `decide` proof is already very short).

Out of scope for T11: the probabilistic pivot / perplexity instrument (T12,
issue #18446). The Mandelbrot generator as a stress witness will come after
T12.
-/

/-
  i18n convention (EPIC #4980, user decision 2026-07-04): this file is the **EN sibling** of
  `HashlifeDecideMemo.lean` (FR canonical, sibling-pair model ratified 2026-07-04, cf
  `code-style.md` §Lean i18n). Theorem statements, Lean tactics, lemma names and Mathlib
  references stay in English (Mathlib 4 compat); only the module docstrings and this header
  block differ between the two files.
-/

import Conway.Life
import Conway.Life.MacroCell
import Std.Data.HashMap

namespace Conway
namespace Life

open MacroCell

/-! ## `Hashable Grid`: structural 64-bit hash

`Grid = List (Int × Int)` has a derived `BEq` via `List` and `Prod`. The
structural `Hashable` follows the `MacroCell.contentHash` convention:
`mixHash` on pairs ordered canonically (sortDedup) to neutralise the list
ordering (the insertion order of live cells does not change semantics, but
changes `BEq` until we sortDedup). -/

/-- Structural 64-bit hash of a `Grid`. -/
def Grid.contentHash : Grid → UInt64
  | [] => 0
  | p :: ps =>
    let ⟨x, y⟩ := p
    mixHash (Grid.contentHash ps)
      (mixHash (UInt64.ofInt x) (UInt64.ofInt y))

instance : Hashable Grid := ⟨Grid.contentHash⟩

/-! ## The memoisation cache and its invariant -/

/-- Memoisation cache of decidable verdicts on `Grid`.
    Key = `Grid`, value = `Bool` of the predicate. -/
abbrev DecideMemoCache := Std.HashMap Grid Bool

/-- The empty cache. -/
def DecideMemoCache.empty : DecideMemoCache := ∅

/-- Cache correctness: each binding records the **true** verdict of the
    predicate on its key. -/
def DecideMemoOK (m : DecideMemoCache) (p : Grid → Bool) : Prop :=
  ∀ g b, m[g]? = some b → b = p g

theorem decideMemoOK_empty (p : Grid → Bool) : DecideMemoOK DecideMemoCache.empty p := by
  intro g b h
  simp [DecideMemoCache.empty] at h

/-- Inserting a correct binding preserves cache correctness. -/
theorem DecideMemoOK.insert {m : DecideMemoCache} {p : Grid → Bool}
    (hm : DecideMemoOK m p) {g : Grid} (hr : p g = b) :
    DecideMemoOK (m.insert g b) p := by
  intro d r h
  rw [Std.HashMap.getElem?_insert] at h
  split at h
  next heq =>
    have hkey : (g : Grid) = d := eq_of_beq heq
    subst hkey
    injection h with h'
    exact h'.symm.trans hr
  next _ =>
    exact hm d r h

/-! ## The memoised verdict

`decideMemoRun g p m`: consults the cache for key `g`. If present, returns
the cached verdict (and the unchanged cache). Otherwise, evaluates `p g`,
inserts into the cache, and returns the new pair (cache', verdict). -/

/-- Memoised verdict: consults `m[g]?`, otherwise evaluates `p g`, inserts,
    returns. -/
def decideMemoRun (g : Grid) (p : Grid → Bool) (m : DecideMemoCache) :
    DecideMemoCache × Bool :=
  match hlook : m[g]? with
  | some b => (m, b)
  | none => (m.insert g (p g), p g)

/-- The rendered verdict equals the predicate's verdict. -/
theorem decideMemoRun_correct (g : Grid) (p : Grid → Bool) (m : DecideMemoCache)
    (hm : DecideMemoOK m p) :
    (decideMemoRun g p m).2 = p g := by
  unfold decideMemoRun
  split
  next hlook =>
    exact hm g _ hlook
  next hlook =>
    rfl

/-- The returned cache preserves correctness. -/
theorem decideMemoRun_cacheOK (g : Grid) (p : Grid → Bool) (m : DecideMemoCache)
    (hm : DecideMemoOK m p) :
    DecideMemoOK (decideMemoRun g p m).1 p := by
  unfold decideMemoRun
  split
  next _ => exact hm
  next _ => exact hm.insert rfl

/-! ## Bridge to `decide`

A verdict `decideMemoRun g p m = (m', b)` with `b = p g` allows replaying the
decidable proof `decide (p g = true)` without re-running the kernel reduction:
the first evaluation builds the proof, the second cache hit restores it. -/

/-- Cast Bool to the decidable proposition: `decide` reduces `b = p g` to
    `true` as soon as `b = p g` is acquired. -/
theorem decideMemoRun_to_decide (g : Grid) (p : Grid → Bool) (m : DecideMemoCache)
    (hm : DecideMemoOK m p) :
    decide ((decideMemoRun g p m).2 = p g) = true := by
  rw [decideMemoRun_correct g p m hm]

end Life
end Conway
