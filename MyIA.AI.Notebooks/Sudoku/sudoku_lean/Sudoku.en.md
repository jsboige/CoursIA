# `sudoku_lean` — English documentation companion

> **Convention — issue #4980, user decision 2026-07-02 (option B).**
> The `.lean` source files (`Sudoku.lean`, `Sudoku/Basic.lean`,
> `Sudoku/Propagation.lean`, `lakefile.lean`) are the **canonical French**
> documentation — the single source of truth, unchanged. This file is the
> **English companion**: a non-compiled Markdown mirror of the same docstrings,
> translated. It follows the `README.md` → `README.en.md` pattern of Epic #1650.
>
> - **Zero build cost** (Markdown is not compiled by `lake`), **zero risk** to
>   compilation — the `.lean` files are untouched.
> - **Source of truth = the `.lean`**. If the two ever disagree, the French in
>   the `.lean` wins; this companion mirrors the source and is regenerated
>   against it. Section order below matches declaration order in each file so
>   drift is easy to spot.
> - Tactical `--` comments (inline, developer-facing, tactic-bound) are
>   French-only in the source by convention and are **not** mirrored here — they
>   are tied to the Lean tactic language and add noise if duplicated.

---

## `Sudoku.lean` — module

# Sudoku — soundness of constraint propagation (Lean 4)

Formalization of the **soundness of the propagation rules** of a Sudoku (naked
single, hidden single), the formal foundation of the solvers taught in the
`Sudoku` series (backtracking, OR-Tools, .NET). See issue #4055 (Lean roadmap
#4038).

### Contents
- `Sudoku.Basic`: the abstract constraint structure — `Scopes` (all-distinct
  scopes), `Solution`, `IsSolution`, `AllDistinctOn`, `IsPeer`, `PresentIn`.
  The abstraction captures any CSP with "all-distinct scopes" (the 9×9 grid is
  an instance, not a special case).
- `Sudoku.Propagation`: the **keystone** `peer_excludes_value` (an assigned cell
  excludes its value from its peers) and the two soundness theorems
  `naked_single_sound` + `hidden_single_sound`, 0 `sorry`.

### Status
- Proved without `sorry`: the soundness of the naked/hidden single rules (via
  the keystone `peer_excludes_value`). Propagation removes **no valid solution**.
- Open (next milestone): the **Sudoku ⇔ exact-cover reduction** (Knuth, 4
  constraint families) and the completeness of the rules. Not `sorry`-backed.
- Out of scope: the "17 clues minimum" result (massive computation, not
  formalizable).

### Cross-reference
- The `Sudoku` series (C#/.NET + Python): the backtracking/OR-Tools/Infer.NET
  solvers whose propagation step this lake formally grounds.
- #2978 (Sudoku as a symbolic regex): the Lean angle there is
  `finiteness-derivatives` (recognizer termination), **without overlap** with
  the propagation/exact-cover formalized here (coordination verified).

---

## `Sudoku/Basic.lean`

### Module

# Sudoku.Basic — constraint structure, solutions, peers

Abstract formalization of a Sudoku (more generally: any constraint-satisfaction
problem with "all-distinct scopes"). A concrete 9×9 Sudoku is an instance of
this framework: the **scopes** are its 27 families (9 rows, 9 columns, 9
blocks), each required to carry **all-distinct** values.

The abstraction is deliberate: the soundness theorems of propagation
(`Propagation.lean`) hold for **any** structure of this type, not just the 9×9.
This is the right level of formalization — the logic of propagation does not
depend on there being 9 values or 3×3 blocks, only on the invariant
"all-distinct per scope".

Cross-reference: the `Sudoku` series (backtracking, OR-Tools, .NET, Infer.NET)
whose propagation solvers this lake formally grounds. See issue #4055.

### `Scopes`

The constraint structure of a Sudoku: a finite set of **scopes** (each a
`Finset` of cells) required to carry all-distinct values.

### `Solution`

A complete assignment: one value per cell.

### `AllDistinctOn`

`σ` is **all-distinct on `s`** if two distinct cells of `s` never carry the same
value (injectivity of `σ` on `s`).

### `IsSolution`

`σ` is a **solution** of the structure `scopes` if it is all-distinct on each
scope. This is the fundamental Sudoku invariant (each row, column, and block
contains each value at most once).

### `AgreesWith`

`σ` **agrees** with a partial assignment `a` wherever `a` is defined.

### `IsPeer`

`c'` is a **peer** of `c` if they are distinct and share at least one scope. Two
peer cells cannot carry the same value in a solution.

### `PresentIn`

A value `v` is **present in the scope `s`** if some cell of `s` carries it. For
a "full house" scope (|s| = |V|) of a solution, every value is present there
(full-house lemma).

### `full_house_present`

**Full-house lemma.** If a scope `s` contains as many cells as possible values
(`s.card = card V`) and an assignment `σ` is all-distinct on `s`, then **every**
value `v` is present in `s`.

This is the pigeonhole argument: `σ` restricted to `s` is injective, so its
image has `card s = card V` distinct elements — i.e. all of `V` — hence every
value appears there. This lemma makes the `PresentIn σ s v` hypothesis of the
"hidden single" (`Propagation.hidden_single_sound`) automatic in the full-house
case (cf #4055).

---

## `Sudoku/Propagation.lean`

### Module

# Sudoku.Propagation — soundness of the propagation rules

Issue #4055. Sudoku solvers (backtracking, OR-Tools, .NET from the `Sudoku`
series) speed up resolution by **propagating** constraints: as soon as a value
is placed, candidates that have become impossible are eliminated. Two canonical
rules:

- **Naked single**: a cell whose only remaining candidate is `v` must contain
  `v`.
- **Hidden single**: a value that can go in only one cell of a scope must go
  there.

This module proves the **soundness** of these rules: they **remove no valid
solution** — eliminating a candidate via propagation is eliminating an
assignment that **no solution uses**. The keystone is `peer_excludes_value`: an
assigned cell excludes its value from all its peers.

**Honest scoping (G.3/G.9).** The soundness of both propagation rules is proved
in full (0 `sorry`). The **Sudoku ⇔ exact-cover reduction** (Knuth, 4 constraint
families), and completeness (do the rules suffice to solve every Sudoku? no in
general — hence backtracking), are natural milestones left **open**, deliberately
**not `sorry`-backed**: the library stays entirely `sorry`-free. The massive
"17 clues minimum" computation result is out of scope (not formalizable).

## Keystone: exclusion by peers

### `peer_excludes_value`

**Keystone.** In a solution, a cell `c` carrying the value `v` excludes `v` from
every **peer** cell `c'` (same scope): `σ c' ≠ v`. This is the fundamental fact
from which all propagation rules derive.

**Proof** (0 `sorry`): `c` and `c'` share a scope `s`; `σ` is all-distinct on
`s`, so `σ c = σ c'` would imply `c = c'`, contradicting `c ≠ c'` (definition of
peer).

## Naked single

### `naked_single_sound`

**Naked single (soundness).** If, in a solution `σ`, every value except `v` is
already carried by a **peer** of `c` (i.e. each `w ≠ v` appears on a peer cell
of `c`), then `σ c = v`.

This is the formalization of the "naked single": cell `c` has only `v` left as a
possible candidate (all other values are excluded by its peers), so every
solution places `v` there. The rule removes no solution because it identifies a
**forced** value.

**Proof** (0 `sorry`): by contradiction, `σ c = w ≠ v`. By the coverage
hypothesis, `w` appears on a peer `c'` of `c`; but `peer_excludes_value`
forbids `c'` from carrying `σ c`. Contradiction.

## Hidden single

### `hidden_single_sound`

**Hidden single (soundness).** If, in a solution `σ` of the structure `scopes`,
the value `v` is present in the scope `s` (`PresentIn σ s v`), with `c ∈ s`, and
`v` is **excluded** from every other cell `c' ∈ s` (each `c' ≠ c` has a peer
carrying `v`), then `σ c = v`.

This is the formalization of the "hidden single": within a scope, `v` can only
go in `c`, so every solution places it there. For a "full house" scope
(`|s| = |V|`), the `PresentIn σ s v` hypothesis is automatic (every value
appears).

**Proof** (0 `sorry`): `v` appears at `c0 ∈ s`. If `c0 ≠ c`, the exclusion
hypothesis gives a peer `c''` of `c0` carrying `v`; but `peer_excludes_value`
forbids `c''` from carrying `σ c0 = v`. Contradiction. Hence `c0 = c`,
`σ c = v`.

---

## `lakefile.lean` — module

# Lean pedagogical mini-project: soundness of Sudoku constraint propagation

A Lean 4 project (with Mathlib) proving the **soundness of the Sudoku
propagation rules** (naked single, hidden single): these rules, used by every
solver taught in the `Sudoku` series (backtracking, OR-Tools, .NET), **remove no
valid solution** — they only eliminate impossible assignments. See issue #4055
(Lean roadmap #4038). Coordination #2978 verified: the Lean angle of #2978 is
regex-recognizer termination (`finiteness-derivatives`), without overlap with the
propagation/exact-cover formalized here.

First Lean theorem of the **Sudoku** series. The formalization is **abstract
over the constraint structure** (a Sudoku = a set of "scopes" `scopes`, each
required to carry all-distinct values): the soundness theorems hold for any
structure of this type (rows, columns, blocks of the 9×9, but also any CSP with
all-distinct scopes). The concrete 9×9 is an instance, not a special case.

**Keystone**: `peer_excludes_value` — an assigned cell excludes its value from
all its "peer" cells (same scope) in any solution. This is the fundamental fact
from which the propagation rules derive:

- `naked_single_sound`: if all values except `v` are already present among the
  peers of a cell, every solution places `v` there.
- `hidden_single_sound`: if a value can go in only one cell of a scope, every
  solution places it there.

The Sudoku ⇔ exact-cover equivalence (Knuth, 4 constraint families) is a natural
milestone left open (not `sorry`-backed) — propagation soundness is delivered in
full.

Mathlib provides `Finset`, injectivity on a set (`Set.InjOn`), and the finite
image arithmetic needed.

Companion notebook (from the `Sudoku` series): pedagogical presentation of the
propagation solvers. Wiring the notebook is the responsibility of the Sudoku
series owner (convention of the sibling lakes: the lake is the formal
deliverable, `lake build` is the proof of execution).
