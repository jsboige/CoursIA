# finiteness_lean — Brzozowski symbolic derivatives

> Series: [`SymbolicAI/Lean`](../README.md) · [`finiteness_lean`](./)

Self-contained pedagogical demonstration **without Mathlib dependency** of the
concept of **symbolic derivative** of a regular expression and of
**Brzozowski's finiteness theorem** (1964) — the theoretical foundation for the
**linear** termination and complexity of modern non-backtracking recognizers.

Lean 4 mini-project from Epic #2978 (deliverable C), shipped via PR #3018.

## Status

- **Toolchain**: `leanprover/lean4:v4.31.0-rc1`
- **Sorry**: **0 sorry, 0 axiom** — everything is proven or illustrated via `#eval`
- **Build**: `lake build Finiteness` — **autonomous, without Mathlib** (Lean core only)
- **Dependencies**: none
- **i18n coverage (EPIC #4980)**: mixed coverage — **inline bilingual aggregator** `Finiteness.lean` (Option B historical pre-#4980, FR + EN sections in `/-! ... -/`) + **substance sibling pair** `Finiteness/Basic.lean` ↔ `Finiteness/Basic_en.lean` (Option A post-#4980, namespace `Finiteness_en` anti-collision, non-docstring content byte-identical CI-detectable) + **Markdown EN companion** `Finiteness.en.md` (non-compiled mirror of docstrings, pre-#4980) + **`README.en.md`** (EN mirror of this file). Out-of-scope: `.lake/packages/`, vendored libs.

## What it formalizes

For a regular expression `r` over an alphabet `α`, the **derivative** of `r` by
a character `a` (Brzozowski, *Derivatives of Regular Expressions*, JACM 1964)
is the expression `D_a(r)` that recognizes exactly the words `w` such that
`a :: w` is recognized by `r`. Iterated over the characters of a word, the
derivative computes **non-backtracking matching**: a word `w` is recognized by
`r` iff the derivative of `r` by `w` is *nullable* (recognizes the empty word ε).

The **finiteness theorem** (Brzozowski 1964): the set of iterated derivatives
of a regular expression is **finite** modulo ACI equivalence (Associativity,
Commutativity, Idempotence) of unions. This finiteness guarantees the
termination and linear complexity of:

- .NET `RegexOptions.NonBacktracking` (PLDI 2023),
- **RE#** (POPL 2025, Varatalu/Veanes/Ernits),
- SymPy.

## Modules

| File | `_en` | Lines | Content |
|------|-------|------:|---------|
| `Finiteness/Basic.lean` | `Basic_en.lean` | 125 | Minimal `Regex α` inductive (empty/eps/char/concat/union/star), `nullable`, `deriv` (Brzozowski derivative), `derivWord`, `accepts` (non-backtracking matching), `#eval` examples illustrating finiteness, 2 `example` lemmas (`D_a(char a) = ε`, `D_b(char a) = ∅`), Conway homonymy note |
| `Finiteness.lean` | `Finiteness.en.md` (MD companion) | 138 | Inline bilingual aggregator: umbrella import + FR + EN sections in `/-! ... -/` + i18n convention note EPIC #4980 (Option B historical pre-#4980, kept for the root) |

## Cite, don't vendor (HARD)

The full **constructive** Lean 4 formalization — building a finite majorant of
the derivative space modulo ACI equivalence — is due to **Ekaterina Zhuchko,
Hendrik Maarand, Margus Veanes, Gabriel Ebner** (*Finiteness of Symbolic
Derivatives in Lean*, ITP 2025), repository
[`ezhuchko/finiteness-derivatives`](https://github.com/ezhuchko/finiteness-derivatives).

Since its upstream license is unconfirmed, **this project does not vendor
their code**: it illustrates the intuition with **original** definitions and
examples, without dependency (no Mathlib). The complete constructive proof
remains in the cited upstream repository, not reproduced here.

## Conway homonymy note (Conway × Conway)

The bridge to the Conway Epic #2162 calls for clarification: **Damian Conway**
(author of the famous *sudoku in Perl regex*, Perlmonks 2002) is not **John
Horton Conway** (mathematician, creator of the *Game of Life* — hero of the
Lean `conway_lean` Epic). The two Conways "meet" in the SymbolicAI/Lean
series: one through regex recognition, the other through the formalization of
the Game of Life.

## Build

```bash
# From this directory (WSL required for lake)
lake build Finiteness
# Autonomous, without Mathlib: builds in a few seconds
```

## Pedagogical notebook

[`Lean-14-Finiteness-Derivatives.ipynb`](../Lean-14-Finiteness-Derivatives.ipynb)
— full pedagogical presentation and bridge to the Conway Epic #2162.

## See also

- **Epic #2978** — Sudoku as a symbolic regex (Conway → BREX/Rex → RE#), deliverable C
- **Epic #2162** — Conway (homonymy bridge + theoretical base for RE#)
- **`conway_lean/`** — Game of Life in Lean (the other Conway)
- **EPIC #4980** — Lean i18n convention (Option A sibling pair post-2026-07-04 + Option B aggregator bilingual pre-#4980)
- Upstream cited repository: [`ezhuchko/finiteness-derivatives`](https://github.com/ezhuchko/finiteness-derivatives) (Zhuchko et al., ITP 2025)

## Conclusion

`finiteness_lean` demonstrates in a **self-contained** way (Lean core alone,
without Mathlib, 0 `sorry`, 0 axiom) the intuition behind two Brzozowski (1964)
results: the **symbolic derivative** of a regular expression and the
**finiteness theorem** of iterated derivatives modulo ACI equivalence. It is
this finiteness that guarantees the termination and **linear** complexity of
modern non-backtracking recognizers (.NET `RegexOptions.NonBacktracking`,
RE#, SymPy).

### What the project brings

A minimal `Regex α` definition (empty/eps/char/concat/union/star), the `deriv`
derivative and its iterated `derivWord`, and non-backtracking `accepts`
matching — illustrated by `#eval` examples and two `example` lemmas. The whole
is proven or illustrated without added axiom, in a mini-project of a single
useful module.

### Honesty of scope

The complete **constructive proof** of finiteness (a finite majorant of the
derivative space modulo ACI) is due to Zhuchko, Maarand, Veanes, and Ebner
(ITP 2025). Since its upstream license is unconfirmed, this project **does not
vendor** their code: it gives **original** definitions and examples, and
refers to the upstream repository for the complete proof. The bridge to the
Conway Epic #2162 passes through a homonymy that must be cleared: **Damian
Conway** (Perl regex) ≠ **John Horton Conway** (Game of Life).

### Where to go next

- **Depth**: the complete constructive proof in the cited upstream repository.
- **Pedagogy**: the `Lean-14-Finiteness-Derivatives.ipynb` notebook.
- **Related Epics**: #2978 (Sudoku as a symbolic regex), #2162 (Conway).