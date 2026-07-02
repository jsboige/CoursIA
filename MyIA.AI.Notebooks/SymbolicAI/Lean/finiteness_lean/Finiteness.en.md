# Finiteness — English documentation companion

> **Convention.** This file is the **English translation of docstrings** in the
> `finiteness_lean` lake. It is a **non-compiled Markdown companion** to the Lean 4
> sources — the **French `.lean` source remains the single source of truth** and
> is unchanged. Tactical `--` comments inside proof bodies are **not** mirrored
> (they remain French-only, tactic-bound). Module docstrings (`/-! ... -/`) and
> per-declaration docstrings (`/-- ... -/`) are translated.
>
> Source lake: [`MyIA.AI.Notebooks/SymbolicAI/Lean/finiteness_lean/`](./).
> Companion convention: PR #4980 rollout, option B (user decision 2026-07-02),
> pilot = PR #4998 (sudoku_lean). See #1650 (multilingual documentation EPIC).

---

## `lakefile.lean` — package manifest

**Module docstring (translated).**

A **self-contained pedagogical Lean project, with no Mathlib dependency**, illustrating the concept of the symbolic derivative of a regular expression and Brzozowski's (1964) finiteness theorem — the theoretical foundation for the termination of non-backtracking matchers (RE#, .NET `RegexOptions.NonBacktracking`).

The **complete** constructive Lean 4 formalization is by Zhuchko, Maarand, Veanes, Ebner (ITP 2025) — repository `ezhuchko/finiteness-derivatives`. Because the upstream license is not confirmed, this project **does not vendor** their code: it illustrates the intuition with **original** definitions and examples. See the notebook [`Lean-14-Finiteness-Derivatives.ipynb`](../Lean-14-Finiteness-Derivatives.ipynb) for the full pedagogical presentation, and issue #2978 (deliverable C).

---

## `Finiteness/Basic.lean` — Brzozowski's symbolic derivatives, pedagogical self-contained proof

**Module docstring (translated).**

Let `r` be a regular expression over an alphabet `α`. The **derivative** of `r` by a character `a` (Janusz Brzozowski, *Derivatives of Regular Expressions*, JACM 1964) is the expression `D_a(r)` that recognizes exactly the words `w` such that the word `a :: w` is recognized by `r`. Iterated over the characters of a word, the derivative computes the **matching** *without backtracking*: a word `w` is recognized by `r` if and only if the derivative of `r` by `w` is **nullable** (recognizes the empty word ε).

### The finiteness theorem

Brzozowski (1964) proves that the set of iterated derivatives of a regular expression is **finite** — modulo the ACI equivalence (Associativity, Commutativity, Idempotence) of unions. This finiteness is what guarantees the **termination** and the **linear complexity** of modern matchers:
  * .NET `RegexOptions.NonBacktracking` (PLDI 2023),
  * **RE#** (POPL 2025, Varatalu/Veanes/Ernits),
  * SymPy.

### The constructive Lean formalization (ITP 2025)

The **complete constructive** Lean 4 formalization — which constructs a finite superset of the derivative space (modulo equivalence) — is by **Ekaterina Zhuchko, Hendrik Maarand, Margus Veanes, Gabriel Ebner** (*Finiteness of Symbolic Derivatives in Lean*, ITP 2025), repository [`ezhuchko/finiteness-derivatives`](https://github.com/ezhuchko/finiteness-derivatives). Because the upstream license is not confirmed, **this file does not vendor their code**: it illustrates the intuition with **original** definitions and examples, with no dependency (no Mathlib). The notebook [`Lean-14-Finiteness-Derivatives.ipynb`](../../Lean-14-Finiteness-Derivatives.ipynb) develops the pedagogical presentation and the bridge to the Conway epic #2162.

### `Regex` — inductive type

A minimal regular expression over the alphabet `α`.
- `empty` : the empty language ∅
- `eps`   : the language of the empty word {ε}
- `char a`: the singleton {a}
- `concat r s` : the concatenation r·s
- `union r s`  : the union r ∪ s
- `star r`     : the Kleene star r*

### `nullable` — definition

`nullable r`: does the regex `r` recognize the empty word ε? (Fixed point of recognition: a nullable derivative means the consumed word is accepted.)

### `deriv` — definition

**Brzozowski's derivative** `D_a(r)`: recognizes the words `w` such that `a :: w ∈ L(r)`. Standard recursive definition; the `concat` case makes a union appear when the left factor is nullable — it is this union that, modulo ACI, bounds the derivative space.

### `derivWord` — definition

Derivative by a word (list of characters): left-folded from left to right.

### `accepts` — definition

A word `w` is recognized by `r` iff its derivative is nullable. This is **non-backtracking matching**: each character is consumed only once, no backtracking. (`matches` is a reserved word in Lean 4, hence the name `accepts`.)

### Examples: finiteness in action

We observe on concrete examples that the derivative space stays finite (and often tiny) — this is precisely Brzozowski's theorem.

#### `aStar` — definition

The language `a*` (Kleene star over the character `'a`).

`a*` is a **fixed point** of its derivative by `'a'`: `D_a(a*) ≡ a*`. The derivative space is therefore reduced to a singleton — hence the linear-time recognition.

#### `abWord` — definition

The language `ab` (the word "ab"). Successive derivatives by prefixes form the finite set {ab, b, ε, ∅}.

#### Concrete derivative: `D_a(char a) = ε`

The singleton is "consumed".

#### Concrete derivative: `D_b(char a) = ∅`

Distinct characters.

### Note on homonymy (pedagogical footnote)

The bridge to the Conway Epic #2162 calls for a clarification: **Damian Conway** (author of the famous *regex sudoku in Perl*, Perlmonks 2002) is **not** **John Horton Conway** (mathematician, creator of the *Game of Life* — the hero of our Epic Lean `conway_lean`). The two Conways "meet" in this SymbolicAI/Lean series: one through regex matching, the other through the formalization of the Game of Life. A wink to document, not a confusion.