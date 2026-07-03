# `finiteness_lean` — English documentation companion

> **Convention — issue #4980, user decision 2026-07-02 (option B).**
> The `.lean` source files (`Finiteness.lean`, `Finiteness/Basic.lean`,
> `lakefile.lean`) are the **canonical French** documentation — the single
> source of truth, unchanged. This file is the **English companion**: a
> non-compiled Markdown mirror of the same docstrings, translated. It follows
> the `README.md` → `README.en.md` pattern of Epic #1650 (pilot: sudoku_lean,
> #4998).
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

## `lakefile.lean` — module

# Lean pedagogical mini-project: Brzozowski symbolic derivatives

A **self-contained project, with no Mathlib dependency**, illustrating the
concept of the symbolic derivative of a regular expression and Brzozowski's
finiteness theorem (1964) — the theoretical foundation for the termination of
non-backtracking recognizers (RE#, .NET `RegexOptions.NonBacktracking`).

The complete **constructive** formalization in Lean 4 is due to Zhuchko,
Maarand, Veanes, Ebner (ITP 2025) — repo `ezhuchko/finiteness-derivatives`.
Since their upstream license is not confirmed, this project **does not vendor**
their code: it illustrates the intuition through original definitions and
examples. See the notebook
[`Lean-14-Finiteness-Derivatives.ipynb`](../Lean-14-Finiteness-Derivatives.ipynb)
for the full pedagogical presentation, and issue #2978 (deliverable C).

(`Finiteness.lean` is a single import line — nothing to mirror.)

---

## `Finiteness/Basic.lean`

### Module

# Brzozowski symbolic derivatives — a self-contained pedagogical demonstration

Let `r` be a regular expression over an alphabet `α`. The **derivative** of `r`
by a character `a` (Janusz Brzozowski, *Derivatives of Regular Expressions*,
JACM 1964) is the expression `D_a(r)` that recognizes exactly those words `w`
such that the word `a :: w` is recognized by `r`. Iterated over the characters
of a word, the derivative computes the match (*matching*) **without
backtracking**: a word `w` is recognized by `r` if and only if the derivative of
`r` by `w` is *nullable* (recognizes the empty word ε).

### The finiteness theorem

Brzozowski (1964) proves that the set of iterated derivatives of a regular
expression is **finite** — modulo the ACI equivalence (Associativity,
Commutativity, Idempotence) of unions. It is this finiteness that guarantees
the **termination** and the **linear** complexity of modern recognizers:
  * .NET `RegexOptions.NonBacktracking` (PLDI 2023),
  * **RE#** (POPL 2025, Varatalu/Veanes/Ernits),
  * SymPy.

### The constructive Lean formalization (ITP 2025)

The **constructive** complete formalization in Lean 4 — one constructs a finite
set bounding the space of derivatives (modulo equivalence) — is due to
**Ekaterina Zhuchko, Hendrik Maarand, Margus Veanes, Gabriel Ebner** (*Finiteness
of Symbolic Derivatives in Lean*, ITP 2025), repo
[`ezhuchko/finiteness-derivatives`](https://github.com/ezhuchko/finiteness-derivatives).
Since its upstream license is not confirmed, **this file does not vendor their
code**: it illustrates the intuition through **original** definitions and
examples, with no dependency (no Mathlib). The notebook
[`Lean-14-Finiteness-Derivatives.ipynb`](../Lean-14-Finiteness-Derivatives.ipynb)
develops the pedagogical presentation and the bridge to the Conway Epic #2162.

### `Regex`

A minimal regular expression over the alphabet `α`.
  * `empty` : empty language ∅
  * `eps`   : empty-word language {ε}
  * `char a`: singleton {a}
  * `concat r s` : concatenation r·s
  * `union r s`  : union r ∪ s
  * `star r`     : Kleene star r*

### `nullable`

`nullable r`: does the regex `r` recognize the empty word ε?
(Fixed point of recognition: a nullable derivative ⇒ the read word is accepted.)

### `deriv`

The **Brzozowski derivative** `D_a(r)`: recognizes the words `w` such that
`a :: w ∈ L(r)`. Standard recursive definition; the `concat` case yields a union
when the left factor is nullable — it is this union that, modulo ACI, bounds
the space of derivatives.

### `derivWord`

Derivative by a word (list of characters): folded from left to right.

### `accepts`

A word `w` is recognized by `r` iff its derivative is nullable. This is
non-backtracking *matching*: each character is consumed exactly once, with no
backtracking. (`matches` is a reserved word in Lean 4, hence the name
`accepts`.)

### Examples: finiteness in action

We observe on concrete examples that the space of derivatives remains finite
(and often tiny) — this is precisely Brzozowski's theorem.

### `aStar`

The language `a*` (Kleene star on the character 'a').

`a*` is a **fixed point** of its derivative by 'a': `D_a(a*) ≡ a*`. The space of
derivatives is thus reduced to a singleton — hence the linear-time recognition.

### `abWord`

The language `ab` (the word "ab"). The successive derivatives by the prefixes
form the finite set {ab, b, ε, ∅}.

Concrete derivative: `D_a(char a) = ε` (the singleton is "consumed").

Concrete derivative: `D_b(char a) = ∅` (distinct characters).

### Note d'homonymie (homonymy footnote)

The bridge to the Conway Epic #2162 calls for a clarification: **Damian Conway**
(author of the famous *sudoku in a Perl regex*, Perlmonks 2002) is not **John
Horton Conway** (mathematician, creator of the *Game of Life* — the hero of our
Lean Epic `conway_lean`). The two Conways "meet" in this SymbolicAI/Lean
series: one through regex recognition, the other through the formalization of
the Game of Life. A nod to document, not a confusion.
