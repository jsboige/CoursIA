/-! # Symbolic Brzozowski derivatives — standalone pedagogical demonstration

English mirror of `Finiteness/Basic.lean` (FR-first canonical), EPIC #4980
(i18n Lean). Convention ratified by ai-01 (2026-07-04, #4980
comment-4881909354): distinct FR + EN sibling files in the same lake, both
compile; namespace `Finiteness_en` (anti-collision with FR); non-docstring
content byte-identical (CI drift-detectable); EN docstrings manually translated.

Let `r` be a regular expression over an alphabet `α`. The **derivative** of `r`
with respect to a character `a` (Janusz Brzozowski, *Derivatives of Regular
Expressions*, JACM 1964) is the expression `D_a(r)` that recognises exactly the
words `w` such that `a :: w` is recognised by `r`. Iterated over the characters
of a word, the derivative performs matching **without backtracking**: a word `w`
is recognised by `r` if and only if the derivative of `r` with respect to `w` is
*nullable* (recognises the empty word ε).

## The finiteness theorem

Brzozowski (1964) proves that the set of iterated derivatives of a regular
expression is **finite** — modulo the ACI equivalence (Associativity,
Comutativity, Idempotence) of unions. It is this finiteness that guarantees the
**termination** and **linear** complexity of modern recognisers:
  * .NET `RegexOptions.NonBacktracking` (PLDI 2023),
  * **RE#** (POPL 2025, Varatalu/Veanes/Ernits),
  * SymPy.

## The constructive Lean formalisation (ITP 2025)

The complete **constructive** formalisation in Lean 4 — one builds a finite set
bounding the space of derivatives (modulo equivalence) — is due to **Ekaterina
Zhuchko, Hendrik Maarand, Margus Veanes, Gabriel Ebner** (*Finiteness of
Symbolic Derivatives in Lean*, ITP 2025), repository
[`ezhuchko/finiteness-derivatives`](https://github.com/ezhuchko/finiteness-derivatives).
As its upstream licence is unconfirmed, **this file does not vendor their code**:
it illustrates the intuition with original definitions and examples, with no
dependency (no Mathlib). The notebook
[`Lean-14-Finiteness-Derivatives.ipynb`](../../Lean-14-Finiteness-Derivatives.ipynb)
develops the pedagogical presentation and the bridge to the Conway epic #2162. -/


namespace Finiteness_en

/-- A minimal regular expression over the alphabet `α`.
    * `empty` : empty language ∅
    * `eps`   : singleton empty-word language {ε}
    * `char a`: singleton {a}
    * `concat r s` : concatenation r·s
    * `union r s`  : union r ∪ s
    * `star r`     : Kleene star r* -/
inductive Regex (α : Type) where
  | empty : Regex α
  | eps   : Regex α
  | char  : α → Regex α
  | concat : Regex α → Regex α → Regex α
  | union  : Regex α → Regex α → Regex α
  | star   : Regex α → Regex α
  deriving Repr

open Regex

/-- `nullable r`: does the regex `r` recognise the empty word ε?
    (Fixed point of recognition: a nullable derivative ⇒ the read word is
    accepted.) -/
def nullable {α : Type} : Regex α → Bool
  | empty => false
  | eps => true
  | char _ => false
  | concat r s => nullable r && nullable s
  | union r s => nullable r || nullable s
  | star _ => true

/-- The **Brzozowski derivative** `D_a(r)`: recognises the words `w` such that
    `a :: w ∈ L(r)`. Standard recursive definition; the `concat` case introduces
    a union when the left factor is nullable — it is this union that, modulo ACI,
    bounds the space of derivatives. -/
def deriv {α : Type} [BEq α] (a : α) : Regex α → Regex α
  | empty => empty
  | eps => empty
  | char b => if a == b then eps else empty
  | concat r s => if nullable r then union (concat (deriv a r) s) (deriv a s)
                  else concat (deriv a r) s
  | union r s => union (deriv a r) (deriv a s)
  | star r => concat (deriv a r) (star r)

/-- Derivative with respect to a word (list of characters): folded left to right. -/
def derivWord {α : Type} [BEq α] (w : List α) (r : Regex α) : Regex α :=
  w.foldl (fun r' c => deriv c r') r

/-- A word `w` is recognised by `r` iff its derivative is nullable. This is
    non-backtracking *matching*: each character is consumed once, with no
    backtracking. (`matches` is a reserved word in Lean 4, hence the name
    `accepts`.) -/
def accepts {α : Type} [BEq α] (w : List α) (r : Regex α) : Bool :=
  nullable (derivWord w r)

/-! ## Examples: finiteness in action

We observe on concrete examples that the space of derivatives remains finite (and
often tiny) — precisely Brzozowski's theorem. -/

/-- The language `a*` (Kleene star over the character 'a'). -/
def aStar : Regex Char := star (char 'a')

/- `a*` is a **fixed point** of its derivative with respect to 'a': `D_a(a*) ≡ a*`.
   The derivative space is thus reduced to a singleton — hence linear-time
   recognition. -/
#eval accepts ['a', 'a', 'a', 'a'] aStar   -- "aaaa" ∈ a*  → true
#eval accepts ['a', 'b'] aStar              -- "ab"  ∉ a*  → false

/-- The language `ab` (the word "ab"). Successive derivatives with respect to the
    prefixes form the finite set {ab, b, ε, ∅}. -/
def abWord : Regex Char := concat (char 'a') (char 'b')

#eval accepts ['a', 'b'] abWord   -- "ab" ∈ ab → true
#eval accepts ['a'] abWord        -- "a"  ∉ ab → false
#eval accepts ['a', 'b', 'c'] abWord -- "abc" ∉ ab → false

/- Concrete derivative: `D_a(char a) = ε` (the singleton is "consumed"). -/
example : deriv 'a' (char 'a') = eps := by
  simp [deriv]

/- Concrete derivative: `D_b(char a) = ∅` (distinct characters). -/
example : deriv 'b' (char 'a') = empty := by
  simp [deriv]

/-! ## Namesake note (pedagogical footnote)

The bridge to the Conway epic #2162 calls for a clarification: **Damian Conway**
(author of the famous *sudoku in Perl regex*, Perlmonks 2002) is not **John
Horton Conway** (mathematician, creator of the *Game of Life* — the hero of our
Lean epic `conway_lean`). The two Conways "meet" in this SymbolicAI/Lean series:
one through regex recognition, the other through the formalisation of the Game of
Life. A wink to document, not a confusion. -/

end Finiteness_en
