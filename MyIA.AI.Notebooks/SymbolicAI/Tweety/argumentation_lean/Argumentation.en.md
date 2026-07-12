# Argumentation — English documentation companion

> **Convention.** This file is the **English translation of docstrings** in the
> `argumentation_lean` lake. It is a **non-compiled Markdown companion** to the Lean 4
> sources — the **French `.lean` source remains the single source of truth** and
> is unchanged. Tactical `--` comments inside proof bodies are **not** mirrored
> (they remain French-only, tactic-bound). Module docstrings (`/-! ... -/`) and
> per-declaration docstrings (`/-- ... -/`) are translated.
>
> Source lake: [`MyIA.AI.Notebooks/SymbolicAI/Tweety/argumentation_lean/`](./).
> Companion convention: PR #4980 rollout, option B (user decision 2026-07-02),
> pilot = PR #4998 (sudoku_lean). See #1650 (multilingual documentation EPIC).

---

## `lakefile.lean` — package manifest

**Module docstring (translated).**

A pedagogical Lean 4 project (with Mathlib) formalizing **Dung's abstract argumentation theory (1995)**: argumentation frameworks, extensions (admissible, complete, grounded, preferred, stable) and the **fixed-point theorem** (the grounded extension = least fixed point of the characteristic function, Knaster–Tarski). See issue #4046 (roadmap #4038).

This is the formal core of the Tweety series and a **direct bridge to the Argumentum Epic #2137**. Dung's theory is *exactly* fixed-point theory on a finite lattice — Mathlib provides `CompleteLattice (Set α)`, `OrderHom.lfp`/`gfp` and Knaster–Tarski out of the box, onto which the semantics map almost literally.

Model: an argumentation framework `AF α` equips an argument type `α` with an attack relation `attacks : α → α → Prop` (the universe of arguments is the entire type `α`, standard encoding). The **characteristic function** `F(S) = { a | S defends a }` is a monotone `OrderHom` on `Set α`; the **grounded** extension is its least fixed point `F.lfp`.

Companion notebook (`Tweety-5-Abstract-Argumentation.ipynb`, Tweety series): pedagogical presentation of Dung frameworks side-by-side Python (tweety) / Lean. The notebook wiring belongs to the Tweety series owner.

---

## `Argumentation.lean` — top-level aggregator

**Module docstring (translated).**

A library formalizing **Dung's abstract argumentation theory**: argumentation frameworks, extensions (admissible, complete, grounded, preferred, stable) and the fixed-point theorem (grounded = lfp of the characteristic function, Knaster–Tarski).

**Status.**

- **Toolchain**: `leanprover/lean4:v4.31.0-rc1` + Mathlib4 (`v4.31.0-rc1`).
- **Sorry**: **0** across the whole module — Dung's Fundamental Lemma, the grounded fixed-point identities, least-completeness, the semantics hierarchy (stable ⇒ preferred ⇒ complete ⇒ admissible), and the key lemma `F_preserves_admissible`.
- **OPEN milestone (documented)**: "the grounded is itself a complete extension" (finite stabilization of the iterated sequence) — **not** sorry-backed, see `Grounded.lean`.

**Modules.**

- `Argumentation.Basic` — `AF α` (attack relation), `conflictFree`, `defends`, monotonicity of defense.
- `Argumentation.Characteristic` — characteristic function `F : Set α →o Set α` (monotone, Knaster–Tarski applicable).
- `Argumentation.Extensions` — `Admissible`, `Complete`, `grounded = F.lfp`, `Preferred`, `Stable`, + the hierarchy (`stable_complete`, `preferred_complete`, `complete_admissible`).
- `Argumentation.Fundamental` — **Dung's Fundamental Lemma** (without sorry).
- `Argumentation.Grounded` — `grounded_fixed`, `grounded_defends_iff_mem`, `grounded_least_complete`, `F_preserves_admissible`.

**Cross-references.**

- Companion notebook `Tweety-5-Abstract-Argumentation.ipynb` (Tweety series): Python (tweety) presentation of Dung frameworks, of which this is the proven counterpart.
- Issue #4046 (roadmap Lean #4038), Epic Argumentum #2137.

### `ArgLattice` — abbrev

The complete lattice `(Set α, ⊆)` on which the characteristic function operates.

---

## `Argumentation/Basic.lean` — argumentation frameworks (Dung 1995) — basic definitions

**Module docstring (translated).**

An **abstract argumentation framework** (Dung, 1995) is a pair `(A, R)` where `A` is a set of arguments and `R ⊆ A × A` an attack relation. We encode it as a structure `AF α` equipping an argument type `α` with a relation `attacks : α → α → Prop`: one reads `af.attacks a b` as "argument `a` attacks argument `b`" (arrow `a → b`). The universe of arguments is the entire type `α` — standard encoding in formalization, which avoids carrying an explicit subset `A` and makes `Set α` a complete lattice without finiteness hypothesis.

Two foundational notions:
- **Conflict-free**: no member of `S` attacks another.
- **Defense**: `S` defends an argument `a` if every attacker of `a` is itself attacked by a member of `S`.

Defense is **monotone** in the defending set (more defenders ⇒ more defended arguments) — the key property that makes the characteristic function `F(S) = {a | S defends a}` an `OrderHom` (see `Characteristic.lean`).

Cross-reference:
- Notebook `Tweety-5-Abstract-Argumentation.ipynb` (Tweety series): Python presentation of Dung frameworks, of which this formalization is the proven counterpart.
- Epic Argumentum #2137.

### `AF` — structure

An abstract argumentation framework of Dung: an argument type `α` equipped with a binary attack relation. `af.attacks a b` reads as "`a` attacks `b`".

- **`attacks : α → α → Prop`** — attack relation: `attacks a b` means argument `a` attacks `b`.

### `AF.conflictFree` — definition

A set `S` is **conflict-free** if no member of `S` attacks another (Dung 1995, Definition 1).

### `AF.defends` — definition

An argument `a` is **defended** by the set `S` if every attacker of `a` is itself attacked by a member of `S` (Dung 1995, Definition 3).

### `AF.defendedBy` — definition

The set of arguments defended by `S`: the image of `S` under Dung's characteristic function. Defined here for convenience; the bundled monotone `OrderHom` version lives in `Characteristic.lean`.

### `conflictFree_empty` — theorem

The empty set is conflict-free: it has no member to attack.

### `defends_mono` — theorem

**Defense is monotone in the defending set**: if `S ⊆ T` and `S` defends `a`, then `T` defends `a` as well. This is the *growth* of the characteristic function, the heart of Dung's fixed-point theory.

### `no_internal_attack_on_defended` — theorem

If `S` is conflict-free, defends its own members, and defends `a`, then no member of `S` attacks `a`: an internal attacker of `a` would itself be attacked by a defender of `a` in `S`, contradicting conflict-freeness. The key lemma for the proof of Dung's *Fundamental Lemma*.

---

## `Argumentation/Characteristic.lean` — Dung's characteristic function — order morphism on `Set α`

**Module docstring (translated).**

The heart of Dung's argumentation theory is the **characteristic function** `F(S) = { a | S defends a }`. Its fundamental property is **monotonicity**: `S ⊆ T ⇒ F(S) ⊆ F(T)` (having more defenders can only enlarge the set of defended arguments). This monotonicity makes it an order morphism `Set α →o Set α`; on the complete lattice `(Set α, ⊆)`, the **Knaster–Tarski** theorem (Mathlib `OrderHom.lfp`) guarantees the existence of a least fixed point — the **grounded** extension.

Mathlib provides `OrderHom.lfp`, `map_lfp` (the lfp is a fixed point), `lfp_le` (the lfp majorizes any pre-fixed-point) and `isLeast_lfp_le`, which we exploit in `Grounded.lean`.

### `AF.characteristic` — definition

**Dung's characteristic function** `F(S) = { a | S defends a }`, bundled as a monotone order morphism on the complete lattice `Set α`. The grounded extension is its least fixed point (`F.lfp`).

### `mem_characteristic_iff` — theorem

Reformulation: `a ∈ F(S) ⇔ S defends a`.

### `characteristic_eq_defendedBy` — theorem

The image of `S` by `F` is exactly the set of arguments defended by `S`. (Definition identity, supplied for rewriting-based reasoning.)

---

## `Argumentation/Extensions.lean` — Dung extensions — admissible, complete, grounded, preferred, stable

**Module docstring (translated).**

Dung's five **semantics** (1995) characterize "rationally acceptable" argument sets according to criteria of coherence and defense of decreasing stringency:

| Semantics | Requirement |
|-----------|-------------|
| **Admissible** | conflict-free + defends its members |
| **Complete** | admissible + contains everything it defends |
| **Grounded** | the smallest complete extension (= lfp of `F`) |
| **Preferred** | a maximal complete extension |
| **Stable** | conflict-free + attacks every outside argument |

Dung's hierarchy: `Stable ⇒ Preferred ⇒ Complete ⇒ Admissible`. Each arrow is proved in this file (`stable_complete`, `preferred_complete`, `complete_admissible`), without `sorry`.

### `AF.Admissible` — definition

`S` is **admissible**: conflict-free and defends each of its members (Dung 1995, Definition 5).

### `AF.Complete` — definition

`S` is **complete**: admissible and contains every argument it defends (Dung 1995, Definition 7).

### `AF.grounded` — definition

The **grounded** extension: the least fixed point of the characteristic function `F` (Knaster–Tarski). Detailed properties in `Grounded.lean`.

### `AF.Preferred` — definition

`S` is **preferred**: a **maximal** complete extension under inclusion (Dung 1995, Definition 10).

### `AF.Stable` — definition

`S` is **stable**: conflict-free and **attacks** every argument outside `S` (Dung 1995, Definition 12).

### `complete_admissible` — theorem

**Complete ⇒ Admissible**: by definition.

### `preferred_complete` — theorem

**Preferred ⇒ Complete**: by definition.

### `stable_complete` — theorem

**Stable ⇒ Complete**: a stable set is admissible (the slightest internal attack would contradict conflict-freeness) and contains everything it defends (otherwise an argument defended outside `S` would be attacked by a member of `S`, contradicting defense).

---

## `Argumentation/Fundamental.lean` — Dung's Fundamental Lemma (1995)

**Module docstring (translated).**

> **Fundamental Lemma (Dung, Proposition 6).** Let `S` be admissible and `a`, `b` two arguments **defended** by `S`. Then (i) `S ∪ {a}` is admissible, and (ii) `b` is defended by `S ∪ {a}`.

This lemma is the **cornerstone** of Dung's theory: it guarantees that defense is *robust* under adjunction of defended arguments, and underlies the existence of complete/grounded/preferred extensions. It is proved here **without any `sorry`**, by first-order reasoning:

- **Internal conflict of `S ∪ {a}`**: an internal attacker `x` of a member `y` triggers (according to the 4 cases `x,y ∈ {a} ∪ S`) a chain of counter-attacks that contradicts the conflict-freeness of `S` combined with the fact that `S` defends `a`.
- **Defense of members**: `S ∪ {a}` defends `a` (given) and each `s ∈ S` (by admissibility of `S`), because `S ⊆ S ∪ {a}` and defense is monotone.
- **(ii)**: immediate by monotonicity (`S ⊆ S ∪ {a}`).

Reference: Dung, *On the Acceptability of Arguments and its Fundamental Role in Nonmonotonic Reasoning, Logic Programming and n-Person Games*, Artificial Intelligence 77 (1995), Proposition 6.

### `AF.fundamental_lemma` — theorem

**Dung's Fundamental Lemma (i)**: if `S` is admissible and defends `a`, then `S ∪ {a}` is admissible.

### `AF.fundamental_lemma_defends` — theorem

**Dung's Fundamental Lemma (ii)**: if `S` (admissible) defends `a` and `b`, then `S ∪ {a}` still defends `b`. Immediate by monotonicity of defense (`S ⊆ S ∪ {a}`).

### `AF.fundamental_lemma_defends_self` — theorem

**Corollary**: if `S` is admissible and defends `a`, then `a` is defended by `S ∪ {a}` (special case of (ii) with `b = a`).

---

## `Argumentation/Grounded.lean` — the grounded extension — fixed point and properties (Knaster–Tarski)

**Module docstring (translated).**

Dung's **grounded** extension is defined as the **least fixed point** of the characteristic function `F`:
```
grounded = F.lfp   (Knaster–Tarski on the complete lattice (Set α, ⊆))
```
Mathlib provides `OrderHom.map_lfp` (`F.lfp` is a fixed point), `OrderHom.lfp_le` (`F.lfp` majorizes any pre-fixed-point) — which we exploit to prove, **without any `sorry`**, the identities characterizing the grounded:

- `grounded_fixed`: `F(grounded) = grounded` (it really is a fixed point).
- `grounded_defends_iff_mem`: `a ∈ grounded ⇔ grounded defends a` (defense characterization, the heart of grounded semantics).
- `grounded_least_complete`: every complete extension contains `grounded` (the grounded is the **smallest** complete extension — `lfp_le`).

Plus Dung's key lemma **`F_preserves_admissible`**: the characteristic function preserves admissibility (`Admissible S ⇒ Admissible (F S)`), the cornerstone of the existence of complete extensions.

### OPEN milestone (documented, NOT sorry-backed)

The proof that `grounded` is **itself** a complete extension (hence conflict-free) is the substantive result of Dung (Proposition 11). It requires, for a finite framework, the **finite stabilization** of the iterated sequence `∅ ⊂ F(∅) ⊂ F²(∅) ⊂ …` toward the `lfp` (each iterate is admissible via `F_preserves_admissible`; the chain stabilizes in `|α|` steps). This finite-iteration↔`lfp` connection is deliberately **not stated as a `sorry`**: the current library remains entirely `sorry`-free, delivering the fixed-point identities, least-completeness, the semantics hierarchy and the Fundamental Lemma.

### `AF.grounded_fixed` — theorem

`grounded` is a **fixed point** of the characteristic function (`F(grounded) = grounded`). Knaster–Tarski identity via `OrderHom.map_lfp`.

### `AF.grounded_defends_iff_mem` — theorem

Defense characterization: `a ∈ grounded` **if and only if** `grounded` defends `a`. Immediate consequence of the fixed point and the definition of `F`.

### `AF.grounded_least_complete` — theorem

`grounded` is the **smallest complete extension**: every complete extension `T` contains `grounded`. Proved via `OrderHom.lfp_le` applied to the pre-fixed-point `F(T) ⊆ T` (a complete extension contains everything it defends).

### `AF.F_preserves_conflictFree` — theorem

The characteristic function **preserves conflict-freeness**: if `S` is conflict-free, then so is `F(S)`.

### `AF.F_preserves_admissible` — theorem

**Dung's Lemma (Proposition 7)**: the characteristic function preserves admissibility — `Admissible S ⇒ Admissible (F S)`. This is the fundamental fact guaranteeing the existence of complete extensions by iteration from `∅`.