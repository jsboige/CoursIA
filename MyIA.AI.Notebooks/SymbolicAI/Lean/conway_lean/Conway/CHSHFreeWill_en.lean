/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## From CHSH to free will: the statistical route

This module is the sixth tranche of the quantum pilot of Epic #13106. The
previous tranches bounded the deterministic classical frontier
(`Conway.CHSH`), its randomized envelope (`Conway.CHSHRandomized`),
imported Mathlib's quantum bound `2√2` (`Conway.CHSHQuantum`), then
saturated Tsirelson with an explicit witness and checked Landau's criterion
(`Conway.CHSHLandau`, consumed by the notebook `Lean-13c`).

What the pilot was still missing is the bridge its Epic announced: the CHSH
series and the Free Will Theorem (`Conway.FreeWillTheorem`, notebook
`Lean-16f`) **both** conclude that quantum responses are indeterministic,
yet through two formally disconnected routes:

- the **contextual route** (Free Will Theorem): three measurement
  directions, axioms SPIN + TWIN + MIN, contradiction by the absence of a
  Kochen-Specker coloring (`kochen_specker`);
- the **statistical route** (CHSH): two settings per party, locality of the
  responses, contradiction by the numerical gap `2 < 2√2`.

This module formalizes the statistical route in the vocabulary of the FWT —
a "local deterministic model" is a family of response functions of the
hidden state, one per party, each blind to the other party's setting (the
structural analogue of MIN) — and proves the indeterminism conclusion:
**no local deterministic model can realize a CHSH score beyond the
classical frontier, in no hidden state**, while quantum mechanics reaches
`2√2`. The responses therefore cannot be functions of the past — the same
conclusion as the FWT, obtained without any coloring.

### Statement status

| Statement | Status |
|---|---|
| Local deterministic frontier state-by-state: `|realizedScore| = 2` | **proved here** (delegated to `CHSH.classical_abs_score`) |
| Saturation by an explicit local model (`canonical`) | **proved here** |
| No state where a local model exceeds `2` (integer) | **proved here** |
| Tsirelson's value `2√2` strictly dominates every local score (real) | **proved here** |
| Indeterminism conclusion: no local model realizes `> 2` in reals | **proved here** |
| Full probabilistic interpretation (states, measurements, expectations on ℝ⁴) | **not established** — declared open, as in `Conway.CHSHQuantum` |
| Equivalence of the two routes (FWT ⟷ CHSH) | **not established** — the hypotheses differ; only the shared conclusion is formalized |

### Digestion grid (10 points, Epic #13106)

1. **Statements and guarantee level**: exact bounds and equalities over `ℤ`
   then `ℝ`, no functional analysis; the constant `2√2` is the one of
   `CHSHQuantum_en.classical_quantum_gap`.
2. **Provenance**: Clauser, Horne, Shimony, Holt (1969), "Proposed
   experiment to test local hidden-variable theories"; Bell (1964) for the
   parent inequality; Tsirelson (1980) for the quantum bound. The link
   "Bell violation ⟹ indeterminism" is the standard reading (Bell 1964,
   §II); the phrasing in "response functions of the past" follows the
   vocabulary of Conway-Kochen (2006/2009).
3. **Novelty**: the repository had the two ingredients separately (bound
   `CHSH.classical_abs_score`, gap `classical_quantum_gap`); the local
   deterministic model as a family of functions of the hidden state, the
   state-by-state frontier and the indeterminism conclusion are new to the
   repository.
4. **Dependencies**: `Conway.CHSH` (score, frontier),
   `Conway.CHSHQuantum` (gap), `Conway.FreeWillTheorem` (`HiddenState`,
   vocabulary); Mathlib restricted to `Mathlib.Tactic.Ring` and the
   `omega` on `|s| = 2` / coercions `ℤ → ℝ`. No `sorry`, no
   axioms beyond the three standard ones.
5. **Trivial condensed / new developed**: the frontier itself is delegated
   (16-case enumeration already paid by `Conway.CHSH`); the new heart is
   the **for every state** step: the classical frontier was a fact about
   four outcomes, it becomes a fact about entire families of response
   functions.
6. **Friction**: the temptation of an expectation statement (average score
   under a distribution of hidden states) was set aside: expectation
   machinery adds nothing to the conclusion (the state-by-state bound is
   stronger for a deterministic model) and would weigh the module down.
7. **Discovery path**: the structural correspondence MIN ⟷
   locality-by-signature was found by rereading the signature of
   `TwoParticleResponse` in `Conway.FreeWillTheorem` — locality there is
   not a hypothesis but a property of the type. The same encoding is
   reused here verbatim.
8. **Limits**: the conclusion covers **deterministic local** models; it
   says nothing about stochastic non-local models nor about the randomized
   bound (see `Conway.CHSHRandomized` for the classical probabilistic
   envelope).
9. **Corpus connection**: consumed by the notebook
   `Lean-13d-CHSH-Indeterminisme-Native.ipynb` (cross bridge with
   `Lean-16f`), prolongation of the 13b/13c series; prerequisites: CHSH
   score and classical frontier (`Lean-13b`).
10. **Transmission**: native notebook with a computed witness,
    correspondence table of the two routes, and cross-review at review
    time.

### i18n — convention #4980 (ratified 2026-07-04)

This file is the **English mirror** of `Conway/CHSHFreeWill.lean`
(`namespace Conway_en` > `namespace CHSHFreeWill_en`, `_en`-suffixed
imports) — sibling pair Pattern A, like `Conway/CHSHLandau_en`. The body
(signatures, defs, proofs) is byte-identical between the two files, up to
the `_en` qualifiers; only the docstrings and comments differ. No inline
bilingual block.
-/

import Conway.CHSH_en
import Conway.CHSHQuantum_en
import Conway.FreeWillTheorem_en

namespace Conway_en

namespace CHSHFreeWill_en

open CHSH_en CHSHQuantum_en FreeWillTheorem_en

/-!
## Step 1: local deterministic model of the CHSH game

The vocabulary is the Free Will Theorem's: responses are functions of the
hidden state (the "past" of the universe). **Locality** is encoded by the
signature, exactly like MIN in
`Conway.FreeWillTheorem.TwoParticleResponse`: Alice's response never sees
Bob's setting, and conversely — not a hypothesis to prove, a property of
the type.
-/

/-- Alice's local response: for each hidden state and each of her two
settings (`true` = x, `false` = y), a predetermined outcome `±1`.

This is the two-setting analogue of
`Conway.FreeWillTheorem.DeterministicResponse`
(which carried three, spin directions). Locality (MIN) lives in the
signature: Bob's setting does not appear. -/
abbrev AliceResponse := HiddenState → Bool → Outcome

/-- Bob's local response: same encoding, Alice's mirror. -/
abbrev BobResponse := HiddenState → Bool → Outcome

/-- CHSH score realized by the model `(α, β)` in the hidden state `state`:
the four predetermined responses are injected into the score of
`Conway.CHSH`. -/
def realizedScore (α : AliceResponse) (β : BobResponse) (state : HiddenState) : ℤ :=
  score (α state true) (α state false) (β state true) (β state false)

/-!
## Step 2: the local frontier, state by state

The classical frontier of `Conway.CHSH` was a fact about four isolated
outcomes. For a local deterministic model it holds **in every hidden
state** — this is the bridge from the particular (one strategy) to the
general (an entire family of strategies indexed by the past).
-/

/-- **Local deterministic frontier, exact form.** In every hidden state,
the score realized by a local deterministic model is exactly `±2`.

The proof delegates the 16-assignment enumeration to
`Conway.CHSH.classical_abs_score`: each hidden state instantiates four
responses, and the frontier applies. -/
theorem local_abs_score (α : AliceResponse) (β : BobResponse) (state : HiddenState) :
    |realizedScore α β state| = 2 :=
  classical_abs_score _ _ _ _

/-- Usual form of the local frontier. -/
theorem local_bound (α : AliceResponse) (β : BobResponse) (state : HiddenState) :
    |realizedScore α β state| ≤ 2 :=
  local_abs_score α β state ▸ le_refl _

/-- **No local deterministic model exceeds the classical frontier, in no
hidden state.** The bound is not an average: it holds state by state, so
no privileged state can save the model. -/
theorem no_state_beyond_classical :
    ¬ ∃ (α : AliceResponse) (β : BobResponse) (state : HiddenState),
        (2 : ℤ) < realizedScore α β state := by
  rintro ⟨α, β, state, h⟩
  have habs : |realizedScore α β state| = 2 := local_abs_score α β state
  have hle : realizedScore α β state ≤ |realizedScore α β state| := le_abs_self _
  omega

/-- The local frontier is **attained**: the canonical model — both parties
always answer `+1` — realizes the score `+2` in every state.
The bound of `local_bound` is therefore tight for local models. -/
def canonicalAlice : AliceResponse := fun _ _ => .positive

def canonicalBob : BobResponse := fun _ _ => .positive

@[simp]
theorem canonical_score (state : HiddenState) :
    realizedScore canonicalAlice canonicalBob state = 2 := by
  simp [realizedScore, canonicalAlice, canonicalBob, score, Outcome.value]

/-!
## Step 3: the Tsirelson gap excludes local deterministic models

Quantum mechanics predicts (and experiment confirms) CHSH correlations of
value `2√2` — strictly above the local frontier
(`Conway.CHSHQuantum.classical_quantum_gap`). Since every local
deterministic model is capped at `2` in each state, none can reproduce the
quantum prediction.
-/

/-- Real form of the local frontier: the realized score, seen as a real,
stays under the classical frontier. -/
theorem local_bound_real (α : AliceResponse) (β : BobResponse) (state : HiddenState) :
    (realizedScore α β state : ℝ) ≤ 2 := by
  have h : realizedScore α β state ≤ 2 := by
    have habs : |realizedScore α β state| = 2 := local_abs_score α β state
    have hle : realizedScore α β state ≤ |realizedScore α β state| := le_abs_self _
    omega
  exact_mod_cast h

/-- **Tsirelson's gap dominates every local score.** The quantum value
`2√2` is strictly above the classical frontier, and every local
deterministic model realizes at most `2`: the gap is incompressible for
these models. -/
theorem tsirelson_beyond_every_local_score :
    (2 : ℝ) < 2 * √2 ∧
      ∀ (α : AliceResponse) (β : BobResponse) (state : HiddenState),
        (realizedScore α β state : ℝ) ≤ 2 :=
  ⟨classical_quantum_gap, local_bound_real⟩

/-- **Indeterminism conclusion via the CHSH route.** No model where the
two parties' responses are deterministic functions of the hidden state
(locality by signature) can realize a CHSH score strictly above the
classical frontier — while the quantum value is `2√2 > 2`.

This is the same conclusion as `Conway.FreeWillTheorem.free_will_theorem`
(the responses are not functions of the past), obtained through a
**statistical** argument (Tsirelson's numerical gap) where the FWT uses a
**contextual** argument (the absence of a Kochen-Specker coloring). The
hypotheses differ — two settings versus three directions, numerical gap
versus impossible coloring — the conclusion is shared. -/
theorem chsh_indeterminism :
    ¬ ∃ (α : AliceResponse) (β : BobResponse) (state : HiddenState),
        (2 : ℝ) < realizedScore α β state := by
  rintro ⟨α, β, state, h⟩
  exact no_state_beyond_classical ⟨α, β, state, by exact_mod_cast h⟩

/-!
## Step 4: structural correspondence of the two routes

  | | Contextual route (FWT, `Lean-16f`) | Statistical route (CHSH, `Lean-13b/13c/13d`) |
  |---|---|---|
  | Settings per party | 3 orthogonal directions | 2 binary settings |
  | Axioms | SPIN + TWIN + MIN | locality (by signature) + quantum statistics |
  | Contradiction engine | `kochen_specker`: no valid coloring | `classical_quantum_gap`: `2 < 2√2` |
  | What is denied | any response function of the past (determinism) | any local deterministic model reproducing `2√2` |
  | Strength of the conclusion | exact, no statistical hypothesis | numerical: quantifies the gap (`2√2 − 2`) |

  The two routes are **complementary**: the FWT says nothing about the
  numerical gap, the CHSH route says nothing about the perfect TWIN
  correlations. The notebook `Lean-13d` walks both columns on the same
  witness.
-/

end CHSHFreeWill_en

end Conway_en
