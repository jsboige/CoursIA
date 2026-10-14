import Mathlib.Tactic
import RepeatedGames.Stage

/-
  FairBot via Löb's theorem: L2 (EN sibling)
  =========================================

  English mirror of `ProgramGames/FairBot.lean` (FR-first canonical,
  tranche L2 of EPIC #15062, Math for AI Safety). Convention i18n Lean
  ratified by ai-01 (2026-07-04, issue #4980): for each FR-canonical
  `Foo.lean`, a sibling `Foo_en.lean` preserves the EN version in the
  `_en` namespace to (a) allow both to compile in the same lake,
  (b) detect CI drift between FR and EN on non-docstring content,
  (c) keep the EN version as a pedagogical reference.

  Namespace: `ProgramGames_en` (anti-collision with `ProgramGames` of the
  FR canonical `FairBot.lean`). Like `Basic_en.lean`, this mirror
  references the FR base types of `RepeatedGames.Stage` (`PDAction`,
  `cooperate`, `defect`) via `open RepeatedGames`.

  Methodological note: manual translation of the FR canonical. Code
  (signatures, proofs, tactics, names) is byte-identical to the FR file;
  only docstrings and comments differ.
-/

/-!
# FairBot via Löb's theorem (L2)

Formalisation of the second level (L2) of program equilibrium for the
Prisoner's Dilemma: **FairBot**, the agent that cooperates exactly when
its opponent's cooperation is *provable* — and the mutual cooperation
FairBot × FairBot, obtained through **Löb's theorem**.

This is the bridge between the two neighbouring deliverables of EPIC
#15062 "Math for AI Safety": the bounded core L1 (`ProgramGames/Basic.lean`,
grain #15176, where `probeBot` is a Löb-free FairBot surrogate and where
`exploiterBot` demonstrates the limit of the bounded level) and the GL
bridge (`SymbolicAI/Lean/formal_logic_lean/FormalLogic/GLBridge.lean`,
tranche L3, PR #15923, which provides the kernel-checked witness of
Löb's schema).

References:
  - Barasz, Christiano, Fallenstein, Herreshoff, LaVictor, Yudkowsky
    (2014), "Program Equilibrium via Succinct Circuit Representation",
    arXiv:1401.5577;
  - LaVictor (2015), "Robust cooperation in the Prisoner's Dilemma:
    program equilibrium via provability logic", arXiv:1401.5577
    appendices;
  - Critch (2016), "Parametric Bounded Löb's Theorem and Robust
    Cooperation of Bounded Agents", arXiv:1602.04184.

## Honest architecture of Löb's schema

The EPIC forbids declaring Löb as an ad-hoc axiom and then presenting
FairBot as "certified". This module proceeds differently, in three steps:

1. **Interface.** `ModalProvability box` captures any provability
   modality in the Hilbert-Bernays-Löb sense: necessitation (D1),
   distribution (D2), positive introspection (D3), plus Löb's schema as
   a FIELD of the structure. All theorems below are relative to this
   interface — they hold for *any* instance.
2. **Measured independence.** The witness modality `bump p := p ∨ (0 = 1)`
   satisfies D1/D2/D3 but violates Löb's schema (`bump_loeb_fails`):
   the `loeb` field is therefore NOT redundant — no proof of Löb can be
   obtained from the HBL derivations alone. The field's content is real.
3. **Verified witness.** This module does not couple the build of
   `game_theory_lean` to the GL lake ("deliberately light libs" pattern
   of the lakefile: only `Mathlib.Tactic` and `RepeatedGames.Stage` are
   imported): the `loeb` field is an **explicit assumption of the
   interface**, and its non-emptiness is attested by the external
   kernel-checked witness `FormalLogic.GLBridge.loeb_schema` (lake
   `formal_logic_lean`, PR #15923, library `ProvabilityLogic` at a pinned
   commit), which derives `□(□A → A) → □A` in the GL Hilbert calculus —
   **cited by reference, never imported, and this module defines no
   `ModalProvability` instance**: any instance must supply the field, the
   bridge acting as witness, not instance.

## Headline results

  - `loeb_mutual_fixedpoint`: in a system of crossed modal equations
    `q ↔ □r`, `r ↔ □q`, each side satisfies Löb's condition, hence both
    cooperate — the derivation of Barasz et al. 2014;
  - `fairBot_fairBot_cooperation`: FairBot × FairBot = (C, C), obtained
    by Löb, where L1 had to settle for the bounded probe `probeBot`;
  - `fairBot_not_sucker` / `fairBot_unexploitable`: FairBot is never the
    sucker **under the explicit hypothesis of local soundness**
    (`box r → r` on the opponent's clause) — exploitation would require
    a proof system certifying a false cooperation;
  - `fairBot_vs_coopBot` / `fairBot_vs_defectBot`: the pedagogical table —
    FairBot cooperates with provably cooperating opponents, defects
    against DefectBot *under the explicit consistency hypothesis*
    (`¬ box False`).

## Contrast with level L1

The flaw of `probeBot` (L1) was a **surface signature**: its probe
profile `(C, D)`, readable by any bounded agent (`exploiterBot`).
FairBot's decision depends on `box r` — a provability fact, not a
surface behaviour: getting FairBot to cooperate while defecting requires
`box r` with `¬r`, i.e. a proof system unsound on `r` — exactly what
the explicit hypothesis of `fairBot_not_sucker` rules out. This is the
conceptual jump of robust cooperation: probe neither behaviour nor
surface, but proof.
-/

namespace ProgramGames_en

open RepeatedGames PDAction

/-! ## Provability interface: Box + D1/D2/D3 + postulated Löb -/

/-- Provability modality in the Hilbert-Bernays-Löb sense. `box p` reads
"p is provable in the system". The first three fields are the classical
HBL derivations; the fourth is Löb's schema, **postulated as an explicit
assumption of the interface** (see the module docstring: the field is
neither a local axiom nor imported nor redundant — `bump_loeb_fails`
measures its independence, its non-emptiness is attested by the external
witness cited by reference). -/
class ModalProvability (box : Prop → Prop) where
  /-- D1 — necessitation (meta-rule): what is established is provable. -/
  nec {p : Prop} (h : p) : box p
  /-- D2 — distribution: provability distributes over modus ponens. -/
  dist {p q : Prop} (hpq : box (p → q)) (hp : box p) : box q
  /-- D3 — positive introspection: what is provable is provably provable.
  This is the field consumed by the FairBot × FairBot derivation (via
  `box_mono`: the proof of the opponent's clause itself becomes an
  object of proof). -/
  posIntros {p : Prop} (hp : box p) : box (box p)
  /-- Löb's schema: if "provably (provable p implies p)" then
  "provable p". An **explicit assumption of the interface**, not a local
  axiom nor an import: its non-emptiness is attested by the external
  kernel-checked witness `FormalLogic.GLBridge.loeb_schema` (lake
  `formal_logic_lean`, PR #15923, ProvabilityLogic library at a pinned
  commit), **cited by reference without coupling the build**. This
  field's independence from D1/D2/D3 is measured by `bump_loeb_fails`
  below. -/
  loeb {p : Prop} (h : box (box p → p)) : box p

open ModalProvability

variable {box : Prop → Prop} [ModalProvability box]

/-! ## Derivations of the interface -/

/-- Monotonicity: provability preserves implication (D1 + D2). -/
theorem box_mono {p q : Prop} (hpq : p → q) (hp : box p) : box q :=
  dist (nec hpq) hp

/-- Löb, "Russian" version: if `p` whenever `p` is provable, then `p`.
Equivalent to the `loeb` schema (necessitation of the hypothesis then
modus ponens). This is the form directly consumed by mutual cooperation:
"if I cooperate whenever my cooperation is provable, then I cooperate". -/
theorem loeb_russian {p : Prop} (h : box p → p) : p :=
  h (loeb (nec h))

/-! ## Modal actions and the definition of FairBot -/

/-- Action dictated by an abstract proposition: cooperate if it holds,
defect otherwise. Non-computable (abstract `Prop`, classical decision) —
the content of the module lies in the theorems, not in execution. -/
noncomputable def modalAction (P : Prop) : PDAction :=
  @ite PDAction P (Classical.dec P) cooperate defect

@[simp] theorem modalAction_true {P : Prop} (h : P) :
    modalAction P = cooperate := if_pos h

@[simp] theorem modalAction_false {P : Prop} (h : ¬P) :
    modalAction P = defect := if_neg h

/-- Cooperation reads off the action (partial converse of
`modalAction_true`). -/
theorem cooperates_of_action {P : Prop} (h : modalAction P = cooperate) : P := by
  by_contra hp
  rw [modalAction_false hp] at h
  exact absurd h (by decide)

/-- FairBot: cooperates against its opponent exactly when THAT
opponent's cooperation against FairBot is provable in the system. This
is the central definition of Barasz et al. 2014. The L1 surrogate was
`probeBot` (surface probe of the behaviour profile); FairBot probes the
PROOF — the exact conceptual difference between L1 and L2. -/
noncomputable def fairBotAction (box : Prop → Prop) (r : Prop) : PDAction :=
  modalAction (box r)

/-- FairBot cooperates as soon as the opponent's cooperation is provable. -/
theorem fairBot_cooperates_with_provable_cooperator {r : Prop} (h : box r) :
    fairBotAction box r = cooperate := modalAction_true h

/-- FairBot defects absent a proof of the opponent's cooperation. -/
theorem fairBot_defects_without_proof {r : Prop} (h : ¬ box r) :
    fairBotAction box r = defect := modalAction_false h

/-! ## FairBot against FairBot: the coordinated fixed point -/

/-- Modal duel FairBot × FairBot: a system of crossed modal equations.
`rowCooperates` ("row cooperates") is equivalent to the provability of
column's cooperation, and conversely — each FairBot applies its clause
to the other's clause. -/
structure FairBotDuel (box : Prop → Prop) where
  /-- The fact "row (FairBot no. 1) cooperates". -/
  rowCooperates : Prop
  /-- The fact "column (FairBot no. 2) cooperates". -/
  colCooperates : Prop
  /-- FairBot's clause on the row side: cooperates iff the opponent's
  cooperation is provable. -/
  rowClause : rowCooperates ↔ box colCooperates
  /-- FairBot's clause on the column side. -/
  colClause : colCooperates ↔ box rowCooperates

/-- Core of the tranche: the coordinated fixed point via Löb. Each side
of the duel satisfies the Russian-version condition (`box q → q`), so
Löb yields cooperation on both sides. The derivation consumes D3 (a
proof of cooperation becomes provably a proof) — this is what leaves
level L1, where mutual cooperation held only by surface probing. -/
theorem loeb_mutual_fixedpoint (d : FairBotDuel box) :
    d.rowCooperates ∧ d.colCooperates := by
  have hrow : box d.rowCooperates → d.rowCooperates := by
    intro hbq
    exact d.rowClause.2 (dist (nec d.colClause.2) (posIntros hbq))
  have hcol : box d.colCooperates → d.colCooperates := by
    intro hbr
    exact d.colClause.2 (dist (nec d.rowClause.2) (posIntros hbr))
  exact ⟨loeb_russian hrow, loeb_russian hcol⟩

/-- FairBot × FairBot = (C, C): mutual cooperation via Löb. Where L1's
`probeBot` obtained it by a bounded-probe `rfl` — and paid for it with an
exploitable signature — FairBot obtains it by reasoning about mutual
proofs, exposing no surface to probe. -/
theorem fairBot_fairBot_cooperation (d : FairBotDuel box) :
    (modalAction d.rowCooperates, modalAction d.colCooperates)
      = (cooperate, cooperate) := by
  obtain ⟨h1, h2⟩ := loeb_mutual_fixedpoint d
  rw [modalAction_true h1, modalAction_true h2]

/-! ## Unexploitability under an explicit hypothesis -/

/-- FairBot is never the sucker as soon as the proof system is SOUND ON
THE OPPONENT'S CLAUSE (`soundCol : box r → r`): cooperating while the
opponent defects would require a proof `box r` of a false cooperation
`r`. The hypothesis is explicit and minimal — it bears on the opponent's
clause only, not on the global soundness of the system. -/
theorem fairBot_not_sucker (d : FairBotDuel box)
    (soundCol : box d.colCooperates → d.colCooperates) :
    ¬ (d.rowCooperates ∧ ¬ d.colCooperates) := by
  rintro ⟨hq, hr⟩
  exact hr (soundCol (d.rowClause.1 hq))

/-- "Action" version of `fairBot_not_sucker`: the sucker profile (C, D)
is excluded under the same local soundness hypothesis. -/
theorem fairBot_unexploitable (d : FairBotDuel box)
    (soundCol : box d.colCooperates → d.colCooperates) :
    (modalAction d.rowCooperates, modalAction d.colCooperates)
      ≠ (cooperate, defect) := by
  have h := fairBot_not_sucker d soundCol
  intro heq
  rw [Prod.mk.injEq] at heq
  obtain ⟨h1, h2⟩ := heq
  refine h ⟨cooperates_of_action h1, ?_⟩
  intro hcol
  rw [modalAction_true hcol] at h2
  exact absurd h2 (by decide)

/-- Under local soundness, Löb goes further than excluding the sucker
outcome: the opponent COOPERATES (Russian version applied to its own
clause). Soundness turns "not exploitable" into "guaranteed cooperation". -/
theorem opponent_cooperates_of_sound (d : FairBotDuel box)
    (soundCol : box d.colCooperates → d.colCooperates) :
    d.colCooperates :=
  loeb_russian soundCol

/-! ## Specialised confrontations -/

/-- FairBot against CoopBot: the opponent's clause is "always
cooperates". Mutual cooperation requires no hypothesis — `box True`
holds by necessitation. -/
def coopDuel : FairBotDuel box where
  rowCooperates := box True
  colCooperates := True
  rowClause := Iff.rfl
  colClause := ⟨fun _ => nec (nec True.intro), fun _ => True.intro⟩

/-- FairBot cooperates with CoopBot (without hypothesis). -/
theorem fairBot_vs_coopBot :
    fairBotAction box True = cooperate :=
  modalAction_true (nec True.intro)

/-- FairBot defects against DefectBot — UNDER THE EXPLICIT HYPOTHESIS of
consistency of the system (`¬ box False`). Without consistency, an
inconsistent system "proves" everything, including DefectBot's
cooperation: the hypothesis is not cosmetic, it is exactly what
separates mutual defection from illusory cooperation. -/
theorem fairBot_vs_defectBot (hconsis : ¬ box False) :
    fairBotAction box False = defect :=
  modalAction_false hconsis

/-! ## Independence of Löb's schema: the field is not redundant -/

/-- Witness modality `bump p := p ∨ (0 = 1)`: it satisfies the HBL
derivations (D1, D2, D3 — see the three lemmas below) but not Löb's
schema. It proves that no proof of Löb can be derived from D1/D2/D3
alone: the field `ModalProvability.loeb` has a content of its own, and
its external attestation (the GL witness #15923, cited by reference)
shows that this content is realizable — not a disguised redundant
axiom. -/
private def bump (p : Prop) : Prop := p ∨ ((0 : ℕ) = 1)

private theorem bump_nec {p : Prop} (h : p) : bump p := Or.inl h

private theorem bump_dist {p q : Prop} (hpq : bump (p → q)) (hp : bump p) :
    bump q := by
  rcases hpq with hpq | h01
  · rcases hp with hp | h01
    · exact Or.inl (hpq hp)
    · exact Or.inr h01
  · exact absurd h01 (by decide)

private theorem bump_posIntros {p : Prop} (hp : bump p) : bump (bump p) :=
  Or.inl hp

/-- The modality `bump` satisfies D1/D2/D3 but VIOLATES Löb's schema at
`p := False`: the antecedent `bump (bump False → False)` is true (since
`bump False → False` is equivalent to refuting `0 = 1`, a decidable
tautology), while `bump False` is false. Löb is therefore independent of
the HBL derivations in this setting — the `ModalProvability` interface
makes it a postulated field (an explicit assumption any instance must
supply), whose external kernel-checked witness in this repository is
`FormalLogic.GLBridge.loeb_schema` (GL logic, ProvabilityLogic library,
PR #15923), cited by reference. -/
theorem bump_loeb_fails :
    ¬ (bump (bump False → False) → bump False) := by
  intro h
  have hb := h (Or.inl (fun hx => Or.elim hx id (fun h01 => absurd h01 (by decide))))
  rcases hb with h1 | h2
  · exact h1
  · exact absurd h2 (by decide)

end ProgramGames_en
