import Mathlib.Tactic
import RepeatedGames.Stage_en

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
  references the base types of `RepeatedGames.Stage_en` (`PDAction`,
  `cooperate`, `defect`) via `open RepeatedGames_en`.

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
FairBot as "certified". This module proceeds differently, in four steps:

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
4. **Measured non-instantiability (T4, #26945).** Instantiating the
   interface by a real provability (PA, the repository's GL organ) FAILS —
   not for lack of Löb, but because of the `nec` field: written
   `(h : p) : box p`, it says "true ⇒ provable" (**reflection**) and not
   "derived ⇒ provable" (Hilbert systems' meta-rule D1, `Provability.D1`
   in the FFL organ). Reflection + Löb collapse every instance
   (`every_instance_boxes_false`, then `every_instance_boxes_everything`)
   : a real provability satisfies D2/D3/Löb but rejects reflection
   (first incompleteness theorem — the Gödel sentence is true and
   unprovable). The instantiation that exists lives one level up, on
   SENTENCES: `FormalLogic.FairBotLoeb` (L3, #17537), mutual cooperation
   of arbitrary FairBots under the named hypotheses `Diagonalization T₀`
   (diagonal lemma) and `𝔅.HBL`.

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
    (`¬ box False`);
  - `every_instance_boxes_false` / `every_instance_boxes_everything`
    (T4 #26945): every instance boxes `False`, then every proposition —
    the `nec` field is reflection, not necessitation; no real provability
    instantiates the interface (first incompleteness theorem), and the
    instantiable version lives in L3 (`FormalLogic.FairBotLoeb`, #17537)
    under diagonal lemma + HBL;
  - `cupodAction` / `CupodDuel`: the zoo extends to the dual CUPOD
    (cooperates unless proof of defection, Critch) — self-play (D, D)
    under named hypotheses **in the true-provability reading** (within
    the interface, T4 degeneracy makes it unconditional:
    `cupod_cupod_mutual_defect_degenerate`), the DUPOC/CUPOD asymmetry
    cited (2nd incompleteness — T4 vacuity measured), bounded theorem
    cited (organ-first: ColombanD/TorchLean prove it);
  - `PrudentBotDuel`: the Payorian PrudentBot `P ↔ □(□P → Q) ∧ □(□¬P →
    ¬Q)`, a direct bridge to Payor's lemma in the `Dynamics-04c`
    notebook (Dynamics series, issue #26985 tranche T-2).

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

open RepeatedGames_en PDAction

/-! ## Provability interface: Box + D1/D2/D3 + postulated Löb -/

/-- Provability modality in the Hilbert-Bernays-Löb sense. `box p` reads
"p is provable in the system". The first three fields are the classical
HBL derivations; the fourth is Löb's schema, **postulated as an explicit
assumption of the interface** (see the module docstring: the field is
neither a local axiom nor imported nor redundant — `bump_loeb_fails`
measures its independence, its non-emptiness is attested by the external
witness cited by reference). -/
class ModalProvability (box : Prop → Prop) where
  /-- D1 — necessitation (meta-rule): what is established is provable.
  "Established" is read here as TRUE (`h : p` is a Lean proof of the truth
  of `p`): the field is therefore **reflection** "true ⇒ provable",
  stronger than Hilbert's meta-rule `T ⊢ φ → T ⊢ □φ` (which goes from the
  DERIVATION to provability, `Provability.D1` in the FFL organ) — the gap
  is measured by `every_instance_boxes_false` (T4 #26945). -/
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

/-! ## T4 (#26945): degeneration of the interface — no real provability
instantiates it

Tranche T4 of #26945 asked to instantiate the interface by the native GL
organ. The answer fits in four lines: the `nec` field is not Hilbert
systems' necessitation (a meta-rule, from the DERIVATION of `p` to
`T ⊢ □p`) but the REFLECTION principle ("true ⇒ provable"). Reflection +
Löb = collapse: every instance boxes `False`, hence everything — the
interface distinguishes no proposition. A real provability (PA, verified
by the `FormalLogic.FairBotLoeb` organ of the GL lake) satisfies D2, D3
and Löb — but not reflection (first incompleteness theorem): the
instantiation fails exactly on the `nec` field, and mutual cooperation
remains true one level up (L3) under the named hypotheses: diagonal lemma
(`Diagonalization T₀`) + HBL (`𝔅.HBL`). The POSITIVE results of this
module remain true — but the degeneration measures their limit: in the
interface, FairBot ALWAYS cooperates (`box r` for every `r`), whereas a
real FairBot's cooperation is conditional (L3 proves it for FairBot ×
FairBot, refutes it against DefectBot). -/

/-- **T4 (#26945) — the reflection + Löb collapse.** Every instance of
`ModalProvability` satisfies `box False`. The proof: if `box False`, done;
otherwise the consistency `¬ box False` is a truth, so `nec` boxes it, and
`loeb` at `p := False` turns `box (box False → False)` into `box False`.
The `nec` field is not Hilbert systems' necessitation meta-rule
(`T ⊢ φ → T ⊢ □φ`, from the DERIVATION to provability — that is
`Provability.D1` in the native FFL organ) but the REFLECTION principle
("true ⇒ provable"), and reflection + Löb are incompatible with
consistency: this is the scheme of the second incompleteness theorem. -/
theorem every_instance_boxes_false : box False := by
  by_cases h : box False
  · exact h
  · exact loeb (p := False) (nec h)

/-- **Corollary: maximal degeneration.** Every instance boxes EVERY
proposition — boxed ex falso: `box False` then `dist` on `False → p`.
The interface thus distinguishes no proposition; its negative hypotheses
(`¬ box r`, `¬ box False`) are unsatisfiable (see
`consistency_hypothesis_unsat` and `no_unprovable_proposition`). The
POSITIVE results of the module (mutual cooperation via Löb) remain
intact: they never consume a negated box. -/
theorem every_instance_boxes_everything {p : Prop} : box p :=
  dist (nec (fun h => h.elim)) every_instance_boxes_false

/-- The consistency hypothesis `¬ box False` of `fairBot_vs_defectBot` is
UNSATISFIABLE in the interface: that theorem is vacuously true. T4
(#26945) measures it instead of leaving it implicit — the instantiable
version of consistency lives one level up, on sentences: it is
`Consistent T` in the `FormalLogic.FairBotLoeb` organ (L3). -/
theorem consistency_hypothesis_unsat : ¬ (¬ box False) :=
  fun h => h every_instance_boxes_false

/-- Symmetric statement for `fairBot_defects_without_proof`: in the
interface, nothing is unprovable — its hypothesis `¬ box r` is
unsatisfiable for every `r`. A real provability separates propositions
(the Gödel sentence is true and unprovable); the axiomatic interface
cannot. -/
theorem no_unprovable_proposition {r : Prop} : ¬ (¬ box r) :=
  fun h => h every_instance_boxes_everything

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

/-- FairBot defects absent a proof of the opponent's cooperation.
**T4 measure (#26945)**: the hypothesis `¬ box r` is unsatisfiable in the
interface (`no_unprovable_proposition`) — the theorem is vacuously true;
see the T4 section. -/
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
is excluded under the same local soundness hypothesis.
Declared alternative proof (different formulation):
`formal_logic_lean/FormalLogic/FairBotLoeb.lean` declares a theorem of the
same name in syntactic reading — `T₀ ⊢ p 🡘 𝔅 q` and `T ⊢ p` yield `T ⊢ q`
under `[𝔅.Kreisel]`. Canonical home of the FairBot agent: this lake
(`game_theory_lean`), where the operational duel lives; the
`formal_logic_lean` version is its Löb generalization. Comparison: here the
hypothesis is the local soundness `box r → r` bearing on the opponent's
clause of a concrete duel, and the conclusion excludes an action profile;
there, the Kreisel hypothesis governs any theory `T` and the conclusion is a
provability — frameworks not transportable term by term, each proof is
canonical in its own. Axioms used: propext, Classical.choice, Quot.sound. -/
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
separates mutual defection from illusory cooperation.
**T4 measure (#26945)**: in the interface, this hypothesis is
UNSATISFIABLE (`consistency_hypothesis_unsat`) — the theorem is
vacuously true; the instantiable consistency lives in L3 (`Consistent T`
in the `FormalLogic.FairBotLoeb` organ).
Declared alternative proof (different formulation):
`formal_logic_lean/FormalLogic/FairBotLoeb.lean` declares a theorem of the
same name under `[Consistent T] [𝔅.Kreisel]` and concludes `T ⊬ p`: the
cooperation is not provable. Canonical home of the FairBot agent: this lake
(`game_theory_lean`); the `formal_logic_lean` version is its syntactic
reading. Comparison: here the conclusion is an action equality
(`fairBotAction box False = defect`) — the duel behavior is determined;
there, a non-provability — the epistemic information missing on this side.
Two distinct strengths, neither contains the other. Axioms used: propext, Classical.choice, Quot.sound. -/
theorem fairBot_vs_defectBot (hconsis : ¬ box False) :
    fairBotAction box False = defect :=
  modalAction_false hconsis

/-! ## The zoo extends: CUPOD, FairBot's dual (Critch) -/

/-- CUPOD (Cooperate Unless Proof Of Defection) cooperates unless it can
prove that its opponent defects. The proposition `r` reads the opponent:
`r` true means "the opponent defects" — beware, the same `r` that read
"the opponent cooperates" at FairBot. Exact dual of `fairBotAction`
(renamed DUPOC by Critch: Defect Unless Proof Of Cooperation). Source:
A. Critch, "Open-Source Game Theory", AI-Safety for Mathematicians, 2026,
archived in the shared repository: "CUPOD cooperates unless it can prove
its opponent defects, and DUPOC defects unless it can prove its opponent
cooperates." -/
noncomputable def cupodAction (box : Prop → Prop) (r : Prop) : PDAction :=
  modalAction (¬ box r)

/-- CUPOD cooperates when it finds no proof of the opponent's defection. -/
theorem cupod_cooperates_without_proof {r : Prop} (h : ¬ box r) :
    cupodAction box r = cooperate :=
  modalAction_true h

/-- CUPOD defects when it finds a proof of the opponent's defection. -/
theorem cupod_defects_with_proof {r : Prop} (h : box r) :
    cupodAction box r = defect :=
  modalAction_false (fun hnr => hnr h)

/-- A meeting of two CUPODs: each defects if and only if it can prove the
other's defection. Structure dual to `FairBotDuel` — the clauses track
*defections* instead of cooperations. -/
structure CupodDuel (box : Prop → Prop) where
  rowDefects : Prop
  colDefects : Prop
  rowClause : rowDefects ↔ box colDefects
  colClause : colDefects ↔ box rowDefects

/-- In a CUPOD-CUPOD duel, every defection is itself provable:
`A → □B → □□B → □A`. T4 NOTE (#26945): this theorem does NOT witness a
non-derivability — in this degenerate interface its converse
`□A → A` is ALSO derivable (everything is: see
`cupod_row_defects_unconditional` and `every_instance_boxes_everything`).
The DUPOC/CUPOD asymmetry — which lives entirely in the direction of
reflection — is an observation about TRUE provability (Critch), to be
instantiated in L3 (`FormalLogic.FairBotLoeb`). -/
theorem cupod_defect_provable (d : CupodDuel box) :
    d.rowDefects → box d.rowDefects :=
  fun hA => box_mono d.rowClause.2 (posIntros (d.rowClause.1 hA))

/-- No proof of the opponent's defection, no defection: CUPOD's clause,
also called its "benevolence". T4 NOTE: the hypothesis
`¬ box d.colDefects` is unsatisfiable in the interface
(`no_unprovable_proposition`) — the statement is vacuously true there. -/
theorem cupod_cooperates_of_no_proof (d : CupodDuel box)
    (h : ¬ box d.colDefects) : ¬ d.rowDefects :=
  fun hA => h (d.rowClause.1 hA)

/-- **T4 witness — degeneracy of the zoo.** In the interface, the row
player's defection is derivable WITHOUT any hypothesis: `rowClause.2`
consumes `every_instance_boxes_everything`. Every "under hypotheses"
reading of this section is therefore trivially unconditional in the
interface — the interface does not discriminate the zoo; only true
provability (L3) can. -/
theorem cupod_row_defects_unconditional (d : CupodDuel box) :
    d.rowDefects :=
  d.rowClause.2 every_instance_boxes_everything

/-- Self-play CUPOD × CUPOD = (D, D) **under the named hypotheses** that
each search succeeds: `hrow`, the row player's search finds a proof of
the opponent's defection; `hcol`, the column player's. The row player's
action is `cupodAction box d.colDefects` — it reads the opponent.

T4 NOTE (#26945): in this degenerate interface, both hypotheses are
supplied FOR FREE by `every_instance_boxes_everything` — the corollary
`cupod_cupod_mutual_defect_degenerate` below establishes (D, D) without
any hypothesis. The "under named hypotheses" reading describes TRUE
provability: there, a consistent system cannot prove the absence of a
proof (Gödel's second incompleteness theorem), and this is the
counter-intuition Critch flags: "CUPOD seems the nicer robot, yet it
defects against itself."

The **bounded** theorem (Critch, "Cooperative and uncooperative
institution designs", 2022) establishes `outcome(CUPOD(k), CUPOD(k)) =
(D, D)` for all sufficiently large k, without hypothesis — in true
provability. It is **cited, not proved** here: organ-first, its
parametric demonstration belongs to the ColombanD/TorchLean corpus
(week-08), which this series cites without carrying it. -/
theorem cupod_cupod_mutual_defect (d : CupodDuel box)
    (hrow : box d.colDefects) (hcol : box d.rowDefects) :
    (cupodAction box d.colDefects, cupodAction box d.rowDefects)
      = (defect, defect) := by
  rw [cupod_defects_with_proof hrow, cupod_defects_with_proof hcol]

/-- **T4 corollary**: in the interface, CUPOD × CUPOD self-play is
UNCONDITIONAL — the hypotheses `hrow`/`hcol` of the version above are
instances of `every_instance_boxes_everything`. This corollary
reconciles the zoo with the degeneracy measured by #26945: whatever the
interface proves "under hypotheses" is always free there; the
discriminating zoo (Critch's) lives in L3. -/
theorem cupod_cupod_mutual_defect_degenerate (d : CupodDuel box) :
    (cupodAction box d.colDefects, cupodAction box d.rowDefects)
      = (defect, defect) :=
  cupod_cupod_mutual_defect d every_instance_boxes_everything
      every_instance_boxes_everything

/-- DUPOC × CUPOD asymmetry (Critch, ibid.): if the DUPOC finds no proof
that the CUPOD cooperates, it defects; if the CUPOD finds no proof that
the DUPOD defects, it cooperates. Outcome: (D, C). In Critch's framing
these hypotheses are not decorative — it is impossible to prove *inside
the system* that CUPOD cooperates (one would need to prove the absence
of a proof of defection), hence DUPOC defects; symmetrically, CUPOD
cooperates. T4 NOTE (#26945): in THIS interface, both negative
hypotheses are unsatisfiable (`no_unprovable_proposition`) — the
statement is vacuously true there, measured by
`dupoc_cupod_asymmetry_vacuous`; Critch's observation describes true
provability (L3). -/
theorem dupoc_cupod_asymmetry {coopCol defCol : Prop}
    (hnoCoop : ¬ box coopCol) (hnoDef : ¬ box defCol) :
    (fairBotAction box coopCol, cupodAction box defCol)
      = (defect, cooperate) := by
  rw [fairBot_defects_without_proof hnoCoop,
      cupod_cooperates_without_proof hnoDef]

/-- **T4 witness — vacuity of the asymmetry in the interface.** The
negative hypotheses of `dupoc_cupod_asymmetry` cannot be satisfied:
nothing is unprovable here (`no_unprovable_proposition`). Critch's
(D, C) outcome is therefore not mechanisable at this level — it lives
in L3. -/
theorem dupoc_cupod_asymmetry_vacuous {coopCol defCol : Prop} :
    ¬ (¬ box coopCol ∧ ¬ box defCol) :=
  fun h => h.1 every_instance_boxes_everything

/-! ## The Payorian PrudentBot: two simulations instead of one -/

/-- The **Payorian** PrudentBot: cooperate iff (1) a proof that "if my
cooperation were provable, the opponent would cooperate" **and** (2) a
proof that "if my defection were provable, the opponent would defect":
`P ↔ □(□P → Q) ∧ □(□¬P → ¬Q)`. Source: comment by
`transhumanist_atom_understander` on the post *Payorian cooperation is
easy with Kripke frames* (Alignment Forum, 2026-03) — the same thread
underlying the `Dynamics-04c` notebook of the Dynamics series. The
original **Löbian** PrudentBot, `PB(X) ↔ □(X(PB) ∧ (¬□⊥ → ¬X(DB)))`
(recalled by Payor in the same thread; Barasz, Christiano, Fallenstein,
Herreshoff, LaVictoire, Yudkowsky, *Robust Cooperation in the Prisoner's
Dilemma*, LORI-V 2014) tests its opponent against DefectBot under one
level of soundness: it is **cited**, not mechanised here. PrudentBot ×
PrudentBot self-play is not treated here — the source leaves it
"non-obvious", and this section does not pretend to settle it. T4 NOTE:
in the degenerate interface the question would anyway be trivial (both
clauses of each player are boxes, hence boxed for free); it is in true
provability — L3 — that it arises. -/
structure PrudentBotDuel (box : Prop → Prop) where
  rowCooperates : Prop
  colCooperates : Prop
  rowClause : rowCooperates ↔ (box (box rowCooperates → colCooperates) ∧
      box (box (¬ rowCooperates) → ¬ colCooperates))
  colClause : colCooperates ↔ (box (box colCooperates → rowCooperates) ∧
      box (box (¬ colCooperates) → ¬ rowCooperates))

/-- A Payorian PrudentBot is never the sucker as soon as the box is
sound on the opponent's clause (`soundCol`): its first clause requires a
proof `box (box P → Q)`, and its own cooperation `P` feeds it by
necessitation — the exact mirror of `fairBot_not_sucker`. -/
theorem prudent_not_sucker (d : PrudentBotDuel box)
    (soundCol : box d.colCooperates → d.colCooperates) :
    ¬ (d.rowCooperates ∧ ¬ d.colCooperates) := by
  rintro ⟨hRow, hNotCol⟩
  exact hNotCol (soundCol (dist (d.rowClause.1 hRow).1 (posIntros (nec hRow))))

/-- The Payorian PrudentBot's first clause **is** the Payorian FairBot
clause `P ↔ □(□P → Q)` — Payor's lemma, which the `Dynamics-04c`
notebook refutes on Kripke frames. This bridge connects L2 to the Python
notebook: cooperating as PrudentBot is cooperating as Payorian FairBot
**plus** the prudence test. -/
theorem prudent_implies_payorian (d : PrudentBotDuel box)
    (hRow : d.rowCooperates) :
    box (box d.rowCooperates → d.colCooperates) :=
  (d.rowClause.1 hRow).1

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
