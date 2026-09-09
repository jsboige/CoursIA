import Mathlib.Tactic
import RepeatedGames.Stage

/-
  Program Equilibrium: bounded core L1 (EN sibling)
  ================================================

  English mirror of `ProgramGames/Basic.lean` (FR-first canonical,
  grain #15176, EPIC #15062). Convention i18n Lean ratified by ai-01
  (2026-07-04, issue #4980 comment-4881909354): for each FR-canonical
  `Foo.lean`, a sibling `Foo_en.lean` preserves the EN version in the
  `_en` namespace to (a) allow both to compile in the same lake,
  (b) detect CI drift between FR and EN on non-docstring content,
  (c) keep the EN version as a pedagogical reference.

  Namespace: `ProgramGames_en` (anti-collision with `ProgramGames` of
  the FR canonical `Basic.lean`). Like the higher-level EN siblings of
  `RepeatedGames` (Discounting_en, GrimTrigger_en), this mirror
  references the FR base types of `RepeatedGames.Stage` (`PDAction`,
  `PrisonersDilemma`, `stagePayoff`) via `open RepeatedGames`.

  Methodological note: manual translation of the FR canonical (no
  historical pre-Option-A EN source to recover; FR-first file since
  origin).
-/

/-!
# Program Equilibrium: bounded core (L1)

Formalisation of the first level (L1) of program equilibrium for the
Prisoner's Dilemma: bounded agents that only consult their opponent's
behaviour against the two trivial probe bots (CoopBot and DefectBot),
with no recursion and no unbounded introspection.

References:
  - Barasz, Christiano, Fallenstein, Herreshoff, LaVictor, Yudkowsky
    (2014), "Program Equilibrium via Succinct Circuit Representation",
    arXiv:1401.5577;
  - Critch (2016), "Parametric Bounded Löb's Theorem and Robust
    Cooperation of Bounded Agents", arXiv:1602.04184.

DELIBERATELY restricted scope (L1 tranche of EPIC #15062
"Math for AI Safety", grain #15176):
  - bounded total agents (`ProgramAgent`), recursion-free `outcome`
    semantics (two function applications), finite confrontation table;
  - decidable organs: `MutualCooperation`, `Unexploitable`;
  - `ProgramNash` verified by proof over a finite family;
  - NO Löb formalisation (ad-hoc or parametric): levels L2/L3 (mutual
    source reasoning, agents of increasing depth) are out of scope.

The module reuses the stage game of `RepeatedGames.Stage` (`PDAction`,
`PrisonersDilemma`, `stagePayoff`).

## Headline results

  - `outcome_probeBot_probeBot`: the probe bot achieves mutual
    cooperation WITH ITSELF by bounded probing, without any Löb
    theorem (a `rfl`);
  - `programNash_probeBot_probeBot`: that cooperation IS a program
    Nash equilibrium of the family — deviating to DefectBot is punished
    (P < R): "probe then reciprocate" sustains cooperation at the
    bounded level, the central insight of Barasz et al. 2014;
  - `probeBot_unexploitable_in_family`: that bot is never the sucker
    within the family of trivial bots;
  - `probeBot_exploited_by_exploiterBot`: BUT a tailor-made bounded
    adversary exploits the probe — ProbeBot's own probe-profile
    signature (C, D) betrays it. Outside the family, without mutual
    source reasoning (L2/L3, Critch 2016 parametric Löb), programmatic
    cooperation is not unfathomable: the exact limit of level L1.
-/

namespace ProgramGames_en

open RepeatedGames
open PDAction

/-! ## Bounded program agents -/

/-- A bounded program agent: a **total** function which, informed of
its opponent's probe profile (action against CoopBot, action against
DefectBot), chooses a Prisoner's Dilemma action. The space of agents is
finite: `PDAction` has two constructors, so
`ProgramAgent := PDAction → PDAction → PDAction` admits 2⁴ = 16
extensionally distinct functions (an enumeration of length-four binary
tables confirms this). Every confrontation reduces to a bounded number
of evaluations: no recursion, no unbounded search, no loops. -/
abbrev ProgramAgent : Type := PDAction → PDAction → PDAction

/-- Probe profile of an agent: its action against CoopBot (first
component) and against DefectBot (second). This is the only
information about the opponent a bounded agent of this core may
consult: a first-level probe, terminating by construction. -/
def probeProfile (A : ProgramAgent) : PDAction × PDAction :=
  (A cooperate cooperate, A defect defect)

/-- Confrontation semantics: each agent plays the action dictated by
its program, informed of the opponent's probe profile. Bounded
evaluation: two function applications, zero recursion. -/
def outcome (A B : ProgramAgent) : PDAction × PDAction :=
  (A (probeProfile B).1 (probeProfile B).2,
   B (probeProfile A).1 (probeProfile A).2)

/-- Payoff of the first player (row) in the confrontation `(A, B)`,
via the matrix of `RepeatedGames.stagePayoff`. -/
def payoff1 (g : PrisonersDilemma) (A B : ProgramAgent) : ℝ :=
  stagePayoff g (outcome A B).1 (outcome A B).2

/-- Payoff of the second player (column) in the confrontation `(A, B)`. -/
def payoff2 (g : PrisonersDilemma) (A B : ProgramAgent) : ℝ :=
  stagePayoff g (outcome A B).2 (outcome A B).1

/-! ## Trivial bots -/

/-- CoopBot: cooperates unconditionally. -/
def coopBot : ProgramAgent := fun _ _ => cooperate

/-- DefectBot: defects unconditionally. -/
def defectBot : ProgramAgent := fun _ _ => defect

/-- ProbeBot: cooperates if and only if the opponent cooperates with
CoopBot. A bounded first-level probe — a surrogate of the literature's
FairBot (Barasz et al. 2014) WITHOUT self-referential reasoning: no
Löb theorem is invoked, nor needed, at this level. Its own probe
profile is `(C, D)` (see `probeProfile_probeBot`), distinct from
CoopBot's — precisely the signature that a tailor-made adversary can
exploit (`exploiterBot`). -/
def probeBot : ProgramAgent := fun p _ => p

/-- ExploiterBot: a tailor-made bounded adversary against ProbeBot. It
cooperates with CoopBot and with DefectBot (profiles (C, C) and (D, D))
but defects against any agent whose probe profile is exactly (C, D) —
ProbeBot's signature. Proves that the first-level probe is NOT
unfathomable in general. -/
def exploiterBot : ProgramAgent :=
  fun p₁ p₂ =>
    match p₁, p₂ with
    | cooperate, defect => defect
    | _, _ => cooperate

/-! ## Decidable organs and finite family -/

/-- Mutual cooperation of the confrontation `(A, B)`. Decidable organ
(equality on `PDAction × PDAction` is decidable). -/
abbrev MutualCooperation (A B : ProgramAgent) : Prop :=
  outcome A B = (cooperate, cooperate)

/-- Unexploitability of `A` in the confrontation `(A, B)`: the sucker
profile (cooperating alone) is excluded. Decidable organ; the
equivalence with "payoff at least `P`" is `unexploitable_iff_payoff`. -/
abbrev Unexploitable (A B : ProgramAgent) : Prop :=
  outcome A B ≠ (cooperate, defect)

/-- Program Nash equilibrium within a finite family `F`: no unilateral
deviation to an agent of `F` strictly improves the deviator's payoff.
Decidable verification family by family (payoffs only take the four
values `T R P S`). -/
def ProgramNash (g : PrisonersDilemma) (F : List ProgramAgent)
    (A B : ProgramAgent) : Prop :=
  (∀ A' ∈ F, payoff1 g A' B ≤ payoff1 g A B) ∧
  (∀ B' ∈ F, payoff2 g A B' ≤ payoff2 g A B)

/-- Finite demonstration family: the three bounded bots. -/
def family : List ProgramAgent := [coopBot, defectBot, probeBot]

/-- Finite confrontation table: the outcomes of all pairs of `F`, row
by row. -/
def confrontationTable (F : List ProgramAgent) : List (PDAction × PDAction) :=
  F.flatMap fun A => F.map fun B => outcome A B

/-! ## Matrix invariants (reuses `RepeatedGames.Stage`) -/

/-- Transitivity `T > R > P`: temptation dominates punishment. -/
lemma temptation_gt_punishment (g : PrisonersDilemma) : g.T > g.P :=
  g.hRP.trans g.hTR

/-- Transitivity `R > P > S`: reward dominates the sucker payoff. -/
lemma reward_gt_sucker (g : PrisonersDilemma) : g.R > g.S :=
  g.hPS.trans g.hRP

/-- An agent is unexploitable iff its payoff is at least the punishment
level `P`: never do worse than mutual defection. -/
theorem unexploitable_iff_payoff (g : PrisonersDilemma) (A B : ProgramAgent) :
    Unexploitable A B ↔ payoff1 g A B ≥ g.P := by
  constructor
  · intro h
    rcases hc : outcome A B with ⟨a, b⟩
    cases a <;> cases b
    · simp only [payoff1, stagePayoff, hc]; exact le_of_lt g.hRP
    · exact absurd hc h
    · simp only [payoff1, stagePayoff, hc]
      exact le_of_lt (temptation_gt_punishment g)
    · simp only [payoff1, stagePayoff, hc]; exact le_refl _
  · intro hpay hcd
    have hS : payoff1 g A B = g.S := by
      simp only [payoff1, stagePayoff, hcd]
    rw [hS] at hpay
    exact lt_irrefl g.S (lt_of_lt_of_le g.hPS hpay)

/-! ## Outcomes of the trivial confrontations (finite computation) -/

@[simp] lemma probeProfile_coopBot :
    probeProfile coopBot = (cooperate, cooperate) := rfl

@[simp] lemma probeProfile_defectBot :
    probeProfile defectBot = (defect, defect) := rfl

/-- ProbeBot's probe signature: it cooperates with CoopBot but defects
against DefectBot — profile `(C, D)`, distinct from CoopBot's. -/
@[simp] lemma probeProfile_probeBot :
    probeProfile probeBot = (cooperate, defect) := rfl

/-- CoopBot against CoopBot: mutual cooperation. -/
lemma outcome_coopBot_coopBot :
    outcome coopBot coopBot = (cooperate, cooperate) := rfl

/-- DefectBot against DefectBot: mutual defection. -/
lemma outcome_defectBot_defectBot :
    outcome defectBot defectBot = (defect, defect) := rfl

/-- CoopBot against DefectBot: the sucker. -/
lemma outcome_coopBot_defectBot :
    outcome coopBot defectBot = (cooperate, defect) := rfl

/-- ProbeBot against ProbeBot: mutual cooperation BY BOUNDED PROBING,
without any Löb theorem. -/
lemma outcome_probeBot_probeBot :
    outcome probeBot probeBot = (cooperate, cooperate) := rfl

/-- ProbeBot against DefectBot: mutual defection, never the sucker. -/
lemma outcome_probeBot_defectBot :
    outcome probeBot defectBot = (defect, defect) := rfl

/-- ProbeBot against CoopBot: mutual cooperation. -/
lemma outcome_probeBot_coopBot :
    outcome probeBot coopBot = (cooperate, cooperate) := rfl

/-! ## Unexploitability: reach and limits of the bounded probe -/

/-- DefectBot is unexploitable against EVERY bounded agent: it never
plays `cooperate`, hence never the sucker profile. -/
theorem defectBot_unexploitable (B : ProgramAgent) :
    Unexploitable defectBot B := by
  intro h
  simp [outcome, defectBot] at h

/-- And the negative test: CoopBot IS exploited by DefectBot. -/
theorem coopBot_exploited_by_defectBot :
    ¬ Unexploitable coopBot defectBot := by
  simp [Unexploitable, outcome, coopBot, defectBot]

/-- ProbeBot is never the sucker within the family of trivial bots
(CoopBot, DefectBot, itself). -/
theorem probeBot_unexploitable_in_family :
    ∀ B ∈ family, Unexploitable probeBot B := by
  intro B hB
  simp [family] at hB
  rcases hB with rfl | rfl | rfl
  · decide
  · decide
  · decide

/-- THE limit of the bounded core L1: a tailor-made bounded adversary
exploits ProbeBot. `exploiterBot` cooperates with both trivial probes
but defects against any agent of signature (C, D) — ProbeBot's probe
profile betrays it. Making cooperation unfathomable requires the
mutual source reasoning of levels L2/L3 (Barasz et al. 2014 circuits,
Critch 2016 parametric Löb), out of scope. -/
theorem probeBot_exploited_by_exploiterBot :
    ¬ Unexploitable probeBot exploiterBot := by
  decide

/-! ## Program Nash equilibrium over the family -/

/-- (DefectBot, DefectBot) is a program Nash equilibrium of the family:
the mutual defection of the stage game survives the move to bounded
programs. -/
theorem programNash_defectBot_defectBot (g : PrisonersDilemma) :
    ProgramNash g family defectBot defectBot := by
  constructor
  · intro A' hA'
    simp [family] at hA'
    rcases hA' with rfl | rfl | rfl
    · simp only [payoff1, outcome, coopBot, defectBot, stagePayoff]
      exact le_of_lt g.hPS
    · exact le_refl _
    · simp only [payoff1, outcome, probeProfile, defectBot, probeBot, stagePayoff]
      exact le_refl _
  · intro B' hB'
    simp [family] at hB'
    rcases hB' with rfl | rfl | rfl
    · simp only [payoff2, outcome, coopBot, defectBot, stagePayoff]
      exact le_of_lt g.hPS
    · exact le_refl _
    · simp only [payoff2, outcome, probeProfile, defectBot, probeBot, stagePayoff]
      exact le_refl _

/-- (ProbeBot, ProbeBot): cooperation by probing IS a program Nash
equilibrium of the family. Deviating to DefectBot is PUNISHED: ProbeBot
defects against DefectBot, so the deviator collects P < R. At the
bounded level, the "probe then reciprocate" program therefore sustains
cooperation WITHOUT any Löb theorem — the central insight of program
equilibrium (Barasz et al. 2014). The L1 limit lies elsewhere: outside
the family, cf `probeBot_exploited_by_exploiterBot`. -/
theorem programNash_probeBot_probeBot (g : PrisonersDilemma) :
    ProgramNash g family probeBot probeBot := by
  constructor
  · intro A' hA'
    simp [family] at hA'
    rcases hA' with rfl | rfl | rfl
    · simp only [payoff1, outcome, probeProfile, coopBot, probeBot, stagePayoff]
      exact le_refl _
    · simp only [payoff1, outcome, probeProfile, defectBot, probeBot, stagePayoff]
      exact le_of_lt g.hRP
    · exact le_refl _
  · intro B' hB'
    simp [family] at hB'
    rcases hB' with rfl | rfl | rfl
    · simp only [payoff2, outcome, probeProfile, coopBot, probeBot, stagePayoff]
      exact le_refl _
    · simp only [payoff2, outcome, probeProfile, defectBot, probeBot, stagePayoff]
      exact le_of_lt g.hRP
    · exact le_refl _

/-- (CoopBot, DefectBot) is not an equilibrium either: CoopBot deviates
to DefectBot to escape the sucker payoff `S < P`. -/
theorem not_programNash_coopBot_defectBot (g : PrisonersDilemma) :
    ¬ ProgramNash g family coopBot defectBot := by
  intro h
  have h1 := h.1 defectBot (by simp [family])
  simp only [payoff1, outcome, defectBot, coopBot, stagePayoff] at h1
  exact lt_irrefl g.S (lt_of_lt_of_le g.hPS h1)

/-! ## Finite tests by evaluation -/

/-- Mutual cooperation of the bounded bots (computation by `decide`). -/
example : MutualCooperation coopBot coopBot := by decide

example : MutualCooperation probeBot probeBot := by decide

example : ¬ MutualCooperation defectBot defectBot := by decide

/-- Mutual defection (computation by `decide`). -/
example : outcome defectBot defectBot = (defect, defect) := by decide

/-- Unexploitability of the trivial bots (computation by `decide`). -/
example : Unexploitable defectBot probeBot := by decide

example : Unexploitable probeBot defectBot := by decide

example : ¬ Unexploitable coopBot defectBot := by decide

/-- The bounded probe betrayed by its signature (computation by
`decide`). -/
example : ¬ Unexploitable probeBot exploiterBot := by decide

/-- Finite confrontation table of the family: 9 outcomes, row by row
(coopBot, defectBot, probeBot). -/
example : confrontationTable family =
    [(cooperate, cooperate), (cooperate, defect), (cooperate, cooperate),
     (defect, cooperate), (defect, defect), (defect, defect),
     (cooperate, cooperate), (defect, defect), (cooperate, cooperate)] := by
  decide

end ProgramGames_en
