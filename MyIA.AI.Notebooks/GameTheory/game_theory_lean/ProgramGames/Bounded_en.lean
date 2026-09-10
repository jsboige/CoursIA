import ProgramGames.Basic_en

/-!
# Program agents with explicit reasoning budgets

This module complements the functional core in `ProgramGames.Basic_en` with a
structural model inspired by Barasz et al. (2014) and Critch's bounded agents
(2016). An agent carries public code and a finite reasoning budget. Its
interpreter is total: a
zero budget immediately produces an action, and no result depends on an
unbounded proof search.

Names overlapping concepts from `Basic_en` carry an explicit qualifier
(`Bounded` or `InFamily`). The module formalises neither provability logic nor
Löb's theorem.
-/

namespace ProgramGames_en

open RepeatedGames PDAction

/-- Public code of a program agent in the explicit-budget model. -/
inductive ProgramCode where
  | cooperateBot
  | defectBot
  | mirror
  deriving DecidableEq, Repr

/-- Program agent associating public code with a finite reasoning budget. It
differs from the functional `ProgramAgent` type in `Basic_en` by making these
two data fields inspectable. -/
structure BoundedAgent where
  code : ProgramCode
  budget : Nat
  deriving DecidableEq, Repr

/-- Total interpreter of public codes. At budget zero, `mirror` defects; with a
positive budget, it cooperates except against explicitly defecting code. -/
def act (agent : BoundedAgent) (opponent : ProgramCode) : PDAction :=
  match agent.code with
  | .cooperateBot => cooperate
  | .defectBot => defect
  | .mirror =>
      match agent.budget with
      | 0 => defect
      | _ + 1 => if opponent = .defectBot then defect else cooperate

/-- Ordered outcome of the explicit-budget interpreter. The qualifier
distinguishes it from `Basic_en.outcome`, based on functional probe profiles. -/
def outcomeBounded (row column : BoundedAgent) : PDAction × PDAction :=
  (act row column.code, act column row.code)

/-- An agent is unexploitable in a finite family if it never cooperates while
its opponent defects. Quantification over a list distinguishes this property
from the binary property `Basic_en.Unexploitable`. -/
def UnexploitableInFamily (agent : BoundedAgent)
    (opponents : List BoundedAgent) : Prop :=
  ∀ opponent ∈ opponents,
    outcomeBounded agent opponent ≠ (cooperate, defect)

/-- Mutual cooperation for two agents with explicit budgets. -/
def MutualCooperationBounded (left right : BoundedAgent) : Prop :=
  outcomeBounded left right = (cooperate, cooperate)

/-- Equilibrium relative to a finite family of explicit-budget agents. No
unilateral substitution in the family strictly improves the relevant payoff. -/
def ProgramNashBounded (game : PrisonersDilemma)
    (family : List BoundedAgent) (left right : BoundedAgent) : Prop :=
  (∀ alternative ∈ family,
    stagePayoff game (outcomeBounded alternative right).1
        (outcomeBounded alternative right).2 ≤
      stagePayoff game (outcomeBounded left right).1
        (outcomeBounded left right).2) ∧
  (∀ alternative ∈ family,
    stagePayoff game (outcomeBounded left alternative).2
        (outcomeBounded left alternative).1 ≤
      stagePayoff game (outcomeBounded left right).2
        (outcomeBounded left right).1)

/-- Computable mutual-cooperation checker. -/
def mutualCooperationCheck (left right : BoundedAgent) : Bool :=
  decide (outcomeBounded left right = (cooperate, cooperate))

/-- Computable unexploitable checker on a finite family. -/
def unexploitableCheck (agent : BoundedAgent)
    (opponents : List BoundedAgent) : Bool :=
  opponents.all fun opponent =>
    decide (outcomeBounded agent opponent ≠ (cooperate, defect))

/-- Computable rank of the canonical payoff: `S=0`, `P=1`, `R=3`, `T=5`. -/
def payoffRank : PDAction → PDAction → Nat
  | cooperate, cooperate => 3
  | cooperate, defect => 0
  | defect, cooperate => 5
  | defect, defect => 1

/-- Canonical `T=5, R=3, P=1, S=0` Prisoner's Dilemma parameters. -/
def canonicalPD : PrisonersDilemma where
  T := 5
  R := 3
  P := 1
  S := 0
  hTR := by norm_num
  hRP := by norm_num
  hPS := by norm_num
  hPD := by norm_num

/-- The finite rank preserves exactly the payoff order of the canonical game. -/
theorem payoffRank_le_iff (a₁ a₂ b₁ b₂ : PDAction) :
    payoffRank a₁ a₂ ≤ payoffRank b₁ b₂ ↔
      stagePayoff canonicalPD a₁ a₂ ≤ stagePayoff canonicalPD b₁ b₂ := by
  cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂ <;>
    norm_num [payoffRank, canonicalPD, stagePayoff]

/-- Computable relative-equilibrium checker for the canonical PD. The finite
ranking avoids pretending to compute the undecidable order of arbitrary reals. -/
def programNashCheck (family : List BoundedAgent)
    (left right : BoundedAgent) : Bool :=
  (family.all fun alternative => decide (
    payoffRank (outcomeBounded alternative right).1
        (outcomeBounded alternative right).2 ≤
      payoffRank (outcomeBounded left right).1
        (outcomeBounded left right).2)) &&
  (family.all fun alternative => decide (
    payoffRank (outcomeBounded left alternative).2
        (outcomeBounded left alternative).1 ≤
      payoffRank (outcomeBounded left right).2
        (outcomeBounded left right).1))

/-- The Boolean checker is sound and complete for equilibrium in the canonical PD. -/
theorem programNashCheck_eq_true (family : List BoundedAgent)
    (left right : BoundedAgent) :
    programNashCheck family left right = true ↔
      ProgramNashBounded canonicalPD family left right := by
  simp [programNashCheck, ProgramNashBounded, payoffRank_le_iff]

/-- Bot that cooperates without inspection. -/
def cooperateBot : BoundedAgent := ⟨.cooperateBot, 0⟩

/-- Bot that defects without inspection. Its name distinguishes it from the
functional `defectBot` in `Basic_en`. -/
def defectBotBounded : BoundedAgent := ⟨.defectBot, 0⟩

/-- Mirror bot with a strictly positive budget. -/
def mirrorBot : BoundedAgent := ⟨.mirror, 1⟩

/-- Finite witness family used by the computable certificates. -/
def basicFamily : List BoundedAgent :=
  [cooperateBot, defectBotBounded, mirrorBot]

/-- Two cooperating bots produce mutual cooperation. -/
theorem cooperate_cooperate :
    MutualCooperationBounded cooperateBot cooperateBot := by
  rfl

/-- Two defecting bots produce mutual defection. -/
theorem defect_defect :
    outcomeBounded defectBotBounded defectBotBounded = (defect, defect) := by
  rfl

/-- The mirror bot cooperates with itself when its budget is positive. -/
theorem mirror_mirror : MutualCooperationBounded mirrorBot mirrorBot := by
  rfl

/-- The defecting bot is unexploitable against every family: its own action is
never `cooperate`. -/
theorem defectBotBounded_unexploitable (opponents : List BoundedAgent) :
    UnexploitableInFamily defectBotBounded opponents := by
  intro opponent hopponent
  simp [outcomeBounded, act, defectBotBounded]

/-- The finite checker confirms that the mirror bot is unexploitable in the
witness family: it defects against `defectBotBounded` and cooperates otherwise. -/
theorem mirror_basicFamily_unexploitable :
    unexploitableCheck mirrorBot basicFamily = true := by
  decide

/-- In the canonical PD and witness family, mutual defection is a relative
equilibrium: every unilateral deviation against the defecting bot pays at most
`P`. -/
theorem defect_profile_programNash :
    ProgramNashBounded canonicalPD basicFamily
      defectBotBounded defectBotBounded := by
  norm_num [ProgramNashBounded, basicFamily, canonicalPD, cooperateBot,
    defectBotBounded, mirrorBot, outcomeBounded, act, stagePayoff]

/-- The Boolean checker exposes the same certificate. -/
theorem defect_profile_check :
    programNashCheck basicFamily defectBotBounded defectBotBounded = true := by
  decide

end ProgramGames_en
