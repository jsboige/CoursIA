import ProgramGames.Basic

/-!
# Agents-programmes à budget explicite

Ce module complète le noyau fonctionnel de `ProgramGames.Basic` par un modèle
structurel inspiré de Barasz et al. (2014) et des agents bornés de Critch (2016).
Un agent porte un code public et un budget de raisonnement fini. Son interprète
est total : un budget
nul produit immédiatement une action et aucun résultat ne dépend d'une recherche
de preuve non bornée.

Les noms qui recouvrent des concepts de `Basic` portent un qualifieur explicite
(`Bounded` ou `InFamily`). Le module ne formalise ni logique de prouvabilité ni
théorème de Löb.
-/

namespace ProgramGames

open RepeatedGames PDAction

/-- Code public d'un agent-programme dans le modèle à budget explicite. -/
inductive ProgramCode where
  | cooperateBot
  | defectBot
  | mirror
  deriving DecidableEq, Repr

/-- Agent-programme associant un code public à un budget de raisonnement fini.
Il diffère du type fonctionnel `ProgramAgent` de `Basic` en rendant ces deux
données inspectables. -/
structure BoundedAgent where
  code : ProgramCode
  budget : Nat
  deriving DecidableEq, Repr

/-- Interprète total des codes publics. À budget nul, `mirror` dévie ; avec un
budget positif, il coopère sauf contre le code explicitement défecteur. -/
def act (agent : BoundedAgent) (opponent : ProgramCode) : PDAction :=
  match agent.code with
  | .cooperateBot => cooperate
  | .defectBot => defect
  | .mirror =>
      match agent.budget with
      | 0 => defect
      | _ + 1 => if opponent = .defectBot then defect else cooperate

/-- Résultat ordonné de l'interprète à budget explicite. Le qualifieur le
distingue de `Basic.outcome`, fondé sur des profils de sondes fonctionnels. -/
def outcomeBounded (row column : BoundedAgent) : PDAction × PDAction :=
  (act row column.code, act column row.code)

/-- Un agent est inexploitable dans une famille finie s'il ne coopère jamais
pendant que son adversaire dévie. La quantification sur une liste distingue
cette propriété de la propriété binaire `Basic.Unexploitable`. -/
def UnexploitableInFamily (agent : BoundedAgent)
    (opponents : List BoundedAgent) : Prop :=
  ∀ opponent ∈ opponents,
    outcomeBounded agent opponent ≠ (cooperate, defect)

/-- Coopération mutuelle pour deux agents à budget explicite. -/
def MutualCooperationBounded (left right : BoundedAgent) : Prop :=
  outcomeBounded left right = (cooperate, cooperate)

/-- Équilibre relatif à une famille finie d'agents à budget explicite. Aucune
substitution unilatérale dans la famille n'améliore strictement le paiement. -/
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

/-- Organe calculable de coopération mutuelle. -/
def mutualCooperationCheck (left right : BoundedAgent) : Bool :=
  decide (outcomeBounded left right = (cooperate, cooperate))

/-- Organe calculable d'inexploitabilité sur une famille finie. -/
def unexploitableCheck (agent : BoundedAgent)
    (opponents : List BoundedAgent) : Bool :=
  opponents.all fun opponent =>
    decide (outcomeBounded agent opponent ≠ (cooperate, defect))

/-- Rang calculable du paiement canonique : `S=0`, `P=1`, `R=3`, `T=5`. -/
def payoffRank : PDAction → PDAction → Nat
  | cooperate, cooperate => 3
  | cooperate, defect => 0
  | defect, cooperate => 5
  | defect, defect => 1

/-- Paramétrage canonique `T=5, R=3, P=1, S=0` du Dilemme du prisonnier. -/
def canonicalPD : PrisonersDilemma where
  T := 5
  R := 3
  P := 1
  S := 0
  hTR := by norm_num
  hRP := by norm_num
  hPS := by norm_num
  hPD := by norm_num

/-- Le rang fini préserve exactement l'ordre des paiements du jeu canonique. -/
theorem payoffRank_le_iff (a₁ a₂ b₁ b₂ : PDAction) :
    payoffRank a₁ a₂ ≤ payoffRank b₁ b₂ ↔
      stagePayoff canonicalPD a₁ a₂ ≤ stagePayoff canonicalPD b₁ b₂ := by
  cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂ <;>
    norm_num [payoffRank, canonicalPD, stagePayoff]

/-- Organe calculable d'équilibre relatif pour le PD canonique. Le classement
fini évite de prétendre calculer l'ordre non décidable des réels arbitraires. -/
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

/-- L'organe booléen est correct et complet pour l'équilibre dans le PD canonique. -/
theorem programNashCheck_eq_true (family : List BoundedAgent)
    (left right : BoundedAgent) :
    programNashCheck family left right = true ↔
      ProgramNashBounded canonicalPD family left right := by
  simp [programNashCheck, ProgramNashBounded, payoffRank_le_iff]

/-- Bot qui coopère sans inspection. -/
def cooperateBot : BoundedAgent := ⟨.cooperateBot, 0⟩

/-- Bot qui dévie sans inspection. Son nom le distingue du `defectBot`
fonctionnel de `Basic`. -/
def defectBotBounded : BoundedAgent := ⟨.defectBot, 0⟩

/-- Bot miroir doté d'un budget strictement positif. -/
def mirrorBot : BoundedAgent := ⟨.mirror, 1⟩

/-- Famille témoin finie utilisée par les certificats calculables. -/
def basicFamily : List BoundedAgent :=
  [cooperateBot, defectBotBounded, mirrorBot]

/-- Deux bots coopérateurs produisent la coopération mutuelle. -/
theorem cooperate_cooperate :
    MutualCooperationBounded cooperateBot cooperateBot := by
  rfl

/-- Deux bots défecteurs produisent la défection mutuelle. -/
theorem defect_defect :
    outcomeBounded defectBotBounded defectBotBounded = (defect, defect) := by
  rfl

/-- Le bot miroir coopère avec lui-même lorsque son budget est positif. -/
theorem mirror_mirror : MutualCooperationBounded mirrorBot mirrorBot := by
  rfl

/-- Le bot défecteur est inexploitable contre toute famille : sa propre action
n'est jamais `cooperate`. -/
theorem defectBotBounded_unexploitable (opponents : List BoundedAgent) :
    UnexploitableInFamily defectBotBounded opponents := by
  intro opponent hopponent
  simp [outcomeBounded, act, defectBotBounded]

/-- Le vérificateur fini confirme l'inexploitabilité du bot miroir dans la
famille témoin : il dévie contre `defectBotBounded` et coopère avec les autres. -/
theorem mirror_basicFamily_unexploitable :
    unexploitableCheck mirrorBot basicFamily = true := by
  decide

/-- Dans le PD canonique et la famille témoin, la défection mutuelle est un
équilibre relatif : toute déviation unilatérale contre le bot défecteur rapporte
au plus `P`. -/
theorem defect_profile_programNash :
    ProgramNashBounded canonicalPD basicFamily
      defectBotBounded defectBotBounded := by
  norm_num [ProgramNashBounded, basicFamily, canonicalPD, cooperateBot,
    defectBotBounded, mirrorBot, outcomeBounded, act, stagePayoff]

/-- Le même certificat est exposé par l'organe booléen. -/
theorem defect_profile_check :
    programNashCheck basicFamily defectBotBounded defectBotBounded = true := by
  decide

end ProgramGames
