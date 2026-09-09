import Mathlib.Tactic
import RepeatedGames.Stage

/-!
# Équilibre en programmes : noyau borné (L1)

Formalisation du premier niveau (L1) de l'équilibre en programmes
(*program equilibrium*) pour le Dilemme du Prisonnier : des agents
bornés qui consultent uniquement le comportement de leur adversaire
contre les deux sondes triviales (CoopBot et DefectBot), sans récursion
ni introspection non bornée.

Références :
  - Barasz, Christiano, Fallenstein, Herreshoff, LaVictor, Yudkowsky
    (2014), « Program Equilibrium via Succinct Circuit Representation »,
    arXiv:1401.5577 ;
  - Critch (2016), « Parametric Bounded Löb's Theorem and Robust
    Cooperation of Bounded Agents », arXiv:1602.04184.

Périmètre VOLONTAIREMENT restreint (tranche L1 de l'EPIC #15062
« Math for AI Safety », grain #15176) :
  - agents bornés et totaux (`ProgramAgent`), sémantique `outcome`
    sans récursion (deux applications de fonction), table de
    confrontations finie ;
  - organes décidables : `MutualCooperation`, `Unexploitable` ;
  - `ProgramNash` vérifié par preuve sur une famille finie ;
  - AUCUNE formalisation de Löb (ad-hoc ou paramétrique) : les niveaux
    L2/L3 (raisonnement sur les sources mutuelles, agents à profondeur
    croissante) sont hors scope.

Le module réutilise le jeu de stage de `RepeatedGames.Stage`
(`PDAction`, `PrisonersDilemma`, `stagePayoff`).

## Résultats-phare

  - `outcome_probeBot_probeBot` : le bot à sonde atteint la coopération
    mutuelle AVEC LUI-MÊME par sondage borné, sans aucun théorème de
    Löb (un `rfl`) ;
  - `programNash_probeBot_probeBot` : cette coopération est un
    équilibre de Nash en programmes DE LA FAMILLE — dévier vers
    DefectBot est puni (P < R) : « sonde puis réciprocité » soutient la
    coopération au niveau borné, l'insight central de Barasz et al. 2014 ;
  - `probeBot_unexploitable_in_family` : ce bot n'est jamais le dindon
    de la farce au sein de la famille des bots triviaux ;
  - `probeBot_exploited_by_exploiterBot` : MAIS un adversaire borné sur
    mesure exploite la sonde — la signature (C, D) du profil de sonde
    de ProbeBot le trahit. Hors de la famille, sans raisonnement sur
    les sources mutuelles (L2/L3, Löb paramétrique de Critch 2016), la
    coopération programmatique n'est pas insondable : c'est la limite
    exacte du niveau L1.
-/

namespace ProgramGames

open RepeatedGames
open PDAction

/-! ## Agents-programmes bornés -/

/-- Un agent-programme borné : une fonction **totale** qui, informée du
profil de sonde de son adversaire (action contre CoopBot, action contre
DefectBot), choisit une action du Dilemme du Prisonnier. L'espace des
agents est fini : `PDAction` a deux constructeurs, donc
`ProgramAgent := PDAction → PDAction → PDAction` admet 2⁴ = 16 fonctions
extensionnellement distinctes (une énumération des tables binaires de
longueur quatre le confirme). Chaque confrontation se réduit à un nombre
borné d'évaluations : aucune récursion, aucune recherche non bornée,
aucune boucle. -/
abbrev ProgramAgent : Type := PDAction → PDAction → PDAction

/-- Profil de sonde d'un agent : son action contre CoopBot (première
composante) et contre DefectBot (seconde). C'est la seule information
sur l'adversaire qu'un agent borné de ce noyau peut consulter : une
sonde de premier niveau, terminale par construction. -/
def probeProfile (A : ProgramAgent) : PDAction × PDAction :=
  (A cooperate cooperate, A defect defect)

/-- Sémantique de confrontation : chaque agent joue l'action dictée par
son programme, informé du profil de sonde de l'adversaire. Évaluation
bornée : deux applications de fonction, zéro récursion. -/
def outcome (A B : ProgramAgent) : PDAction × PDAction :=
  (A (probeProfile B).1 (probeProfile B).2,
   B (probeProfile A).1 (probeProfile A).2)

/-- Paiement du premier joueur (row) dans la confrontation `(A, B)`,
via la matrice de `RepeatedGames.stagePayoff`. -/
def payoff1 (g : PrisonersDilemma) (A B : ProgramAgent) : ℝ :=
  stagePayoff g (outcome A B).1 (outcome A B).2

/-- Paiement du second joueur (column) dans la confrontation `(A, B)`. -/
def payoff2 (g : PrisonersDilemma) (A B : ProgramAgent) : ℝ :=
  stagePayoff g (outcome A B).2 (outcome A B).1

/-! ## Bots triviaux -/

/-- CoopBot : coopère inconditionnellement. -/
def coopBot : ProgramAgent := fun _ _ => cooperate

/-- DefectBot : dévie inconditionnellement. -/
def defectBot : ProgramAgent := fun _ _ => defect

/-- ProbeBot : coopère si et seulement si l'adversaire coopère avec
CoopBot. Sonde bornée de premier niveau — surrogate du FairBot de la
littérature (Barasz et al. 2014) SANS raisonnement autoréférentif :
aucun théorème de Löb n'est invoqué ni nécessaire à ce niveau. Son
profil de sonde propre est `(C, D)` (voir `probeProfile_probeBot`),
distinct de celui de CoopBot — c'est cette signature qui le rend
exploitable par un adversaire sur mesure (`exploiterBot`). -/
def probeBot : ProgramAgent := fun p _ => p

/-- ExploiterBot : adversaire borné sur mesure contre ProbeBot. Il
coopère avec CoopBot et avec DefectBot (profils (C, C) et (D, D)) mais
dévie contre tout agent dont le profil de sonde est exactement (C, D) —
la signature de ProbeBot. Prouve que la sonde de premier niveau n'est
PAS insondable en général. -/
def exploiterBot : ProgramAgent :=
  fun p₁ p₂ =>
    match p₁, p₂ with
    | cooperate, defect => defect
    | _, _ => cooperate

/-! ## Organes décidables et famille finie -/

/-- Coopération mutuelle de la confrontation `(A, B)`. Organe décidable
(l'égalité sur `PDAction × PDAction` est décidable). -/
abbrev MutualCooperation (A B : ProgramAgent) : Prop :=
  outcome A B = (cooperate, cooperate)

/-- Inexploitabilité de `A` dans la confrontation `(A, B)` : le profil
du dindon (coopérer seul) est exclu. Organe décidable ; l'équivalence
avec « paiement au moins `P` » est `unexploitable_iff_payoff`. -/
abbrev Unexploitable (A B : ProgramAgent) : Prop :=
  outcome A B ≠ (cooperate, defect)

/-- Équilibre de Nash en programmes au sein d'une famille finie `F` :
aucune déviation unilatérale vers un agent de `F` n'améliore
strictement le paiement du déviant. Vérification décidable famille par
famille (les paiements ne prennent que les quatre valeurs `T R P S`). -/
def ProgramNash (g : PrisonersDilemma) (F : List ProgramAgent)
    (A B : ProgramAgent) : Prop :=
  (∀ A' ∈ F, payoff1 g A' B ≤ payoff1 g A B) ∧
  (∀ B' ∈ F, payoff2 g A B' ≤ payoff2 g A B)

/-- Famille finie de démonstration : les trois bots bornés. -/
def family : List ProgramAgent := [coopBot, defectBot, probeBot]

/-- Table de confrontations finie : les issues de tous les couples de
`F`, ligne par ligne. -/
def confrontationTable (F : List ProgramAgent) : List (PDAction × PDAction) :=
  F.flatMap fun A => F.map fun B => outcome A B

/-! ## Invariants de la matrice (réutilise `RepeatedGames.Stage`) -/

/-- Transitivité `T > R > P` : la tentation domine la punition. -/
lemma temptation_gt_punishment (g : PrisonersDilemma) : g.T > g.P :=
  g.hRP.trans g.hTR

/-- Transitivité `R > P > S` : la récompense domine le dindon. -/
lemma reward_gt_sucker (g : PrisonersDilemma) : g.R > g.S :=
  g.hPS.trans g.hRP

/-- Un agent est inexploitable ssi son paiement est au moins le niveau
de punition `P` : ne jamais faire pire que la défection mutuelle. -/
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

/-! ## Issues des confrontations triviales (calcul fini) -/

@[simp] lemma probeProfile_coopBot :
    probeProfile coopBot = (cooperate, cooperate) := rfl

@[simp] lemma probeProfile_defectBot :
    probeProfile defectBot = (defect, defect) := rfl

/-- Signature de sonde de ProbeBot : il coopère avec CoopBot mais
dévie contre DefectBot — profil `(C, D)`, distinct de celui de CoopBot. -/
@[simp] lemma probeProfile_probeBot :
    probeProfile probeBot = (cooperate, defect) := rfl

/-- CoopBot contre CoopBot : coopération mutuelle. -/
lemma outcome_coopBot_coopBot :
    outcome coopBot coopBot = (cooperate, cooperate) := rfl

/-- DefectBot contre DefectBot : défection mutuelle. -/
lemma outcome_defectBot_defectBot :
    outcome defectBot defectBot = (defect, defect) := rfl

/-- CoopBot contre DefectBot : le dindon de la farce. -/
lemma outcome_coopBot_defectBot :
    outcome coopBot defectBot = (cooperate, defect) := rfl

/-- ProbeBot contre ProbeBot : coopération mutuelle PAR SONDAGE BORNÉ,
sans aucun théorème de Löb. -/
lemma outcome_probeBot_probeBot :
    outcome probeBot probeBot = (cooperate, cooperate) := rfl

/-- ProbeBot contre DefectBot : défection mutuelle, jamais dindon. -/
lemma outcome_probeBot_defectBot :
    outcome probeBot defectBot = (defect, defect) := rfl

/-- ProbeBot contre CoopBot : coopération mutuelle. -/
lemma outcome_probeBot_coopBot :
    outcome probeBot coopBot = (cooperate, cooperate) := rfl

/-! ## Inexploitabilité : portée et limites de la sonde bornée -/

/-- DefectBot est inexploitable contre TOUT agent borné : il ne joue
jamais `cooperate`, donc jamais le profil du dindon. -/
theorem defectBot_unexploitable (B : ProgramAgent) :
    Unexploitable defectBot B := by
  intro h
  simp [outcome, defectBot] at h

/-- Et le test négatif : CoopBot EST exploité par DefectBot. -/
theorem coopBot_exploited_by_defectBot :
    ¬ Unexploitable coopBot defectBot := by
  simp [Unexploitable, outcome, coopBot, defectBot]

/-- ProbeBot n'est jamais le dindon de la farce au sein de la famille
des bots triviaux (CoopBot, DefectBot, lui-même). -/
theorem probeBot_unexploitable_in_family :
    ∀ B ∈ family, Unexploitable probeBot B := by
  intro B hB
  simp [family] at hB
  rcases hB with rfl | rfl | rfl
  · decide
  · decide
  · decide

/-- LA limite du noyau borné L1 : un adversaire borné sur mesure
exploite ProbeBot. `exploiterBot` coopère avec les deux sondes triviales
mais dévie contre tout agent de signature (C, D) — le profil de sonde
de ProbeBot le trahit. Rendre la coopération insondable exige le
raisonnement sur les sources mutuelles des niveaux L2/L3 (circuits de
Barasz et al. 2014, Löb paramétrique de Critch 2016), hors scope. -/
theorem probeBot_exploited_by_exploiterBot :
    ¬ Unexploitable probeBot exploiterBot := by
  decide

/-! ## Équilibre de Nash en programmes sur la famille -/

/-- (DefectBot, DefectBot) est un équilibre de Nash en programmes de la
famille : la défection mutuelle du jeu statique survit au passage aux
programmes bornés. -/
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

/-- (ProbeBot, ProbeBot) : la coopération mutuelle par sondage EST un
équilibre de Nash en programmes de la famille. Dévier vers DefectBot
est PUNI : ProbeBot dévie contre DefectBot, le déviant récolte P < R.
Au niveau borné, le programme « sonde puis réciprocité » soutient donc
la coopération SANS aucun théorème de Löb — l'insight central de
l'équilibre en programmes (Barasz et al. 2014). La limite du L1 est
ailleurs : hors de la famille, cf `probeBot_exploited_by_exploiterBot`. -/
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

/-- (CoopBot, DefectBot) n'est pas un équilibre non plus : CoopBot
dévie vers DefectBot pour échapper au paiement du dindon `S < P`. -/
theorem not_programNash_coopBot_defectBot (g : PrisonersDilemma) :
    ¬ ProgramNash g family coopBot defectBot := by
  intro h
  have h1 := h.1 defectBot (by simp [family])
  simp only [payoff1, outcome, defectBot, coopBot, stagePayoff] at h1
  exact lt_irrefl g.S (lt_of_lt_of_le g.hPS h1)

/-! ## Tests finis par évaluation -/

/-- Coopération mutuelle des bots bornés (calcul par `decide`). -/
example : MutualCooperation coopBot coopBot := by decide

example : MutualCooperation probeBot probeBot := by decide

example : ¬ MutualCooperation defectBot defectBot := by decide

/-- Défection mutuelle (calcul par `decide`). -/
example : outcome defectBot defectBot = (defect, defect) := by decide

/-- Inexploitabilité des bots triviaux (calcul par `decide`). -/
example : Unexploitable defectBot probeBot := by decide

example : Unexploitable probeBot defectBot := by decide

example : ¬ Unexploitable coopBot defectBot := by decide

/-- La sonde bornée trahie par sa signature (calcul par `decide`). -/
example : ¬ Unexploitable probeBot exploiterBot := by decide

/-- Table de confrontations finie de la famille : 9 issues, ligne par
ligne (coopBot, defectBot, probeBot). -/
example : confrontationTable family =
    [(cooperate, cooperate), (cooperate, defect), (cooperate, cooperate),
     (defect, cooperate), (defect, defect), (defect, defect),
     (cooperate, cooperate), (defect, defect), (cooperate, cooperate)] := by
  decide

end ProgramGames
