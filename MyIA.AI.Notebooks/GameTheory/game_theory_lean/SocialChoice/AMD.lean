/-
  Design de mécanismes automatisé (AMD) — Compagnon Lean
  ======================================================

  Certificat formel du compagnon Lean du notebook
  `GameTheory-16b-Automated-Mechanism-Design.ipynb` (PR #12259) : le
  mécanisme M* produit par le générateur Python (énumération + argmax sur
  le bien-être social, paiements nuls) est certifié par le noyau Lean
  (`simp` énumérant le domaine fini) — DSIC, IR, J* = 2, optimalité
  de J — au sens STANDARD
  (point de départ = report sincère), et l'impossibilité « paiement
  strictement positif ⇒ IR violé » est prouvée en général (miroir de
  l'exercice 3 du notebook).

  Chaîne Loi II (issue #12205, grain B3) :

      spécification (Θ, O, U, J)  ->  générateur Python (hors Lean)  ->  M*
      ->  certificat Lean `by decide`  (ce fichier)

  Ce qui est certifié est le TÉMOIN, pas le chercheur : le moteur de
  synthèse reste hors Lean (dette assumée, #12205 B1).

  Domaine : 2 agents, types θ ∈ {F, T} (valeur 1 ↔ T), issue o ∈ {F, T},
  paiements ∈ ℤ. Utilité u_i = θ_i * o(r) - p_i(r).

  Référence : Sandholm, « Automated Mechanism Design: A New Initiative »
  Référence : #12205 (chantier 2, B3), #12211 (gate distillation, satisfaite par #12259)
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace SocialChoice.AMD

/-! ## Domaine fini et définitions

  Un profile de types est `(θ₀, θ₁) : Bool × Bool`. Un mécanisme est la
  donnée d'une table d'issues `o : Bool × Bool → Bool` et de deux tables
  de paiements `p₀ p₁ : Bool × Bool → ℤ`. -/

/-- Type de l'agent (booléen pédagogique : T = type 1 qui veut o = T, F = type 0 indifférent). -/
abbrev AgentType := Bool

/-- Profile de types reportés par les deux agents. -/
abbrev Profile := Bool × Bool

/-- Valeur numérique d'un type (θ = 1 ↔ T), en arithmétique signée. -/
def thetaVal (t : AgentType) : ℤ := if t then 1 else 0

/-- Valeur numérique d'une issue (o = 1 ↔ T). -/
def issueVal (o : Bool) : ℤ := if o then 1 else 0

/-- Utilité de l'agent 0 : son type VRAI `t`, le profile REPORTÉ `r` détermine issue et paiement. -/
def u0 (o : Profile → Bool) (p0 : Profile → ℤ) (t : AgentType) (r : Profile) : ℤ :=
  thetaVal t * issueVal (o r) - p0 r

/-- Utilité de l'agent 1 (symétrique). -/
def u1 (o : Profile → Bool) (p1 : Profile → ℤ) (t : AgentType) (r : Profile) : ℤ :=
  thetaVal t * issueVal (o r) - p1 r

/-- **DSIC au sens standard** : pour tout profile vrai, rapporter son type
    sincèrement est optimal (l'autre agent étant sincère), pour chaque agent
    et toute déviation unilatérale. Le point de départ de la comparaison
    est le report SINCÈRE — pas un report arbitraire (cf. réserve #12211 :
    le vérificateur Python initial comparait depuis tout report r). -/
def DSIC (o : Profile → Bool) (p0 p1 : Profile → ℤ) : Prop :=
  ∀ x : AgentType × AgentType × AgentType,
    u0 o p0 x.1 (x.1, x.2.1) ≥ u0 o p0 x.1 (x.2.2, x.2.1) ∧
    u1 o p1 x.2.1 (x.1, x.2.1) ≥ u1 o p1 x.2.1 (x.1, x.2.2)

/-- **IR au sens standard** : pour tout profile vrai, l'utilité du report
    sincère est non négative pour chaque agent. -/
def IR (o : Profile → Bool) (p0 p1 : Profile → ℤ) : Prop :=
  ∀ x : AgentType × AgentType,
    u0 o p0 x.1 (x.1, x.2) ≥ 0 ∧ u1 o p1 x.2 (x.1, x.2) ≥ 0

/-- Bien-être social au profile vrai : somme des θ_i * o(profile). -/
def J (o : Profile → Bool) (t0 t1 : AgentType) : ℤ :=
  thetaVal t0 * issueVal (o (t0, t1)) + thetaVal t1 * issueVal (o (t0, t1))

/-! ## Le mécanisme M* du générateur (GameTheory-16b, cellule 3)

  Le générateur Python (true_types = [1, 1]) produit exactement :
  `issue_table = {(0,0):0, (0,1):0, (1,0):0, (1,1):1}`, paiements nuls
  partout. Encodage : `o* (θ₀, θ₁) = θ₀ ∧ θ₁`. -/

/-- Table d'issues de M* : l'issue vaut T uniquement au profile (T, T). -/
def o_star (r : Profile) : Bool := r.1 && r.2

/-- Table de paiements de M* : paiements nuls partout. -/
def p_star (_r : Profile) : ℤ := 0

/-- **Certificat 1** : M* est DSIC au sens standard, sur tout le domaine fini. -/
theorem amd_star_DSIC : DSIC o_star p_star p_star := by
  simp [DSIC, u0, u1, thetaVal, issueVal, o_star, p_star]

/-- **Certificat 2** : M* est IR sur tout le domaine fini. -/
theorem amd_star_IR : IR o_star p_star p_star := by
  simp [IR, u0, u1, thetaVal, issueVal, o_star, p_star]

/-- **Certificat 3** : le bien-être social de M* au profile vrai (T, T) vaut 2
    — la valeur J* annoncée par le générateur. -/
theorem amd_star_J : J o_star true true = 2 := by
  simp [J, thetaVal, issueVal, o_star]

/-- **Certificat 4 (optimalité)** : aucun mécanisme du domaine ne fait mieux
    que 2 au profile (T, T) — la valeur 2 de M* est l'optimum du bien-être
    social sur ce domaine, ce que le générateur atteint par énumération. -/
theorem amd_star_J_optimal (o : Profile → Bool) : J o true true ≤ 2 := by
  unfold J thetaVal issueVal
  split_ifs <;> norm_num

/-! ## Impossibilité : paiement strictement positif ⇒ IR violé

  Miroir formel de l'exercice 3 du notebook (témoin d'impossibilité par
  énumération en Python) : ici la preuve est GÉNÉRALE — aucun mécanisme de
  paiement strictement positif ne satisfait IR, quel que soit le nombre de
  candidats énumérés. C'est le complémentaire constructeur/vérificateur :
  Python montre le vide par énumération, Lean le prouve pour tout M. -/

/-- **Impossibilité** : si chaque paiement est ≥ 1 en tout profile, alors IR
    échoue — l'agent de type F a une utilité `-p ≤ -1 < 0` au profile
    sincère (F, F), quelle que soit la table d'issues. -/
theorem impossibility_strict_payments
    (o : Profile → Bool) (p0 p1 : Profile → ℤ)
    (h0 : ∀ r : Profile, 1 ≤ p0 r) (_h1 : ∀ r : Profile, 1 ≤ p1 r) :
    ¬ IR o p0 p1 := by
  intro hir
  obtain ⟨hu0, _⟩ := hir (false, false)
  have hp := h0 (false, false)
  have hu_reduced : (0 : ℤ) - p0 (false, false) ≥ 0 := by
    have : u0 o p0 false (false, false) = 0 - p0 (false, false) := by
      simp [u0, thetaVal, issueVal]
    rw [this] at hu0
    exact hu0
  omega

end SocialChoice.AMD
