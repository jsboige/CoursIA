/-
  Réputation et dissuasion d'entrée (chaîne de magasins, vérifié au noyau)
  =============================================================

  Forme stratégique réduite de l'histoire classique de dissuasion d'entrée
  sur deux périodes (Kreps-Wilson / Milgrom-Roberts) : un incumbent fait
  face à une entrée en période 1, répond Fight ou Accommodate, et un second
  entrant décide d'entrer ou non en période 2 *après avoir observé* la
  réponse de période 1.

  L'incumbent (joueur 1) est l'un des deux types :
  - type 0, « rationnel » : se battre coûte à chaque période prise
    isolément (paiements de stade : Fight 0 < Accommodate 2) ;
  - type 1, « dur » (type par engagement) : se battre est intrinsèquement
    préféré (Fight 3 > Accommodate 0).

  Poids de prior égaux (1, 1). Le monopole de période 2 (l'entrant reste
  dehors) paie l'incumbent 5.

  Voir le fichier original pour les encodages d'actions (plans réduits,
  `Fin 4`). Parce que l'équilibre de forme normale admet aussi des menaces
  non crédibles, on impose un raffinement *de crédibilité* décidable tenant
  lieu de rationalité séquentielle en dernière période.

  Résultats (tous par `decide` + éta-expansion des stratégies) :
  - `gRep` (information incomplète, réputation possible) a un BNE crédible
    unique : le type rationnel *fusionne* avec le type dur et se bat en
    période 1, l'entrant reste dehors après un combat. L'incumbent
    rationnel gagne 5.
  - `gNoRep` (benchmark à information complète : l'incumbent est connu
    rationnel) a un BNE crédible unique : accommoder, entrée a lieu,
    paiement 4.
  - `reputation_pays` : 4 < 5 dans toute paire d'équilibres crédibles —
    l'incitation de l'incumbent à se battre vient *uniquement* de
    l'incertitude de l'entrant sur son type, i.e. de la réputation.

  Voir #2610 (formalisation GT-Lean, phase bayésienne 5).
-/

import Bayesian.BNE

/-! ### Plan decoders -/

/-- Réponse de période 1 encodée dans un plan d'incumbent
    (0 = Accommodate, 1 = Fight). -/
def planR1 (a : Fin 4) : Nat := a.val / 2

/-- Réponse de période 2 (si entrée) encodée dans un plan d'incumbent
    (0 = Accommodate, 1 = Fight). -/
def planR2 (a : Fin 4) : Nat := a.val % 2

/-- Décision d'entrée de période 2 de l'entrant sur le chemin : la composante
    de son plan sélectionnée par la réponse observée de période 1
    (0 = Out, 1 = In). -/
def entryOf (a1 a2 : Fin 4) : Nat :=
  if planR1 a1 = 1 then a2.val / 2 else a2.val % 2

/-! ### Stage payoffs -/

/-- Paiement sur deux périodes de l'incumbent *rationnel* : se battre coûte -/
def incRational (a1 a2 : Fin 4) : Int :=
  (if planR1 a1 = 1 then 0 else 2) +
  (if entryOf a1 a2 = 0 then 5
   else if planR2 a1 = 1 then 0 else 2)

/-- Paiement sur deux périodes de l'incumbent *dur* (engagement) : se battre -/
def incTough (a1 a2 : Fin 4) : Int :=
  (if planR1 a1 = 1 then 3 else 0) +
  (if entryOf a1 a2 = 0 then 5
   else if planR2 a1 = 1 then 3 else 0)

/-- Paiement de l'entrant en période 2 : 0 dehors, 2 s'il entre et -/
def entrantU (a1 a2 : Fin 4) : Int :=
  if entryOf a1 a2 = 0 then 0
  else if planR2 a1 = 1 then -3 else 2

/-! ### The two games -/

/-- Le jeu de réputation : l'entrant ne connaît pas le type de -/
def gRep : BayesGame2 where
  nT1 := 2
  nT2 := 1
  nA1 := 4
  nA2 := 4
  w := fun _ _ => 1
  u1 := fun t1 _ a1 a2 =>
    if t1.val = 0 then incRational a1 a2 else incTough a1 a2
  u2 := fun _ _ a1 a2 => entrantU a1 a2

/-- Le benchmark à information complète : l'incumbent est connu pour être -/
def gNoRep : BayesGame2 where
  nT1 := 1
  nT2 := 1
  nA1 := 4
  nA2 := 4
  w := fun _ _ => 1
  u1 := fun _ _ a1 a2 => incRational a1 a2
  u2 := fun _ _ a1 a2 => entrantU a1 a2

/-- Vérification : le benchmark est exactement le jeu de réputation -/
theorem gNoRep_restriction :
    ∀ a1 a2 : Fin 4,
      gNoRep.u1 ⟨0, by decide⟩ ⟨0, by decide⟩ a1 a2 =
        gRep.u1 ⟨0, by decide⟩ ⟨0, by decide⟩ a1 a2 ∧
      gNoRep.u2 ⟨0, by decide⟩ ⟨0, by decide⟩ a1 a2 =
        gRep.u2 ⟨0, by decide⟩ ⟨0, by decide⟩ a1 a2 := by
  decide

/-! ### Raffinement de crédibilité

Le BNE en forme normale admet des menaces non crédibles de période 2
(par exemple dans le benchmark, « le rationnel se bat en période 2 /
l'entrant reste dehors » est un profil de Nash qui paie l'incumbent 7
— mais la menace ne serait jamais exécutée). La rationalité
séquentielle en *dernière* période est une condition finie et
décidable sur les plans : la réponse de période 2 de chaque type doit
être une meilleure réponse de stade. -/

/-- Crédibilité dans le jeu de réputation : le type rationnel accommode -/
@[reducible] def credRep (s1 : Strategy1 gRep) : Prop :=
  planR2 (s1 ⟨0, by decide⟩) = 0 ∧ planR2 (s1 ⟨1, by decide⟩) = 1

/-- Crédibilité dans le benchmark : l'incumbent (rationnel) -/
@[reducible] def credNoRep (s1 : Strategy1 gNoRep) : Prop :=
  planR2 (s1 ⟨0, by decide⟩) = 0

/-! ### Canonical strategy constructors (reputation game) -/

/-- Stratégies de l'incumbent dans `gRep`, depuis les deux plans -/
def mkRepS1 (x y : Fin 4) : Strategy1 gRep :=
  fun t1 => if t1.val = 0 then x else y

/-- Les stratégies de l'entrant dans `gRep` sont constantes (un seul type). -/
def mkRepS2 (z : Fin 4) : Strategy2 gRep := fun _ => z

/-- Toute stratégie d'incumbent est déterminée par ses deux valeurs. -/
theorem repS1_eta (s1 : Strategy1 gRep) :
    s1 = mkRepS1 (s1 ⟨0, by decide⟩) (s1 ⟨1, by decide⟩) := by
  funext t1
  cases t1 using Fin.cases with
  | zero => rfl
  | succ j =>
    cases j using Fin.cases with
    | zero => rfl
    | succ j' => exact j'.elim0

/-- Toute stratégie d'entrant est une constante canonique. -/
theorem repS2_eta (s2 : Strategy2 gRep) :
    s2 = mkRepS2 (s2 ⟨0, by decide⟩) := by
  funext t2
  cases t2 using Fin.cases with
  | zero => rfl
  | succ j => exact j.elim0

/-! ### Analyse d'équilibre du jeu de réputation

Profil cible : le rationnel joue le plan 2 = (Fight, Accommodate), le
dur joue le plan 3 = (Fight, Fight), l'entrant joue le plan 1 = (Out
après Fight, In après Accommodate). -/

/-- Le profil de fusion est un BNE du jeu de réputation. -/
theorem gRep_bne :
    isBNE gRep (mkRepS1 ⟨2, by decide⟩ ⟨3, by decide⟩)
      (mkRepS2 ⟨1, by decide⟩) := by
  decide

/-- Le profil de fusion est crédible. -/
theorem gRep_bne_credible :
    credRep (mkRepS1 ⟨2, by decide⟩ ⟨3, by decide⟩) := by
  decide

/-- Sur les stratégies canoniques, le BNE crédible de `gRep` est unique : -/
theorem gRep_unique_aux :
    ∀ x y z : Fin 4,
      isBNE gRep (mkRepS1 x y) (mkRepS2 z) →
      credRep (mkRepS1 x y) →
        x = ⟨2, by decide⟩ ∧ y = ⟨3, by decide⟩ ∧ z = ⟨1, by decide⟩ := by
  decide

/-- Sur les stratégies canoniques, tout BNE crédible de `gRep` paie -/
theorem gRep_payoff_aux :
    ∀ x y z : Fin 4,
      isBNE gRep (mkRepS1 x y) (mkRepS2 z) →
      credRep (mkRepS1 x y) →
        interimU1 gRep ⟨0, by decide⟩ x (mkRepS2 z) = 5 := by
  decide

/-- Le jeu de réputation a un BNE crédible essentiellement unique. -/
theorem gRep_unique (s1 : Strategy1 gRep) (s2 : Strategy2 gRep)
    (h : isBNE gRep s1 s2) (hc : credRep s1) :
    s1 = mkRepS1 ⟨2, by decide⟩ ⟨3, by decide⟩ ∧
    s2 = mkRepS2 ⟨1, by decide⟩ := by
  rw [repS1_eta s1] at h hc
  rw [repS2_eta s2] at h
  have hu := gRep_unique_aux _ _ _ h hc
  exact ⟨by rw [repS1_eta s1, hu.1, hu.2.1],
         by rw [repS2_eta s2, hu.2.2]⟩

/-- Dans tout BNE crédible du jeu de réputation, l'incumbent rationnel
    gagne 5. -/
theorem gRep_credible_payoff (s1 : Strategy1 gRep) (s2 : Strategy2 gRep)
    (h : isBNE gRep s1 s2) (hc : credRep s1) :
    interimU1 gRep ⟨0, by decide⟩ (s1 ⟨0, by decide⟩) s2 = 5 := by
  rw [repS1_eta s1] at h hc
  rw [repS2_eta s2] at h ⊢
  exact gRep_payoff_aux _ _ _ h hc

/-- Dans tout BNE crédible du jeu de réputation le type *rationnel* se bat -/
theorem rational_fights_in_equilibrium
    (s1 : Strategy1 gRep) (s2 : Strategy2 gRep)
    (h : isBNE gRep s1 s2) (hc : credRep s1) :
    planR1 (s1 ⟨0, by decide⟩) = 1 := by
  rw [repS1_eta s1] at h hc
  rw [repS2_eta s2] at h
  have hu := gRep_unique_aux _ _ _ h hc
  rw [hu.1]
  decide

/-- Dans tout BNE crédible du jeu de réputation, l'entrée de période 2 est -/
theorem reputation_deters_entry
    (s1 : Strategy1 gRep) (s2 : Strategy2 gRep)
    (h : isBNE gRep s1 s2) (hc : credRep s1) :
    entryOf (s1 ⟨0, by decide⟩) (s2 ⟨0, by decide⟩) = 0 ∧
    entryOf (s1 ⟨1, by decide⟩) (s2 ⟨0, by decide⟩) = 0 := by
  rw [repS1_eta s1] at h hc
  rw [repS2_eta s2] at h
  have hu := gRep_unique_aux _ _ _ h hc
  rw [hu.1, hu.2.1, hu.2.2]
  decide

/-! ### Equilibrium analysis of the benchmark -/

/-- Les stratégies d'incumbent dans `gNoRep` sont constantes. -/
def mkNoS1 (x : Fin 4) : Strategy1 gNoRep := fun _ => x

/-- Les stratégies d'entrant dans `gNoRep` sont constantes. -/
def mkNoS2 (z : Fin 4) : Strategy2 gNoRep := fun _ => z

theorem noS1_eta (s1 : Strategy1 gNoRep) :
    s1 = mkNoS1 (s1 ⟨0, by decide⟩) := by
  funext t1
  cases t1 using Fin.cases with
  | zero => rfl
  | succ j => exact j.elim0

theorem noS2_eta (s2 : Strategy2 gNoRep) :
    s2 = mkNoS2 (s2 ⟨0, by decide⟩) := by
  funext t2
  cases t2 using Fin.cases with
  | zero => rfl
  | succ j => exact j.elim0

/-- (Accommodate, Accommodate) / (In, In) est un BNE crédible du benchmark. -/
theorem gNoRep_bne :
    isBNE gNoRep (mkNoS1 ⟨0, by decide⟩) (mkNoS2 ⟨3, by decide⟩) := by
  decide

/-- Sur les stratégies canoniques, le BNE crédible du benchmark est unique :
    un incumbent connu rationnel ne peut pas dissuader l'entrée. -/
theorem gNoRep_unique_aux :
    ∀ x z : Fin 4,
      isBNE gNoRep (mkNoS1 x) (mkNoS2 z) →
      credNoRep (mkNoS1 x) →
        x = ⟨0, by decide⟩ ∧ z = ⟨3, by decide⟩ := by
  decide

/-- Sur les stratégies canoniques, tout BNE crédible du benchmark paie
    l'incumbent exactement 4 (accommodation sur les deux périodes). -/
theorem gNoRep_payoff_aux :
    ∀ x z : Fin 4,
      isBNE gNoRep (mkNoS1 x) (mkNoS2 z) →
      credNoRep (mkNoS1 x) →
        interimU1 gNoRep ⟨0, by decide⟩ x (mkNoS2 z) = 4 := by
  decide

/-- Dans tout BNE crédible du benchmark, l'incumbent gagne 4. -/
theorem gNoRep_credible_payoff
    (s1 : Strategy1 gNoRep) (s2 : Strategy2 gNoRep)
    (h : isBNE gNoRep s1 s2) (hc : credNoRep s1) :
    interimU1 gNoRep ⟨0, by decide⟩ (s1 ⟨0, by decide⟩) s2 = 4 := by
  rw [noS1_eta s1] at h hc
  rw [noS2_eta s2] at h ⊢
  exact gNoRep_payoff_aux _ _ h hc

/-! ### Punchline -/

/-- **La réputation paie.** Dans tout équilibre crédible, l'incumbent -/
theorem reputation_pays
    (s1 : Strategy1 gRep) (s2 : Strategy2 gRep)
    (t1 : Strategy1 gNoRep) (t2 : Strategy2 gNoRep)
    (hR : isBNE gRep s1 s2) (hcR : credRep s1)
    (hN : isBNE gNoRep t1 t2) (hcN : credNoRep t1) :
    interimU1 gNoRep ⟨0, by decide⟩ (t1 ⟨0, by decide⟩) t2 <
      interimU1 gRep ⟨0, by decide⟩ (s1 ⟨0, by decide⟩) s2 := by
  rw [gRep_credible_payoff s1 s2 hR hcR,
      gNoRep_credible_payoff t1 t2 hN hcN]
  decide
