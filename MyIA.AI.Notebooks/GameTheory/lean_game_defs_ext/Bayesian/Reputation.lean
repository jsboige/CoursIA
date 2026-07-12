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

  ---
  English:
  Reputation and Entry Deterrence (chain-store, kernel-checked)
  =============================================================

  A reduced strategic form of the classic two-period entry-deterrence
  story (Kreps-Wilson / Milgrom-Roberts): an incumbent faces entry in
  period 1, responds Fight or Accommodate, and a second entrant decides
  whether to enter in period 2 *after observing* the period-1 response.

  The incumbent (player 1) is one of two types:
  - type 0, "rational": fighting costs in every period taken in
    isolation (stage payoffs: Fight 0 < Accommodate 2);
  - type 1, "tough" (commitment type): fighting is intrinsically
    preferred (Fight 3 > Accommodate 0).

  Equal prior weights (1, 1). Period-2 monopoly (entrant stays out)
  pays the incumbent 5.

  Action encodings (reduced plans, `Fin 4`, bit 0 = Accommodate/Out,
  bit 1 = Fight/In):
  - incumbent plan `a1`: `a1.val = 2*r1 + r2` where `r1` is the
    period-1 response and `r2` the period-2 response if entry occurs;
  - entrant plan `a2`: `a2.val = 2*eF + eA` where `eF` (resp. `eA`) is
    the period-2 entry decision after observing Fight (resp.
    Accommodate) in period 1.

  Because raw normal-form equilibrium also admits non-credible threats
  ("I will fight in period 2" by the rational type — never carried out
  if tested), we impose a decidable *credibility* refinement standing
  in for sequential rationality in the last period: each type's
  period-2 response must be a stage best reply (rational accommodates,
  tough fights).

  Results (all by `decide` + eta-expansion of strategies):
  - `gRep` (incomplete information, reputation possible) has a unique
    credible BNE: the rational type *pools* with the tough type and
    fights in period 1, the entrant stays out after a fight. The
    rational incumbent earns 5.
  - `gNoRep` (complete information benchmark: the incumbent is known
    rational) has a unique credible BNE: accommodate, entry occurs,
    payoff 4.
  - `reputation_pays`: 4 < 5 in every credible equilibrium pair — the
    incumbent's incentive to fight comes *only* from the entrant's
    uncertainty about its type, i.e. from reputation. The rational type
    fights in period 1 even though fighting is myopically dominated
    (`rational_fights_in_equilibrium`).

  See #2610 (GT-Lean formalization, Bayesian phase 5).
-/

import Bayesian.BNE

/-! ### Plan decoders -/

/-- Réponse de période 1 encodée dans un plan d'incumbent
    (0 = Accommodate, 1 = Fight).
    English: Period-1 response encoded in an incumbent plan
    (0 = Accommodate, 1 = Fight). -/
def planR1 (a : Fin 4) : Nat := a.val / 2

/-- Réponse de période 2 (si entrée) encodée dans un plan d'incumbent
    (0 = Accommodate, 1 = Fight).
    English: Period-2 response (if entry occurs) encoded in an incumbent plan
    (0 = Accommodate, 1 = Fight). -/
def planR2 (a : Fin 4) : Nat := a.val % 2

/-- Décision d'entrée de période 2 de l'entrant sur le chemin : la composante
    de son plan sélectionnée par la réponse observée de période 1
    (0 = Out, 1 = In).
    English: The entrant's period-2 entry decision on path: the component of
    its plan selected by the observed period-1 response
    (0 = Out, 1 = In). -/
def entryOf (a1 a2 : Fin 4) : Nat :=
  if planR1 a1 = 1 then a2.val / 2 else a2.val % 2

/-! ### Stage payoffs -/

/-- Paiement sur deux périodes de l'incumbent *rationnel* : se battre coûte
    English: Two-period payoff of the *rational* incumbent: fighting costs in
    period 1 (0 vs 2), monopoly pays 5, and the period-2 response is
    paid at stage values (Fight 0, Accommodate 2). -/
def incRational (a1 a2 : Fin 4) : Int :=
  (if planR1 a1 = 1 then 0 else 2) +
  (if entryOf a1 a2 = 0 then 5
   else if planR2 a1 = 1 then 0 else 2)

/-- Paiement sur deux périodes de l'incumbent *dur* (engagement) : se battre
    English: Two-period payoff of the *tough* (commitment) incumbent: fighting
    is intrinsically preferred (3 vs 0) in both periods. -/
def incTough (a1 a2 : Fin 4) : Int :=
  (if planR1 a1 = 1 then 3 else 0) +
  (if entryOf a1 a2 = 0 then 5
   else if planR2 a1 = 1 then 3 else 0)

/-- Paiement de l'entrant en période 2 : 0 dehors, 2 s'il entre et
    English: Period-2 entrant's payoff: 0 out, 2 if it enters and the incumbent
    accommodates, -3 if it enters and the incumbent fights. -/
def entrantU (a1 a2 : Fin 4) : Int :=
  if entryOf a1 a2 = 0 then 0
  else if planR2 a1 = 1 then -3 else 2

/-! ### The two games -/

/-- Le jeu de réputation : l'entrant ne connaît pas le type de
    English: The reputation game: the entrant does not know the incumbent's
    type (rational or tough, equal weights). -/
def gRep : BayesGame2 where
  nT1 := 2
  nT2 := 1
  nA1 := 4
  nA2 := 4
  w := fun _ _ => 1
  u1 := fun t1 _ a1 a2 =>
    if t1.val = 0 then incRational a1 a2 else incTough a1 a2
  u2 := fun _ _ a1 a2 => entrantU a1 a2

/-- Le benchmark à information complète : l'incumbent est connu pour être
    English: The complete-information benchmark: the incumbent is known to be
    rational (a single type). Same actions, same payoff tables. -/
def gNoRep : BayesGame2 where
  nT1 := 1
  nT2 := 1
  nA1 := 4
  nA2 := 4
  w := fun _ _ => 1
  u1 := fun _ _ a1 a2 => incRational a1 a2
  u2 := fun _ _ a1 a2 => entrantU a1 a2

/-- Vérification : le benchmark est exactement le jeu de réputation
    English: Sanity check: the benchmark is exactly the reputation game
    restricted to the rational type — not an unrelated game. -/
theorem gNoRep_restriction :
    ∀ a1 a2 : Fin 4,
      gNoRep.u1 ⟨0, by decide⟩ ⟨0, by decide⟩ a1 a2 =
        gRep.u1 ⟨0, by decide⟩ ⟨0, by decide⟩ a1 a2 ∧
      gNoRep.u2 ⟨0, by decide⟩ ⟨0, by decide⟩ a1 a2 =
        gRep.u2 ⟨0, by decide⟩ ⟨0, by decide⟩ a1 a2 := by
  decide

/-! ### Credibility refinement

Normal-form BNE admits non-credible period-2 threats (e.g. in the
benchmark, "rational fights period 2 / entrant stays out" is a Nash
profile paying the incumbent 7 — but the threat would never be carried
out). Sequential rationality in the *last* period is a finite,
decidable condition on plans: each type's period-2 response must be a
stage best reply. -/

/-- Crédibilité dans le jeu de réputation : le type rationnel accommode
    English: Credibility in the reputation game: the rational type accommodates
    in period 2 (2 > 0), the tough type fights (3 > 0). -/
@[reducible] def credRep (s1 : Strategy1 gRep) : Prop :=
  planR2 (s1 ⟨0, by decide⟩) = 0 ∧ planR2 (s1 ⟨1, by decide⟩) = 1

/-- Crédibilité dans le benchmark : l'incumbent (rationnel)
    English: Credibility in the benchmark: the (rational) incumbent
    accommodates in period 2. -/
@[reducible] def credNoRep (s1 : Strategy1 gNoRep) : Prop :=
  planR2 (s1 ⟨0, by decide⟩) = 0

/-! ### Canonical strategy constructors (reputation game) -/

/-- Stratégies de l'incumbent dans `gRep`, depuis les deux plans
    English: Incumbent strategies in `gRep`, from the two type-contingent
    plans. -/
def mkRepS1 (x y : Fin 4) : Strategy1 gRep :=
  fun t1 => if t1.val = 0 then x else y

/-- Les stratégies de l'entrant dans `gRep` sont constantes (un seul type).
    English: Entrant strategies in `gRep` are constants (one type). -/
def mkRepS2 (z : Fin 4) : Strategy2 gRep := fun _ => z

/-- Toute stratégie d'incumbent est déterminée par ses deux valeurs.
    English: Every incumbent strategy is determined by its two values. -/
theorem repS1_eta (s1 : Strategy1 gRep) :
    s1 = mkRepS1 (s1 ⟨0, by decide⟩) (s1 ⟨1, by decide⟩) := by
  funext t1
  cases t1 using Fin.cases with
  | zero => rfl
  | succ j =>
    cases j using Fin.cases with
    | zero => rfl
    | succ j' => exact j'.elim0

/-- Toute stratégie d'entrant est une constante canonique.
    English: Every entrant strategy is a canonical constant. -/
theorem repS2_eta (s2 : Strategy2 gRep) :
    s2 = mkRepS2 (s2 ⟨0, by decide⟩) := by
  funext t2
  cases t2 using Fin.cases with
  | zero => rfl
  | succ j => exact j.elim0

/-! ### Equilibrium analysis of the reputation game

Target profile: rational plays plan 2 = (Fight, Accommodate), tough
plays plan 3 = (Fight, Fight), entrant plays plan 1 = (Out after
Fight, In after Accommodate). -/

/-- Le profil de fusion est un BNE du jeu de réputation.
    English: The pooling profile is a BNE of the reputation game. -/
theorem gRep_bne :
    isBNE gRep (mkRepS1 ⟨2, by decide⟩ ⟨3, by decide⟩)
      (mkRepS2 ⟨1, by decide⟩) := by
  decide

/-- Le profil de fusion est crédible.
    English: The pooling profile is credible. -/
theorem gRep_bne_credible :
    credRep (mkRepS1 ⟨2, by decide⟩ ⟨3, by decide⟩) := by
  decide

/-- Sur les stratégies canoniques, le BNE crédible de `gRep` est unique :
    English: Over canonical strategies, the credible BNE of `gRep` is unique:
    both incumbent types fight in period 1 (the rational type pools),
    and the entrant enters iff it observed Accommodate. -/
theorem gRep_unique_aux :
    ∀ x y z : Fin 4,
      isBNE gRep (mkRepS1 x y) (mkRepS2 z) →
      credRep (mkRepS1 x y) →
        x = ⟨2, by decide⟩ ∧ y = ⟨3, by decide⟩ ∧ z = ⟨1, by decide⟩ := by
  decide

/-- Sur les stratégies canoniques, tout BNE crédible de `gRep` paie
    English: Over canonical strategies, every credible BNE of `gRep` pays the
    rational incumbent exactly 5 (deterrence: 0 in period 1, monopoly
    5 in period 2). -/
theorem gRep_payoff_aux :
    ∀ x y z : Fin 4,
      isBNE gRep (mkRepS1 x y) (mkRepS2 z) →
      credRep (mkRepS1 x y) →
        interimU1 gRep ⟨0, by decide⟩ x (mkRepS2 z) = 5 := by
  decide

/-- Le jeu de réputation a un BNE crédible essentiellement unique.
    English: The reputation game has an essentially unique credible BNE. -/
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
    gagne 5.
    English: In every credible BNE of the reputation game, the rational
    incumbent earns 5. -/
theorem gRep_credible_payoff (s1 : Strategy1 gRep) (s2 : Strategy2 gRep)
    (h : isBNE gRep s1 s2) (hc : credRep s1) :
    interimU1 gRep ⟨0, by decide⟩ (s1 ⟨0, by decide⟩) s2 = 5 := by
  rw [repS1_eta s1] at h hc
  rw [repS2_eta s2] at h ⊢
  exact gRep_payoff_aux _ _ _ h hc

/-- Dans tout BNE crédible du jeu de réputation le type *rationnel* se bat
    English: In every credible BNE of the reputation game the *rational* type
    fights in period 1, even though fighting is myopically dominated
    (stage value 0 < 2): the pooling/signaling motive. -/
theorem rational_fights_in_equilibrium
    (s1 : Strategy1 gRep) (s2 : Strategy2 gRep)
    (h : isBNE gRep s1 s2) (hc : credRep s1) :
    planR1 (s1 ⟨0, by decide⟩) = 1 := by
  rw [repS1_eta s1] at h hc
  rw [repS2_eta s2] at h
  have hu := gRep_unique_aux _ _ _ h hc
  rw [hu.1]
  decide

/-- Dans tout BNE crédible du jeu de réputation, l'entrée de période 2 est
    English: In every credible BNE of the reputation game, period-2 entry is
    deterred against both types: the entrant observes Fight on path
    and stays out. -/
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

/-- Les stratégies d'incumbent dans `gNoRep` sont constantes.
    English: Incumbent strategies in `gNoRep` are constants. -/
def mkNoS1 (x : Fin 4) : Strategy1 gNoRep := fun _ => x

/-- Les stratégies d'entrant dans `gNoRep` sont constantes.
    English: Entrant strategies in `gNoRep` are constants. -/
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

/-- (Accommodate, Accommodate) / (In, In) est un BNE crédible du benchmark.
    English: (Accommodate, Accommodate) / (In, In) is a credible BNE of the
    benchmark. -/
theorem gNoRep_bne :
    isBNE gNoRep (mkNoS1 ⟨0, by decide⟩) (mkNoS2 ⟨3, by decide⟩) := by
  decide

/-- Sur les stratégies canoniques, le BNE crédible du benchmark est unique :
    un incumbent connu rationnel ne peut pas dissuader l'entrée.
    English: Over canonical strategies, the credible BNE of the benchmark is
    unique: a known-rational incumbent cannot deter entry. -/
theorem gNoRep_unique_aux :
    ∀ x z : Fin 4,
      isBNE gNoRep (mkNoS1 x) (mkNoS2 z) →
      credNoRep (mkNoS1 x) →
        x = ⟨0, by decide⟩ ∧ z = ⟨3, by decide⟩ := by
  decide

/-- Sur les stratégies canoniques, tout BNE crédible du benchmark paie
    l'incumbent exactement 4 (accommodation sur les deux périodes).
    English: Over canonical strategies, every credible BNE of the benchmark
    pays the incumbent exactly 4 (accommodation in both periods). -/
theorem gNoRep_payoff_aux :
    ∀ x z : Fin 4,
      isBNE gNoRep (mkNoS1 x) (mkNoS2 z) →
      credNoRep (mkNoS1 x) →
        interimU1 gNoRep ⟨0, by decide⟩ x (mkNoS2 z) = 4 := by
  decide

/-- Dans tout BNE crédible du benchmark, l'incumbent gagne 4.
    English: In every credible BNE of the benchmark, the incumbent earns 4. -/
theorem gNoRep_credible_payoff
    (s1 : Strategy1 gNoRep) (s2 : Strategy2 gNoRep)
    (h : isBNE gNoRep s1 s2) (hc : credNoRep s1) :
    interimU1 gNoRep ⟨0, by decide⟩ (s1 ⟨0, by decide⟩) s2 = 4 := by
  rw [noS1_eta s1] at h hc
  rw [noS2_eta s2] at h ⊢
  exact gNoRep_payoff_aux _ _ h hc

/-! ### Punchline -/

/-- **La réputation paie.** Dans tout équilibre crédible, l'incumbent
    English: **Reputation pays.** In every credible equilibrium, the rational
    incumbent earns strictly more under incomplete information (5,
    entry deterred by pooling with the tough type) than under complete
    information (4, entry occurs and is accommodated). The value of
    reputation is exactly the entrant's uncertainty about the
    incumbent's type: with the type known, the same incumbent with the
    same payoffs cannot deter anything. -/
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
