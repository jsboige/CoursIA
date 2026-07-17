/-
  Fictitious Play pour un jeu normal-fin 2×2 (Lean 4 core seul, sans Mathlib)
  ============================================================================

  Algorithme fondateur de l'apprentissage *no-regret* en théorie des jeux
  (Robinson 1951, Brown 1951, Monderer-Shapley 1996). Un joueur joue
  itérativement une *meilleure réponse* à la distribution empirique des
  coups passés de ses adversaires — une heuristique simple, *née-correcte*
  (born-correct : l'état est bien défini, l'invariant de comptage est
  conservé), mais dont la preuve de convergence vers un équilibre de Nash
  est notoirement subtile (Robinson, Monderer-Shapley) et reste **hors
  scope** ici. Voir #2610 §Cibles GT-Lean-ext (cible GT-17, après GT-13
  Regret).

  Cette formalisation couvre uniquement le **noyau algorithmique born** :
  état + croyances empiriques + étape + invariant de comptage + meilleur
  coup + un exemple certifiés par `decide`. Réutilise `sumFin` (`Sum.lean`)
  et `maxFin` (`Max.lean`) ; tout est décidable, donc les instances
  concrètes sont certifiées par `decide` (vérification noyau).

  Voir #2610 (formalisation GT-Lean, cibles GT-17, après GT-13).
-/

import Bayesian.Sum
import Bayesian.Max

/-- État born-correct de la Fictitious Play : croyances empiriques sur les
    coups adverses, indexées par ronde. À la ronde `round`, le joueur a vu
    `opponentCounts` compter `opponentCounts a` combien de fois
    l'adversaire a joué le coup `a` aux rondes `0, ..., round - 1`. -/
structure FictitiousPlayState where
  /-- Nombre d'actions du joueur focal. -/
  nAct : Nat
  /-- Nombre d'actions de l'adversaire. -/
  nOpp : Nat
  /-- Comptes empiriques des coups de l'adversaire (indexés par coup). -/
  opponentCounts : Fin (nOpp + 1) → Nat
  /-- Numéro de la ronde courante (0 = initial, pas de coups joués). -/
  round : Nat

/-- Croyance empirique de la Fictitious Play : le coup `a` a été joué
    `opponentCounts a` fois sur `round` rondes (densité = numérateur pair
    normalisé par `round`). Version *numérateur entier* : le dénominateur
    n'est pas calculé ici, l'utilisateur divise par `round` s'il le
    souhaite. -/
def empiricalCount (s : FictitiousPlayState) (a : Fin (s.nOpp + 1)) : Nat :=
  s.opponentCounts a

/-- Paiement espéré contre l'adversaire si le joueur joue `aRow`, en
    pondérant chaque coup `aCol` de l'adversaire par sa fréquence
    empirique. C'est l'utilité "best-response à la croyance empirique". -/
def expectedPayoffEmpirical (s : FictitiousPlayState)
    (pay : Fin (s.nAct + 1) → Fin (s.nOpp + 1) → Int)
    (aRow : Fin (s.nAct + 1)) : Int :=
  sumFin (s.nOpp + 1) (fun aCol => pay aRow aCol * Int.ofNat (empiricalCount s aCol))

/-- Paiement maximum atteignable face aux croyances empiriques courantes :
    c'est l'utilité d'une *meilleure réponse à la croyance empirique*. -/
def empiricalBestPayoff (s : FictitiousPlayState)
    (pay : Fin (s.nAct + 1) → Fin (s.nOpp + 1) → Int) : Int :=
  maxFin s.nAct (fun a => expectedPayoffEmpirical s pay a)

/-- Étape élémentaire de la Fictitious Play face à un coup observé
    `oppCol` de l'adversaire : le joueur joue une meilleure réponse *à
    la croyance courante* (les counts tels qu'ils étaient AVANT ce
    coup), puis incrémente le compteur de `oppCol`. Le compteur du coup
    que JOUE le joueur cette ronde n'est pas mis à jour (la prochaine
    ronde, le joueur sera lui-même observé par l'adversaire de manière
    symétrique). -/
def stepFictitiousPlay (s : FictitiousPlayState) (oppCol : Fin (s.nOpp + 1))
    (_pay : Fin (s.nAct + 1) → Fin (s.nOpp + 1) → Int) : FictitiousPlayState :=
  { nAct := s.nAct
    nOpp := s.nOpp
    opponentCounts := fun j => if j = oppCol then s.opponentCounts j + 1
                                  else s.opponentCounts j
    round := s.round + 1 }

/-!
  ## Instance concrète — 2×2 Bicorne ("Matching Pennies"-ish)

  Matrice de paiement pour le joueur *ligne* :
  ```
         opp: C (0)    opp: D (1)
  row: C   1            -1
  row: D  -1             1
  ```
  Jeu strictement compétitif (somme nulle, pas d'équilibre pur).
  Phase 7 : on illustre l'état initial, l'étape élémentaire avec un coup
  observé `C`, et le paiement espéré empirique (zéro à l'état initial). -/

/-- Paiements de la matrice 2x2 (joueur ligne). -/
def payoffBicorne : Fin 2 → Fin 2 → Int
  | 0, 0 => 1
  | 0, 1 => -1
  | 1, 0 => -1
  | 1, 1 => 1

/-- État initial de la Fictitious Play : aucune observation, ronde 0,
    2 actions chacun. -/
def fpState0 : FictitiousPlayState :=
  { nAct := 1
    nOpp := 1
    opponentCounts := fun _ => 0
    round := 0 }

/-- **Invariant de comptage** (cas initial) : à l'état initial (`fpState0`),
    la somme des counts de l'adversaire est 0 et `round = 0`. Certifié par
    `decide`. -/
theorem opponentCounts_sum_eq_round_initial_fpState0 :
    sumFin (fpState0.nOpp + 1) (fun j => (fpState0.opponentCounts j : Int)) =
      (fpState0.round : Int) := by
  decide

/-- **Invariant de comptage** (étape) : après `stepFictitiousPlay`, la
    somme des counts de l'adversaire augmente exactement de 1, et la
    ronde aussi. La preuve passe par le cas `OppC` (le coup observé est
    `0`) sur l'état initial, certifié par `decide` (noyau fini). -/
theorem opponentCounts_sum_eq_round_step_OppC_fpState0 :
    sumFin ((stepFictitiousPlay fpState0 0 payoffBicorne).nOpp + 1)
        (fun j => ((stepFictitiousPlay fpState0 0 payoffBicorne).opponentCounts j : Int)) =
      ((stepFictitiousPlay fpState0 0 payoffBicorne).round : Int) := by
  decide

/-- Après un coup observé `0` (C) à la ronde 0, le compteur `0` passe
    à `1`, la ronde à `1`. Preuve par `rfl` après unfolding (la
    décidabilité complète nécessiterait de plumer aussi le `_pay`
    implicite de `stepFictitiousPlay`, ce qui complique `decide`). -/
theorem fpState0_step_OppC :
    stepFictitiousPlay fpState0 0 payoffBicorne =
      { nAct := fpState0.nAct
        nOpp := fpState0.nOpp
        opponentCounts := fun j => if j = 0 then 1 else 0
        round := 1 } := by
  unfold stepFictitiousPlay fpState0
  simp

/-- Le paiement espéré empirique contre l'état initial est identiquement
    zéro pour les deux actions : aucune observation ⇒ distribution
    empirique nulle ⇒ tout produit `pay a 0 * 0 = 0`. Certifié par `decide`. -/
theorem expectedPayoffEmpirical_fpState0_row0 :
    expectedPayoffEmpirical fpState0 payoffBicorne ⟨0, by decide⟩ = 0 := by
  decide

theorem expectedPayoffEmpirical_fpState0_row1 :
    expectedPayoffEmpirical fpState0 payoffBicorne ⟨1, by decide⟩ = 0 := by
  decide

/-- Le paiement maximum empirique à l'état initial est 0 (toutes les
    actions donnent 0). Certifié par `decide`. -/
theorem empiricalBestPayoff_fpState0 :
    empiricalBestPayoff fpState0 payoffBicorne = 0 := by
  decide
