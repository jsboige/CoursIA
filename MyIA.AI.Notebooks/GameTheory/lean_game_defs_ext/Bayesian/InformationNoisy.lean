/-
  Valeur de l'information pour un signal bruite (tables jointes finies)
  =====================================================================

  `Information.lean` traite les signaux *deterministes* : un signal y est
  une application des etats vers les realisations, donc une partition de
  l'espace d'etats. Un signal **bruite** ne partitionne pas : plusieurs
  etats peuvent produire la meme realisation, et une realisation peut
  rester compatible avec plusieurs etats. Il faut alors une table jointe.

  Representation retenue : une table de poids joints **naturels**
  `p : Fin nS → Fin (nX + 1) → Nat` (etat × realisation), avec des
  paiements entiers. C'est la voie exacte annoncee par #22374 : elle
  evite toute division conditionnelle.

  Hypotheses, ecrites ici parce qu'elles portent la comparaison :

  - `p s x` est un **poids**, pas une probabilite : la masse totale
    `Σ_(s,x) p s x` n'est pas normalisee a 1. Le facteur de normalisation
    est strictement positif des que la table n'est pas nulle. Toutes les
    valeurs definies ci-dessous sont brutes, a l'echelle de cette masse ;
    deux tables proportionnelles decrivent le meme probleme et donnent des
    valeurs dans le meme rapport.
  - le prior du decideur est le **marginal** de la table, `priorMass s` :
    on ne transporte pas un prior separe, qui pourrait contredire la table
    et faire diverger les deux semantiques.
  - une realisation de masse nulle n'est pas une erreur : ses
    contributions valent zero par construction (aucune division n'est
    prise), donc un signal impossible ne fabrique ni `NaN` ni exception.

  Ce qui est prouve dans ce module (premiere tranche de #22374) :
  `valueNoisyNoInfo_le_valueNoisySignal` — la valeur brute d'un decideur
  qui observe le signal domine celle d'un decideur non informe, avec les
  memes poids joints. La preuve est le lemme maitre `maxFin_sumFin_le`
  applique aux realisations du signal, plus la commutation des sommes.

  Ce qui reste a faire dans les tranches suivantes, et n'est **pas**
  affirme ici : dominance de l'information parfaite (`valueNoisyPerfect`),
  cas independant a EVSI nulle, pont vers `Signal` deterministe, adaptateur
  exact vers les instances JSON du banc `voi`.

  Voir #22374 (extension de la phase bayesienne 4 de #2610).
-/

import Bayesian.Information

/-- Probleme de decision fini a un decideur, avec un signal bruite decrit
    par une table de poids joints etat × realisation. Les paiements sont
    entiers et les poids naturels : les valeurs sont exactes, sans
    division. -/
structure NoisyProblem where
  /-- Nombre d'etats du monde. -/
  nS : Nat
  /-- Nombre d'actions moins un (les actions sont `Fin (nA + 1)`). -/
  nA : Nat
  /-- Nombre de realisations du signal moins une. -/
  nX : Nat
  /-- Poids joint non normalise de l'etat `s` et de la realisation `x`. -/
  p : Fin nS → Fin (nX + 1) → Nat
  /-- Paiement entier de l'action `a` dans l'etat `s`. -/
  u : Fin nS → Fin (nA + 1) → Int

/-- Masse jointe (non normalisee) d'une realisation du signal. -/
def signalMass (D : NoisyProblem) (x : Fin (D.nX + 1)) : Int :=
  sumFin D.nS (fun s => (D.p s x : Int))

/-- Poids marginal de l'etat `s` induit par la table jointe : c'est le
    prior effectivement employe par le decideur. -/
def priorMass (D : NoisyProblem) (s : Fin D.nS) : Int :=
  sumFin (D.nX + 1) (fun x => (D.p s x : Int))

/-- Paiement joint de l'action `a` dans l'etat `s` et la realisation `x` :
    le poids de la cellule fois le paiement. -/
def jointPayoff (D : NoisyProblem) (s : Fin D.nS) (x : Fin (D.nX + 1))
    (a : Fin (D.nA + 1)) : Int :=
  (D.p s x : Int) * D.u s a

/-- Valeur brute du decideur non informe : une seule action, choisie sur le
    prior marginal de la table jointe. -/
def valueNoisyNoInfo (D : NoisyProblem) : Int :=
  maxFin D.nA (fun a => sumFin D.nS (fun s => priorMass D s * D.u s a))

/-- Valeur brute du decideur qui observe la realisation du signal : il
    choisit une action par realisation, sur les poids de la cellule. -/
def valueNoisySignal (D : NoisyProblem) : Int :=
  sumFin (D.nX + 1) (fun x => maxFin D.nA (fun a =>
    sumFin D.nS (fun s => jointPayoff D s x a)))

/-- Le paiement d'une action, agrege sur les realisations, est exactement le
    paiement pondere par le prior marginal : la table jointe et le prior ne
    sont qu'une seule donnee. -/
theorem sumFin_jointPayoff (D : NoisyProblem) (s : Fin D.nS)
    (a : Fin (D.nA + 1)) :
    sumFin (D.nX + 1) (fun x => jointPayoff D s x a) =
    priorMass D s * D.u s a := by
  unfold jointPayoff priorMass
  rw [sumFin_congr (fun x => Int.mul_comm (D.p s x : Int) (D.u s a)),
    sumFin_mul_left, Int.mul_comm]

/-- **La valeur brute d'un signal bruite domine celle du decideur non
    informe.** Les deux valeurs sont a l'echelle de la masse de la table :
    l'inegalite porte sur les valeurs brutes, pas sur une EVSI normalisee. -/
theorem valueNoisyNoInfo_le_valueNoisySignal (D : NoisyProblem) :
    valueNoisyNoInfo D ≤ valueNoisySignal D := by
  unfold valueNoisyNoInfo valueNoisySignal
  have hswap : ∀ a : Fin (D.nA + 1),
      sumFin D.nS (fun s => priorMass D s * D.u s a) =
      sumFin (D.nX + 1) (fun x => sumFin D.nS (fun s => jointPayoff D s x a)) := by
    intro a
    calc sumFin D.nS (fun s => priorMass D s * D.u s a)
        = sumFin D.nS (fun s => sumFin (D.nX + 1)
            (fun x => jointPayoff D s x a)) :=
          sumFin_congr (fun s => (sumFin_jointPayoff D s a).symm)
      _ = sumFin (D.nX + 1) (fun x => sumFin D.nS
            (fun s => jointPayoff D s x a)) := sumFin_comm _
  calc maxFin D.nA (fun a => sumFin D.nS (fun s => priorMass D s * D.u s a))
      = maxFin D.nA (fun a => sumFin (D.nX + 1) (fun x => sumFin D.nS
            (fun s => jointPayoff D s x a))) := by
        exact congrArg (maxFin D.nA) (funext hswap)
    _ ≤ sumFin (D.nX + 1) (fun x => maxFin D.nA (fun a => sumFin D.nS
            (fun s => jointPayoff D s x a))) :=
        maxFin_sumFin_le (fun x a => sumFin D.nS (fun s => jointPayoff D s x a))

/-
  Verification concrete : le parapluie de `Information.lean`, cette fois
  avec une prevision **bruitee**. Deux etats (pluie, soleil), deux actions
  (parapluie, le laisser), deux bulletins (annonce pluie, annonce soleil).
  La prevision est bonne mais imparfaite : poids joints (3, 1) puis (1, 3),
  pour un prior marginal de 4 dans chaque etat.
-/

/-- Parapluie avec une prevision bruitee : le bulletin est correct avec un
    poids de 3 contre 1 pour l'erreur. -/
def noisyUmbrella : NoisyProblem where
  nS := 2
  nA := 1
  nX := 1
  p := fun s x => if s.val = x.val then 3 else 1
  u := fun s a =>
    if s.val = 0 then (if a.val = 0 then 2 else -3)
    else (if a.val = 0 then 0 else 3)

/-- Non informe, le decideur prend toujours le parapluie : valeur brute 8,
    soit 2 par etat pour un poids marginal de 4. -/
theorem noisyUmbrella_valueNoisyNoInfo :
    valueNoisyNoInfo noisyUmbrella = 8 := by decide

/-- Informe, il suit le bulletin : 6 + 6, soit 12. La valeur brute du
    signal depasse donc strictement celle du non informe. -/
theorem noisyUmbrella_valueNoisySignal :
    valueNoisySignal noisyUmbrella = 12 := by decide

/-- Le gain brut du signal est strictement positif sur cet exemple : la
    borne de `valueNoisyNoInfo_le_valueNoisySignal` est atteinte de facon
    stricte, elle n'est pas un artefact de la representation. -/
theorem noisyUmbrella_strict_gain :
    valueNoisyNoInfo noisyUmbrella < valueNoisySignal noisyUmbrella := by
  decide
