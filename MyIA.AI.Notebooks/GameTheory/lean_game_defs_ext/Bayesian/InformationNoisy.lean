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

  Ce qui est prouve dans ce module (deux tranches de #22374) :

  - `valueNoisyNoInfo_le_valueNoisySignal` — la valeur brute d'un decideur
    qui observe le signal domine celle d'un decideur non informe, avec les
    memes poids joints (lemme maitre `maxFin_sumFin_le` applique aux
    realisations du signal, plus la commutation des sommes) ;
  - `valueNoisySignal_le_valueNoisyPerfect` — l'information parfaite domine
    tout signal bruite, meme en valeurs brutes non normalisees (lemme
    maitre `sumFin_maxFin_mul_le`, forme algebrique de Blackwell, cas de
    masse nulle traite a part) ;
  - une realisation de masse nulle contribue **exactement** zero, par
    theoreme (`valueNoisySignal_zero_mass_cell`) et non par absence de
    division ;
  - `valueNoisyNoInfo_nonneg`, `valueNoisySignal_nonneg`,
    `valueNoisyPerfect_nonneg` — les trois valeurs sont non negatives
    **sous l'hypothese** `NonnegPayouts`. L'hypothese est necessaire :
    `NoisyProblem` ne contraint pas le signe de `u`, et une instance bien
    formee de valeur strictement negative existe (voir la section « Signe
    des valeurs »).

  Ce qui reste a faire dans les tranches suivantes, et n'est **pas**
  affirme ici : cas independant a EVSI nulle, pont vers `Signal`
  deterministe, adaptateur exact vers les instances JSON du banc `voi`,
  carnet compagnon reexecute.

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

/-- Valeur brute de l'information parfaite : l'etat est revele, le decideur
    choisit une action par etat sur le prior marginal de la table jointe. -/
def valueNoisyPerfect (D : NoisyProblem) : Int :=
  sumFin D.nS (fun s => maxFin D.nA (fun a => priorMass D s * D.u s a))

/-! ## Signaux de masse nulle

Une realisation de masse nulle est un signal impossible. La representation
etant exacte (aucune division conditionnelle), elle ne peut pas fabriquer de
division par zero : ce qui reste a prouver est que sa contribution est
exactement nulle, et non « presque nulle » par arrondi. -/

/-- Une somme de termes non negatifs est non negative. -/
theorem sumFin_nonneg {n : Nat} {f : Fin n → Int} (h : ∀ i, 0 ≤ f i) :
    0 ≤ sumFin n f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sumFin_succ]
    have h0 := h 0
    have ht := ih (f := fun i => f i.succ) (fun i => h i.succ)
    omega

/-- Si une somme de termes non negatifs est nulle, chaque terme est nul :
    c'est ce qui rend la masse nulle d'une realisation transmissible a ses
    cellules. -/
theorem eq_zero_of_sumFin_nonneg {n : Nat} {f : Fin n → Int}
    (h : ∀ i, 0 ≤ f i) (hsum : sumFin n f = 0) : ∀ i, f i = 0 := by
  induction n with
  | zero => intro i; exact i.elim0
  | succ n ih =>
    intro i
    rw [sumFin_succ] at hsum
    have ht := sumFin_nonneg (f := fun j => f j.succ) (fun j => h j.succ)
    have h0nn := h 0
    have h0 : f 0 = 0 := by omega
    cases i using Fin.cases with
    | zero => exact h0
    | succ j =>
      exact ih (f := fun j => f j.succ) (fun j => h j.succ) (by omega) j

/-- Une realisation de masse nulle a tous ses poids joints nuls. -/
theorem p_eq_zero_of_signalMass_zero (D : NoisyProblem) (x : Fin (D.nX + 1))
    (h : signalMass D x = 0) (s : Fin D.nS) : D.p s x = 0 := by
  unfold signalMass at h
  have hz : (D.p s x : Int) = 0 :=
    eq_zero_of_sumFin_nonneg (f := fun s => (D.p s x : Int))
      (fun s => by omega) h s
  omega

/-- Le paiement agrege d'une action sur une realisation de masse nulle est
    exactement nul : un signal impossible ne fabrique aucune valeur. -/
theorem jointPayoff_zero_mass (D : NoisyProblem) (x : Fin (D.nX + 1))
    (h : signalMass D x = 0) (a : Fin (D.nA + 1)) :
    sumFin D.nS (fun s => jointPayoff D s x a) = 0 := by
  have hp := p_eq_zero_of_signalMass_zero D x h
  have hz : (fun s => jointPayoff D s x a) = (fun _ => (0 : Int)) := by
    funext s
    simp [jointPayoff, hp s]
  rw [hz]
  exact sumFin_zero_fun D.nS

/-- La meilleure action sur une realisation de masse nulle vaut zero, sans
    division et sans exception. -/
theorem valueNoisySignal_zero_mass_cell (D : NoisyProblem)
    (x : Fin (D.nX + 1)) (h : signalMass D x = 0) :
    maxFin D.nA (fun a => sumFin D.nS (fun s => jointPayoff D s x a)) = 0 := by
  have hfun : (fun a => sumFin D.nS (fun s => jointPayoff D s x a)) =
      (fun _ => (0 : Int)) :=
    funext (fun a => jointPayoff_zero_mass D x h a)
  rw [hfun, maxFin_zero_fun]

/-! ## L'information parfaite domine tout signal bruite

L'etape decisive est un lemme de factorisation : pour des poids non negatifs,
la somme des maxima par realisation est au plus le maximum de la somme. C'est
la forme algebrique de l'argument de Blackwell — un decideur qui connait
l'etat peut toujours appliquer la politique que le signal lui aurait
prescrite, donc l'information parfaite ne peut pas valoir moins. -/

/-- **Factorisation par etat.** Pour des poids non negatifs `w` et des
    paiements `v`, `Σ_x max_a (w x * v a) ≤ max_a ((Σ_x w x) * v a)`.

    C'est l'etape qui fait passer de « une action par realisation » a « une
    action par etat ». Le cas `Σ w = 0` se traite a part (tous les poids
    sont nuls, les deux membres valent zero) ; sinon l'indice atteignant le
    maximum de la somme domine tous les paiements, et la positivite de la
    masse permet de simplifier. -/
theorem sumFin_maxFin_mul_le {m n : Nat} (w : Fin m → Int)
    (hw : ∀ x, 0 ≤ w x) (v : Fin (n + 1) → Int) :
    sumFin m (fun x => maxFin n (fun a => w x * v a)) ≤
    maxFin n (fun a => sumFin m w * v a) := by
  by_cases hzero : sumFin m w = 0
  · have hw0 : ∀ x, w x = 0 := eq_zero_of_sumFin_nonneg hw hzero
    have hL : sumFin m (fun x => maxFin n (fun a => w x * v a)) = 0 := by
      have hz : ∀ x : Fin m, maxFin n (fun a => w x * v a) = 0 := by
        intro x
        have hfun : (fun a => w x * v a) = (fun _ => (0 : Int)) := by
          funext a
          simp [hw0 x]
        rw [hfun, maxFin_zero_fun]
      rw [sumFin_congr hz, sumFin_zero_fun]
    have hR : maxFin n (fun a => sumFin m w * v a) = 0 := by
      have hfun : (fun a => sumFin m w * v a) = (fun _ => (0 : Int)) := by
        funext a
        simp [hzero]
      rw [hfun, maxFin_zero_fun]
    rw [hL, hR]
    omega
  · have hpos : 0 < sumFin m w := by
      have := sumFin_nonneg hw
      omega
    have hstar : ∀ a : Fin (n + 1), v a ≤ v (argmaxFin n (fun a => sumFin m w * v a)) := by
      intro a
      exact Int.le_of_mul_le_mul_left (le_argmaxFin (fun a => sumFin m w * v a) a) hpos
    have hbound : ∀ x : Fin m,
        maxFin n (fun a => w x * v a) ≤ w x * v (argmaxFin n (fun a => sumFin m w * v a)) := by
      intro x
      apply maxFin_le
      intro a
      exact Int.mul_le_mul_of_nonneg_left (hstar a) (hw x)
    calc sumFin m (fun x => maxFin n (fun a => w x * v a))
        ≤ sumFin m (fun x => w x * v (argmaxFin n (fun a => sumFin m w * v a))) :=
          sumFin_mono hbound
      _ = sumFin m w * v (argmaxFin n (fun a => sumFin m w * v a)) := by
          rw [sumFin_congr (fun x =>
                Int.mul_comm (w x) (v (argmaxFin n (fun a => sumFin m w * v a)))),
              sumFin_mul_left, Int.mul_comm]
      _ ≤ maxFin n (fun a => sumFin m w * v a) :=
          le_maxFin (fun a => sumFin m w * v a) _

/-- **L'information parfaite domine tout signal bruite.** Meme dans la
    representation jointe non normalisee, ou les valeurs sont brutes. -/
theorem valueNoisySignal_le_valueNoisyPerfect (D : NoisyProblem) :
    valueNoisySignal D ≤ valueNoisyPerfect D := by
  unfold valueNoisySignal valueNoisyPerfect
  have hstep : sumFin (D.nX + 1) (fun x => maxFin D.nA (fun a =>
        sumFin D.nS (fun s => jointPayoff D s x a))) ≤
      sumFin (D.nX + 1) (fun x => sumFin D.nS (fun s =>
        maxFin D.nA (fun a => jointPayoff D s x a))) :=
    sumFin_mono (fun x => maxFin_sumFin_le (fun s a => jointPayoff D s x a))
  have hcomm : sumFin (D.nX + 1) (fun x => sumFin D.nS (fun s =>
        maxFin D.nA (fun a => jointPayoff D s x a))) =
      sumFin D.nS (fun s => sumFin (D.nX + 1) (fun x =>
        maxFin D.nA (fun a => jointPayoff D s x a))) :=
    sumFin_comm _
  have hper : sumFin D.nS (fun s => sumFin (D.nX + 1) (fun x =>
        maxFin D.nA (fun a => jointPayoff D s x a))) ≤
      sumFin D.nS (fun s => maxFin D.nA (fun a => priorMass D s * D.u s a)) := by
    apply sumFin_mono
    intro s
    have hw : ∀ x : Fin (D.nX + 1), 0 ≤ (D.p s x : Int) := fun x => by omega
    have := sumFin_maxFin_mul_le (m := D.nX + 1) (n := D.nA)
      (w := fun x => (D.p s x : Int)) hw (v := fun a => D.u s a)
    simpa [jointPayoff, priorMass] using this
  rw [hcomm] at hstep
  exact Int.le_trans hstep hper

/-! ## Signe des valeurs : ce qui le porte, et ce qui ne le porte pas

Les trois valeurs de ce module sont **brutes**, et rien dans `NoisyProblem`
ne contraint le signe des paiements `u : Fin nS → Fin (nA + 1) → Int`. Une
instance bien formee peut donc valoir strictement moins que zero : avec
`nS = 1`, `nA = 1`, `nX = 1`, `p ≡ 1`, `u ≡ -1`, on a `priorMass = 1`,
chaque realisation a une masse de 1, la meilleure action vaut -1 dans
chaque etat, et `valueNoisySignal = -2`.

La non-negativite n'est donc **pas** une propriete du type : c'est une
propriete sous hypothese. Elle est enoncee et prouvee ici, plutot que
laissee implicite dans une docstring. -/

/-- Les paiements sont non negatifs partout : l'hypothese qui porte le
    signe des valeurs du module. -/
def NonnegPayouts (D : NoisyProblem) : Prop :=
  ∀ (s : Fin D.nS) (a : Fin (D.nA + 1)), 0 ≤ D.u s a

/-- Un poids marginal est non negatif : c'est une somme de poids naturels. -/
theorem priorMass_nonneg (D : NoisyProblem) (s : Fin D.nS) :
    0 ≤ priorMass D s := by
  unfold priorMass
  exact sumFin_nonneg (fun x => Int.natCast_nonneg (D.p s x))

/-- Un paiement joint est non negatif des que les paiements le sont. -/
theorem jointPayoff_nonneg (D : NoisyProblem) (h : NonnegPayouts D)
    (s : Fin D.nS) (x : Fin (D.nX + 1)) (a : Fin (D.nA + 1)) :
    0 ≤ jointPayoff D s x a := by
  unfold jointPayoff
  exact Int.mul_nonneg (Int.natCast_nonneg (D.p s x)) (h s a)

/-- **La valeur du decideur non informe est non negative** sous paiements
    non negatifs. -/
theorem valueNoisyNoInfo_nonneg (D : NoisyProblem) (h : NonnegPayouts D) :
    0 ≤ valueNoisyNoInfo D := by
  unfold valueNoisyNoInfo
  refine Int.le_trans ?_ (le_maxFin (fun a =>
    sumFin D.nS (fun s => priorMass D s * D.u s a)) 0)
  exact sumFin_nonneg (fun s => Int.mul_nonneg (priorMass_nonneg D s) (h s 0))

/-- **La valeur brute d'un signal bruite est non negative** sous paiements
    non negatifs. -/
theorem valueNoisySignal_nonneg (D : NoisyProblem) (h : NonnegPayouts D) :
    0 ≤ valueNoisySignal D := by
  unfold valueNoisySignal
  apply sumFin_nonneg
  intro x
  refine Int.le_trans ?_ (le_maxFin (fun a =>
    sumFin D.nS (fun s => jointPayoff D s x a)) 0)
  exact sumFin_nonneg (fun s => jointPayoff_nonneg D h s x 0)

/-- **La valeur de l'information parfaite est non negative** sous paiements
    non negatifs. -/
theorem valueNoisyPerfect_nonneg (D : NoisyProblem) (h : NonnegPayouts D) :
    0 ≤ valueNoisyPerfect D := by
  unfold valueNoisyPerfect
  apply sumFin_nonneg
  intro s
  refine Int.le_trans ?_ (le_maxFin (fun a => priorMass D s * D.u s a) 0)
  exact Int.mul_nonneg (priorMass_nonneg D s) (h s 0)

/-- Informe parfaitement, le decideur du parapluie bruite vaut 20 (poids
    marginal 4 dans chaque etat, meilleur paiement 2 puis 3). -/
theorem noisyUmbrella_valueNoisyPerfect :
    valueNoisyPerfect noisyUmbrella = 20 := by decide

/-- La chaine complete sur l'exemple : non informe (8) ≤ informe (12) ≤
    parfaitement informe (20). -/
theorem noisyUmbrella_chain :
    valueNoisyNoInfo noisyUmbrella ≤ valueNoisySignal noisyUmbrella ∧
    valueNoisySignal noisyUmbrella ≤ valueNoisyPerfect noisyUmbrella := by
  constructor
  · exact valueNoisyNoInfo_le_valueNoisySignal noisyUmbrella
  · exact valueNoisySignal_le_valueNoisyPerfect noisyUmbrella

/-! ## Ancres d'axiomes

Les axiomes des theoremes du module, imprimes par `lake build` : la claim
« ni `sorryAx`, ni `native_decide`, ni `Classical.choice` » devient
rejouable par le prochain lecteur, au lieu de ne vivre que dans un corps
de PR. -/

#print axioms sumFin_jointPayoff
#print axioms valueNoisyNoInfo_le_valueNoisySignal
#print axioms noisyUmbrella_valueNoisyNoInfo
#print axioms noisyUmbrella_valueNoisySignal
#print axioms noisyUmbrella_strict_gain
#print axioms sumFin_nonneg
#print axioms eq_zero_of_sumFin_nonneg
#print axioms p_eq_zero_of_signalMass_zero
#print axioms jointPayoff_zero_mass
#print axioms valueNoisySignal_zero_mass_cell
#print axioms sumFin_maxFin_mul_le
#print axioms valueNoisySignal_le_valueNoisyPerfect
#print axioms priorMass_nonneg
#print axioms jointPayoff_nonneg
#print axioms valueNoisyNoInfo_nonneg
#print axioms valueNoisySignal_nonneg
#print axioms valueNoisyPerfect_nonneg
#print axioms noisyUmbrella_valueNoisyPerfect
#print axioms noisyUmbrella_chain

