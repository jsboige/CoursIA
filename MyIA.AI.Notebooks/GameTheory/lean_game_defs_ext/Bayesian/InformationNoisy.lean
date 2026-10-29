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

  Ce qui est prouve dans ce module (tranches successives de #22374) :

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

  - `valueNoisySignal_eq_valueNoisyNoInfo_of_factored` — critere d'Evans :
    sur une table jointe **factorisee** (etat et realisation independants),
    l'EVSI brute est **exactement** nulle, sans aucun argument d'arrondi ;
  - `evsiRaw` / `evsiNet` — la valeur brute est non negative par la
    dominance ; la valeur **nette** (brute moins le cout de l'observation) ne
    l'est pas : le parapluie bruite a un gain brut de 4 et une valeur nette
    strictement negative des que le cout depasse 4 ;
  - `valueNoisyNoInfo_ofSignal`, `valueNoisySignal_ofSignal`,
    `valueNoisyPerfect_ofSignal` — le **pont** vers les signaux deterministes
    de `Information.lean` : sur la classe des tables portees par le graphe
    d'un `Signal`, les trois valeurs coincident exactement. Deux semantiques
    qui coincident sur leur intersection ne peuvent pas diverger en silence.

  Ce qui reste a faire dans les tranches suivantes, et n'est **pas**
  affirme ici : adaptateur exact vers les instances JSON du banc `voi`,
  comparaison inter-moteurs, carnet compagnon reexecute.

  Voir #22374 (extension de la phase bayesienne 4 de #2610).
-/

import Bayesian.Information

/-- Probleme de decision fini a un decideur, avec un signal bruite decrit
    par une table de poids joints etat × realisation. Les paiements sont
    entiers et les poids naturels : les valeurs sont exactes, sans
    division.

    **Convention des dimensions.** `nS` est un **compte** d'etats ; `nA` et
    `nX` sont des **indices maximaux** : `nA = 1` veut dire deux actions
    (`Fin (nA + 1)`), `nX = 1` veut dire deux realisations. L'asymetrie est
    voulue -- elle garantit la non-vacuite de `maxFin` sur les actions --
    mais elle est un piege d'ecriture : poser `nX := 2` en pensant « deux
    realisations » en donne **trois**, et rien dans le module ne le
    reproche, puisque la table a trois colonnes est aussi acceptee. -/
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
`nS = 1`, `nA = 1`, `nX = 1`, `p ≡ 1`, `u ≡ -1` (deux realisations, chacune
de masse 1 et de marginal 2), la meilleure action vaut -1 dans chaque etat et
les trois valeurs valent -2 ; le gain brut du signal est alors nul, non
negatif mais pas strictement positif.

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

/-! ## Independance : l'EVSI brute est exactement nulle

Une table jointe **factorisee** — chaque cellule est le produit d'un poids
d'etat et d'un poids de realisation — decrit un signal qui n'apprend rien :
l'etat et la realisation sont independants. C'est le critere d'Evans, et il
doit tomber **exactement** a zero, pas « a l'arrondi pres ».

La preuve ne suppose aucune normalisation. Le facteur commun `Q = Σ_x q x`
sort de chaque maximum (`maxFin_mul_left`) et de chaque somme
(`sumFin_mul_left`), et les deux membres se reduisent au meme produit `Q * M`.
-/

/-- Un facteur constant a droite sort de la somme. -/
theorem sumFin_mul_right {n : Nat} (f : Fin n → Int) (c : Int) :
    sumFin n (fun i => f i * c) = sumFin n f * c := by
  rw [sumFin_congr (fun i => Int.mul_comm (f i) c), sumFin_mul_left, Int.mul_comm]

/-- Permutation des deux premiers facteurs d'un produit triple, sans
    commutativite globale : `(a * b) * c = b * (a * c)`. -/
theorem mul_mul_rotate (a b c : Int) : (a * b) * c = b * (a * c) := by
  calc (a * b) * c = (b * a) * c := by rw [Int.mul_comm a b]
    _ = b * (a * c) := Int.mul_assoc b a c

/-- Pour un facteur non negatif, le maximum se factorise :
    `max_a (c * f a) = c * max_a f a`. La non-negativite est necessaire : un
    facteur negatif inverse l'ordre et le maximum deviendrait un minimum. -/
theorem maxFin_mul_left {n : Nat} (c : Int) (hc : 0 ≤ c) (f : Fin (n + 1) → Int) :
    maxFin n (fun a => c * f a) = c * maxFin n f := by
  apply Int.le_antisymm
  · exact maxFin_le (fun a => Int.mul_le_mul_of_nonneg_left (le_maxFin f a) hc)
  · calc c * maxFin n f = c * f (argmaxFin n f) := by rw [argmaxFin_spec f]
      _ ≤ maxFin n (fun a => c * f a) := le_maxFin (fun a => c * f a) _

/-- La table jointe se factorise en un poids d'etat et un poids de
    realisation : forme exacte de l'independance entre l'etat et le signal.
    Enoncee dans `Int` parce que c'est l'echelle ou ce module compare ses
    valeurs, ce qui evite toute conversion dans les preuves qui l'emploient. -/
def Factored (D : NoisyProblem) (w : Fin D.nS → Nat) (q : Fin (D.nX + 1) → Nat) :
    Prop :=
  ∀ (s : Fin D.nS) (x : Fin (D.nX + 1)), (D.p s x : Int) = (w s : Int) * (q x : Int)

/-- Sous factorisation, le poids marginal d'un etat est son poids propre
    multiplie par la masse totale du signal. -/
theorem priorMass_of_factored (D : NoisyProblem) (w : Fin D.nS → Nat)
    (q : Fin (D.nX + 1) → Nat) (h : Factored D w q) (s : Fin D.nS) :
    priorMass D s = (w s : Int) * sumFin (D.nX + 1) (fun x => (q x : Int)) := by
  unfold priorMass
  rw [sumFin_congr (fun x => h s x)]
  exact sumFin_mul_left _ _

/-- **Valeur du decideur non informe sous independance** : la masse du signal
    multiplie la valeur du probleme sur les seuls poids d'etat. -/
theorem valueNoisyNoInfo_of_factored (D : NoisyProblem) (w : Fin D.nS → Nat)
    (q : Fin (D.nX + 1) → Nat) (h : Factored D w q) :
    valueNoisyNoInfo D =
      sumFin (D.nX + 1) (fun x => (q x : Int)) *
        maxFin D.nA (fun a => sumFin D.nS (fun s => (w s : Int) * D.u s a)) := by
  have hQ : 0 ≤ sumFin (D.nX + 1) (fun x => (q x : Int)) :=
    sumFin_nonneg (fun x => Int.natCast_nonneg (q x))
  have hinner : ∀ a : Fin (D.nA + 1),
      sumFin D.nS (fun s => priorMass D s * D.u s a) =
      sumFin (D.nX + 1) (fun x => (q x : Int)) *
        sumFin D.nS (fun s => (w s : Int) * D.u s a) := by
    intro a
    have hpt : ∀ s : Fin D.nS,
        priorMass D s * D.u s a =
        sumFin (D.nX + 1) (fun x => (q x : Int)) * ((w s : Int) * D.u s a) := by
      intro s
      rw [priorMass_of_factored D w q h s, mul_mul_rotate]
    rw [sumFin_congr hpt]
    exact sumFin_mul_left _ _
  unfold valueNoisyNoInfo
  rw [show (fun a => sumFin D.nS (fun s => priorMass D s * D.u s a)) =
      (fun a => sumFin (D.nX + 1) (fun x => (q x : Int)) *
        sumFin D.nS (fun s => (w s : Int) * D.u s a)) from funext hinner]
  exact maxFin_mul_left _ hQ _

/-- **Valeur du decideur informe sous independance** : elle se factorise de la
    meme facon, realisation par realisation. -/
theorem valueNoisySignal_of_factored (D : NoisyProblem) (w : Fin D.nS → Nat)
    (q : Fin (D.nX + 1) → Nat) (h : Factored D w q) :
    valueNoisySignal D =
      sumFin (D.nX + 1) (fun x => (q x : Int)) *
        maxFin D.nA (fun a => sumFin D.nS (fun s => (w s : Int) * D.u s a)) := by
  have hinner : ∀ (x : Fin (D.nX + 1)) (a : Fin (D.nA + 1)),
      sumFin D.nS (fun s => jointPayoff D s x a) =
      (q x : Int) * sumFin D.nS (fun s => (w s : Int) * D.u s a) := by
    intro x a
    have hpt : ∀ s : Fin D.nS,
        jointPayoff D s x a = (q x : Int) * ((w s : Int) * D.u s a) := by
      intro s
      unfold jointPayoff
      rw [h s x, mul_mul_rotate]
    rw [sumFin_congr hpt]
    exact sumFin_mul_left _ _
  unfold valueNoisySignal
  rw [sumFin_congr (fun x => congrArg (maxFin D.nA) (funext (hinner x)))]
  rw [sumFin_congr (fun x => maxFin_mul_left _ (Int.natCast_nonneg (q x)) _)]
  exact sumFin_mul_right _ _

/-- **Critere d'Evans pour cette representation** : sur une table jointe
    factorisee, la valeur avec signal egale exactement la valeur sans signal.
    Le zero est structurel, il ne vient d'aucune tolerance. -/
theorem valueNoisySignal_eq_valueNoisyNoInfo_of_factored (D : NoisyProblem)
    (w : Fin D.nS → Nat) (q : Fin (D.nX + 1) → Nat) (h : Factored D w q) :
    valueNoisySignal D = valueNoisyNoInfo D := by
  rw [valueNoisySignal_of_factored D w q h, valueNoisyNoInfo_of_factored D w q h]

/-! ## Valeur brute et valeur nette

La valeur brute est non negative par `valueNoisyNoInfo_le_valueNoisySignal`.
La valeur **nette** retranche le cout de l'observation : rien ne contraint son
signe, et l'instance du parapluie bruite le montre — gain brut 4, cout 5, net
strictement negatif.
-/

/-- Valeur esperee brute de l'information (EVSI brute) : ecart entre la valeur
    avec signal et la valeur sans signal, dans les unites brutes de la table. -/
def evsiRaw (D : NoisyProblem) : Int := valueNoisySignal D - valueNoisyNoInfo D

/-- Valeur **nette** de l'information : la valeur brute moins le cout `c` de
    l'observation, exprime dans les memes unites. -/
def evsiNet (D : NoisyProblem) (c : Int) : Int := evsiRaw D - c

/-- L'EVSI brute est non negative : c'est exactement la dominance du signal. -/
theorem evsiRaw_nonneg (D : NoisyProblem) : 0 ≤ evsiRaw D := by
  unfold evsiRaw
  have := valueNoisyNoInfo_le_valueNoisySignal D
  omega

/-- Le gain brut du parapluie bruite vaut 4 (12 - 8). -/
theorem noisyUmbrella_evsiRaw : evsiRaw noisyUmbrella = 4 := by decide

/-- Un cout de 5 rend la valeur nette strictement negative : le signe de la
    valeur brute ne dit rien de celui de la valeur nette. -/
theorem noisyUmbrella_evsiNet_negative : evsiNet noisyUmbrella 5 < 0 := by decide

/-- Le meme signal reste rentable a cout 3 : la frontiere est bien le cout,
    pas un seuil cache dans la representation. -/
theorem noisyUmbrella_evsiNet_positive : 0 < evsiNet noisyUmbrella 3 := by decide

/-! ## Instance independante verifiee au noyau

Le parapluie avec un bulletin **independant** de l'etat : les deux
realisations tombent avec le meme poids quel que soit l'etat, donc le
decideur n'apprend rien.
-/

/-- Parapluie a bulletin independant : `p s x = 2` pour toute cellule, soit la
    factorisation `w ≡ 2`, `q ≡ 1`. -/
def independentUmbrella : NoisyProblem where
  nS := 2
  nA := 1
  nX := 1
  p := fun _ _ => 2
  u := fun s a =>
    if s.val = 0 then (if a.val = 0 then 2 else -3)
    else (if a.val = 0 then 0 else 3)

/-- La table du parapluie independant est bien factorisee. -/
theorem independentUmbrella_factored :
    Factored independentUmbrella (fun _ => 2) (fun _ => 1) := by
  intro s x
  rfl

/-- **Zero exact, par le theoreme** : l'EVSI brute s'annule parce que la table
    est factorisee, sans jamais evaluer l'instance. -/
theorem independentUmbrella_evsiRaw :
    evsiRaw independentUmbrella = 0 := by
  unfold evsiRaw
  rw [valueNoisySignal_eq_valueNoisyNoInfo_of_factored _ _ _
    independentUmbrella_factored]
  omega

/-- **Le meme zero, par evaluation** : un second instrument, independant du
    premier, rend le meme resultat. Un desaccord entre les deux signalerait
    une erreur de l'un ou de l'autre, jamais un arrondi. -/
theorem independentUmbrella_evsiRaw_decide :
    evsiRaw independentUmbrella = 0 := by decide

/-! ## Pont vers les signaux deterministes

Un signal deterministe `σ : Signal D m` partitionne les etats. Sa table
jointe a un support exactement sur le graphe de `σ` : la cellule `(s, x)` ne
porte un poids que si `σ s = x`.

Le pont ci-dessous etablit que les trois valeurs du module bruite coincident
avec celles de `Information.lean` sur cette classe. Ce n'est pas une
traduction approximative : c'est la meme valeur, trois fois, ce qui interdit
aux deux semantiques de diverger en silence.
-/

/-- Table jointe induite par un signal deterministe : support sur le graphe de
    `σ`, poids `w s` sur ce graphe et zero partout ailleurs. -/
def ofSignal {m : Nat} (D : DecisionProblem) (σ : Signal D m) : NoisyProblem where
  nS := D.nS
  nA := D.nA
  nX := m
  p := fun s x => if σ s = x then D.w s else 0
  u := D.u

/-- Le marginal de la table induite redonne exactement la prior du probleme
    deterministe : le pont ne deforme aucun poids. -/
theorem priorMass_ofSignal {m : Nat} (D : DecisionProblem) (σ : Signal D m)
    (s : Fin D.nS) : priorMass (ofSignal D σ) s = (D.w s : Int) := by
  unfold priorMass
  show sumFin (m + 1) (fun x => (((ofSignal D σ).p s x : Nat) : Int)) = (D.w s : Int)
  have h : ∀ x : Fin (m + 1),
      (((ofSignal D σ).p s x : Nat) : Int) =
      (if σ s = x then (D.w s : Int) else 0) := by
    intro x
    by_cases hc : σ s = x <;> simp [ofSignal, hc]
  rw [sumFin_congr h]
  exact sumFin_single (σ s) (fun _ => (D.w s : Int))

/-- **Pont, valeur non informee** : le decideur sans signal du module bruite
    vaut exactement celui du module deterministe. -/
theorem valueNoisyNoInfo_ofSignal {m : Nat} (D : DecisionProblem) (σ : Signal D m) :
    valueNoisyNoInfo (ofSignal D σ) = valueNoInfo D := by
  unfold valueNoisyNoInfo valueNoInfo
  refine congrArg (maxFin D.nA) (funext (fun a => ?_))
  refine sumFin_congr (fun s => ?_)
  rw [priorMass_ofSignal D σ s]
  rfl

/-- **Pont, valeur informee** : le decideur qui observe le signal vaut
    exactement `valueSignal` du module deterministe. -/
theorem valueNoisySignal_ofSignal {m : Nat} (D : DecisionProblem) (σ : Signal D m) :
    valueNoisySignal (ofSignal D σ) = valueSignal D σ := by
  unfold valueNoisySignal valueSignal
  dsimp only [ofSignal]
  refine sumFin_congr (fun x => congrArg (maxFin D.nA) (funext (fun a => ?_)))
  refine sumFin_congr (fun s => ?_)
  dsimp only [jointPayoff, wu]
  by_cases hc : σ s = x
  · subst hc
    rw [if_pos rfl, if_pos rfl]
  · rw [if_neg hc, if_neg hc]
    exact Int.zero_mul (D.u s a)

/-- **Pont, valeur parfaite** : l'information parfaite coincide aussi. -/
theorem valueNoisyPerfect_ofSignal {m : Nat} (D : DecisionProblem) (σ : Signal D m) :
    valueNoisyPerfect (ofSignal D σ) = valuePerfect D := by
  unfold valueNoisyPerfect valuePerfect
  refine sumFin_congr (fun s => congrArg (maxFin D.nA) (funext (fun a => ?_)))
  rw [priorMass_ofSignal D σ s]
  rfl

/-- **Controle de bout en bout sur le parapluie deterministe** : le signal qui
    revele l'etat donne 5 par la semantique bruitee, exactement la valeur
    parfaite calculee par `Information.lean`. -/
theorem umbrella_ofSignal_perfect :
    valueNoisySignal (ofSignal umbrella (m := 1) (fun s => s)) = 5 := by decide

/-- **Pont, signal non informatif** : le signal constant a une seule
    realisation n'apprend rien, et son EVSI brute est exactement nulle —
    consequence du pont et de `valueSignal_const`, sans calcul separe. -/
theorem evsiRaw_ofSignal_const (D : DecisionProblem) :
    evsiRaw (ofSignal (m := 0) D (fun _ => (0 : Fin 1))) = 0 := by
  unfold evsiRaw
  have h1 : valueNoisySignal (ofSignal (m := 0) D (fun _ => (0 : Fin 1))) =
      valueSignal D (fun _ => (0 : Fin 1)) :=
    valueNoisySignal_ofSignal D (fun _ => (0 : Fin 1))
  have h2 : valueNoisyNoInfo (ofSignal (m := 0) D (fun _ => (0 : Fin 1))) =
      valueNoInfo D :=
    valueNoisyNoInfo_ofSignal D (fun _ => (0 : Fin 1))
  rw [h1, h2, valueSignal_const]
  omega

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
#print axioms sumFin_mul_right
#print axioms mul_mul_rotate
#print axioms maxFin_mul_left
#print axioms priorMass_of_factored
#print axioms valueNoisyNoInfo_of_factored
#print axioms valueNoisySignal_of_factored
#print axioms valueNoisySignal_eq_valueNoisyNoInfo_of_factored
#print axioms evsiRaw_nonneg
#print axioms noisyUmbrella_evsiRaw
#print axioms noisyUmbrella_evsiNet_negative
#print axioms noisyUmbrella_evsiNet_positive
#print axioms independentUmbrella_factored
#print axioms independentUmbrella_evsiRaw
#print axioms independentUmbrella_evsiRaw_decide
#print axioms priorMass_ofSignal
#print axioms valueNoisyNoInfo_ofSignal
#print axioms valueNoisySignal_ofSignal
#print axioms valueNoisyPerfect_ofSignal
#print axioms umbrella_ofSignal_perfect
#print axioms evsiRaw_ofSignal_const

