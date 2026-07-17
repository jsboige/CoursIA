/-
  Enchère scellée au second prix (Vickrey)
  ========================================

  Le résultat compagnon de `Auction.lean` (enchère au premier prix) :
  dans l'enchère au second prix (Vickrey 1961), le gagnant paie l'offre
  PERDANTE, et l'offre sincère devient une stratégie faiblement
  dominante — pour tout nombre de valorisations `n`, pas seulement sur
  les petites instances.

  Encodage (mêmes conventions que `Auction.lean`, Lean 4 core seul) :
  - Les valorisations sont les *types*, les offres sont les *actions*
    d'un `BayesGame2` avec un poids de prior uniforme 1.
  - Les utilités sont mises à l'échelle par 2 pour que le cas d'égalité
    reste dans `Int` : gain = `2*(v - b_opp)` (payer l'offre adverse),
    égalité = `v - b`, perte = `0`.

  Résultats (tous pour `n` arbitraire) :
  - `spa_truthful_dominant1/2` : l'offre sincère domine faiblement toute
    autre offre PONCTUELLEMENT — face à toute offre adverse, dans tout
    état. C'est l'argument classique de dominance de Vickrey, par
    disjonction des cas sur qui gagne.
  - `spa_interim_best1/2` : la dominance ponctuelle se transfère à
    l'utilité interimaire via `sumFin_mono`.
  - `spa_truthful_bne` : le profil sincère est un équilibre de Nash
    bayésien pour TOUT `n` — un théorème général, contrastant avec
    l'enchère au premier prix où l'offre sincère n'est pas un BNE
    (`truthful_not_bne_two/three` dans `Auction.lean`).
  - `spa_truthful_pos_three` : contrairement à l'enchère au premier prix
    (où l'offre sincère rapporte exactement 0, `interimU1_truthful`), le
    soumissionnaire sincère de Vickrey conserve une rente informationnelle
    strictement positive (instance vérifiée au noyau).

  Voir #2610 (formalisation GT-Lean, phase bayésienne 3).
-/

import Bayesian.BNE

/-- Enchère scellée au second prix à deux enchérisseurs, valorisations et
    offres dans `Fin n`, prior uniforme. Le gagnant paie l'offre adverse ;
    les utilités sont mises à l'échelle par 2 pour que le cas d'égalité
    reste entier. -/
@[reducible] def spa (n : Nat) : BayesGame2 where
  nT1 := n
  nT2 := n
  nA1 := n
  nA2 := n
  w := fun _ _ => 1
  u1 := fun v1 _ b1 b2 =>
    if b2.val < b1.val then 2 * ((v1.val : Int) - b2.val)
    else if b1.val = b2.val then (v1.val : Int) - b2.val
    else 0
  u2 := fun _ v2 b1 b2 =>
    if b1.val < b2.val then 2 * ((v2.val : Int) - b1.val)
    else if b1.val = b2.val then (v2.val : Int) - b1.val
    else 0

/-- Offre sincère du joueur 1 dans l'enchère au second prix. -/
@[reducible] def spaTruthful1 (n : Nat) : Strategy1 (spa n) := fun v => v

/-- Offre sincère du joueur 2 dans l'enchère au second prix. -/
@[reducible] def spaTruthful2 (n : Nat) : Strategy2 (spa n) := fun v => v

/-- Argument de dominance de Vickrey, joueur 1 : l'offre sincère domine
    faiblement toute autre offre face à toute offre adverse, dans tout
    état. Quel que soit l'adversaire et son offre, dévier de `v` ne peut
    que faire perdre une victoire rentable (cas `b1 < v`) ou acheter une
    victoire non rentable (cas `b1 > v`) — cela n'améliore jamais l'offre
    `v`, parce que le PRIX (l'offre adverse) ne dépend pas de sa propre
    offre. -/
theorem spa_truthful_dominant1 (n : Nat) (v t2 b1 b2 : Fin n) :
    (spa n).u1 v t2 b1 b2 ≤ (spa n).u1 v t2 v b2 := by
  show (if b2.val < b1.val then 2 * ((v.val : Int) - b2.val)
        else if b1.val = b2.val then (v.val : Int) - b2.val
        else 0)
      ≤ (if b2.val < v.val then 2 * ((v.val : Int) - b2.val)
        else if v.val = b2.val then (v.val : Int) - b2.val
        else 0)
  repeat' split
  all_goals omega

/-- Argument de dominance de Vickrey, joueur 2 (symétrique). -/
theorem spa_truthful_dominant2 (n : Nat) (t1 v b1 b2 : Fin n) :
    (spa n).u2 t1 v b1 b2 ≤ (spa n).u2 t1 v b1 v := by
  show (if b1.val < b2.val then 2 * ((v.val : Int) - b1.val)
        else if b1.val = b2.val then (v.val : Int) - b1.val
        else 0)
      ≤ (if b1.val < v.val then 2 * ((v.val : Int) - b1.val)
        else if b1.val = v.val then (v.val : Int) - b1.val
        else 0)
  repeat' split
  all_goals omega

/-- La dominance ponctuelle se transfère à l'utilité interimaire : face à
    N'IMPORTE QUELLE stratégie adverse, tout type du joueur 1 préfère
    faiblement l'offre sincère (par monotonie de la somme pondérée). -/
theorem spa_interim_best1 (n : Nat) (v a : Fin n) (s2 : Strategy2 (spa n)) :
    interimU1 (spa n) v a s2 ≤ interimU1 (spa n) v (spaTruthful1 n v) s2 := by
  apply sumFin_mono
  intro t2
  exact Int.mul_le_mul_of_nonneg_left
    (spa_truthful_dominant1 n v t2 a (s2 t2)) (by omega)

/-- Meilleure réponse interimaire, côté joueur 2. -/
theorem spa_interim_best2 (n : Nat) (v a : Fin n) (s1 : Strategy1 (spa n)) :
    interimU2 (spa n) v a s1 ≤ interimU2 (spa n) v (spaTruthful2 n v) s1 := by
  apply sumFin_mono
  intro t1
  exact Int.mul_le_mul_of_nonneg_left
    (spa_truthful_dominant2 n t1 v (s1 t1) a) (by omega)

/-- **Théorème de Vickrey** (fini, deux enchérisseurs) : le profil sincère
    est un équilibre de Nash bayésien de l'enchère au second prix pour
    TOUT `n`. Un théorème général — pas de `decide`, pas de vérification
    d'instance — contrastant avec l'enchère au premier prix, où l'offre
    sincère n'est pas un BNE (`truthful_not_bne_two/three`). -/
theorem spa_truthful_bne (n : Nat) :
    isBNE (spa n) (spaTruthful1 n) (spaTruthful2 n) :=
  ⟨fun t1 a => spa_interim_best1 n t1 a (spaTruthful2 n),
   fun t2 a => spa_interim_best2 n t2 a (spaTruthful1 n)⟩

/-- Rente informationnelle : dans l'équilibre sincère de Vickrey avec
    valorisations `{0, 1, 2}`, le type haut gagne une utilité interimaire
    strictement positive (concrètement 6, mis à l'échelle : gagne en
    payant 0 et 1 face aux types bas, à égalité à 2 pour un surplus nul)
    — alors que l'offre sincère dans l'enchère au PREMIER prix rapporte
    exactement 0 (`interimU1_truthful` dans `Auction.lean`). -/
theorem spa_truthful_pos_three :
    0 < interimU1 (spa 3) ⟨2, by decide⟩
        (spaTruthful1 3 ⟨2, by decide⟩) (spaTruthful2 3) := by
  decide
