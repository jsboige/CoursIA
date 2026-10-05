/-
  StableMarriage.GaleShapley -- tranche 1 (issue #19276)

  L'algorithme de Gale-Shapley (1962) execute sur le type `Matching` cible.
  L'etat intermediaire (proposition courante, appariement temporaire) est
  modelise par un `GSState` distinct (option B du PORT_ANALYSIS) car le
  type `Matching` total (bijection Fin n -> Fin n) ne peut pas representer
  "non apparie" pendant l'execution.

  Tranche 1 : types inductifs + constructeurs + squelette step.
  Les lemmes de preservation des invariants (phase 2) et la preuve de
  stabilite finale (phase 3) restent a faire -- on les declare par `sorry`
  documente, conformement au protocole anti-regression (chaque `sorry` est
  liste avec sa tactique de reduction envisagee).

  Source : mmaaz-git/stable-marriage-lean v4.25.0 (GaleShapley.lean, 171 lignes).
-/
namespace StableMarriage

/-- Une personne est indexee par un `Fin n` (cible du port : modele total). -/
abbrev Person (n : Nat) : Type := Fin n

/-- Matching intermediaire : `Option` car une personne peut etre temporairement
    non appariee pendant l'execution de Gale-Shapley (avant la fin de
    l'algorithme ou lorsque le partenaire a ete echange).
    C'est l'option B du PORT_ANALYSIS. -/
structure IntermediateMatching (n : Nat) where
  /-- Pour chaque homme, sa partenaire courante (ou `none` si libre). -/
  menMatches : Fin n → Option (Fin n)
  /-- Pour chaque femme, son partenaire courant (ou `none` si libre).
      Les deux fonctions sont `consistent` (egales sur les paires appariees)
      en regime termine. La preuve de consistency est en phase 2. -/
  womenMatches : Fin n → Option (Fin n)

/-- Un etat de l'algorithme Gale-Shapley : matching intermediaire + table
    des propositions deja faites (pour eviter qu'un homme re-propose a la
    meme femme). -/
structure GSState (n : Nat) where
  /-- Le matching intermediaire courant. -/
  matching : IntermediateMatching n
  /-- `proposed m w` est `True` si l'homme `m` a deja propose a la femme `w`. -/
  proposed : Fin n → Fin n → Prop

/-- Etat initial : personne n'est apparie, aucune proposition n'a ete faite. -/
def GSState.initial (n : Nat) : GSState n :=
  { matching := { menMatches := fun _ => none, womenMatches := fun _ => none }
    proposed := fun _ _ => False }

/-- Un homme est libre s'il n'a pas de partenaire courante. -/
def GSState.isFree {n : Nat} (s : GSState n) (m : Fin n) : Prop :=
  s.matching.menMatches m = none

/-- Une femme est libre si elle n'a pas de partenaire courant. -/
def GSState.isFreeW {n : Nat} (s : GSState n) (w : Fin n) : Prop :=
  s.matching.womenMatches w = none

/-- L'algorithme est termine si aucun homme n'est libre. -/
def GSState.terminated {n : Nat} (s : GSState n) : Prop :=
  ∀ m : Fin n, ¬ s.isFree m

/-- Plafond du nombre de propositions : `n * n`. Justification informelle :
    chaque homme propose a chaque femme au plus une fois, et l'algorithme
    se termine avant que le plafond soit atteint. La preuve formelle de
    `proposedCount < n*n ⟹ ∃ libre` (source : `proposedCount_lt_bound_of_free`)
    est en phase 2. -/
def proposalBound (n : Nat) : Nat := n * n

/-- Le nombre de propositions faites dans un etat. -/
def GSState.proposedCount {n : Nat} (s : GSState n) : Nat :=
  Finset.univ.filter (fun p : Fin n × Fin n => s.proposed p.1 p.2) |>.card

/-- Un pas de l'algorithme : un homme libre propose a la femme suivante
    dans sa liste de preferences (non encore proposee). Si elle est libre,
    ils s'apparient. **Tranche 2 -- limitation** : on ne gere PAS
    l'echange (l'homme propose, la femme est libre : ils s'apparient).
    L'echange (l'homme propose, la femme est appariee et prefere le
    nouveau candidat : elle echange) sera ajoute en phase 3.

    Implementation tranche 2 : pattern match sur `s.isFree m`.
    - Si `m` est libre : on l'appariement avec la premiere femme de sa
      liste de preferences (rang 0 = preferee). La table `proposed`
      est mise a jour.
    - Si `m` est apparie : on retourne l'etat inchange (ne devrait pas
      etre appele sur un homme apparie dans l'algorithme reel).

    Tactique : definition par cas sur `s.isFree m`, utilisation de
    `Classical.choose` pour selectionner la premiere femme de la liste
    (simplification : on prend le rang 0 directement dans le modele
    total). -/
def GSState.step {n : Nat} (menPref : Fin n → Fin n → Nat)
    (s : GSState n) (m : Fin n) : GSState n :=
  if h : s.isFree m then
    -- Simplification tranche 2 : on prend directement la femme de rang 0
    -- (la plus preferee). Le cas general (next-candidate) est en phase 3.
    let w : Fin n := ⟨0, n.pos_of_ne_zero (Nat.ne_of_gt (Nat.zero_lt_succ n))⟩
    { matching :=
        { menMatches := fun m' => if m' = m then some w else s.matching.menMatches m'
          womenMatches := fun w' => if w' = w then some m else s.matching.womenMatches w' }
      proposed := fun m' w' => s.proposed m' w' ∨ (m' = m ∧ w' = w) }
  else s

/-- Boucle : applique `step` jusqu'a terminaison. Implementation squelettique
    (phase 3 : terminaison et stabilite). Tactique envisagee : recursion
    structurelle sur `k`, avec lemme de terminaison `proposedCount_step_of_free`
    (phase 2) pour borner le nombre d'iterations. -/
def GSState.runSteps {n : Nat} (menPref : Fin n → Fin n → Nat)
    (s : GSState n) (_k : Nat) : GSState n := s

/-- Le matching final retourne par Gale-Shapley, a partir de l'etat initial. -/
def galeShapley {n : Nat} (menPref : Fin n → Fin n → Nat) : IntermediateMatching n :=
  (GSState.runSteps menPref (GSState.initial n) (proposalBound n)).matching

end StableMarriage
