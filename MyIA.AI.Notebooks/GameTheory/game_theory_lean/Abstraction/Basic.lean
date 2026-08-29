/-
  # Abstraction.Basic — la dette d'abstraction peut croître en raffinant

  Grain #12204 (opération 2), jeu `GameTheory-19-Abstraction-a-Dette.ipynb`.

  ## Ce que le notebook mesure

  Le notebook GT-19 observe, sur SES données, une dette d'exploitabilité
  (meilleure réponse ligne + meilleure réponse colonne) **non croissante**
  le long du raffinement de partition, avec un palier (cellule 8 :
  « P6 0.0000 / P4 1.9091 / P3 1.9091 / P2 6.4211 », soit la chaîne
  122/19 → 21/11 = 21/11 → 0 indexée par grossièreté décroissante).
  Une généralisation naturelle mais excessive serait : « raffiner une
  abstraction ne peut jamais aggraver la dette retransportée ».

  ## Verdict de ce module : réfutation certifiée

  Ce module construit un modèle fini en **stratégies pures sur les
  entiers** et y **réfute** la généralisation : un contre-exemple nommé
  (`raffinement_aggrave_la_dette`) où raffiner {{0,1,2}} en {{0}},{1,2}}
  fait passer la dette totale retransportée de **3 à 4** (aggravation
  stricte), tandis que la partition discrète {0},{1,2} → {0},{1},{2}
  retombe à **0**. La courbe observée par GT-19 n'est donc pas un
  théorème : c'est une propriété de SES matrices, pas de la
  construction « abstraire puis retransporter » en général.

  ## Modèle

  * `Duel` : matrice 2×2 à coefficients entiers `(a, b, c, d)`, joueur
    ligne maximise, joueur colonne minimise (jeu à somme nulle).
  * Stratégies **pures** : `Strat := Bool × Bool` (action ligne, action
    colonne). Pas de stratégies mixtes : le modèle suffit à réfuter
    l'énoncé universel, et reste entièrement décidable par le noyau.
  * `dette M s` : exploitation du profil `s` dans le duel `M` =
    `vHaut M j - vBas M i` (gain de meilleure réponse ligne + gain de
    meilleure réponse colonne, ce second étant `g - min_j g`).
  * `EstSelle` : le profil `s` est une selle pure locale
    (`g = vHaut` et `g = vBas`).
  * Abstraction : le duel abstrait d'un bloc d'états est la **somme**
    des duels du bloc (`sommeBloc`). Le notebook GT-19 utilise la
    moyenne de bloc ; diviser par une taille de bloc strictement
    positive préserve les comparaisons argmax/argmin à l'intérieur d'un
    duel abstrait unique (le choix de selle pure est invariant par
    homothétie positive), donc la somme est le substitut exact en
    entiers de la moyenne — et chaque calcul réduit dans `Int`.
  * Raffinement : `Raffine fin coarse` — deux états dans un même bloc
    fin sont dans un même bloc grossier. Chaîne certifiée du
    contre-exemple : `partQ` (bloc unique {0,1,2}) ⊐ `partP`
    ({{0},{1,2}}) ⊐ `partD` (discret), chaque étape strictement plus
    fine (théorèmes `*_strict`).
  * Dette d'une partition : somme sur les états de la dette de la
    selle du bloc retransportée (`detteBloc`).

  ## Certification

  Tout est prouvé par `decide`/`rfl` (réduction du noyau) : aucune
  dépendance à Mathlib, aucun `sorry`, aucun `native_decide`, aucun
  `Classical.choice`. Les seuls axiomes présents dans le module sont
  `propext`/`Quot.sound`, hérités des lemmes d'ordre `Int` du cœur
  utilisés par les trois théorèmes généraux ; les théorèmes concrets
  (selles, dettes, raffinements, inégalité) n'en dépendent d'aucun.
  Les selles des blocs non triviaux sont prouvées **uniques**, et le
  théorème-phare quantifie sur tout choix de selles : l'aggravation ne
  dépend pas d'un choix arbitraire.
-/

/-- Un duel 2×2 à somme nulle sur les entiers : `(a, b, c, d)` ligne par ligne. -/
abbrev Duel : Type := Int × Int × Int × Int

/-- Une stratégie pure : (action du joueur ligne, action du joueur colonne). -/
abbrev Strat : Type := Bool × Bool

/-- Gain du joueur ligne pour le profil `(i, j)` dans le duel `M`. -/
def gain (M : Duel) (i j : Bool) : Int :=
  match i, j with
  | false, false => M.1
  | false, true  => M.2.1
  | true,  false => M.2.2.1
  | true,  true  => M.2.2.2

/-- Meilleure réponse ligne contre l'action colonne `j` : `max` des deux lignes. -/
def vHaut (M : Duel) (j : Bool) : Int := max (gain M false j) (gain M true j)

/-- Meilleure défense colonne contre l'action ligne `i` : `min` des deux colonnes. -/
def vBas (M : Duel) (i : Bool) : Int := min (gain M i false) (gain M i true)

/--
Dette (exploitabilité) du profil pur `s` dans le duel `M` : gain de
meilleure réponse ligne `vHaut - g` plus gain de meilleure réponse
colonne `g - vBas`, qui se telescope en `vHaut j - vBas i`.
-/
def dette (M : Duel) (s : Strat) : Int := vHaut M s.2 - vBas M s.1

/-- `s` est une selle pure locale : le gain y atteint `vHaut` et `vBas`. -/
abbrev EstSelle (M : Duel) (s : Strat) : Prop :=
  gain M s.1 s.2 = vHaut M s.2 ∧ gain M s.1 s.2 = vBas M s.1

/-- Somme coordonnée par coordonnée de deux duels. -/
def plusDuel (M N : Duel) : Duel :=
  (M.1 + N.1, M.2.1 + N.2.1, M.2.2.1 + N.2.2.1, M.2.2.2 + N.2.2.2)

/--
Duel abstrait d'un bloc d'états : SOMME des duels du bloc (voir
l'en-tête du module pour la comparaison avec la moyenne du notebook).
-/
def sommeBloc : List Duel → Duel
  | [] => (0, 0, 0, 0)
  | M :: Ms => plusDuel M (sommeBloc Ms)

/-- Dette totale retransportée d'une stratégie dans un bloc d'états. -/
def detteBloc : List Duel → Strat → Int
  | [], _ => 0
  | M :: Ms, s => dette M s + detteBloc Ms s

/--
`fin` raffine `coarse` : deux états étiquetés pareillement par `fin`
le sont aussi par `coarse`. Les états sont des `Nat` et une partition
est sa fonction d'étiquette ; les états hors du jeu (≥ 3) reçoivent
des étiquettes cohérentes avec le raffinement.
-/
def Raffine (fin coarse : Nat → Nat) : Prop :=
  ∀ s t : Nat, fin s = fin t → coarse s = coarse t

/-! ## Lois générales (valables pour tout duel entier) -/

/-- Le gain d'un profil pur est encadré entre `vBas` et `vHaut`. -/
theorem encadrement (M : Duel) (s : Strat) :
    vBas M s.1 ≤ gain M s.1 s.2 ∧ gain M s.1 s.2 ≤ vHaut M s.2 := by
  cases s with
  | mk i j =>
    cases i <;> cases j <;> first
      | exact ⟨Int.min_le_left _ _, Int.le_max_left _ _⟩
      | exact ⟨Int.min_le_left _ _, Int.le_max_right _ _⟩
      | exact ⟨Int.min_le_right _ _, Int.le_max_left _ _⟩
      | exact ⟨Int.min_le_right _ _, Int.le_max_right _ _⟩

/-- La dette d'un profil pur est non négative. -/
theorem dette_nonneg (M : Duel) (s : Strat) : 0 ≤ dette M s := by
  have h := encadrement M s
  unfold dette
  exact Int.sub_nonneg.mpr (Int.le_trans h.1 h.2)

/-- Une selle pure locale n'a aucune dette dans son propre duel. -/
theorem selle_dette_nulle {M : Duel} {s : Strat} (h : EstSelle M s) : dette M s = 0 := by
  unfold dette
  rw [← h.1, ← h.2, Int.sub_self]

/-! ## Le contre-exemple : trois duels, deux raffinements

  État 0 : `(1, 0, 0, -1)` — selle pure unique `(0, 1)`.
  État 1 : `(-2, 0, 0, 1)` — selle pure unique `(1, 0)`.
  État 2 : `(2, 0, -1, 0)` — selle pure unique `(0, 1)`.

  Partition grossière `partQ` : bloc unique {0,1,2}, duel abstrait
  `(1, 0, -1, 0)`, selle unique `(0, 1)` — dette retransportée 3.
  Partition raffinée `partP` : {{0},{1,2}}, bloc {1,2} de duel abstrait
  `(0, 0, -1, 1)`, selle unique `(0, 0)` — dette retransportée 4.
  Partition discrète `partD` : dette 0 (chaque état joue sa selle).
-/

/-- Duel de l'état 0 : matrice `[[1, 0], [0, -1]]`. -/
def d0 : Duel := (1, 0, 0, -1)

/-- Duel de l'état 1 : matrice `[[-2, 0], [0, 1]]`. -/
def d1 : Duel := (-2, 0, 0, 1)

/-- Duel de l'état 2 : matrice `[[2, 0], [-1, 0]]`. -/
def d2 : Duel := (2, 0, -1, 0)

/-- Partition grossière : un bloc unique {0, 1, 2}. -/
def partQ (_ : Nat) : Nat := 0

/-- Partition raffinée : blocs {0} et {1, 2}. -/
def partP (s : Nat) : Nat := if s = 0 then 0 else 1

/-- Partition discrète : blocs {0}, {1}, {2}. -/
def partD (s : Nat) : Nat := s

/-- Duel abstrait du bloc grossier {0, 1, 2}. -/
def blocQ : Duel := sommeBloc [d0, d1, d2]

/-- Duel abstrait du bloc raffiné {1, 2}. -/
def blocP : Duel := sommeBloc [d1, d2]

/-- Selle du duel abstrait grossier : ligne 0, colonne 1. -/
def stratBlocQ : Strat := (false, true)

/-- Selle du duel abstrait du bloc {1, 2} : ligne 0, colonne 0. -/
def stratBlocP : Strat := (false, false)

/-- Selles propres des trois états (partition discrète). -/
def stratEtat0 : Strat := (false, true)
/-- Selle propre de l'état 1 : ligne 1, colonne 0. -/
def stratEtat1 : Strat := (true, false)
/-- Selle propre de l'état 2 : ligne 0, colonne 1. -/
def stratEtat2 : Strat := (false, true)

/-! ### Les sommes de blocs sont bien celles annoncées -/

/-- Le bloc grossier {0,1,2} a pour duel abstrait `(1, 0, -1, 0)`. -/
theorem blocQ_valeur : blocQ = (1, 0, -1, 0) := rfl

/-- Le bloc {1,2} a pour duel abstrait `(0, 0, -1, 1)`. -/
theorem blocP_valeur : blocP = (0, 0, -1, 1) := rfl

/-! ### Chaîne de raffinement Q ⊐ P ⊐ D (strictement décroissante) -/

/-- `partP` raffine `partQ` : {{0},{1,2}} découpe {0,1,2}. -/
theorem raffinement_P_de_Q : Raffine partP partQ := fun _ _ _ => rfl

/-- `partD` raffine `partP` : {0},{1},{2} découpe {{0},{1,2}}. -/
theorem raffinement_D_de_P : Raffine partD partP := fun s t h => (show s = t from h) ▸ rfl

/-- Le raffinement Q → P est strict : `partQ` ne raffine pas `partP`. -/
theorem raffinement_P_strict : ¬ Raffine partQ partP :=
  fun h => absurd (h 0 1 rfl) (by decide)

/-- Le raffinement P → D est strict : `partP` ne raffine pas `partD`. -/
theorem raffinement_D_strict : ¬ Raffine partP partD :=
  fun h => absurd (h 1 2 rfl) (by decide)

/-! ### Selles (existence, unicité) — toutes certifiées par le noyau -/

/-- Le duel abstrait grossier a une selle pure : `(0, 1)`. -/
theorem selle_blocQ : EstSelle blocQ stratBlocQ := by decide

/-- Cette selle est l'unique selle pure du duel grossier. -/
theorem selle_blocQ_unique : ∀ i j : Bool, EstSelle blocQ (i, j) → (i, j) = stratBlocQ := by
  intro i j h
  cases i <;> cases j <;> first
    | rfl
    | exact absurd h (by decide)

/-- Le duel abstrait du bloc {1,2} a une selle pure : `(0, 0)`. -/
theorem selle_blocP : EstSelle blocP stratBlocP := by decide

/-- Cette selle est l'unique selle pure du duel du bloc {1,2}. -/
theorem selle_blocP_unique : ∀ i j : Bool, EstSelle blocP (i, j) → (i, j) = stratBlocP := by
  intro i j h
  cases i <;> cases j <;> first
    | rfl
    | exact absurd h (by decide)

/-- Selle propre de l'état 0. -/
theorem selle_etat0 : EstSelle d0 stratEtat0 := by decide

/-- Selle propre de l'état 1. -/
theorem selle_etat1 : EstSelle d1 stratEtat1 := by decide

/-- Selle propre de l'état 2. -/
theorem selle_etat2 : EstSelle d2 stratEtat2 := by decide

/-! ### Dettes retransportées par partition -/

/--
Dette de la partition grossière : la selle `(0,1)` du bloc {0,1,2}
retransportée coûte 0 à l'état 0, 3 à l'état 1, 0 à l'état 2,
soit **3** au total.
-/
theorem dette_partitionQ : detteBloc [d0, d1, d2] stratBlocQ = 3 := by decide

/--
Dette de la partition raffinée : la selle propre de {0} coûte 0, la
selle `(0,0)` du bloc {1,2} coûte 2 à l'état 1 et 2 à l'état 2,
soit **4** au total.
-/
theorem dette_partitionP : dette d0 stratEtat0 + detteBloc [d1, d2] stratBlocP = 4 := by decide

/--
Dette de la partition discrète : chaque état joue sa selle propre,
coût nul (conséquence aussi de `selle_dette_nulle`).
-/
theorem dette_discrete :
    dette d0 stratEtat0 + (dette d1 stratEtat1 + dette d2 stratEtat2) = 0 := by decide

/-! ## Théorème-phare : le raffinement aggrave strictement la dette

  Quel que soit le choix de selle dans chaque bloc (les blocs non
  triviaux ont une selle unique, les blocs singletons une selle sans
  dette), raffiner {{0,1,2}} en {{0},{1,2}} augmente strictement la
  dette retransportée : **3 < 4**. La non-croissance observée par le
  notebook GT-19 n'est donc pas un théorème général.
-/

/--
CONTRE-EXEMPLE NOMMÉ au « raffiner ne peut qu'améliorer la dette » :
pour tout choix de selles `tQ` (bloc grossier), `t0` (bloc singleton
{0}) et `tP` (bloc {1,2}) — les deux blocs non triviaux forçant
`tQ = stratBlocQ` et `tP = stratBlocP` par unicité — la dette totale
retransportée passe de 3 (grossier) à 4 (raffiné), aggravation
stricte indépendante de tout choix.
-/
theorem raffinement_aggrave_la_dette (tQ t0 tP : Strat)
    (h0 : EstSelle d0 t0)
    (uQ : ∀ i j : Bool, EstSelle blocQ (i, j) → (i, j) = tQ)
    (uP : ∀ i j : Bool, EstSelle blocP (i, j) → (i, j) = tP) :
    detteBloc [d0, d1, d2] tQ < dette d0 t0 + detteBloc [d1, d2] tP := by
  have e1 : tQ = stratBlocQ := (uQ stratBlocQ.1 stratBlocQ.2 selle_blocQ).symm
  have e2 : tP = stratBlocP := (uP stratBlocP.1 stratBlocP.2 selle_blocP).symm
  have e3 : dette d0 t0 = 0 := selle_dette_nulle h0
  rw [e1, e2, e3]
  decide

/-- Résumé numérique certifié : 0 < dette(Q) = 3 < dette(P) = 4, discret = 0. -/
theorem courbe_dette :
    0 < detteBloc [d0, d1, d2] stratBlocQ ∧
    detteBloc [d0, d1, d2] stratBlocQ < dette d0 stratEtat0 + detteBloc [d1, d2] stratBlocP ∧
    dette d0 stratEtat0 + (dette d1 stratEtat1 + dette d2 stratEtat2) = 0 := by decide
