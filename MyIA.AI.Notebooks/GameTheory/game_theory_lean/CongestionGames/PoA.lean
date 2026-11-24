/-
Copyright (c) 2026 CoursIA. Tous droits reserves.
-/
import Mathlib.Tactic
import Mathlib.Data.Fin.VecNotation

/-!
# Prix de l'anarchie des jeux de congestion affines (borne elementaire 2)

Compagnon Lean du carnet `GameTheory-04h-Routing-PriceOfAnarchy-Python.ipynb`
(critere 4 de l'issue #21927, grain #24423) : la borne 2x du prix de
l'anarchie pour l'**equilibre minimisant le potentiel de Rosenthal** d'un
jeu de congestion atomique a couts lineaires, prouvee en entier sur `Nat`
sans fraction, plus deux temoins calcules par `decide`.

## Architecture honnete

* **Modele** : `n` joueurs atomiques, aretes `E` (type fini), pente `a e`
  (cout de `e` sous charge `x` : `a e * x`), strategies = ensembles finis
  d'aretes. Tout vit dans `Nat` : aucune fraction, aucun `Real`.
* **Potentiel de Rosenthal, forme doublee** `Phi' = sum_e a_e x_e (x_e + 1)`
  (le potentiel classique `sum_e a_e x_e^2 / 2` sans division par 2).
  Les equilibres de Nash sont exactement les points ou toute deviation
  unite ne peut pas decroitre `Phi'` : la forme doublee la rend **entiere**.
* **Theoremes** :
  - `potential_exchange` : identite d'exactitude — pour une deviation
    unilaterale, `Phi'` varie exactement comme **deux fois** le cout du
    joueur deviant (c'est le facteur 2 qui donne la borne 2).
  - `minPotential_is_nash` : un minimiseur du potentiel sur les profils
    jouables est un equilibre de Nash.
  - `cost_minPotential_le_two` : la chaine de Rosenthal
    `C(sigma-hat) <= Phi'(sigma-hat) <= Phi'(tau) <= 2 C(tau)` pour tout
    profil jouable `tau` — l'equilibre potentiel-minimal coute au plus
    **deux fois** l'optimum social.
* **Temoin 1** (`w2Good` / `w2Bad`, `decide`) : une instance a 2 joueurs
  ou le **pire** equilibre de Nash coute exactement 2 fois l'optimum —
  le facteur 2 n'est pas un artefact de preuve.
* **Temoin 2** (`w3Bad`, `decide`) : une instance a 3 joueurs avec deux
  equilibres de Nash, dont un a 15/7 > 2 fois l'optimum — la borne
  elementaire couvre l'equilibre **potentiel-minimal**, pas tous les
  equilibres (la borne affine generale 5/2 de Christodoulou-Koutsoupias
  2005 demande des arguments de lissegite hors scope de ce module).

## References

* Rosenthal (1973), *A class of games possessing pure-strategy Nash
  equilibria*, Int. J. Game Theory 2.
* Christodoulou, Koutsoupias (2005), *On the price of anarchy and
  stability of correlated equilibria of linear congestion games*,
  ESA 2005 (borne 5/2 pour tous les equilibres, non prouvee ici).
* Roughgarden, Tardos (2002), borne 4/3 non-atomique — see le carnet
  Python 04h pour la version flux.

Le carnet Python mesure la version non-atomique (Pigou, 4/3) ; ce module
prouve la version atomique elementaire (2). Le corps de l'issue decrit un
« Pigou a deux aretes » : sur des aretes **paralleles purement lineaires**
l'anarchie est en fait nulle (l'exercice 1 du carnet le fait verifier par
enumeration), le temoin 2-aretes ci-dessus utilise trois aretes avec des
strategies emboitees `{e0}` / `{e1, e2}` — c'est l'emboitement, pas le
nombre d'aretes, qui cree l'anarchie.
-/

namespace CongestionGames

variable {E : Type} [Fintype E] [DecidableEq E] {n : ℕ}

/-! ## Modele : charges, couts, potentiel -/

/-- Charge de l'arete `e` sous le profil `sigma` : nombre de joueurs dont la
strategie courante contient `e`. -/
def load (σ : Fin n → Finset E) (e : E) : ℕ :=
  (Finset.univ.filter (fun i => e ∈ σ i)).card

/-- Cout individuel du joueur `i` sous `sigma` : somme des latences des
aretes de sa strategie, chacune a la charge courante. -/
def playerCost (a : E → ℕ) (σ : Fin n → Finset E) (i : Fin n) : ℕ :=
  ∑ e ∈ σ i, a e * load σ e

/-- Cout social (latence totale) : `sum_e a_e * x_e^2`. C'est la somme des
couts individuels : chaque arete `e` contribue `x_e` fois sa latence
`a_e * x_e`. -/
def socialCost (a : E → ℕ) (σ : Fin n → Finset E) : ℕ :=
  ∑ e, a e * load σ e * load σ e

/-- Potentiel de Rosenthal sous forme doublee (entiere) :
`Phi' = sum_e a_e * x_e * (x_e + 1)`. Le potentiel classique vaut
`Phi' / 2` ; la forme doublee evite toute fraction. -/
def potential (a : E → ℕ) (σ : Fin n → Finset E) : ℕ :=
  ∑ e, a e * load σ e * (load σ e + 1)

/-! ## Charges apres une deviation unilaterale -/

/-- L'arete gagnee par la deviation de `i` vers `s` voit sa charge
augmenter d'un. -/
lemma load_update_of_mem_of_not_mem (σ : Fin n → Finset E) (i : Fin n) (s : Finset E)
    (e : E) (hes : e ∈ s) (heσ : e ∉ σ i) :
    load (Function.update σ i s) e = load σ e + 1 := by
  have hset : (Finset.univ.filter (fun j => e ∈ Function.update σ i s j))
      = insert i (Finset.univ.filter (fun j => e ∈ σ j)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Function.update_apply, Finset.mem_insert]
    by_cases h : j = i
    · rw [h]
      simp [hes, heσ]
    · simp [h]
  have hnotmem : i ∉ Finset.univ.filter (fun j => e ∈ σ j) := by
    intro hmem
    exact heσ (Finset.mem_filter.mp hmem).2
  simp only [load, hset, Finset.card_insert_of_notMem hnotmem]

/-- L'arete perdue par la deviation de `i` vers `s` voit sa charge
diminuer d'un. -/
lemma load_update_of_mem_of_not_mem' (σ : Fin n → Finset E) (i : Fin n) (s : Finset E)
    (e : E) (heσ : e ∈ σ i) (hes : e ∉ s) :
    load (Function.update σ i s) e + 1 = load σ e := by
  have hset : (Finset.univ.filter (fun j => e ∈ σ j))
      = insert i (Finset.univ.filter (fun j => e ∈ Function.update σ i s j)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Function.update_apply, Finset.mem_insert]
    by_cases h : j = i
    · rw [h]
      simp [heσ, hes]
    · simp [h]
  have hnotmem : i ∉ Finset.univ.filter (fun j => e ∈ Function.update σ i s j) := by
    intro hmem
    have hmem' : e ∈ Function.update σ i s i := (Finset.mem_filter.mp hmem).2
    rw [Function.update_self] at hmem'
    exact hes hmem'
  simp only [load, hset, Finset.card_insert_of_notMem hnotmem]

/-- Une arete soit present dans les deux strategies, soit absente des
deux, garde sa charge. -/
lemma load_update_eq_of_iff (σ : Fin n → Finset E) (i : Fin n) (s : Finset E)
    (e : E) (h : e ∈ σ i ↔ e ∈ s) :
    load (Function.update σ i s) e = load σ e := by
  have hset : (Finset.univ.filter (fun j => e ∈ Function.update σ i s j))
      = (Finset.univ.filter (fun j => e ∈ σ j)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Function.update_apply]
    by_cases hj : j = i
    · rw [hj, if_pos rfl]
      exact h.symm
    · rw [if_neg hj]
  simp only [load, hset]

/-! ## Identite d'exactitude du potentiel -/

/-- **Exactitude du potentiel de Rosenthal** : lorsque le joueur `i` devie
de `sigma i` vers `s`, le potentiel double `Phi'` croit exactement comme
deux fois le cout du joueur. C'est le coeur de la borne 2 : le potentiel
double est le potentiel « exact » des deviations. -/
theorem potential_exchange (a : E → ℕ) (σ : Fin n → Finset E) (i : Fin n) (s : Finset E) :
    potential a (Function.update σ i s) + 2 * playerCost a σ i
      = potential a σ + 2 * playerCost a (Function.update σ i s) i := by
  have expand :
      2 * playerCost a σ i
        = ∑ e ∈ Finset.univ, (if e ∈ σ i then 2 * (a e * load σ e) else 0) := by
    have h1 : ∑ e ∈ σ i, (if e ∈ σ i then 2 * (a e * load σ e) else 0)
        = ∑ e ∈ Finset.univ, (if e ∈ σ i then 2 * (a e * load σ e) else 0) :=
      Finset.sum_subset (Finset.subset_univ _) (fun e _ he => by simp [he])
    rw [playerCost, Finset.mul_sum, ← h1]
    exact Finset.sum_congr rfl fun _ he => (if_pos he).symm
  have expand' :
      2 * playerCost a (Function.update σ i s) i
        = ∑ e ∈ Finset.univ,
            (if e ∈ s then 2 * (a e * load (Function.update σ i s) e) else 0) := by
    have h1' : ∑ e ∈ s, (if e ∈ s then 2 * (a e * load (Function.update σ i s) e) else 0)
        = ∑ e ∈ Finset.univ,
            (if e ∈ s then 2 * (a e * load (Function.update σ i s) e) else 0) :=
      Finset.sum_subset (Finset.subset_univ _) (fun e _ he => by simp [he])
    rw [playerCost, Finset.mul_sum, ← h1']
    exact Finset.sum_congr (by simp) fun _ he => (if_pos he).symm
  simp only [potential, expand, expand']
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h1 : e ∈ σ i <;> by_cases h2 : e ∈ s
  · -- arete commune : charge inchangee
    have hload : load (Function.update σ i s) e = load σ e :=
      load_update_eq_of_iff σ i s e ⟨fun _ => h2, fun _ => h1⟩
    simp [hload, h1, h2]
  · -- arete perdue : charge x -> x - 1
    have hload : load (Function.update σ i s) e + 1 = load σ e :=
      load_update_of_mem_of_not_mem' σ i s e h1 h2
    have hx : load σ e = load (Function.update σ i s) e + 1 := by omega
    simp only [h1, h2, if_true, if_false]
    rw [hx]
    ring
  · -- arete gagnee : charge x -> x + 1
    have hload : load (Function.update σ i s) e = load σ e + 1 :=
      load_update_of_mem_of_not_mem σ i s e h2 h1
    simp only [h1, h2, if_true, if_false]
    rw [hload]
    ring
  · -- arete absente des deux : charge inchangee
    have hload : load (Function.update σ i s) e = load σ e :=
      load_update_eq_of_iff σ i s e ⟨fun h => (h1 h).elim, fun h => (h2 h).elim⟩
    simp [hload, h1, h2]

/-! ## Equilibres et la borne 2 -/

/-- `sigma` est un profil jouable : chaque joueur utilise une strategie
disponible. -/
def PlaysIn (S : Fin n → Finset (Finset E)) (σ : Fin n → Finset E) : Prop :=
  ∀ i, σ i ∈ S i

/-- `sigma` est un equilibre de Nash : aucune deviation unilaterale
disponible ne diminue strictement le cout du deviant. -/
def IsNash (a : E → ℕ) (S : Fin n → Finset (Finset E)) (σ : Fin n → Finset E) : Prop :=
  ∀ i, ∀ s ∈ S i, playerCost a σ i ≤ playerCost a (Function.update σ i s) i

/-- Une deviation preserve la jouabilite. -/
lemma playsIn_update (S : Fin n → Finset (Finset E)) {σ : Fin n → Finset E}
    (hσ : PlaysIn S σ) (i : Fin n) (s : Finset E) (hs : s ∈ S i) :
    PlaysIn S (Function.update σ i s) := by
  intro j
  by_cases h : j = i
  · subst h; simpa [Function.update_self] using hs
  · simpa [Function.update_of_ne h] using hσ j

/-- **Le minimiseur du potentiel est un equilibre de Nash.** Si une
deviation strictement benefique existait, l'identite d'exactitude
`potential_exchange` ferait decroitre le potentiel — contredisant la
minimalite. -/
theorem minPotential_isNash (a : E → ℕ) (S : Fin n → Finset (Finset E))
    {σh : Fin n → Finset E}
    (hσh : PlaysIn S σh)
    (hmin : ∀ τ, PlaysIn S τ → potential a σh ≤ potential a τ) :
    IsNash a S σh := by
  intro i s hs
  by_contra hstrict
  simp only [not_le] at hstrict
  have hex := potential_exchange a σh i s
  have hpot : potential a (Function.update σh i s) < potential a σh := by omega
  have hmin' := hmin (Function.update σh i s) (playsIn_update S hσh i s hs)
  omega

/-- Maillon 1 de la chaine : le cout social est majore par le potentiel
double, arete par arete (`x^2 <= x * (x+1)`). -/
lemma socialCost_le_potential (a : E → ℕ) (σ : Fin n → Finset E) :
    socialCost a σ ≤ potential a σ :=
  Finset.sum_le_sum fun e _ => Nat.mul_le_mul_left _ (Nat.le_succ _)

/-- Maillon 3 de la chaine : le potentiel double est majore par deux fois
le cout social, arete par arete (`x * (x+1) <= 2 * x^2`). -/
lemma potential_le_two_socialCost (a : E → ℕ) (σ : Fin n → Finset E) :
    potential a σ ≤ 2 * socialCost a σ := by
  have key : ∀ x : ℕ, x * (x + 1) ≤ 2 * x * x := by
    intro x
    rcases Nat.eq_zero_or_pos x with h | h
    · subst h; simp
    · have h2 : x + 1 ≤ x + x := by omega
      calc x * (x + 1) ≤ x * (x + x) := Nat.mul_le_mul_left _ h2
        _ = 2 * x * x := by ring
  calc potential a σ
      = ∑ e, a e * (load σ e * (load σ e + 1)) :=
        Finset.sum_congr rfl fun e _ => by ring
    _ ≤ ∑ e, a e * (2 * load σ e * load σ e) :=
        Finset.sum_le_sum fun e _ => Nat.mul_le_mul_left _ (key _)
    _ = 2 * socialCost a σ := by
        rw [socialCost, Finset.mul_sum]
        exact Finset.sum_congr rfl fun e _ => by ring

/-- **Borne elementaire 2 du prix de l'anarchie (Rosenthal)** : pour tout
jeu de congestion atomique a couts lineaires, l'equilibre minimisant le
potentiel coute au plus deux fois l'optimum social. La chaine complete :
`C(sigma-hat) <= Phi'(sigma-hat) <= Phi'(tau) <= 2 C(tau)`. -/
theorem cost_minPotential_le_two (a : E → ℕ) (S : Fin n → Finset (Finset E))
    {σh τ : Fin n → Finset E}
    (hσh : PlaysIn S σh)
    (hmin : ∀ τ', PlaysIn S τ' → potential a σh ≤ potential a τ')
    (hτ : PlaysIn S τ) :
    socialCost a σh ≤ 2 * socialCost a τ :=
  Nat.le_trans (socialCost_le_potential a σh)
    (Nat.le_trans (hmin τ hτ) (potential_le_two_socialCost a τ))

/-! ## Temoin 1 : l'anarchie atteint exactement 2 (decide) -/

/-- Pentes du temoin a 2 joueurs : `e0` autoroute chere, `e1` route lente,
`e2` contournement lent. -/
def w2a : Fin 3 → ℕ := ![2, 1, 3]

/-- Strategies du temoin : les deux joueurs peuvent prendre `e0` seuls,
ou l'emboiter avec l'autre (`P2` peut combiner `e1` et `e2`). -/
def w2S : Fin 2 → Finset (Finset (Fin 3)) :=
  ![{{0}, {1}}, {{0}, {1, 2}}]

/-- L'equilibre coordonne : `P1` prend `e1`, `P2` prend `e0`. Cout 3,
potentiel 6 (minimal). -/
def w2Good : Fin 2 → Finset (Fin 3) := ![{1}, {0}]

/-- L'equilibre anarchique : chacun prefere son chemin court, `P2` emboite
`e1` et `e2`. Cout 6, potentiel 12. -/
def w2Bad : Fin 2 → Finset (Fin 3) := ![{0}, {1, 2}]

theorem w2Good_playsIn : PlaysIn w2S w2Good := by unfold PlaysIn; decide

theorem w2Bad_playsIn : PlaysIn w2S w2Bad := by unfold PlaysIn; decide

/-- Les deux profils temoins sont des equilibres de Nash (enumeration
decidable des deviations). -/
theorem w2Good_isNash : IsNash w2a w2S w2Good := by unfold IsNash playerCost load; decide

theorem w2Bad_isNash : IsNash w2a w2S w2Bad := by unfold IsNash playerCost load; decide

/-- L'equilibre coordonne est l'optimum social (enumeration exhaustive des
profils jouables). -/
theorem w2Good_optimal : ∀ τ, PlaysIn w2S τ → socialCost w2a w2Good ≤ socialCost w2a τ := by
  unfold PlaysIn socialCost load; decide

theorem w2Good_potential_min : ∀ τ, PlaysIn w2S τ → potential w2a w2Good ≤ potential w2a τ := by
  unfold PlaysIn potential load; decide

/-- **Le facteur 2 est atteint exactement** : le pire equilibre de Nash
coute exactement deux fois l'optimum sur cette instance a deux joueurs. -/
theorem witness_ratio_exactly_two :
    IsNash w2a w2S w2Good ∧ IsNash w2a w2S w2Bad
      ∧ socialCost w2a w2Bad = 2 * socialCost w2a w2Good := by
  refine ⟨w2Good_isNash, w2Bad_isNash, ?_⟩
  unfold socialCost load; decide

/-! ## Temoin 2 : 15/7 — la borne ne couvre pas tous les equilibres -/

/-- Pentes du temoin a 3 joueurs. -/
def w3a : Fin 3 → ℕ := ![3, 1, 3]

/-- Strategies du temoin : trois joueurs, deux familles d'aretes
emboitees. -/
def w3S : Fin 3 → Finset (Finset (Fin 3)) :=
  ![{{0}, {1}}, {{0}, {1, 2}}, {{2}, {0, 1}}]

/-- L'optimum (equilibre potentiel-minimal) : cout 7. -/
def w3Good : Fin 3 → Finset (Fin 3) := ![{1}, {0}, {2}]

/-- Le pire equilibre de Nash : cout 15 — strictement plus que deux fois
l'optimum (14). -/
def w3Bad : Fin 3 → Finset (Fin 3) := ![{1}, {1, 2}, {0, 1}]

theorem w3Good_playsIn : PlaysIn w3S w3Good := by unfold PlaysIn; decide

theorem w3Bad_playsIn : PlaysIn w3S w3Bad := by unfold PlaysIn; decide

theorem w3Good_isNash : IsNash w3a w3S w3Good := by unfold IsNash playerCost load; decide

theorem w3Bad_isNash : IsNash w3a w3S w3Bad := by unfold IsNash playerCost load; decide

set_option maxRecDepth 20000 in
theorem w3Good_optimal : ∀ τ, PlaysIn w3S τ → socialCost w3a w3Good ≤ socialCost w3a τ := by
  unfold PlaysIn socialCost load; decide

/-- **15/7 > 2** : cette instance possede deux equilibres de Nash, le pire
coute 15 contre un optimum de 7. La borne elementaire 2 est donc une
affirmation sur l'equilibre **potentiel-minimal** — l'hypothese n'est pas
decorative, et la borne 5/2 pour tous les equilibres (Christodoulou-
Koutsoupias 2005) demande d'autres outils (lissegite). -/
theorem witness_beyond_two :
    IsNash w3a w3S w3Good ∧ IsNash w3a w3S w3Bad
      ∧ 2 * socialCost w3a w3Good < socialCost w3a w3Bad := by
  refine ⟨w3Good_isNash, w3Bad_isNash, ?_⟩
  unfold socialCost load; decide

end CongestionGames
