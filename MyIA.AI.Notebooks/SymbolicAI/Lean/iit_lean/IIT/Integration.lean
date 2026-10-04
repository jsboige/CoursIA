/-
! # Intégration par coupes — proxy relationnel (Phase 1)

Premier module du premier lake Lean de la série IIT (Epic Aaronson #16781,
veine 5 — « l'objet qui a mordu IIT, en Lean si possible »). Sous-grain #18599.

Ce qui est formalisé ici est un **proxy relationnel de décomposition par
coupe**, pas une version de Φ (voir le grade ci-dessous). Un système
déterministe à `n` éléments est une fonction d'états ; une coupe le partage en
deux côtés non vides ; la coupe est *indépendante* si l'image du système est
exactement le produit des images de ses parties. La critique d'Aaronson
(construire un objet à intégration énorme et à comportement trivial) devient
un **couple de théorèmes** :

* `cutIndep_of_sides_independent` — un système dont les deux moitiés évoluent
  indépendamment l'une de l'autre est **décomposable** ;
* `broadcast_integrated` — le système *broadcast-parité* (chaque élément prend
  la parité de l'état global) est **intégré pour toute coupe**, alors que sa
  dynamique est triviale : `broadcast_two_cycle` montre que toute orbite
  atteint un point fixe en deux pas.

**Grade (la sur-montée interdite)** : le proxy mesure la décomposition
déterministe de l'image. Il ne capture ni l'information effective sous
perturbation, ni la partition minimale au sens MIP, ni une quelconque valeur
numérique de Φ. La cardinalité quantitative (`|imA| · |imB| - |im f|`) est
renvoyée en Phase 2. La source de la critique est un billet de blog (2014),
pas une publication formelle : ce lake **crée** l'objet formel, il n'en est
pas une transcription.

Sans dépendance Mathlib : les preuves sont des témoins constructifs sur `Fin`,
`Bool` et `xor`, aucune arithmétique cardinale n'est nécessaire.
-/

namespace IIT

/-- Un état d'un système à `n` éléments : une valuation booléenne des éléments. -/
abbrev State (n : Nat) := Fin n → Bool

/-- Système déterministe : matrice de transition sous forme de fonction d'états. -/
abbrev System (n : Nat) := State n → State n

/-- Une coupe non triviale d'un système à `n` éléments : chaque côté porte au moins un élément. -/
structure Cut (n : Nat) where
  /-- `sel i = true` place l'élément `i` côté A, `false` côté B. -/
  sel : Fin n → Bool
  /-- Le côté A est non vide. -/
  ha : ∃ i, sel i = true
  /-- Le côté B est non vide. -/
  hb : ∃ i, sel i = false

/-- Motif du côté A d'un état : les bits A préservés, les bits B mis à `false`. -/
def projT {n : Nat} (c : Cut n) (s : State n) : State n :=
  fun i => if c.sel i then s i else false

/-- Motif du côté B d'un état : les bits B préservés, les bits A mis à `false`. -/
def projF {n : Nat} (c : Cut n) (s : State n) : State n :=
  fun i => if c.sel i then false else s i

/-- Une coupe est **indépendante** pour un système si tout couple de motifs
réalisables séparément est réalisable ensemble : l'image du système est le
produit des images de ses deux parties. -/
def cutIndep {n : Nat} (c : Cut n) (f : System n) : Prop :=
  ∀ x y : State n, ∃ z : State n,
    projT c (f z) = projT c (f x) ∧ projF c (f z) = projF c (f y)

/-- Un système est **décomposable** s'il existe une coupe indépendante. -/
def decomposable {n : Nat} (f : System n) : Prop := ∃ c : Cut n, cutIndep c f

/-- Un système est **intégré** si aucune coupe n'est indépendante. -/
def integrated {n : Nat} (f : System n) : Prop := ¬ decomposable f

/-! ## Théorème A — les systèmes produits sont décomposables

Si chaque côté d'une coupe n'influence que lui-même (les bits de sortie côté A
ne dépendent que des bits d'entrée côté A, idem côté B), alors la coupe est
indépendante : le témoin `z` mélange simplement les entrées des deux côtés. -/

/-- Décomposition des systèmes à dynamiques latérales indépendantes :
le mélange des entrées réalise tout couple de motifs réalisables séparément. -/
theorem cutIndep_of_sides_independent {n : Nat} (c : Cut n) (f : System n)
    (hA : ∀ s s' : State n, (∀ i, c.sel i = true → s i = s' i) →
      ∀ i, c.sel i = true → f s i = f s' i)
    (hB : ∀ s s' : State n, (∀ i, c.sel i = false → s i = s' i) →
      ∀ i, c.sel i = false → f s i = f s' i) :
    cutIndep c f := by
  intro x y
  refine ⟨fun i => if c.sel i then x i else y i, ?_, ?_⟩
  · funext i
    by_cases h : c.sel i = true
    · simp only [projT, h]
      exact hA _ _ (fun j hj => by simp only [hj, if_true]) i h
    · simp [projT, h]
  · funext i
    by_cases h : c.sel i = false
    · simp only [projF, h]
      exact hB _ _ (fun j hj => by simp [hj]) i h
    · simp [projF, h]

/-- Énoncé figé n° 1 de #18599 : un système dont les deux moitiés évoluent
indépendamment (relativement à une coupe) est décomposable. Alias de
`cutIndep_of_sides_independent` sous le nom figé dans l'issue. -/
theorem product_decomposable {n : Nat} (c : Cut n) (f : System n)
    (hA : ∀ s s' : State n, (∀ i, c.sel i = true → s i = s' i) →
      ∀ i, c.sel i = true → f s i = f s' i)
    (hB : ∀ s s' : State n, (∀ i, c.sel i = false → s i = s' i) →
      ∀ i, c.sel i = false → f s i = f s' i) :
    decomposable f :=
  ⟨c, cutIndep_of_sides_independent c f hA hB⟩

/-! ## Le système broadcast-parité

Chaque élément de l'état suivant prend la **parité** de l'état courant :
l'information globale est diffusée partout, et l'image du système se réduit à
deux états constants. C'est la forme la plus simple de « l'objet qui a mordu
IIT » : intégration maximale au sens du proxy, comportement trivial. -/

/-- Parité d'un état (nombre de bits vrais modulo 2), par récurrence sur `n` :
tête d'indice 0 puis queue décalée par `Fin.succ`. -/
def parity : (n : Nat) → State n → Bool
  | 0, _ => false
  | n + 1, s => xor (s ⟨0, Nat.succ_pos n⟩) (parity n (fun i => s i.succ))

/-- Le système broadcast-parité : l'état suivant est uniformément égal à la
parité de l'état courant. -/
def broadcast {n : Nat} : System n := fun s => fun _ => parity n s

/-- La parité d'un état tout-faux est nulle, par récurrence structurelle
mirroir de `parity` (la récurrence sur `n` seule ne généralise pas `s`). -/
theorem parity_allFalse : ∀ (n : Nat) (s : State n), (∀ i, s i = false) →
    parity n s = false
  | 0, _, _ => rfl
  | n + 1, s, h => by
      rw [parity, h ⟨0, Nat.succ_pos n⟩,
        parity_allFalse n (fun i => s i.succ) (fun i => h i.succ)]
      rfl

/-- La parité d'un état tout-vrai code l'imparité de `n` (sans lemme
`Nat.mod` dédié : la bascule est close par `omega` sur `% 2`). -/
theorem parity_allTrue {n : Nat} :
    parity n (fun _ => true) = decide (n % 2 = 1) := by
  induction n with
  | zero => rfl
  | succ m ih =>
      rw [parity]
      show xor true (parity m (fun _ => true)) = decide ((m + 1) % 2 = 1)
      rw [ih]
      cases hm : m % 2 with
      | zero =>
          have h1 : (m + 1) % 2 = 1 := by omega
          simp [h1]
      | succ k =>
          have hk : k = 0 := by omega
          have h1 : (m + 1) % 2 = 0 := by omega
          simp [hk, h1]

/-- Le bit unique (indice 0) rend la parité impaire, quelle que soit la taille
(formulation à `decide` explicite : la coercion Prop→Bool ne s'insère pas
dans un `have` non typé vers `Bool`). -/
theorem parity_oneHot_zero : ∀ (n : Nat), 0 < n →
    parity n (fun j => decide (j.val = 0)) = true
  | 0, h => absurd h (Nat.not_lt_zero 0)
  | n + 1, _ => by
      have hp : parity n (fun i : Fin n =>
          decide ((i.succ : Fin (n + 1)).val = 0)) = false :=
        parity_allFalse _ _ (fun i => by simp)
      rw [parity, hp]
      rfl

/-- Parité d'un état constant : nulle si le bit est faux, parité de `n` sinon. -/
theorem parity_const (n : Nat) (b : Bool) :
    parity n (fun _ => b) = (b && decide (n % 2 = 1)) := by
  cases b with
  | false => exact parity_allFalse _ _ (fun _ => rfl)
  | true => simp [parity_allTrue]

/-! ## Théorème B — le broadcast est intégré pour toute coupe -/

/-- **L'objet qui a mordu IIT, en théorème.** Le broadcast-parité est intégré
pour toute coupe : quel que soit le partage non trivial, le couple de
motifs (côté A diffusé vrai, côté B diffusé faux) n'est jamais réalisé
ensemble — alors que chaque motif l'est séparément. Intégration universelle,
comportement trivial. -/
theorem broadcast_integrated {n : Nat} : integrated (broadcast (n := n)) := by
  intro ⟨c, hc⟩
  obtain ⟨i₀, hi₀⟩ := c.ha
  obtain ⟨j₀, hj₀⟩ := c.hb
  have hn : 0 < n := Fin.pos i₀
  have hx := hc (fun j => decide (j.val = 0)) (fun _ => false)
  obtain ⟨z, hzT, hzF⟩ := hx
  have hT : parity n z = true := by
    have h0 := congrFun hzT i₀
    simp [projT, hi₀, broadcast] at h0
    rw [h0, parity_oneHot_zero n hn]
  have hF : parity n z = false := by
    have h1 := congrFun hzF j₀
    simp [projF, hj₀, broadcast] at h1
    rw [h1, parity_allFalse n (fun _ => false) (fun _ => rfl)]
  rw [hF] at hT
  exact absurd hT (by simp)

/-! ## Théorème C — la dynamique du broadcast est triviale -/

/-- Toute orbite du broadcast atteint un point fixe en deux pas : la dynamique
est triviale bien que le système soit intégré pour toute coupe. Le contraste
avec `broadcast_integrated` est le contenu formel de la critique. -/
theorem broadcast_two_cycle {n : Nat} (s : State n) :
    broadcast (broadcast (broadcast s)) = broadcast (broadcast s) := by
  funext i
  show parity n (fun _ => parity n (fun _ => parity n s))
     = parity n (fun _ => parity n s)
  rw [parity_const, parity_const]
  simp

/-- Énoncé figé n° 3 de #18599 : la dynamique du broadcast est triviale.
Alias de `broadcast_two_cycle` sous le nom figé dans l'issue. -/
theorem broadcast_trivial_dynamics {n : Nat} (s : State n) :
    broadcast (broadcast (broadcast s)) = broadcast (broadcast s) :=
  broadcast_two_cycle s

end IIT
