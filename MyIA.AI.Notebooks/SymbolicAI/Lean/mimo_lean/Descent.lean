/-!
# Descente à flips — Phase 1 : squelette de la Proposition 9.1 (cœur, sans Mathlib)

Ce module formalise la **colonne vertébrale combinatoire** de l'algorithme de
détection MIMO par flips de coordonnées (Papailiopoulos, 2026 — issue #10984) :
une descente sur un espace d'états où chaque flip **accepté** fait décroître
strictement le coût. Le fichier est volontairement **sans aucune dépendance**
(cœur Lean 4 uniquement) : la fonction objectif réelle (Lemme 11.1) et
l'analyse LMMSE (Lemme 5.1) arrivent en Phase 2 (`Objective.lean`, Mathlib) ;
la converse §11 en Phase 3 via le lake externe SLT.

Le théorème phare `descent_target_before_ceiling` est la forme abstraite de la
Proposition 9.1 du papier : sous (i) stricte décroissance du coût à chaque
flip accepté, (ii) confinement du coût dans une barrière `B`, et (iii) absence
de point bloquant hors de la cible, tout run **terminal** atteint la cible en
un nombre de flips **strictement inférieur au plafond `M_N`**.

Les quatres ingrédients de la preuve, chacun intéressant pédagogiquement :

1. `run_tail_cost_lt` — la décroissance stricte se propage du pas local à
   toute la queue du run (récurrence sur la structure du run) ;
2. `run_nodup` — un run ne revisite jamais un état (sinon le coût serait
   strictement inférieur à lui-même) ;
3. `run_length_le_cost` — le nombre de flips d'un run démarrant en `s₀` est
   majoré par `cost s₀` (le « budget de descente ») ;
4. `descent_flips_le_barrier` — sous la barrière de confinement `B`, le
   nombre de flips est majoré par `B`, donc strictement par `M_N > B`.
-/

namespace Mimo

variable {σ : Type} {accept : σ → σ → Prop} {cost : σ → Nat} {target : σ → Prop}

/-- Un **run** de l'algorithme : suite d'états dont chaque paire consécutive
est un flip **accepté** (relation `accept`). Le cas `single` couvre le run
réduit à l'état initial ; `nil` le run vide (pratique pour les récurrences). -/
inductive Run (accept : σ → σ → Prop) : List σ → Prop
  | nil : Run accept []
  | single (s : σ) : Run accept [s]
  | cons (s t : σ) (rest : List σ) (h : accept s t) (hr : Run accept (t :: rest)) :
      Run accept (s :: t :: rest)

/-- Dernier état d'un run démarrant en `s₀` : là où l'algorithme s'arrête. -/
def lastState : σ → List σ → σ
  | s, [] => s
  | _, t :: rest => lastState t rest

/-! ## Lemme 1 — la décroissance stricte se propage à toute la queue -/

/-- Si chaque flip accepté décroît strictement le coût, alors le coût de tout
état visité après `s₀` est strictement inférieur à `cost s₀`. C'est la clé de
la non-révisite et du budget de descente. -/
theorem run_tail_cost_lt (hstrict : ∀ s t, accept s t → cost t < cost s) :
    ∀ (rest : List σ) (s₀ : σ), Run accept (s₀ :: rest) →
      ∀ x ∈ rest, cost x < cost s₀ := by
  intro rest
  induction rest with
  | nil => intro _ _ x hx; cases hx
  | cons u rest' ih =>
    intro s₀ hL x hx
    cases hL with
    | cons _ _ _ h hr =>
      cases List.mem_cons.1 hx with
      | inl hxu => subst hxu; exact hstrict _ _ h
      | inr hx' => exact Nat.lt_trans (ih u hr x hx') (hstrict _ _ h)

/-! ## Lemme 2 — un run ne revisite jamais un état -/

/-- Un run à coût strictement décroissant est sans répétition : l'espace
d'états peut être infini, le run lui-même vit dans un ensemble fini d'états
distincts (autant de visites que de valeurs de coût strictement décroissantes). -/
theorem run_nodup (hstrict : ∀ s t, accept s t → cost t < cost s)
    {L : List σ} (hL : Run accept L) : L.Nodup := by
  induction hL with
  | nil => exact List.nodup_nil
  | single s => simp
  | cons s u rest h hr ih =>
    refine List.nodup_cons.2 ⟨?_, ih⟩
    intro hmem
    have hrun : Run accept (s :: u :: rest) := Run.cons s u rest h hr
    have hlt := run_tail_cost_lt hstrict (u :: rest) s hrun s hmem
    exact absurd hlt (Nat.lt_irrefl _)

/-! ## Lemme 3 — le budget de descente majore le nombre de flips -/

/-- Le nombre de flips d'un run démarrant en `s₀` est au plus `cost s₀` :
chaque flip consomme au moins une unité de coût (valeurs dans `Nat`), et le
coût ne peut pas descendre sous zéro. -/
theorem run_length_le_cost (hstrict : ∀ s t, accept s t → cost t < cost s) :
    ∀ (rest : List σ) (s₀ : σ), Run accept (s₀ :: rest) →
      rest.length ≤ cost s₀ := by
  intro rest
  induction rest with
  | nil => intro _ _; exact Nat.zero_le _
  | cons u rest' ih =>
    intro s₀ hL
    cases hL with
    | cons _ _ _ h hr =>
      have h1 : rest'.length ≤ cost u := ih u hr
      have h2 : cost u < cost s₀ := hstrict _ _ h
      have h3 : (u :: rest').length = rest'.length + 1 := rfl
      omega

/-! ## Proposition 9.1 — confinement, plafond de flips, atteinte de la cible -/

/-- **Barrière de confinement** : si le coût de tout état visité reste sous
`B`, alors le nombre de flips est majoré par `B`. Dans le papier, la barrière
reflète la géométrie du problème (le coût ne s'échappe pas d'une tranche
bornée) ; ici elle est une hypothèse, instanciée en Phase 2. -/
theorem descent_flips_le_barrier (hstrict : ∀ s t, accept s t → cost t < cost s)
    (s₀ : σ) (rest : List σ) (B : Nat)
    (hbarrier : ∀ s ∈ s₀ :: rest, cost s ≤ B)
    (hL : Run accept (s₀ :: rest)) :
    rest.length ≤ B := by
  have h1 := run_length_le_cost hstrict rest s₀ hL
  have h0 := hbarrier s₀ (by simp)
  omega

/-- **Proposition 9.1 (forme abstraite, squelette Phase 1).** Soit un run
**terminal** (aucun flip accepté n'échappe du dernier état) sous les trois
hypothèses du papier :

- `hstrict` — chaque flip accepté décroît strictement le coût (Lemme 11.1 en
  Phase 2 : le coût d'un flip s'écrit `4·(ρ/N·‖hᵢ‖² + √(ρ/N)·hᵢᵀw)`, et seuls
  les flips diminuant l'objectif sont acceptés) ;
- `hbarrier` — le coût reste confiné sous `B` sur tout le run ;
- `hnostall` — hors de la cible, un flip accepté existe toujours (l'algorithme
  ne se bloque que sur la cible).

Alors le dernier état du run **appartient à la cible**, et le run a utilisé
**strictement moins de `M_N` flips** dès que le plafond `M_N` dépasse la
barrière `B`. C'est exactement la garantie de complexité de l'algorithme :
terminaison dans la cible avant l'épuisement du budget de flips. -/
theorem descent_target_before_ceiling
    (hstrict : ∀ s t, accept s t → cost t < cost s)
    (hnostall : ∀ s : σ, (∀ u, ¬ accept s u) → target s)
    (s₀ : σ) (rest : List σ) (B M_N : Nat)
    (hbarrier : ∀ s ∈ s₀ :: rest, cost s ≤ B)
    (hL : Run accept (s₀ :: rest))
    (hterm : ∀ u, ¬ accept (lastState s₀ rest) u)
    (hceiling : B < M_N) :
    target (lastState s₀ rest) ∧ rest.length < M_N :=
  ⟨hnostall _ hterm,
   Nat.lt_of_le_of_lt (descent_flips_le_barrier hstrict s₀ rest B hbarrier hL) hceiling⟩

end Mimo
