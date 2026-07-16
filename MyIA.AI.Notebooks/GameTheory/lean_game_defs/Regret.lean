/-
  Minimisation du regret et définitions du CFR en Lean 4
  =====================================================

  Définit les structures pour l'apprentissage basé sur le regret dans les jeux :
  - Regret : écart entre le paiement obtenu et le meilleur paiement possible
  - RegretMatching : règle de mise à jour de stratégie à partir des regrets cumulés
  - CFR (Counterfactual Regret Minimization) : algorithme clé pour
    résoudre les jeux à information imparfaite

  Basé sur GameTheory-13-ImperfectInfo-CFR.ipynb

  Note : ce sont des définitions pédagogiques. Une formalisation complète
  nécessiterait la théorie de la mesure et des preuves de convergence
  (non abordées ici).

  ---
  Jumelage i18n : ce module est le FR canonique (sibling pair Pattern A,
  ratifié par user 2026-07-04 sur EPIC #4980). Le miroir anglais vit dans
  `Regret_en.lean` (variante reuse-FR-names : comme `Nash.lean`, `Regret.lean`
  dépend des modules de base partagés `Basic` et `Bayesian`, donc le miroir EN
  les importe et re-déclare ses propres définitions dans `namespace RegretEn`).
  Le corps des définitions, signatures et tactiques est byte-identique entre
  les deux fichiers ; seules les docstrings `/-! ... -/` (titres de section) et
  `/-- ... -/` (docstrings de déclarations) diffèrent, FR dans ce fichier,
  EN dans `Regret_en.lean`.
-/

import Basic
import Bayesian

/-!
## Notions de regret
-/

/-- Regret instantané pour une action : de combien cette action
    aurait été meilleure que ce qui a réellement été joué.

    regret(a) = u(a) - u(a_played)
-/
def instantRegret (payoff : Fin n → Float) (played : Fin n) (action : Fin n) : Float :=
  payoff action - payoff played

/-- Regret cumulé pour chaque action sur T itérations.
    Stocké sous forme d'application de l'indice d'action vers le regret accumulé.
-/
def CumulativeRegret (n : Nat) := Fin n → Float

/-- Initialise un regret nul. -/
def zeroRegret (n : Nat) : CumulativeRegret n := fun _ => 0

/-- Met à jour le regret cumulé avec une nouvelle observation. -/
def updateRegret {n : Nat} (regret : CumulativeRegret n)
    (payoff : Fin n → Float) (played : Fin n) : CumulativeRegret n :=
  fun a => regret a + instantRegret payoff played a

/-!
## Regret matching
-/

/-- Regret matching : convertit les regrets cumulés positifs en une stratégie.

    Pour chaque action a : σ(a) = R+(a) / Σ_a' R+(a')
    où R+ est la partie positive du regret cumulé.

    Si tous les regrets sont non positifs, jouer uniformément.
-/
def regretMatchingStrategy {n : Nat} (regret : CumulativeRegret n) : Fin n → Float :=
  let posRegret (a : Fin n) : Float := max 0 (regret a)
  let total := (List.finRange n).foldl (fun acc a => acc + posRegret a) 0
  if total > 0 then
    fun a => posRegret a / total
  else
    fun _ => (1.0 : Float) / n.toFloat  -- uniforme

/-!
## Regret externe (cohérence de Hannan)
-/

/-- Regret externe : écart entre le paiement réalisé et la meilleure
    action fixe avec le recul.

    R_T = max_a Σ_t u_t(a) - Σ_t u_t(a_t)
-/
def externalRegret (T : Nat) (payoffs : Fin T → (Fin n → Float))
    (played : Fin T → Fin n) : Float :=
  let bestFixed := (List.finRange n).foldl
    (fun acc a => max acc ((List.finRange T).foldl
      (fun s t => s + payoffs t a) 0))
    0
  let realized := (List.finRange T).foldl
    (fun s t => s + payoffs t (played t)) 0
  bestFixed - realized

/-!
## Regret contrefactuel
-/

/-- Regret contrefactuel pour un joueur à un ensemble d'information.

    L'idée clé du CFR : minimiser le regret contrefactuel à chaque
    ensemble d'information indépendamment, et la stratégie moyenne converge
    vers un équilibre de Nash dans les jeux à somme nulle à deux joueurs.

    CFR(I, a) = Σ_z∈Z_I  π_{-i}(z) · (u_i(z, a) - u_i(z, σ(I)))

    où π_{-i} est la probabilité d'atteindre z en excluant le joueur i.
-/
structure CounterfactualRegret where
  /-- L'identifiant de l'ensemble d'information. -/
  infoSet : String
  /-- Le joueur. -/
  player : Nat
  /-- Regret pour chaque action disponible. -/
  actionRegrets : List (String × Float)  -- (nom_action, valeur_regret)
  deriving Repr

/-!
## État du solveur CFR
-/

/-- L'état maintenu par un solveur CFR au fil des itérations. -/
structure CFRState where
  /-- Regret contrefactuel cumulé par ensemble d'information et action. -/
  cumulativeRegret : List (String × List (String × Float))
  /-- Stratégie cumulée (somme des stratégies pondérées par la probabilité d'atteinte). -/
  strategySum : List (String × List (String × Float))
  /-- Nombre d'itérations effectuées. -/
  iterations : Nat
  deriving Repr

/-- Initialise un état CFR vide. -/
def initCFRState : CFRState where
  cumulativeRegret := []
  strategySum := []
  iterations := 0

/-!
## Notions de convergence
-/

/-- Le regret moyen tend vers zéro (ε-équilibre de Nash). -/
def epsilonNash (ε : Float) (externalReg : Float) : Prop :=
  externalReg <= ε

/-- Apprentissage sans regret : le regret externe moyen tend vers zéro.
    Les paiements et les coups sont indexés par `Nat` (horizon infini) ; le regret
    à l'horizon `t` est calculé sur le préfixe des `t` premières rondes.
-/
def noRegret (payoffs : Nat → (Fin n → Float))
    (played : Nat → Fin n) : Prop :=
  ∀ ε > 0, ∃ T0, ∀ t ≥ T0,
    externalRegret t (fun s => payoffs s.val) (fun s => played s.val) / t.toFloat < ε

/-!
## Fictitious play (tiré de GT-17 Section 3)
-/

/-- Fictitious play : chaque joueur joue la meilleure réponse face à la
    distribution empirique des coups passés de l'adversaire.

    Brown (1951) : converge vers l'équilibre de Nash pour :
    - les jeux à somme nulle à 2 joueurs
    - les jeux 2x2
    - les jeux à intérêts identiques
-/
structure FictitiousPlayState (n : Nat) where
  /-- Fréquence empirique des actions de chaque joueur. -/
  actionCounts : Fin n → (Fin m → Nat)
  /-- Nombre de rondes jouées. -/
  rounds : Nat
  -- pas de `deriving Repr` : `actionCounts` est un type fonctionnel, non dérivable

/-- Meilleure réponse face à la distribution empirique de l'adversaire.

    Conceptuellement : argmax_a Σ_{a_{-i}} empiricalDist(a_{-i}) · u_i(a, a_{-i}).
    Dans une formalisation complète, cela utiliserait l'argmax de Mathlib.
-/
def isBestResponseToEmpirical {m : Nat}
    (payoff : Fin 2 → (Fin 2 → Fin m) → Float)
    (empiricalDist : Fin 2 → (Fin m → Float))
    (player : Fin 2) (action : Fin m) : Prop :=
  ∀ other : Fin m,
    let expected := fun a =>
      (List.finRange m).foldl
        (fun acc a' => acc + empiricalDist (if player.val = 0 then 1 else 0) a' *
                       payoff player (fun j => if j = player then a else a'))
        0
    expected action >= expected other
