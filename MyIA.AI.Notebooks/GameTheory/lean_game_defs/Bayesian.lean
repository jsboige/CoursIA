/-
  Définitions de la théorie des jeux bayésienne en Lean 4
  =======================================================

  Définit les structures pour les jeux à information incomplète (Harsanyi) :
  - BayesianGame : jeux avec types privés et croyance commune (prior)
  - TypeStrategy : stratégie conditionnée par le type privé
  - BayesianNashEquilibrium : concept d'équilibre pour l'info incomplète
  - SignalingGame : jeux en deux phases (émetteur/récepteur)
  - InformationSet : partition des nœuds de décision (info imparfaite)

  Basé sur GameTheory-11-BayesianGames.ipynb et
           GameTheory-13-ImperfectInfo-CFR.ipynb

  Note : ce sont des définitions pédagogiques à but d'enseignement.
  Pour une formalisation complète, il faudrait la probabilité mesurée
  et les espaces mesurables de Mathlib.

  ---
  English:
  Bayesian Game Theory Definitions in Lean 4
  ============================================

  Defines structures for games with incomplete information (Harsanyi):
  - BayesianGame: Games with private types and common prior
  - TypeStrategy: Strategy conditioned on private type
  - BayesianNashEquilibrium: Equilibrium concept for incomplete info
  - SignalingGame: Two-phase games (sender/receiver)
  - InformationSet: Partition of decision nodes (imperfect info)

  Based on GameTheory-11-BayesianGames.ipynb and
           GameTheory-13-ImperfectInfo-CFR.ipynb

  Note: These are pedagogical definitions for teaching purposes.
  For a full formalization, one would need measure-theoretic probability
  and measurable spaces from Mathlib.
-/

import Basic

/-!
## Utilitaires (évite la dépendance Mathlib)

---
English:
## Utility (avoids Mathlib dependency)
-/

/-- Met à jour une fonction dépendante à un indice donné.
    Équivalent au `Function.update` de Mathlib mais autonome.
    Utilise l'égalité décidable sur `Fin` pour la comparaison.
    English: Update a dependent function at a given index.
    Equivalent to Mathlib's `Function.update` but self-contained.
    Uses `Fin` decidable equality for comparison. -/
def funUpdate {n : Nat} {β : Fin n → Type} (f : (i : Fin n) → β i)
    (i : Fin n) (x : β i) : (j : Fin n) → β j :=
  fun j => if h : j = i then h ▸ x else f j

/-!
## Espaces de types et croyances

---
English:
## Type Spaces and Beliefs
-/

/-- Un espace de types pour un joueur : l'ensemble des types privés possibles.
    English: A type space for a player: the set of possible private types -/
def TypeSpace (α : Type) := List α

/-- Une croyance commune (prior) sur les profils de types (simplifié : poids uniformes).
    English: A common prior over type profiles (simplified: uniform weights) -/
structure CommonPrior (T : Type) (n : Nat) where
  /-- Profils de types possibles : liste de n-uplets.
      English: Possible type profiles: list of n-tuples -/
  typeProfiles : List (Fin n → T)
  /-- Probabilité de chaque profil (simplifiée en poids rationnel).
      English: Probability of each profile (simplified as rational weight) -/
  weights : List Nat
  /-- Les poids somment à 100 (probabilités mises à l'échelle).
      English: Weights sum to 100 (scaled probabilities) -/
  weightsSum100 : weights.sum = 100 := by decide

/-!
## Structure du jeu bayésien

---
English:
## Bayesian Game Structure
-/

/-- Un jeu bayésien (information incomplète) à types finis.

    Chaque joueur a un type privé tiré d'une croyance commune.
    Les stratégies associent des types à des actions. Les paiements
    dépendent du profil de types complet et du profil d'actions.

    English: A Bayesian (incomplete information) game with finite types.

    Each player has a private type drawn from a common prior.
    Strategies map types to actions. Payoffs depend on the full
    type profile and action profile.
-/
structure BayesianGame (PlayerType : Type) where
  /-- Nombre de joueurs.
      English: Number of players -/
  numPlayers : Nat
  /-- Types possibles pour chaque joueur.
      English: Possible types for each player -/
  typeSet : Fin numPlayers → List PlayerType
  /-- Nombre d'actions disponibles pour chaque joueur.
      English: Number of actions available to each player -/
  numActions : Fin numPlayers → Nat
  /-- Le paiement dépend du profil de types ET du profil d'actions.
      English: Payoff depends on type profile AND action profile -/
  payoff : (i : Fin numPlayers) →
           (types : Fin numPlayers → PlayerType) →
           (actions : (j : Fin numPlayers) → Fin (numActions j)) → Int
  /-- Probabilité a priori (prior) sur les profils de types (simplifié).
      English: Common prior probability over type profiles (simplified) -/
  priorProb : (types : Fin numPlayers → PlayerType) → Float

/-!
## Stratégies conditionnées par le type

---
English:
## Type-Conditioned Strategies
-/

/-- Une stratégie (pure) conditionnée par le type : associe son propre type à une action.
    English: A type-conditioned (pure) strategy: maps own type to an action -/
def TypeStrategy (g : BayesianGame α) (i : Fin g.numPlayers) :=
  α → Fin (g.numActions i)

/-- Un profil de stratégies par type : une par joueur.
    English: A profile of type strategies: one per player -/
def TypeStrategyProfile (g : BayesianGame α) :=
  (i : Fin g.numPlayers) → TypeStrategy g i

/-!
## Paiement espéré (simplifié)

---
English:
## Expected Payoff (Simplified)
-/

/-- Paiement espéré du joueur i étant donné un profil de stratégies par type
    et un profil de types particulier (simplifié : pas d'intégration).

    Dans une formalisation complète, cela impliquerait de sommer sur tous
    les profils de types pondérés par la croyance commune.

    English: Expected payoff for player i given a type strategy profile
    and a particular type profile (simplified: no integration).

    In a full formalization this would involve summing over all
    type profiles weighted by the common prior.
-/
def expectedPayoffBayesian (g : BayesianGame α)
    (profile : TypeStrategyProfile g)
    (types : Fin g.numPlayers → α)
    (i : Fin g.numPlayers) : Int :=
  g.payoff i types (fun j => profile j (types j))

/-!
## Équilibre de Nash bayésien

---
English:
## Bayesian Nash Equilibrium
-/

/-- Équilibre de Nash bayésien : aucun joueur ne peut améliorer en déviant,
    étant donné son type.

    Pour chaque joueur i et chaque type t_i du joueur i, le profil de
    stratégies doit être une meilleure réponse conditionnellement à t_i.
    (Simplifié : vérifié sur un seul profil de types.)

    English: Bayesian Nash Equilibrium: no player can improve by deviating,
    given their type.

    For each player i and each type t_i of player i, the strategy
    profile must be a best response conditional on t_i.
    (Simplified: checks for a single type profile.)
-/
def isBayesianNashEquilibrium (g : BayesianGame α)
    (profile : TypeStrategyProfile g)
    (types : Fin g.numPlayers → α) : Prop :=
  ∀ (i : Fin g.numPlayers) (altStrategy : TypeStrategy g i),
    expectedPayoffBayesian g profile types i >=
    expectedPayoffBayesian g (funUpdate profile i altStrategy) types i

/-!
## Ensembles d'information (information imparfaite)

---
English:
## Information Sets (Imperfect Information)
-/

/-- Un ensemble d'information regroupe des nœuds de décision qu'un joueur ne
    peut pas distinguer. Modélisé comme un ensemble d'historiques de jeu.

    Tiré de GT-13 : « l'ensemble d'information d'un joueur à un moment du jeu
    est l'ensemble des nœuds où il pourrait être, compte tenu de ce qu'il observe. »

    English: An information set groups decision nodes that a player cannot
    distinguish between. Modeled as a set of game histories.

    From GT-13: "A player's information set at any point in the game
    is the set of nodes they might be at, given what they observe."
-/
structure InformationSet where
  /-- Joueur confronté à cet ensemble d'information.
      English: Player who faces this information set -/
  player : Nat
  /-- Historiques possibles (états du jeu) dans cet ensemble.
      English: Possible histories (game states) in this set -/
  nodes : List String
  /-- Actions disponibles dans cet ensemble d'information.
      English: Available actions at this information set -/
  actions : List String

/-- Vérifie si deux historiques appartiennent au même ensemble d'information.
    English: Check if two histories belong to the same information set -/
def sameInfoSet (h1 h2 : String) (iset : InformationSet) : Bool :=
  iset.nodes.contains h1 && iset.nodes.contains h2

/-!
## Jeux de signal (Spence 1973)

---
English:
## Signaling Games (Spence 1973)
-/

/-- Un jeu de signal : l'émetteur observe son type, envoie un message,
    le récepteur observe le message, choisit une action.

    Tiré de GT-11 Section 6 (modèle de signal de Spence).
    Deux joueurs : Émetteur (joueur 0) et Récepteur (joueur 1).

    English: A signaling game: sender observes type, sends message,
    receiver observes message, chooses action.

    From GT-11 Section 6 (Spence signaling model).
    Two players: Sender (player 0) and Receiver (player 1).
-/
structure SignalingGame (MessageType : Type) (ActionResult : Type) where
  /-- Types possibles de l'émetteur.
      English: Possible types of the sender -/
  senderTypes : List MessageType
  /-- Messages que l'émetteur peut envoyer.
      English: Messages the sender can send -/
  messages : List MessageType
  /-- Actions que le récepteur peut entreprendre.
      English: Actions the receiver can take -/
  receiverActions : List ActionResult
  /-- Paiement de l'émetteur : dépend du type, du message envoyé, de l'action du récepteur.
      English: Sender payoff: depends on type, message sent, receiver action -/
  senderPayoff : MessageType → MessageType → ActionResult → Int
  /-- Paiement du récepteur : dépend du type, du message envoyé, de l'action du récepteur.
      English: Receiver payoff: depends on type, message sent, receiver action -/
  receiverPayoff : MessageType → MessageType → ActionResult → Int
  /-- Probabilité a priori de chaque type de l'émetteur.
      English: Prior probability of each sender type -/
  typePrior : MessageType → Float

/-- Stratégie de l'émetteur : type → message.
    English: A sender strategy: type → message -/
def SenderStrategy (_g : SignalingGame α β) := α → α

/-- Stratégie du récepteur : message → action.
    English: A receiver strategy: message → action -/
def ReceiverStrategy (_g : SignalingGame α β) := α → β

/-!
## Enchère au premier prix (tiré de GT-11 Section 5)

---
English:
## First-Price Auction (from GT-11 Section 5)
-/

/-- Une enchère scellée au premier prix avec valeurs privées.

    Chaque enchérisseur a une valorisation privée. Il soumet une offre.
    L'offre la plus élevée gagne et paie son offre.

    English: A first-price sealed-bid auction with private values.

    Each bidder has a private valuation. They submit a bid.
    Highest bid wins and pays their bid.
-/
structure FirstPriceAuction where
  /-- Nombre d'enchérisseurs.
      English: Number of bidders -/
  numBidders : Nat
  /-- Valeur maximale possible.
      English: Maximum possible value -/
  maxValue : Nat
  /-- Stratégie d'enchère : valorisation → offre (simplifié, identique pour tous).
      English: Bidding strategy: valuation → bid (simplified, same for all) -/
  bidStrategy : Nat → Nat
  /-- Vérifie si l'enchère est valide (0 ≤ offre ≤ maxValue).
      English: Check if bid is valid (0 ≤ bid ≤ maxValue) -/
  validBid : (bid : Nat) → Bool := fun bid => bid <= maxValue

/-- Détermine le gagnant de l'enchère étant donné les offres.
    Renvoie l'indice du premier enchérisseur avec l'offre maximale.
    Nécessite n ≥ 1 (au moins un enchérisseur).
    English: Determine winner of auction given bids.
    Returns the index of the first bidder with the maximum bid.
    Requires n ≥ 1 (at least one bidder). -/
def auctionWinner {n : Nat} (h_n : n ≥ 1) (bids : Fin n → Nat) : Fin n :=
  let maxBid := (List.finRange n).foldl (fun acc i => max acc (bids i)) 0
  -- Le premier joueur ayant offert le maximum gagne (départage les égalités)
  match (List.finRange n).find? (fun i => bids i = maxBid) with
  | some i => i
  | none => ⟨0, by omega⟩

/-- Revenu pour l'enchérisseur (l'organisateur de l'enchère).
    English: Revenue for the auctioneer -/
def auctionRevenue {n : Nat} (h_n : n ≥ 1) (bids : Fin n → Nat) : Nat :=
  bids (auctionWinner h_n bids)

/-!
## Poker de Kuhn (tiré de GT-13 Section 2)

---
English:
## Kuhn Poker (from GT-13 Section 2)
-/

/-- Une carte au poker de Kuhn (simplifié : Valet=0, Dame=1, Roi=2).
    `abbrev` (et non `def`) pour que les instances de `Fin 3` (`LT`, `DecidableEq`, ...) se propagent.
    English: A card in Kuhn poker (simplified: Jack=0, Queen=1, King=2).
    `abbrev` (not `def`) so `Fin 3` instances (`LT`, `DecidableEq`, ...) propagate. -/
abbrev KuhnCard := Fin 3

/-- Historique des actions dans une donne de poker de Kuhn.
    English: History of actions in a Kuhn poker round -/
inductive KuhnAction where
  | check : KuhnAction
  | bet : KuhnAction
  | fold : KuhnAction
  | call : KuhnAction
  deriving Repr, BEq

instance : ToString KuhnAction where
  toString a := match a with
    | .check => "check"
    | .bet => "bet"
    | .fold => "fold"
    | .call => "call"

/-- Un état de partie de poker de Kuhn.
    English: A Kuhn poker game state -/
structure KuhnState where
  /-- Cartes distribuées à chaque joueur.
      English: Cards dealt to each player -/
  cards : Fin 2 → KuhnCard
  /-- Historique des actions.
      English: Action history -/
  history : List KuhnAction

-- pas de `deriving Repr` : `cards` est un type fonctionnel, non dérivable. Instance manuelle :
instance : Repr KuhnState where
  reprPrec s _ :=
    let c0 := toString (s.cards ⟨0, by omega⟩)
    let c1 := toString (s.cards ⟨1, by omega⟩)
    s!"KuhnState({c0}, {c1}, {toString s.history})"

/-- Vérifie si une partie de poker de Kuhn a atteint un état terminal.
    English: Check if a Kuhn poker game has reached a terminal state -/
def KuhnIsTerminal (history : List KuhnAction) : Bool :=
  match history with
  | [KuhnAction.check, KuhnAction.check] => true    -- les deux checkent
  | [KuhnAction.check, KuhnAction.bet, KuhnAction.fold] => true
  | [KuhnAction.check, KuhnAction.bet, KuhnAction.call] => true
  | [KuhnAction.bet, KuhnAction.fold] => true
  | [KuhnAction.bet, KuhnAction.call] => true
  | _ => false

/-- Renvoie l'ensemble d'information d'un joueur au poker de Kuhn.
    English: Get the information set for a player in Kuhn poker -/
def kuhnInfoSet (card : KuhnCard) (history : List KuhnAction) : String :=
  s!"card={card.val}-hist={toString history}"

/-- Paiement du joueur 1 dans les états terminaux du poker de Kuhn.
    Renvoie 0 pour les états non terminaux.
    English: Payoff for player 1 in terminal Kuhn poker states.
    Returns 0 for non-terminal states.
-/
def kuhnPayoff (cards : Fin 2 → KuhnCard) (history : List KuhnAction) : Int :=
  match history with
  | [KuhnAction.check, KuhnAction.check] =>
    if cards 0 > cards 1 then 1 else -1
  | [KuhnAction.check, KuhnAction.bet, KuhnAction.fold] => 1  -- J1 gagne le pot
  | [KuhnAction.check, KuhnAction.bet, KuhnAction.call] =>
    if cards 0 > cards 1 then 2 else -2  -- pot = 2
  | [KuhnAction.bet, KuhnAction.fold] => 1   -- J2 se couche, J1 gagne le pot
  | [KuhnAction.bet, KuhnAction.call] =>
    if cards 0 > cards 1 then 2 else -2  -- pot = 2
  | _ => 0  -- non terminal
