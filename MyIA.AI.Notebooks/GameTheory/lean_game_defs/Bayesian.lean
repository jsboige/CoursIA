/-
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

/-! ## Utility (avoids Mathlib dependency) -/

/-- Update a dependent function at a given index.
    Equivalent to Mathlib's `Function.update` but self-contained.
    Uses `Fin` decidable equality for comparison. -/
def funUpdate {n : Nat} {β : Fin n → Type} (f : (i : Fin n) → β i)
    (i : Fin n) (x : β i) : (j : Fin n) → β j :=
  fun j => if h : j = i then h ▸ x else f j

/-! ## Type Spaces and Beliefs -/

/-- A type space for a player: the set of possible private types -/
def TypeSpace (α : Type) := List α

/-- A common prior over type profiles (simplified: uniform weights) -/
structure CommonPrior (T : Type) (n : Nat) where
  /-- Possible type profiles: list of n-tuples -/
  typeProfiles : List (Fin n → T)
  /-- Probability of each profile (simplified as rational weight) -/
  weights : List Nat
  /-- Weights sum to 100 (scaled probabilities) -/
  weightsSum100 : weights.sum = 100 := by decide

/-! ## Bayesian Game Structure -/

/-- A Bayesian (incomplete information) game with finite types.

    Each player has a private type drawn from a common prior.
    Strategies map types to actions. Payoffs depend on the full
    type profile and action profile.
-/
structure BayesianGame (PlayerType : Type) where
  /-- Number of players -/
  numPlayers : Nat
  /-- Possible types for each player -/
  typeSet : Fin numPlayers → List PlayerType
  /-- Number of actions available to each player -/
  numActions : Fin numPlayers → Nat
  /-- Payoff depends on type profile AND action profile -/
  payoff : (i : Fin numPlayers) →
           (types : Fin numPlayers → PlayerType) →
           (actions : (j : Fin numPlayers) → Fin (numActions j)) → Int
  /-- Common prior probability over type profiles (simplified) -/
  priorProb : (types : Fin numPlayers → PlayerType) → Float

/-! ## Type-Conditioned Strategies -/

/-- A type-conditioned (pure) strategy: maps own type to an action -/
def TypeStrategy (g : BayesianGame α) (i : Fin g.numPlayers) :=
  α → Fin (g.numActions i)

/-- A profile of type strategies: one per player -/
def TypeStrategyProfile (g : BayesianGame α) :=
  (i : Fin g.numPlayers) → TypeStrategy g i

/-! ## Expected Payoff (Simplified) -/

/-- Expected payoff for player i given a type strategy profile
    and a particular type profile (simplified: no integration).

    In a full formalization this would involve summing over all
    type profiles weighted by the common prior.
-/
def expectedPayoffBayesian (g : BayesianGame α)
    (profile : TypeStrategyProfile g)
    (types : Fin g.numPlayers → α)
    (i : Fin g.numPlayers) : Int :=
  g.payoff i types (fun j => profile j (types j))

/-! ## Bayesian Nash Equilibrium -/

/-- Bayesian Nash Equilibrium: no player can improve by deviating,
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

/-! ## Information Sets (Imperfect Information) -/

/-- An information set groups decision nodes that a player cannot
    distinguish between. Modeled as a set of game histories.

    From GT-13: "A player's information set at any point in the game
    is the set of nodes they might be at, given what they observe."
-/
structure InformationSet where
  /-- Player who faces this information set -/
  player : Nat
  /-- Possible histories (game states) in this set -/
  nodes : List String
  /-- Available actions at this information set -/
  actions : List String

/-- Check if two histories belong to the same information set -/
def sameInfoSet (h1 h2 : String) (iset : InformationSet) : Bool :=
  iset.nodes.contains h1 && iset.nodes.contains h2

/-! ## Signaling Games (Spence 1973) -/

/-- A signaling game: sender observes type, sends message,
    receiver observes message, chooses action.

    From GT-11 Section 6 (Spence signaling model).
    Two players: Sender (player 0) and Receiver (player 1).
-/
structure SignalingGame (MessageType : Type) (ActionResult : Type) where
  /-- Possible types of the sender -/
  senderTypes : List MessageType
  /-- Messages the sender can send -/
  messages : List MessageType
  /-- Actions the receiver can take -/
  receiverActions : List ActionResult
  /-- Sender payoff: depends on type, message sent, receiver action -/
  senderPayoff : MessageType → MessageType → ActionResult → Int
  /-- Receiver payoff: depends on type, message sent, receiver action -/
  receiverPayoff : MessageType → MessageType → ActionResult → Int
  /-- Prior probability of each sender type -/
  typePrior : MessageType → Float

/-- A sender strategy: type → message -/
def SenderStrategy (_g : SignalingGame α β) := α → α

/-- A receiver strategy: message → action -/
def ReceiverStrategy (_g : SignalingGame α β) := α → β

/-! ## First-Price Auction (from GT-11 Section 5) -/

/-- A first-price sealed-bid auction with private values.

    Each bidder has a private valuation. They submit a bid.
    Highest bid wins and pays their bid.
-/
structure FirstPriceAuction where
  /-- Number of bidders -/
  numBidders : Nat
  /-- Maximum possible value -/
  maxValue : Nat
  /-- Bidding strategy: valuation → bid (simplified, same for all) -/
  bidStrategy : Nat → Nat
  /-- Check if bid is valid (0 ≤ bid ≤ maxValue) -/
  validBid : (bid : Nat) → Bool := fun bid => bid <= maxValue

/-- Determine winner of auction given bids.
    Returns the index of the first bidder with the maximum bid.
    Requires n ≥ 1 (at least one bidder). -/
def auctionWinner {n : Nat} (h_n : n ≥ 1) (bids : Fin n → Nat) : Fin n :=
  let maxBid := (List.finRange n).foldl (fun acc i => max acc (bids i)) 0
  -- First player who bid the maximum wins (tie-breaking)
  match (List.finRange n).find? (fun i => bids i = maxBid) with
  | some i => i
  | none => ⟨0, by omega⟩

/-- Revenue for the auctioneer -/
def auctionRevenue {n : Nat} (h_n : n ≥ 1) (bids : Fin n → Nat) : Nat :=
  bids (auctionWinner h_n bids)

/-! ## Kuhn Poker (from GT-13 Section 2) -/

/-- A card in Kuhn poker (simplified: Jack=0, Queen=1, King=2).
    `abbrev` (not `def`) so `Fin 3` instances (`LT`, `DecidableEq`, ...) propagate. -/
abbrev KuhnCard := Fin 3

/-- History of actions in a Kuhn poker round -/
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

/-- A Kuhn poker game state -/
structure KuhnState where
  /-- Cards dealt to each player -/
  cards : Fin 2 → KuhnCard
  /-- Action history -/
  history : List KuhnAction

-- no deriving Repr: `cards` is a function type, not derivable. Manual instance:
instance : Repr KuhnState where
  reprPrec s _ :=
    let c0 := toString (s.cards ⟨0, by omega⟩)
    let c1 := toString (s.cards ⟨1, by omega⟩)
    s!"KuhnState({c0}, {c1}, {toString s.history})"

/-- Check if a Kuhn poker game has reached a terminal state -/
def KuhnIsTerminal (history : List KuhnAction) : Bool :=
  match history with
  | [KuhnAction.check, KuhnAction.check] => true    -- both check
  | [KuhnAction.check, KuhnAction.bet, KuhnAction.fold] => true
  | [KuhnAction.check, KuhnAction.bet, KuhnAction.call] => true
  | [KuhnAction.bet, KuhnAction.fold] => true
  | [KuhnAction.bet, KuhnAction.call] => true
  | _ => false

/-- Get the information set for a player in Kuhn poker -/
def kuhnInfoSet (card : KuhnCard) (history : List KuhnAction) : String :=
  s!"card={card.val}-hist={toString history}"

/-- Payoff for player 1 in terminal Kuhn poker states.
    Returns 0 for non-terminal states.
-/
def kuhnPayoff (cards : Fin 2 → KuhnCard) (history : List KuhnAction) : Int :=
  match history with
  | [KuhnAction.check, KuhnAction.check] =>
    if cards 0 > cards 1 then 1 else -1
  | [KuhnAction.check, KuhnAction.bet, KuhnAction.fold] => 1  -- P1 wins pot
  | [KuhnAction.check, KuhnAction.bet, KuhnAction.call] =>
    if cards 0 > cards 1 then 2 else -2  -- pot = 2
  | [KuhnAction.bet, KuhnAction.fold] => 1   -- P2 folds, P1 wins pot
  | [KuhnAction.bet, KuhnAction.call] =>
    if cards 0 > cards 1 then 2 else -2  -- pot = 2
  | _ => 0  -- non-terminal
