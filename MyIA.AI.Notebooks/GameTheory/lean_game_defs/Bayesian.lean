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
  Jumelage i18n : ce module est le FR canonique (sibling pair Pattern A,
  ratifié par user 2026-07-04 sur EPIC #4980). Le miroir anglais vit dans
  `Bayesian_en.lean` (variante reuse-FR-names : il `import Basic` comme ce
  fichier et redéclare ses déclarations dans `namespace BayesianEn`). Le corps
  des définitions, signatures, structures, inductifs, instances et tactiques
  est byte-identique entre les deux fichiers ; seules les docstrings
  `/-! ... -/` (titres de section) et `/-- ... -/` (docstrings de champs et
  déclarations) diffèrent, FR dans ce fichier, EN dans `Bayesian_en.lean`.
-/

import Basic

/-!
## Utilitaires (évite la dépendance Mathlib)
-/

/-- Met à jour une fonction dépendante à un indice donné.
    Équivalent au `Function.update` de Mathlib mais autonome.
    Utilise l'égalité décidable sur `Fin` pour la comparaison. -/
def funUpdate {n : Nat} {β : Fin n → Type} (f : (i : Fin n) → β i)
    (i : Fin n) (x : β i) : (j : Fin n) → β j :=
  fun j => if h : j = i then h ▸ x else f j

/-!
## Espaces de types et croyances
-/

/-- Un espace de types pour un joueur : l'ensemble des types privés possibles. -/
def TypeSpace (α : Type) := List α

/-- Une croyance commune (prior) sur les profils de types (simplifié : poids uniformes). -/
structure CommonPrior (T : Type) (n : Nat) where
  /-- Profils de types possibles : liste de n-uplets. -/
  typeProfiles : List (Fin n → T)
  /-- Probabilité de chaque profil (simplifiée en poids rationnel). -/
  weights : List Nat
  /-- Les poids somment à 100 (probabilités mises à l'échelle). -/
  weightsSum100 : weights.sum = 100 := by decide

/-!
## Structure du jeu bayésien
-/

/-- Un jeu bayésien (information incomplète) à types finis.

    Chaque joueur a un type privé tiré d'une croyance commune.
    Les stratégies associent des types à des actions. Les paiements
    dépendent du profil de types complet et du profil d'actions.
-/
structure BayesianGame (PlayerType : Type) where
  /-- Nombre de joueurs. -/
  numPlayers : Nat
  /-- Types possibles pour chaque joueur. -/
  typeSet : Fin numPlayers → List PlayerType
  /-- Nombre d'actions disponibles pour chaque joueur. -/
  numActions : Fin numPlayers → Nat
  /-- Le paiement dépend du profil de types ET du profil d'actions. -/
  payoff : (i : Fin numPlayers) →
           (types : Fin numPlayers → PlayerType) →
           (actions : (j : Fin numPlayers) → Fin (numActions j)) → Int
  /-- Probabilité a priori (prior) sur les profils de types (simplifié). -/
  priorProb : (types : Fin numPlayers → PlayerType) → Float

/-!
## Stratégies conditionnées par le type
-/

/-- Une stratégie (pure) conditionnée par le type : associe son propre type à une action. -/
def TypeStrategy (g : BayesianGame α) (i : Fin g.numPlayers) :=
  α → Fin (g.numActions i)

/-- Un profil de stratégies par type : une par joueur. -/
def TypeStrategyProfile (g : BayesianGame α) :=
  (i : Fin g.numPlayers) → TypeStrategy g i

/-!
## Paiement espéré (simplifié)
-/

/-- Paiement espéré du joueur i étant donné un profil de stratégies par type
    et un profil de types particulier (simplifié : pas d'intégration).

    Dans une formalisation complète, cela impliquerait de sommer sur tous
    les profils de types pondérés par la croyance commune.
-/
def expectedPayoffBayesian (g : BayesianGame α)
    (profile : TypeStrategyProfile g)
    (types : Fin g.numPlayers → α)
    (i : Fin g.numPlayers) : Int :=
  g.payoff i types (fun j => profile j (types j))

/-!
## Équilibre de Nash bayésien
-/

/-- Équilibre de Nash bayésien : aucun joueur ne peut améliorer en déviant,
    étant donné son type.

    Pour chaque joueur i et chaque type t_i du joueur i, le profil de
    stratégies doit être une meilleure réponse conditionnellement à t_i.
    (Simplifié : vérifié sur un seul profil de types.)
-/
def isBayesianNashEquilibrium (g : BayesianGame α)
    (profile : TypeStrategyProfile g)
    (types : Fin g.numPlayers → α) : Prop :=
  ∀ (i : Fin g.numPlayers) (altStrategy : TypeStrategy g i),
    expectedPayoffBayesian g profile types i >=
    expectedPayoffBayesian g (funUpdate profile i altStrategy) types i

/-!
## Ensembles d'information (information imparfaite)
-/

/-- Un ensemble d'information regroupe des nœuds de décision qu'un joueur ne
    peut pas distinguer. Modélisé comme un ensemble d'historiques de jeu.

    Tiré de GT-13 : « l'ensemble d'information d'un joueur à un moment du jeu
    est l'ensemble des nœuds où il pourrait être, compte tenu de ce qu'il observe. »
-/
structure InformationSet where
  /-- Joueur confronté à cet ensemble d'information. -/
  player : Nat
  /-- Historiques possibles (états du jeu) dans cet ensemble. -/
  nodes : List String
  /-- Actions disponibles dans cet ensemble d'information. -/
  actions : List String

/-- Vérifie si deux historiques appartiennent au même ensemble d'information. -/
def sameInfoSet (h1 h2 : String) (iset : InformationSet) : Bool :=
  iset.nodes.contains h1 && iset.nodes.contains h2

/-!
## Jeux de signal (Spence 1973)
-/

/-- Un jeu de signal : l'émetteur observe son type, envoie un message,
    le récepteur observe le message, choisit une action.

    Tiré de GT-11 Section 6 (modèle de signal de Spence).
    Deux joueurs : Émetteur (joueur 0) et Récepteur (joueur 1).
-/
structure SignalingGame (MessageType : Type) (ActionResult : Type) where
  /-- Types possibles de l'émetteur. -/
  senderTypes : List MessageType
  /-- Messages que l'émetteur peut envoyer. -/
  messages : List MessageType
  /-- Actions que le récepteur peut entreprendre. -/
  receiverActions : List ActionResult
  /-- Paiement de l'émetteur : dépend du type, du message envoyé, de l'action du récepteur. -/
  senderPayoff : MessageType → MessageType → ActionResult → Int
  /-- Paiement du récepteur : dépend du type, du message envoyé, de l'action du récepteur. -/
  receiverPayoff : MessageType → MessageType → ActionResult → Int
  /-- Probabilité a priori de chaque type de l'émetteur. -/
  typePrior : MessageType → Float

/-- Stratégie de l'émetteur : type → message. -/
def SenderStrategy (_g : SignalingGame α β) := α → α

/-- Stratégie du récepteur : message → action. -/
def ReceiverStrategy (_g : SignalingGame α β) := α → β

/-!
## Enchère au premier prix (tiré de GT-11 Section 5)
-/

/-- Une enchère scellée au premier prix avec valeurs privées.

    Chaque enchérisseur a une valorisation privée. Il soumet une offre.
    L'offre la plus élevée gagne et paie son offre.
-/
structure FirstPriceAuction where
  /-- Nombre d'enchérisseurs. -/
  numBidders : Nat
  /-- Valeur maximale possible. -/
  maxValue : Nat
  /-- Stratégie d'enchère : valorisation → offre (simplifié, identique pour tous). -/
  bidStrategy : Nat → Nat
  /-- Vérifie si l'enchère est valide (0 ≤ offre ≤ maxValue). -/
  validBid : (bid : Nat) → Bool := fun bid => bid <= maxValue

/-- Détermine le gagnant de l'enchère étant donné les offres.
    Renvoie l'indice du premier enchérisseur avec l'offre maximale.
    Nécessite n ≥ 1 (au moins un enchérisseur). -/
def auctionWinner {n : Nat} (h_n : n ≥ 1) (bids : Fin n → Nat) : Fin n :=
  let maxBid := (List.finRange n).foldl (fun acc i => max acc (bids i)) 0
  -- Le premier joueur ayant offert le maximum gagne (départage les égalités)
  match (List.finRange n).find? (fun i => bids i = maxBid) with
  | some i => i
  | none => ⟨0, by omega⟩

/-- Revenu pour l'enchérisseur (l'organisateur de l'enchère). -/
def auctionRevenue {n : Nat} (h_n : n ≥ 1) (bids : Fin n → Nat) : Nat :=
  bids (auctionWinner h_n bids)

/-!
## Poker de Kuhn (tiré de GT-13 Section 2)
-/

/-- Une carte au poker de Kuhn (simplifié : Valet=0, Dame=1, Roi=2).
    `abbrev` (et non `def`) pour que les instances de `Fin 3` (`LT`, `DecidableEq`, ...) se propagent. -/
abbrev KuhnCard := Fin 3

/-- Historique des actions dans une donne de poker de Kuhn. -/
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

/-- Un état de partie de poker de Kuhn. -/
structure KuhnState where
  /-- Cartes distribuées à chaque joueur. -/
  cards : Fin 2 → KuhnCard
  /-- Historique des actions. -/
  history : List KuhnAction

-- pas de `deriving Repr` : `cards` est un type fonctionnel, non dérivable. Instance manuelle :
instance : Repr KuhnState where
  reprPrec s _ :=
    let c0 := toString (s.cards ⟨0, by omega⟩)
    let c1 := toString (s.cards ⟨1, by omega⟩)
    s!"KuhnState({c0}, {c1}, {toString s.history})"

/-- Vérifie si une partie de poker de Kuhn a atteint un état terminal. -/
def KuhnIsTerminal (history : List KuhnAction) : Bool :=
  match history with
  | [KuhnAction.check, KuhnAction.check] => true    -- les deux checkent
  | [KuhnAction.check, KuhnAction.bet, KuhnAction.fold] => true
  | [KuhnAction.check, KuhnAction.bet, KuhnAction.call] => true
  | [KuhnAction.bet, KuhnAction.fold] => true
  | [KuhnAction.bet, KuhnAction.call] => true
  | _ => false

/-- Renvoie l'ensemble d'information d'un joueur au poker de Kuhn. -/
def kuhnInfoSet (card : KuhnCard) (history : List KuhnAction) : String :=
  s!"card={card.val}-hist={toString history}"

/-- Paiement du joueur 1 dans les états terminaux du poker de Kuhn.
    Renvoie 0 pour les états non terminaux.
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
