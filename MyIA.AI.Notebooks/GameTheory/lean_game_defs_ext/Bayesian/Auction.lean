/-
  Enchère scellée au premier prix (discrète, deux enchérisseurs)
  ===============================================================

  L'application classique des jeux bayésiens (Vickrey 1961, Harsanyi
  1967) : deux enchérisseurs avec des valorisations privées tirées
  uniformément dans `{0, …, n-1}` soumettent simultanément des offres
  dans `{0, …, n-1}` ; la plus haute offre gagne et paie sa propre offre,
  les égalités partagent le surplus.

  Choix d'encodage (tout en Lean 4 core, sans Mathlib) :
  - Les valorisations sont les *types* et les offres sont les *actions*
    d'un `BayesGame2`, avec un poids de prior uniforme 1 sur chaque profil de types.
  - Les utilités sont mises à l'échelle par 2 pour que le cas d'égalité
    (la moitié du surplus) reste dans `Int` : gain = `2*(v - b)`, égalité =
    `v - b`, perte = `0`. Par un raisonnement de type `isBNE_scaleW`,
    mettre à l'échelle tous les paiements par une constante positive ne
    change pas les meilleures réponses, donc l'analyse d'équilibre est
    fidèle.

  Résultats :
  - `fpa_u1_truthful`/`interimU1_truthful` : offrir sa propre valeur
    donne une utilité *exactement nulle*, pour tout n, tout type, face à
    toute stratégie adverse — gagner à un prix égal à sa valeur ne laisse
    aucun surplus. (Théorème général, pas une instance `decide`.)
  - `truthful_not_bne_two/three` : l'offre sincère n'est PAS un BNE
    (contre-exemple vérifié au noyau via `decide`).
  - `shade_bne_two/three` : la stratégie d'ombrage `bid = v / 2` est un BNE
    (vérifié au noyau via `decide`) — l'analogue discret de l'équilibre du
    manuel `b(v) = v/2` pour deux enchérisseurs uniformes.
  - `shading_beats_truthful_three` : sous l'ombrage, le type haut gagne
    une utilité interimaire strictement positive, contrastant avec le zéro
    de l'offre sincère.

  Voir #2610 (formalisation GT-Lean, phase bayésienne 2).

  ---
  English:
  First-Price Sealed-Bid Auction (discrete, two bidders)
  ======================================================

  The classic application of Bayesian games (Vickrey 1961, Harsanyi
  1967): two bidders with private valuations drawn uniformly from
  `{0, …, n-1}` simultaneously submit bids in `{0, …, n-1}`; the
  highest bid wins and pays its own bid, ties split the surplus.

  Encoding choices (all core Lean 4, no Mathlib):
  - Valuations are the *types* and bids are the *actions* of a
    `BayesGame2`, with uniform prior weight 1 on every type profile.
  - Utilities are scaled by 2 so that the tie case (half the surplus)
    stays in `Int`: win = `2*(v - b)`, tie = `v - b`, lose = `0`.
    By `isBNE_scaleW`-style reasoning, scaling all payoffs by a
    positive constant does not change best responses, so the
    equilibrium analysis is faithful.

  Results:
  - `fpa_u1_truthful`/`interimU1_truthful`: bidding one's own value
    yields *exactly zero* utility, for every n, every type, against
    every opponent strategy — winning at a price equal to one's value
    leaves no surplus. (General theorem, not a `decide` instance.)
  - `truthful_not_bne_two/three`: truthful bidding is NOT a BNE
    (kernel-checked counterexample via `decide`).
  - `shade_bne_two/three`: the shaded strategy `bid = v / 2` is a BNE
    (kernel-checked via `decide`) — the discrete analogue of the
    textbook equilibrium `b(v) = v/2` for two uniform bidders.
  - `shading_beats_truthful_three`: under shading the high type earns
    strictly positive interim utility, in contrast with the zero of
    truthful bidding.

  See #2610 (GT-Lean formalization, Bayesian phase 2).
-/

import Bayesian.BNE

/-- Enchère scellée au premier prix à deux enchérisseurs, valorisations et
    offres dans `Fin n`, prior uniforme, utilités mises à l'échelle par 2 (pour
    que le partage du surplus en cas d'égalité reste entier).
    English: First-price sealed-bid auction with two bidders, valuations and
    bids in `Fin n`, uniform prior, utilities scaled by 2 (so the tie
    split of the surplus stays integral). -/
@[reducible] def fpa (n : Nat) : BayesGame2 where
  nT1 := n
  nT2 := n
  nA1 := n
  nA2 := n
  w := fun _ _ => 1
  u1 := fun v1 _ b1 b2 =>
    if b2.val < b1.val then 2 * ((v1.val : Int) - b1.val)
    else if b1.val = b2.val then (v1.val : Int) - b1.val
    else 0
  u2 := fun _ v2 b1 b2 =>
    if b1.val < b2.val then 2 * ((v2.val : Int) - b2.val)
    else if b1.val = b2.val then (v2.val : Int) - b2.val
    else 0

/-- Offre sincère du joueur 1 : offrir exactement sa valorisation.
    English: Truthful bidding for player 1: bid exactly one's valuation. -/
@[reducible] def truthful1 (n : Nat) : Strategy1 (fpa n) := fun v => v

/-- Offre sincère du joueur 2.
    English: Truthful bidding for player 2. -/
@[reducible] def truthful2 (n : Nat) : Strategy2 (fpa n) := fun v => v

/-- Offrir sa propre valeur donne un paiement nul face à N'IMPORTE QUELLE
    offre adverse : gagner ou être à égalité à un prix égal à la valorisation
    ne laisse aucun surplus, et perdre ne paie rien.
    English: Bidding one's own value yields zero payoff against ANY opposing
    bid: winning or tying at a price equal to the valuation leaves no
    surplus, and losing pays nothing. -/
theorem fpa_u1_truthful (n : Nat) (v t2 b2 : Fin n) :
    (fpa n).u1 v t2 v b2 = 0 := by
  show (if b2.val < v.val then 2 * ((v.val : Int) - v.val)
        else if v.val = b2.val then (v.val : Int) - v.val
        else 0) = 0
  split
  · omega
  · split
    · omega
    · rfl

/-- L'offre sincère rapporte une utilité interimaire exactement 0, pour toute
    valorisation, face à toute stratégie adverse (n général).
    English: Truthful bidding earns interim utility exactly 0, for every
    valuation, against every opponent strategy (general `n`). -/
theorem interimU1_truthful (n : Nat) (v : Fin n) (s2 : Strategy2 (fpa n)) :
    interimU1 (fpa n) v (truthful1 n v) s2 = 0 := by
  have h : ∀ t2 : Fin n,
      ((fpa n).w v t2 : Int) * (fpa n).u1 v t2 (truthful1 n v) (s2 t2)
        = (fun _ : Fin n => (0 : Int)) t2 := by
    intro t2
    show ((fpa n).w v t2 : Int) * (fpa n).u1 v t2 v (s2 t2) = 0
    rw [fpa_u1_truthful]
    exact Int.mul_zero _
  show sumFin n (fun t2 =>
      ((fpa n).w v t2 : Int) * (fpa n).u1 v t2 (truthful1 n v) (s2 t2)) = 0
  rw [sumFin_congr h, sumFin_zero_fun]

/-- Conséquence ex-ante : l'offre sincère rapporte 0 au global.
    English: Ex-ante consequence: truthful bidding earns 0 overall. -/
theorem exAnteU1_truthful (n : Nat) (s2 : Strategy2 (fpa n)) :
    exAnteU1 (fpa n) (truthful1 n) s2 = 0 := by
  have h : ∀ v : Fin n,
      interimU1 (fpa n) v (truthful1 n v) s2
        = (fun _ : Fin n => (0 : Int)) v :=
    fun v => interimU1_truthful n v s2
  show sumFin n (fun v => interimU1 (fpa n) v (truthful1 n v) s2) = 0
  rw [sumFin_congr h, sumFin_zero_fun]

/-- Ombrage d'offre : offrir la moitié de sa valorisation (division entière) —
    l'analogue discret de l'équilibre du manuel `b(v) = v/2` pour deux
    enchérisseurs à valorisations uniformes.
    English: Bid shading: bid half one's valuation (integer division) — the
    discrete analogue of the textbook equilibrium `b(v) = v/2` for two
    bidders with uniform valuations. -/
@[reducible] def shade1 (n : Nat) : Strategy1 (fpa n) :=
  fun v => ⟨v.val / 2, by
    have hv : v.val < n := v.isLt
    show v.val / 2 < n
    omega⟩

/-- Ombrage d'offre pour le joueur 2.
    English: Bid shading for player 2. -/
@[reducible] def shade2 (n : Nat) : Strategy2 (fpa n) :=
  fun v => ⟨v.val / 2, by
    have hv : v.val < n := v.isLt
    show v.val / 2 < n
    omega⟩

/-- Avec deux valorisations possibles `{0, 1}` et des offres `{0, 1}`, les deux
    enchérisseurs offrant 0 quel que soit leur type (= `shade`) est un BNE,
    certifié par évaluation au noyau.
    English: With two possible valuations `{0, 1}` and bids `{0, 1}`, both
    bidders bidding 0 regardless of type (= `shade`) is a BNE,
    certified by kernel evaluation. -/
theorem shade_bne_two : isBNE (fpa 2) (shade1 2) (shade2 2) := by decide

/-- … et l'offre sincère n'est PAS un BNE ici.
    English: ... and truthful bidding is NOT a BNE there. -/
theorem truthful_not_bne_two :
    ¬ isBNE (fpa 2) (truthful1 2) (truthful2 2) := by decide

/-- Avec les valorisations `{0, 1, 2}` et les offres `{0, 1, 2}`, le profil
    ombragé (`0, 0 → offre 0` ; `2 → offre 1`) est un BNE.
    English: With valuations `{0, 1, 2}` and bids `{0, 1, 2}`, the shaded
    profile (`0, 0 → bid 0`; `2 → bid 1`) is a BNE. -/
theorem shade_bne_three : isBNE (fpa 3) (shade1 3) (shade2 3) := by decide

/-- … et l'offre sincère n'est pas non plus un BNE ici : le type haut
    préfère strictement sous-offrir.
    English: ... and truthful bidding is NOT a BNE there either: the high type
    strictly prefers to underbid. -/
theorem truthful_not_bne_three :
    ¬ isBNE (fpa 3) (truthful1 3) (truthful2 3) := by decide

/-- L'ombrage paie : face à un adversaire qui ombrage, la valorisation haute
    (v = 2) gagne une utilité interimaire strictement positive en offrant 1 —
    contrastant avec le zéro exact de l'offre sincère
    (`interimU1_truthful`). Concrètement la valeur est 5 (mise à l'échelle) :
    gagne face aux deux types bas (2·(2-1) deux fois) et est à égalité avec le
    type haut (2-1).
    English: Shading pays: against a shading opponent, the high valuation
    (v = 2) earns strictly positive interim utility by bidding 1 —
    in contrast with the exact zero of truthful bidding
    (`interimU1_truthful`). Concretely the value is 5 (scaled):
    wins against both low types (2·(2-1) twice) and ties the high
    type (2-1). -/
theorem shading_beats_truthful_three :
    0 < interimU1 (fpa 3) ⟨2, by decide⟩ (shade1 3 ⟨2, by decide⟩) (shade2 3) := by
  decide
