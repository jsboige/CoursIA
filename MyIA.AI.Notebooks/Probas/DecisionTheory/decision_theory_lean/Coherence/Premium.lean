import Mathlib
import Coherence.Basic
import Coherence.DutchBook
import Coherence.Probability

/-!
# Coherence.Premium — lecture actuarielle du Dutch Book : cohérence d'un barème

T6 de l'EPIC #12904 (jambe actuarielle Decision Theory). Le théorème de de Finetti
prouvé dans `DutchBook.lean` reçoit ici sa lecture **actuarérielle** : le « ticket
payant 1 € si A se réalise » devient un **contrat de couverture** (indemnité unitaire
sur l'événement A), la « fonction de prix » devient un **barème de primes**, et le
Dutch Book devient un **arbitrage de tarification** — un courtier (ou un client
instruit, ou un concurrent) qui assemble un portefeuille de contrats à **profit sûr**,
c'est-à-dire une **perte stricte et sûre pour l'assureur** en tout état du monde.

Trois résultats, 0 `sorry`, chacun une lecture métier du socle `DutchBook.lean` /
`Probability.lean` :

1. **`incoherent_premium_sure_insurer_loss`** — un barème qui viole
   l'inclusion–exclusion sur deux garanties expose l'assureur à une perte sûre :
   le witness de `non_additive_implies_dutch_book`, lu de l'autre côté du comptoir
   (les mises changent de signe), est le portefeuille d'arbitrage du courtier.
2. **`coherent_premium_disjoint_additive`** — la règle de tarification quotidienne :
   pour deux risques **disjoints** (deux segments de clientèle, deux garanties non
   chevauchantes), un barème à la fois cohérent au sens des livrets à quatre tickets
   et au sens mono-ticket satisfait `π(A ∪ B) = π(A) + π(B)` — la prime du risque
   combiné est la somme des primes des segments. La démonstration combine
   `coherent_on_implies_additive` (inclusion–exclusion) et la normalisation
   `π ∅ = 0` forcée par le mono-ticket (`single_coherent_iff_prob_bounds`).
3. **`pure_premium_tariff_unarbitrageable`** — un barème calculé par espérance
   (prime pure `π(A) = Σ_{ω ∈ A} p(ω)`, poids non négatifs sommant à 1) n'offre
   **aucun** portefeuille à profit sûr : conséquence immédiate de
   `priceFromWeights_coherent_on` et de la symétrie `coherent_on_iff_no_sure_profit`.

**Cadrage honnête (G.3/G.9).** Le point 2 est une equivalence de deux cohérences
(quatre tickets sur `(A, B)` + mono-ticket global), pas le `coherent_iff_probability`
complet — dont la réciproque générale reste le jalon ouvert de `DutchBook.lean`
(séparation d'hyperplans / dualité LP). Les résultats sont énoncés sur le barème
unitaire (indemnité 1 €) ; l'extrapolation à des montants quelconques (contrats
`(α, β)` couverture × capital) suit par linéarité des mises et n'est pas re-développée
ici. Voir la sous-série PyMC `DecisionTheory/` (EPIC #12904, tranches T1-T5) pour la
face numérique (prime pure, chargement, partial pooling).
-/

namespace Coherence

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## Barème de primes, résultat de l'assureur, arbitrage de tarification -/

/-- Un **barème de primes** : chaque événement `A` (garantie) est couvert à hauteur
    de 1 € d'indemnité pour une prime unitaire `π A`. C'est exactement le cadre de
    de Finetti (`Price`) relu côté assureur : le ticket devient contrat, le prix
    devient prime. -/
abbrev PremiumSchedule (Ω : Type*) [Fintype Ω] [DecidableEq Ω] := Event Ω → ℝ

/-- **Résultat net de l'assureur** à l'état `ω` sur un portefeuille client de quatre
    contrats `(A, B, A∩B, A∪B)` avec souscriptions `(sA, sB, sAB, sAU)` (souscription
    positive = le client achète la couverture, négative = il la place côté assureur) :
    primes encaissées moins indemnités versées. C'est l'opposé exact du gain du livret
    client (`ieGain`) — les deux parties du comptoir voient des résultats opposés. -/
def InsurerNet (π : PremiumSchedule Ω) (A B : Event Ω) (sA sB sAB sAU : ℝ) (ω : Ω) : ℝ :=
  -ieGain π A B sA sB sAB sAU ω

/-- Un **arbitrage de tarification** : un portefeuille client dont le résultat est
    strictement positif en tout état — donc un résultat strictement négatif (perte
    sûre) pour l'assureur en tout état. C'est le Dutch Book de `DutchBook.lean` lu du
    point de vue de la compagnie : « un jeu de primes incohérent est un pari perdant
    sûr » — pour celui qui l'a affiché. -/
def TariffArbitrage (π : PremiumSchedule Ω) (A B : Event Ω) (sA sB sAB sAU : ℝ) : Prop :=
  ∀ ω : Ω, InsurerNet π A B sA sB sAB sAU ω < 0

/-- Un barème n'offre **aucun profit sûr** (au sens des livrets à quatre tickets sur
    `(A, B)`) : aucun portefeuille client n'est un arbitrage de tarification. C'est le
    miroir exact de `CoherentOn` (aucune perte sûre côté client). -/
def NoSureProfit (π : PremiumSchedule Ω) (A B : Event Ω) : Prop :=
  ∀ sA sB sAB sAU : ℝ, ¬ TariffArbitrage π A B sA sB sAB sAU

/-! ## Symétrie comptoir : aucune perte sûre pour le client ⟺ aucun profit sûr -/

/-- Les mises de signe opposé donnent le gain de signe opposé : le livret `(-sA, -sB,
    -sAB, -sAU)` est l'exacte contrepartie du livret `(sA, sB, sAB, sAU)`. C'est la
    linéarité des mises dans `ieGain` — la clé du changement de point de vue
    client/assureur. -/
lemma ieGain_neg (q : Price Ω) (A B : Event Ω) (sA sB sAB sAU : ℝ) (ω : Ω) :
    ieGain q A B (-sA) (-sB) (-sAB) (-sAU) ω = -ieGain q A B sA sB sAB sAU ω := by
  simp only [ieGain]
  ring

/-- **Changement de côté du comptoir.** Un barème est cohérent (aucun Dutch Book côté
    client, `CoherentOn`) si et seulement s'il n'offre aucun profit sûr (aucun
    arbitrage côté client, `NoSureProfit`) : les deux lectures sont la même propriété,
    reliée par l'inversion des signes des mises (`ieGain_neg`). Pour l'assureur, la
    cohérence de son barème et l'absence d'arbitrage contre lui sont donc une seule et
    même exigence. -/
theorem coherent_on_iff_no_sure_profit (π : PremiumSchedule Ω) (A B : Event Ω) :
    CoherentOn π A B ↔ NoSureProfit π A B := by
  constructor
  · intro hc sA sB sAB sAU harb
    refine hc (-sA) (-sB) (-sAB) (-sAU) ?_
    intro ω
    have h := harb ω
    simp only [InsurerNet] at h
    rw [ieGain_neg]
    linarith
  · intro hnp sA sB sAB sAU harb
    refine hnp (-sA) (-sB) (-sAB) (-sAU) ?_
    intro ω
    have h := harb ω
    simp only [InsurerNet]
    rw [ieGain_neg]
    linarith

/-! ## Théorèmes cibles (lecture actuarielle) -/

/-- **Barème incohérent ⟹ perte sûre de l'assureur.** Si le barème `π` viole
    l'inclusion–exclusion sur deux garanties `A, B`, un courtier construit un
    portefeuille de contrats à profit strict en tout état — l'assureur subit une
    perte stricte et sûre. C'est le théorème `non_additive_implies_dutch_book` lu de
    l'autre côté du comptoir : le witness du Dutch Book (mises à perte sûre côté
    client) devient, par inversion des signes, le portefeuille d'arbitrage du
    courtier. -/
theorem incoherent_premium_sure_insurer_loss (π : PremiumSchedule Ω) (A B : Event Ω)
    (h : π (A ∪ B) + π (A ∩ B) ≠ π A + π B) :
    ∃ sA sB sAB sAU : ℝ, TariffArbitrage π A B sA sB sAB sAU := by
  obtain ⟨sA, sB, sAB, sAU, hloss⟩ := non_additive_implies_dutch_book π A B h
  refine ⟨-sA, -sB, -sAB, -sAU, ?_⟩
  intro ω
  have h' := hloss ω
  simp only [InsurerNet]
  rw [ieGain_neg]
  linarith

/-- **Additivité sur risques disjoints — la règle de segmentation.** Pour deux
    garanties **disjointes** (`A ∩ B = ∅` : deux segments de clientèle sans
    chevauchement, deux risques exclusifs), un barème à la fois cohérent au sens des
    livrets à quatre tickets (sur `(A, B)`) et cohérent au sens mono-ticket satisfait

    `π (A ∪ B) = π A + π B` :

    la prime du risque combiné est exactement la somme des primes des segments.
    La preuve combine l'inclusion–exclusion forcée par la cohérence
    (`coherent_on_implies_additive` : `π(A∪B) + π(∅) = π A + π B` ici) et la
    normalisation `π ∅ = 0` forcée par le mono-ticket (`probBounds_empty` via
    `single_coherent_iff_prob_bounds`). Une prime de pool supérieure (ou inférieure)
    à la somme des primes de segments est donc soit une incohérence exploitable,
    soit le signe qu'un chargement non tarifé s'est glissé dans le barème. -/
theorem coherent_premium_disjoint_additive [Nonempty Ω] (π : PremiumSchedule Ω)
    (A B : Event Ω) (hdj : A ∩ B = ∅)
    (hc4 : CoherentOn π A B) (hc1 : SingleCoherent π) :
    π (A ∪ B) = π A + π B := by
  have hIE := coherent_on_implies_additive π A B hc4
  have hb : ProbBounds π := (single_coherent_iff_prob_bounds π).mp hc1
  have h0 : π (∅ : Event Ω) = 0 := probBounds_empty π hb
  rw [hdj] at hIE
  rw [h0] at hIE
  linarith

/-- **La prime pure est inarbitrable.** Un barème construit par espérance sous des
    poids `p` non négatifs sommant à 1 — la **prime pure** `π(A) = Σ_{ω ∈ A} p(ω)` de
    la théorie actuarielle — n'offre aucun portefeuille à profit sûr : aucun courtier
    ne peut arbitrer une tarification espérance-consistante. Conséquence immédiate de
    `priceFromWeights_coherent_on` (aucun Dutch Book côté client) et de la symétrie
    `coherent_on_iff_no_sure_profit` (c'est alors aussi aucun profit sûr côté
    courtier). La prime pure est ainsi le seul barème à la fois break-even en
    espérance et inarbitrable — le point de départ obligatoire du chargement de
    sécurité (tranches T1/T2 de l'EPIC #12904). -/
theorem pure_premium_tariff_unarbitrageable (p : Ω → ℝ) (hnn : ∀ ω, (0:ℝ) ≤ p ω)
    (hsum : ∑ ω, p ω = 1) (A B : Event Ω) :
    NoSureProfit (priceFromWeights p) A B :=
  (coherent_on_iff_no_sure_profit (priceFromWeights p) A B).mp
    (priceFromWeights_coherent_on p hnn hsum A B)

end Coherence
