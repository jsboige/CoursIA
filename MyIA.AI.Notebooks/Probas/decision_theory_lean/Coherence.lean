import Coherence.Basic
import Coherence.DutchBook
import Coherence.Probability

/-!
# Decision Theory — Dutch Book / cohérence (de Finetti)

Formalisation du théorème de cohérence de de Finetti (cas fini) : la fondation
conceptuelle des probabilités. Des prix de pari **incohérents** (violant
l'inclusion–exclusion) exposent l'agent à un **Dutch Book** — un livret de paris à
perte sûre. La cohérence *force* donc les axiomes de probabilité.

## Contenu
- `Coherence.Basic` : événements (`Event`), fonctions de prix (`Price`), indicatrices,
  et l'identité d'inclusion–exclusion (`ind_inclusion_exclusion`) — la clé de voûte.
- `Coherence.DutchBook` : la direction constructive « incohérence ⟹ Dutch Book »
  (`non_additive_implies_dutch_book`, witness explicite, 0 `sorry`) et sa contraposée
  « cohérence ⟹ additivité » (`coherent_on_implies_additive`).
- `Coherence.Probability` : la **caractérisation mono-livret** de de Finetti
  (`single_coherent_iff_prob_bounds`) — une fonction de prix `q` est cohérente au sens
  mono-livret (aucun Dutch Book à un seul ticket) **ssi** elle satisfait les bornes de
  probabilité `0 ≤ q A ≤ 1`, `q ∅ = 0`, `q univ = 1`. Chaque axiome violé admet un
  Dutch Book explicite à un seul ticket (`single_dutch_book_of_neg/high/pos_empty/univ_lt`),
  0 `sorry`. Plus la **réciproque quatre-tickets** pour les prix issus de poids
  probabilistes (`priceFromWeights_coherent_on`), par l'argument d'espérance
  `E_p[gain] = 0` (`sum_weights_mul_ind` → `expected_ticket_gain_zero` →
  `expected_ieGain_zero` → contradiction sur un état chargé, `exists_pos_weight`).

## Statut
- Prouvé sans `sorry` : la direction constructive (violation de l'inclusion–exclusion
  ⟹ Dutch Book avec mises explicites `(1,1,−1,−1)` ou l'inverse), la cohérence ⟹
  additivité sur deux événements, la **caractérisation mono-livret** complète
  (`single_coherent_iff_prob_bounds`, axiomes `[propext, Classical.choice, Quot.sound]`),
  et la **réciproque quatre-tickets pour les vraies probabilités**
  (`priceFromWeights_coherent_on` : aucun livret à quatre tickets n'arbitre un prix issu
  de poids non négatifs sommant à 1).
- Ouvert (jalon suivant) : le `coherent_iff_probability` **complet** — livrets de taille
  arbitraire sur un prix cohérent QUELCONQUE, via la reconstruction de la mesure
  `q A = Σ_{ω ∈ A} q {ω}` (montrer qu'un prix cohérent est nécessairement de la forme
  `priceFromWeights`), ou la séparation d'hyperplans / dualité LP en dimension finie.
  Les versions mono-livret et quatre-tickets-sur-poids livrées ici en constituent le
  noyau tractable (faisabilité Lean « MOYENNE », cf #4050).

## Références croisées
- `Utility` (même lake) : représentation d'utilité espérée vNM — l'autre fondation
  de la théorie de la décision sous risque.
- Infer-14 (Infer.NET) : utilité espérée bayésienne sous postérieure.
- PyMC-1 (PyMC) : estimation d'utilité espérée par échantillonnage postérieur.
-/
