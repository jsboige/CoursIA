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
  0 `sorry`.

## Statut
- Prouvé sans `sorry` : la direction constructive (violation de l'inclusion–exclusion
  ⟹ Dutch Book avec mises explicites `(1,1,−1,−1)` ou l'inverse), la cohérence ⟹
  additivité sur deux événements, et la **caractérisation mono-livret** complète
  (`single_coherent_iff_prob_bounds`, 0 `sorry`, axiomes `[propext, Classical.choice,
  Quot.sound]`).
- Ouvert (jalon suivant) : le `coherent_iff_probability` **complet** (livrets de taille
  arbitraire, via la reconstruction de la mesure `q A = Σ_{ω ∈ A} q {ω}` puis l'argument
  d'espérance, ou la séparation d'hyperplans / dualité LP en dimension finie). La version
  mono-livret livrée ici en constitue le noyau tractable (faisabilité Lean « MOYENNE »,
  cf #4050).

## Références croisées
- `Utility` (même lake) : représentation d'utilité espérée vNM — l'autre fondation
  de la théorie de la décision sous risque.
- Infer-14 (Infer.NET) : utilité espérée bayésienne sous postérieure.
- PyMC-1 (PyMC) : estimation d'utilité espérée par échantillonnage postérieur.
-/
