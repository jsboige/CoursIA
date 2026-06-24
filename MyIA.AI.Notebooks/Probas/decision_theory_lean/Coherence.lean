import Coherence.Basic
import Coherence.DutchBook

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

## Statut
- Prouvé sans `sorry` : la direction constructive (violation de l'inclusion–exclusion
  ⟹ Dutch Book avec mises explicites `(1,1,−1,−1)` ou l'inverse), et la cohérence ⟹
  additivité sur deux événements.
- Ouvert (jalon suivant) : la réciproque « additivité ⟹ cohérence » et le
  `coherent_iff_probability` complet (additivité générale + normalisation
  `q ∅ = 0`, `q univ = 1`), qui nécessitent la séparation d'hyperplans / dualité LP
  en dimension finie (faisabilité Lean « MOYENNE », cf #4050).

## Références croisées
- `Utility` (même lake) : représentation d'utilité espérée vNM — l'autre fondation
  de la théorie de la décision sous risque.
- Infer-14 (Infer.NET) : utilité espérée bayésienne sous postérieure.
- PyMC-14 (PyMC) : estimation d'utilité espérée par échantillonnage postérieur.
-/
