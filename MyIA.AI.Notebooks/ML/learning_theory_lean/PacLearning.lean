import Mathlib
import PacLearning.Data
import PacLearning.Sample

/-!
# PacLearning — théorie PAC (Valiant 1984), module classe finie, Lean 4

Module `PacLearning` du lake `learning_theory_lean`, frère de `Perceptron` (théorème
de Novikoff). Tandis que `Perceptron` formalise la **convergence d'un algorithme**
spécifique (le perceptron, borne `(R/γ)²`), `PacLearning` formalise la **théorie de
la généralisation** au sens de Valiant (1984) : *quand* peut-on garantir qu'une
hypothèse bien classée sur l'échantillon généralise, et avec *combien d'exemples* ?

## Cadre PAC (Probably Approximately Correct)

Pour une classe d'hypothèses finie `H` (sur un espace d'instances `X` muni d'une
distribution `D`), la **complexité d'échantillon** dit : pour atteindre une erreur
vraie `≤ ε` avec probabilité `≥ 1 - δ` sur un échantillon `S ∼ D^m`, il suffit de

    m ≥ (1/ε) · (ln |H| + ln(1/δ))

exemples i.i.d. (borne de Shalev-Shwartz & Ben-David, *Understanding Machine
Learning*, §2). La preuve combine :
1. **Hoeffding** — pour une hypothèse `h` fixée, `|L_S(h) - L_D(h)|` est concentré
   autour de `0` quand `m` croît ;
2. **Union bound** sur la classe finie `H` — la probabilité qu'**aucune**
   hypothèse ne dévie de plus de `ε` de son erreur vraie est `≥ 1 - δ` dès que
   `m` dépasse le seuil ci-dessus.

## Itération 1 — modèle + propriétés élémentaires (livré)

- `PacLearning/Data.lean` — distribution `Distribution` (poids normalisé `X → ℝ`),
  erreur vraie `trueError` (masse des instances mal classées), erreur empirique
  `empError` (proportion d'erreurs sur un échantillon). Propriétés **élémentaires
  0-sorry**, symétriques pour les deux erreurs : non-négativité (`trueError_nonneg`,
  `empError_nonneg`), borne supérieure `≤ 1` (`trueError_le_one`, `empError_le_one`),
  nullité quand `h = f` (`trueError_self`, `empError_self`), symétrie `h ↔ f`
  (`trueError_comm`, `empError_comm`).

## Itération 2 — complexité d'échantillon (en cours, décomposée en briques)

⚠ **Mathlib v4.31.0-rc1 n'expose PAS de lemme de concentration de Hoeffding**
(vérifié : ni `Probability.Hoeffding`, ni Chernoff). La borne se prouve donc
**en self-contained** via la méthode de Chernoff (`log t ≤ t − 1` + Markov sur
`exp(t · X̄)`), par briques atomiques 0-sorry :

- `PacLearning/Sample.lean` (ce livrable, **brique 1/3**) — distribution produit
  `D^m` sur l'espace des échantillons `Fin n → X` : poids `sampleWeight`
  (`∏ i, D.weight (S i)`), non-négativité, **normalisation**
  `sampleWeight_sum_one` (`∑ S, sampleWeight D S = 1` via Fubini discret
  `sum_pow'` puis `D.sum_one`). C'est le cadre probabiliste requis pour parler
  de tirages i.i.d. `S ∼ D^m`.
- **Brique 2/3 — OPEN** : concentration de Hoeffding-for-Bernoulli,
  `ℙ_S [ |empError − trueError| > ε ] ≤ 2·exp(−2mε²)` (Markov + `log t ≤ t − 1`
  sur les indicateurs `𝟙[h(S i) ≠ f(S i)]`, self-contained).
- **Brique 3/3 — OPEN** : `pac_finite_class_bound`, `m ≥ (1/ε)(ln|H| + ln(1/δ))`
  (union bound sur `H` fini, `Finset.sum_le_*`). Le théorème phare de Valiant.

## Référence

- L. G. Valiant, *A theory of the learnable*, Communications of the ACM **27**
  (1984).
- S. Shalev-Shwartz & S. Ben-David, *Understanding Machine Learning*, Cambridge
  University Press (2014), §2 (finite hypothesis classes) et §6 (VC dimension).
- Voir l'issue #4293 (roadmap Lean #4038).
-/

namespace PacLearning

/-- Statut : itération 1 livrée (modèle + propriétés élémentaires 0-sorry) ;
itération 2 en cours — **brique 1/3 livrée** (`Sample.lean` : distribution produit
`D^m` + normalisation). Briques 2/3 (Hoeffding-for-Bernoulli self-contained) et
3/3 (`pac_finite_class_bound` union bound) documentées OPEN. -/
abbrev Status : Prop := True

end PacLearning
