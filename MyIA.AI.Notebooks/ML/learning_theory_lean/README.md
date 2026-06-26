# learning_theory_lean — Learning theory (Perceptron / Novikoff + PAC / Valiant), Lean 4

Lake Lean 4 (Mathlib) à la racine de la série **ML**, mutualisant deux résultats
fondamentaux de **théorie de l'apprentissage** sous un même umbrella généraliste
(cf `decision_theory_lean` qui co-localise Gittins + Utility + Coherence) :

1. **Module `Perceptron`** — convergence du Perceptron (théorème de Novikoff,
   1962) : pour des données linéairement séparables de marge `γ > 0` et de rayon
   `R`, l'algorithme effectue au plus `(R/γ)²` mises à jour avant de trouver un
   classifieur correct. Le sous-module `Tightness` montre en outre que cette borne
   est **serrée** (atteinte avec égalité par un témoin concret sur `ℂ`).
2. **Module `PacLearning`** — théorie PAC (Valiant, 1984) : cadre de la
   **généralisation** — *quand* une hypothèse bien classée sur l'échantillon
   généralise-t-elle, et avec *combien d'exemples* ? Ce module pose le modèle
   (distribution, erreur vraie `trueError`, erreur empirique `empError`) et les
   propriétés élémentaires ; la **borne de complexité d'échantillon** classe finie
   `m ≥ (1/ε)(ln|H| + ln(1/δ))` (Hoeffding + union bound) est itération suivante.

C'est le **premier lake Lean de la série ML** (aucun lake Lean en ML auparavant,
roadmap #4038 Tier 2). La preuve de Novikoff est **géométrique élémentaire** :
deux inégalités de croissance du vecteur de poids `wₖ`, combinées par
Cauchy–Schwarz, donnent la borne. Les deux modules sont **entièrement 0-sorry**
sur leur périmètre prouvé : le module `Perceptron` est complet (Novikoff +
serrage `Tightness`) ; le module `PacLearning` livre son itération 1 (modèle +
propriétés élémentaires), la borne phare de Valiant étant documentée OPEN (pas
sorry-backed).

## Statut

- **Toolchain** : `leanprover/lean4:v4.31.0-rc1` + Mathlib4 (`v4.31.0-rc1`)
- **Sorry** : **0** sur tout le module. La borne `novikoff_mistake_bound`
  (`n · γ² ≤ R²`), le Lemme A d'alignement (`⟪wₖ, u⟫ ≥ kγ`) et le Lemme B de norme
  (`‖wₖ‖² ≤ kR²`) sont entièrement prouvés, ainsi que le **serrage**
  `novikoff_bound_is_sharp` (témoin sur `ℂ` atteignant l'égalité `n·γ² = R²`).
- **Build** : `lake build Perceptron` (dépend de Mathlib4)

## Ce qui est formalisé

Sur un **espace préhilbertien réel abstrait** `V` (la borne est indépendante de la
dimension), la règle de mise à jour du perceptron est :

```
w_{k+1} = wₖ + yₖ · xₖ        (w₀ = 0)
```

lancée sur chaque erreur de classification `(xₖ, yₖ)` (étiquettes `yₖ ∈ {±1}`). Une
**exécution valide** (`PerceptronRun`) enregistre qu'on se place sur `n` mises à
jour consécutives, chacune étant une **erreur** (`yₖ · ⟨wₖ, xₖ⟩ ≤ 0`), sur des points
de norme `≤ R` séparés par un vecteur unitaire `u` avec marge `γ`.

Ces deux invariants (erreur + marge) sont exactement ce qui fait fonctionner la
preuve de Novikoff : l'erreur plafonne la croissance de `‖w‖`, la marge garantit
celle de `⟨w, u⟩`.

### Prouvé (0 sorry)

- **Lemme A — alignement** (`align_growth`) : `⟪wₖ, u⟫_ℝ ≥ k · γ`. Chaque erreur
  ajoute `yₖ · xₖ` à `w`, et l'hypothèse de marge garantit
  `yₖ · ⟪u, xₖ⟫_ℝ ≥ γ`, donc l'alignement sur le séparateur croît d'au moins `γ`.
- **Lemme B — norme** (`norm_bound`) : `‖wₖ‖² ≤ k · R²`. Chaque erreur ajoute au
  plus `R²` à `‖w‖²` (via le développement `‖a + b‖² = ‖a‖² + 2⟪a, b⟫ + ‖b‖²`), le
  terme croisé étant `≤ 0` car la mise à jour est une erreur.
- **Théorème de convergence** (`novikoff_mistake_bound`) : Cauchy–Schwarz
  `⟪wₙ, u⟫ ≤ ‖wₙ‖ · ‖u‖ = ‖wₙ‖` (avec `‖u‖ = 1`) donne `n · γ ≤ ‖wₙ‖`, donc
  `(n · γ)² ≤ ‖wₙ‖² ≤ n · R²`, i.e. **`n · γ² ≤ R²`**.

### Serrage de la borne (sharpness)

- **`novikoff_bound_is_sharp`** (`Tightness.lean`) : la borne `(R/γ)²` est
  **optimale** — on exhibe une exécution valide sur `ℂ` (espace préhilbertien réel
  de dimension 2) qui l'**atteint avec égalité** `n · γ² = R²`. Deux points
  `x₀ = 1 + I`, `x₁ = 1 − I` (demi-droites orthogonales), tous deux d'étiquette
  `+1`, séparés par `u = 1` avec marge `γ = 1`, de norme `‖xₖ‖ = √2` (donc
  `R = √2`), et `n = 2` : on a `n · γ² = 2 = (√2)² = R²`. Puisque l'inégalité
  universelle `≤ R²` et l'égalité du témoin coexistent, aucune borne de la forme
  `n · γ² ≤ c · R²` avec `c < 1` n'est valable sur toutes les exécutions : la
  constante `1` devant `(R/γ)²` est la meilleure possible.

La preuve ne dépend d'aucune hypothèse de dimension : tout vient de la structure
d'espace préhilbertien réel (`InnerProductSpace ℝ V`), de la commutativité du
produit scalaire réel, de Cauchy–Schwarz (`real_inner_le_norm`) et du développement
du carré de la norme d'une somme (`real_inner_add_add_self`), tous fournis par
Mathlib.

## Modules

| Fichier | sorry | Contenu |
|---------|-------|---------|
| `Perceptron/Data.lean` | 0 | Espace préhilbertien réel, `norm_sq_eq_inner_self`, développement `norm_add_sq_eq` (`‖a+b‖² = ‖a‖² + 2⟪a,b⟫ + ‖b‖²`), étiquettes `±1` (`IsLabel`, `LabeledPoint`). |
| `Perceptron/Perceptron.lean` | 0 | Suite des poids `perceptronWeights` (`w₀ = 0`, `w_{k+1} = wₖ + yₖ · xₖ`), structure `PerceptronRun` (données séparables + trace d'erreurs + invariants de marge/rayon). |
| `Perceptron/Convergence.lean` | 0 | Lemme A `align_growth` (`⟪wₖ,u⟫ ≥ kγ`), Lemme B `norm_bound` (`‖wₖ‖² ≤ kR²`), Cauchy–Schwarz ⟹ **`novikoff_mistake_bound`** (`n · γ² ≤ R²`). |
| `Perceptron/Tightness.lean` | 0 | **Saturation de la borne** : témoin concret sur `ℂ` (`x₀ = 1+I`, `x₁ = 1−I`, séparés par `u = 1`, `n = 2`, `γ = 1`, `R = √2`) atteignant l'égalité `n·γ² = R²` ⟹ **`novikoff_bound_is_sharp`** (la borne `(R/γ)²` est optimale — aucune constante `< 1` ne l'améliore). Utilitaire `complex_inner_re` (produit scalaire réel de `ℂ` en coordonnées). |
| `Perceptron.lean` | 0 | Imports parapluie + doc de statut. |
| `PacLearning/Data.lean` | 0 | Cadre PAC (Valiant 1984) : `Distribution` (poids normalisé `X → ℝ`), erreur vraie `trueError` (masse des instances mal classées), erreur empirique `empError` (proportion d'erreurs sur un échantillon). Propriétés élémentaires symétriques pour les deux erreurs : `trueError_nonneg`/`empError_nonneg` (`≥ 0`), `trueError_le_one`/`empError_le_one` (`≤ 1`), `trueError_self`/`empError_self` (`h=f ⟹ 0`), `trueError_comm`/`empError_comm` (symétrie `h↔f`). |
| `PacLearning.lean` | 0 | Imports parapluie + doc de statut. |

## Build

```bash
# Depuis ce répertoire (WSL recommandé)
lake build Perceptron    # théorème de Novikoff
lake build PacLearning   # cadre PAC (modèle + propriétés élémentaires)
# Dépend de Mathlib4 — le premier build est lourd, les builds suivants utilisent le cache
```

## Notebook compagnon

Le lake est le **livrable formel** (convention des lakes frères : `lake build`
SUCCESS = preuve d'exécution). Il vient en pendant prouvé des notebooks de la
série **ML** : [`ML.Net/`](../ML.Net/) (classification linéaire, entraînement et
évaluation de classifieurs en C#/.NET), dont le perceptron est l'ancêtre
historique de la classification linéaire. La formalisation Lean démontre *pourquoi*
le perceptron converge — la garantie algorithmique que la pratique ML.NET met en
œuvre. Le module `PacLearning` a son pendant empirique dans le notebook companion
`02-ML-Cours/2.8-Theorie-PAC` (issue #4294).

## Référence

- A. B. J. Novikoff, *On convergence proofs for perceptrons*, Symposium on the
  Mathematical Theory of Automata, Polytechnic Institute of Brooklyn (1962).
- L. G. Valiant, *A theory of the learnable*, Communications of the ACM **27**
  (1984).
- S. Shalev-Shwartz & S. Ben-David, *Understanding Machine Learning*, Cambridge
  University Press (2014), §2 (classes finies) et §6 (VC dimension).

## Voir aussi

- **Issue #4051** — création du lake + module Perceptron (roadmap Lean #4038, Tier 2 « first ML theorem »)
- **Issue #4293** — renommage `perceptron_lean → learning_theory_lean` + module PacLearning (mutualisation, cf `decision_theory_lean`)
- **`ML/`** — série Machine Learning (ML.NET C#, Data Science with Agents Python)
- **Epic #2651** — prose pédagogique README
