# perceptron_lean — Convergence du Perceptron (théorème de Novikoff), Lean 4

Lake Lean 4 (Mathlib) à la racine de la série **ML**, formalisant le **théorème de
convergence du Perceptron** (Novikoff, 1962) : pour des données linéairement
séparables de marge `γ > 0` et de rayon `R`, l'algorithme du perceptron effectue au
plus `(R/γ)²` mises à jour (erreurs de classification) avant de trouver un
classifieur correct.

C'est le **premier théorème Lean de la série ML** (aucun lake Lean en ML
auparavant, roadmap #4038 Tier 2). La preuve est **géométrique élémentaire et
entièrement 0-sorry** : deux inégalités de croissance du vecteur de poids `wₖ`,
combinées par Cauchy–Schwarz, donnent la borne.

## Statut

- **Toolchain** : `leanprover/lean4:v4.31.0-rc1` + Mathlib4 (`v4.31.0-rc1`)
- **Sorry** : **0** sur tout le module. La borne `novikoff_mistake_bound`
  (`n · γ² ≤ R²`), le Lemme A d'alignement (`⟪wₖ, u⟫ ≥ kγ`) et le Lemme B de norme
  (`‖wₖ‖² ≤ kR²`) sont entièrement prouvés.
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
| `Perceptron.lean` | 0 | Imports parapluie + doc de statut. |

## Build

```bash
# Depuis ce répertoire (WSL recommandé)
lake build Perceptron
# Dépend de Mathlib4 — le premier build est lourd, les builds suivants utilisent le cache
```

## Notebook compagnon

Le lake est le **livrable formel** (convention des lakes frères : `lake build`
SUCCESS = preuve d'exécution). Il vient en pendant prouvé des notebooks de la
série **ML** : [`ML.Net/`](../ML.Net/) (classification linéaire, entraînement et
évaluation de classifieurs en C#/.NET), dont le perceptron est l'ancêtre
historique de la classification linéaire. La formalisation Lean démontre *pourquoi*
le perceptron converge — la garantie algorithmique que la pratique ML.NET met en
œuvre.

## Référence

A. B. J. Novikoff, *On convergence proofs for perceptrons*, Symposium on the
Mathematical Theory of Automata, Polytechnic Institute of Brooklyn (1962).

## Voir aussi

- **Issue #4051** — création du lake (roadmap Lean #4038, Tier 2 « first ML theorem »)
- **`ML/`** — série Machine Learning (ML.NET C#, Data Science with Agents Python)
- **Epic #2651** — prose pédagogique README
