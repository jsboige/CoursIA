# decision_theory_lean — Théorie de la décision (Lean 4)

Lake **à la racine de la série `Probas`**, formalisant des résultats canoniques de
théorie de la décision — visible des deux pistes de la série (Infer.NET / PyMC).

Deux modules livrés :

- **Gittins** : le problème du **bandit manchot multi-bras** (multi-armed bandit) et
  l'**indice de Gittins** (Gittins 1979, Weber 1992) — la politique optimale pour le
  bandit actualisé à horizon infini. Les **briques de l'actualisation géométrique
  sont entièrement prouvées** (PR #2911) ; le **théorème phare d'optimalité est
  énoncé mais intraitable** dans le Mathlib actuel (pas de formalisation
  MDP/Bellman), maintenu en `sorry`.
- **Utility** : la **représentation d'utilité espérée** de **von Neumann–Morgenstern**
  (PR courante, `See #4049`). Le module formalise les **quatre axiomes vNM**
  (complétude, transitivité, indépendance, continuité/Archimède) sur les loteries,
  prouve **sans aucun `sorry`** la **direction saine** du théorème (existence d'une
  représentation ⟹ rationalité, i.e. les quatre axiomes) et la **stabilité affine**
  (cardinalité : l'utilité n'est déterminée qu'à transformation affine positive
  près). La **direction d'existence** (rationalité ⟹ représentation, Herstein–Milnor
  1953) est documentée comme **jalon ouvert**.

Modules prévus (roadmap Lean #4038) : cohérence **Dutch Book / de Finetti** (#4050).
Notebook compagnon Lean :
[`Infer/Infer-20b-Lean-Gittins.ipynb`](../Infer/Infer-20b-Lean-Gittins.ipynb).

## Statut

- **Toolchain** : `leanprover/lean4:v4.30.0-rc2`
- **Sorry** : **5** — tous dans `Gittins/GittinsTheorem.lean` (le théorème
  d'optimalité + propriétés de l'indice). `Gittins/Discount.lean` = **0 sorry**
  (entièrement prouvé), `Gittins/Basic.lean` = 0. Le module **`Utility` entier =
  0 sorry** (direction saine vNM + stabilité affine, entièrement prouvé).
- **Build** : `lake build Gittins Utility` (dépend de Mathlib4)
- **Dépendances** : Mathlib4 (`v4.30.0-rc2`) — analyse réelle pour les lemmes
  d'actualisation, structure ordonnée et affine de `ℝ` pour vNM

## Ce qui est formalisé

Un **bandit manchot multi-bras** : à chaque étape, une politique choisit l'un de
plusieurs bras (`BanditArm`) et observe une récompense ; l'objectif est de maximiser
la récompense actualisée espérée totale (actualisation `γ ∈ (0,1)`). L'**indice de
Gittins** d'un bras est le point fixe d'un problème d'arrêt optimal ; la **politique
à indice de Gittins** (jouer le bras d'indice le plus élevé) est optimale pour le
bandit actualisé.

La formalisation est scindée en une couche **prouvée** et une couche **énoncée** :

- **Prouvé** (`Discount.lean`) : les identités de série géométrique sous-tendant la
  valeur actualisée — `∑' γ^n = 1/(1-γ)`, `∑' γ^n·r = r/(1-γ)`, et
  `discount_monotone` (γ₁ ≤ γ₂ ⇒ ∑' γ₁^n ≤ ∑' γ₂^n). `discount_monotone` est prouvé
  **en forme close** via `geometric_series_converges` +
  `one_div_le_one_div_of_le`, en contournant l'absence de `tsum_le_tsum` sur le `ℝ`
  nu dans Mathlib v4.30.0-rc2.
- **Énoncé, intractable** (`GittinsTheorem.lean`) : `gittinsIndex` (arrêt optimal),
  `gittins_optimality` (le théorème central — la politique à indice maximise la
  récompense actualisée espérée), `gittins_index_known_arm`,
  `gittins_index_monotone_discount`. Tous en `sorry`.

### Représentation d'utilité espérée (von Neumann–Morgenstern)

Le module **`Utility`** formalise le théorème de **représentation d'utilité
espérée** (von Neumann–Morgenstern 1944) : un agent classe des **loteries**
(distributions de probabilité à support fini sur un ensemble fini d'issues `α`) selon
une **préférence** `P p q` (« `p` faiblement préférée à `q` »). Ce théorème relie le
comportement axiomatique au **maximisation d'utilité espérée** : `P` satisfait les
quatre axiomes vNM **si et seulement si** il existe une utilité `u : α → ℝ` telle que
`P p q ↔ E_p[u] ≥ E_q[u]`, unique à transformation affine positive près.

La formalisation livre **sans aucun `sorry`** la **direction saine** et la
**stabilité affine** :

- **Prouvé** (`Representation.lean`) :
  - `expected_utility_rep_is_rational` — **direction saine** : si une utilité `u`
    représente `P` (`P p q ↔ E_p[u] ≥ E_q[u]`), alors `P` est **rationnelle**
    (satisfait les quatre axiomes). Chaque axiome se réduit à un fait élémentaire sur
    l'ordre et la structure affine de `ℝ` : la complétude vient de la totalité de `≥`
    sur `ℝ`, la transitivité de sa transitivité, l'indépendance de l'**affinité de
    l'espérance** (`E_{t·p+(1-t)·r}[u] = t·E_p[u]+(1-t)·E_r[u]`), la continuité de
    l'existence d'un **point de croisement** de l'interpolation affine.
  - `affine_rep_is_rep` — **cardinalité / stabilité affine** : si `u` représente
    `P`, toute transformée affine positive `a·u + b` (avec `a > 0`) représente aussi
    `P`. C'est la raison pour laquelle seules les **différences** d'utilité (pas les
    niveaux) sont identifiées par les données de choix.
- **Énoncé, jalon ouvert** (direction d'existence) : la réciproque — **toute
  préférence rationnelle admet une représentation d'utilité espérée** — est la moitié
  substantielle du théorème (Herstein & Milnor, 1953). Sa preuve procède en montrant
  que la préférence est représentée par un **fonctionnel linéaire** sur le simplexe
  des loteries (l'indépendance donne la linéarité le long des mélanges, la continuité
  l'étend à l'intérieur), puis que ce fonctionnel est une espérance `E_p[u]` pour un
  certain `u : α → ℝ`. Cela requiert un argument non trivial de séparation / algèbre
  linéaire et est laissé comme **jalon naturel**. Il est délibérément **non énoncé
  comme un `sorry`** : la bibliothèque actuelle est entièrement `sorry`-free.

Les primitives (`Utility/Basic.lean`) : `Lottery` (loterie à support fini sur un
`Fintype`), `expectation`, le mélange convexe `mix`, et les identités affine
d'espérance (`expectation_mix`, `expectation_affine`). Les quatre axiomes sont
définis dans `Utility/Axioms.lean`.

#### Lien avec la piste Infer.NET / PyMC

La formalisation est le **fondement théorique des décisions** prises dans les
notebooks d'inférence bayésienne de la série `Probas` :

- **Infer-14** (Infer.NET) : les utilités à *moyenne a posteriori* calculées là sont
  une instance de `expectation` sur une **postérieure bayésienne** ; la
  représentation vNM justifie de **classer les actions par utilité espérée**.
- **PyMC-14** (PyMC) : les estimations d'utilité espérée par **échantillonnage de la
  postérieure** approximent le même opérateur `expectation` ; l'**unicité affine**
  explique pourquoi seules les **différences** d'utilité (pas les niveaux) sont
  identifiables à partir des données de choix.

## Modules

| Fichier | Lignes | sorry | Contenu |
|---------|--------|-------|---------|
| `Gittins/Basic.lean` | 37 | 0 | Types fondamentaux — `BanditArm`, `BanditInstance` (bras + actualisation γ), `Policy := Nat → Nat`, `RewardHistory`, `pullCount`, `empiricalMean`. Lean 4 pur, sans Mathlib. |
| `Gittins/Discount.lean` | 68 | 0 | Actualisation géométrique **prouvée** via l'analyse réelle de Mathlib : `geometric_series_converges`, `one_minus_gamma_pos`, `present_value_constant`, `discount_monotone`. |
| `Gittins/GittinsTheorem.lean` | 96 | 5 | Le théorème phare **énoncé avec sorry** : `gittinsIndex`, `gittinsPolicy` (argmax), `gittins_optimality`, `gittins_index_known_arm`, `gittins_index_monotone_discount`. (`gittins_beats_greedy` est un placeholder `: True := trivial`, pas un sorry.) |
| `Gittins.lean` | 19 | 0 | Imports parapluie |
| `Utility/Basic.lean` | 91 | 0 | Primitives vNM — `Lottery` (loterie sur `Fintype`), `expectation`, mélange convexe `mix` (preuve de validité), identités affine d'espérance (`expectation_mix`, `expectation_add`, `expectation_smul`, `expectation_const`, `expectation_affine`). |
| `Utility/Axioms.lean` | 65 | 0 | Les **quatre axiomes vNM** — `IsComplete`, `IsTransitive`, `IsIndependent`, `IsContinuous` (solvabilité des mélanges), `IsRational`, plus `StrictPref`. |
| `Utility/Representation.lean` | 181 | 0 | **Direction saine prouvée** (`rep_complete`, `rep_transitive`, `rep_independent`, `rep_continuous`, `expected_utility_rep_is_rational`) + **stabilité affine** (`affine_rep_is_rep`). Direction d'existence documentée comme jalon ouvert. |
| `Utility.lean` | ~30 | 0 | Imports parapluie + doc de statut |

## Pourquoi le théorème d'optimalité est intractable

Une preuve complète de `gittins_optimality` requiert :

1. Une **caractérisation par arrêt optimal** de l'indice de Gittins (valeur de
   retraite / point fixe),
2. La **décomposabilité de l'indice** entre bras indépendants,
3. Une **récurrence sur l'horizon de planification**, et
4. Une **espérance formelle** sur la distribution de récompense.

Mathlib (v4.30.0-rc2) n'a **aucune formalisation de MDP, de bandit ou d'équation de
Bellman**, ni d'API d'espérance mesurée-théorique adaptée ici. Une preuve complète est
estimée à ~2000–5000 lignes de définitions support — de niveau recherche, au-delà
d'une seule PR. Le théorème est donc **énoncé** (avec l'énoncé précis préservé dans
son docstring) plutôt qu'affaibli silencieusement.

## Build

```bash
# Depuis ce répertoire (WSL requis)
lake build Gittins Utility
# Dépend de Mathlib4 — le premier build est lourd, les builds suivants utilisent le cache
```

## Notebook compagnon

[`Infer/Infer-20b-Lean-Gittins.ipynb`](../Infer/Infer-20b-Lean-Gittins.ipynb) — présentation
pédagogique du problème du bandit et de l'indice de Gittins, reliant le matériel de
programmation probabiliste Infer.NET à la formalisation Lean.

## Voir aussi

- **PR #2911** — `discount_monotone` prouvé en forme close (sorry 1→0)
- **`Probas/Infer/`** — série probabiliste Infer.NET (inférence bayésienne, priors conjugués) ; **Infer-14** = utilité espérée sous postérieure bayésienne
- **`Probas/PyMC/`** — série PyMC ; **PyMC-14** = utilité espérée par échantillonnage de postérieure
- **Epic #2651** — audit README/structure (série Lean)
