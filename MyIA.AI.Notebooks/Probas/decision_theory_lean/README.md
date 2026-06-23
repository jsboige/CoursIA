# decision_theory_lean — Théorie de la décision (Lean 4)

Lake **à la racine de la série `Probas`**, formalisant des résultats canoniques de
théorie de la décision — visible des deux pistes de la série (Infer.NET / PyMC).
Premier module livré : le problème du **bandit manchot multi-bras** (multi-armed
bandit) et l'**indice de Gittins** (Gittins 1979, Weber 1992) — la politique
optimale pour le bandit actualisé à horizon infini. Les **briques de l'actualisation
géométrique sont entièrement prouvées** (PR #2911) ; le **théorème phare
d'optimalité est énoncé mais intraitable** dans le Mathlib actuel (pas de
formalisation MDP/Bellman), maintenu en `sorry`.

Modules prévus (roadmap Lean #4038) : représentation **von Neumann–Morgenstern**
(#4049) et cohérence **Dutch Book / de Finetti** (#4050). Notebook compagnon Lean :
[`Infer/Infer-20b-Lean-Gittins.ipynb`](../Infer/Infer-20b-Lean-Gittins.ipynb).

## Statut

- **Toolchain** : `leanprover/lean4:v4.30.0-rc2`
- **Sorry** : **5** — tous dans `GittinsTheorem.lean` (le théorème d'optimalité +
  propriétés de l'indice). `Discount.lean` = **0 sorry** (entièrement prouvé),
  `Basic.lean` = 0.
- **Build** : `lake build Gittins` (dépend de Mathlib4)
- **Dépendances** : Mathlib4 (`v4.30.0-rc2`) — analyse réelle pour les lemmes d'actualisation

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

## Modules

| Fichier | Lignes | sorry | Contenu |
|---------|--------|-------|---------|
| `Gittins/Basic.lean` | 37 | 0 | Types fondamentaux — `BanditArm`, `BanditInstance` (bras + actualisation γ), `Policy := Nat → Nat`, `RewardHistory`, `pullCount`, `empiricalMean`. Lean 4 pur, sans Mathlib. |
| `Gittins/Discount.lean` | 68 | 0 | Actualisation géométrique **prouvée** via l'analyse réelle de Mathlib : `geometric_series_converges`, `one_minus_gamma_pos`, `present_value_constant`, `discount_monotone`. |
| `Gittins/GittinsTheorem.lean` | 96 | 5 | Le théorème phare **énoncé avec sorry** : `gittinsIndex`, `gittinsPolicy` (argmax), `gittins_optimality`, `gittins_index_known_arm`, `gittins_index_monotone_discount`. (`gittins_beats_greedy` est un placeholder `: True := trivial`, pas un sorry.) |
| `Gittins.lean` | 19 | 0 | Imports parapluie |

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
lake build Gittins
# Dépend de Mathlib4 — le premier build est lourd, les builds suivants utilisent le cache
```

## Notebook compagnon

[`Infer/Infer-20b-Lean-Gittins.ipynb`](../Infer/Infer-20b-Lean-Gittins.ipynb) — présentation
pédagogique du problème du bandit et de l'indice de Gittins, reliant le matériel de
programmation probabiliste Infer.NET à la formalisation Lean.

## Voir aussi

- **PR #2911** — `discount_monotone` prouvé en forme close (sorry 1→0)
- **`Probas/Infer/`** — série probabiliste Infer.NET (inférence bayésienne, priors conjugués)
- **Epic #2651** — audit README/structure (série Lean)
