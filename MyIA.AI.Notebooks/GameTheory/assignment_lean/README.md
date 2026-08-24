# assignment_lean — Problème d'affectation (Kuhn-Munkres)

Lake compagnon du notebook [GameTheory-27-Munkres-Assignment.ipynb](../GameTheory-27-Munkres-Assignment.ipynb), hommage à James R. Munkres (1930-2026) — issue #12598 (1/3).

Il formalise la **charpente de correction** de la méthode hongroise (Kuhn 1955, Munkres 1957) :

| Module | Contenu |
|---|---|
| `Assignment/Definitions.lean` | Matrice de coûts, matching parfait (permutation), valeur, optimalité |
| `Assignment/Duality.lean` | Potentiels duaux `u`/`v`, réalisabilité duale, **dualité faible** |
| `Assignment/Optimality.lean` | Certificat d'optimalité à **gap nul** (+ lemme des arêtes d'égalité) |
| `Assignment/KuhnMunkres.lean` | Graphe d'égalité, **invariant de sortie**, **resserrement hongrois** préserve la réalisabilité duale |

Chaque module a son sibling `_en` (docstrings anglaises, namespace `Assignment_en`) — convention i18n EPIC #4980.

## Théorèmes

- `weak_duality` — toute affectation est au-dessus de la valeur duale (reindexation le long de la permutation + monotonie terme à terme).
- `dualValue_eq_of_edges` — toutes les arêtes du matching d'égalité ⇒ valeurs primale et duale coïncident.
- `optimality_of_zero_gap` — dual réalisable + gap nul ⇒ optimal. C'est le triple test du notebook GT-27 (section 3) devenu preuve noyau.
- `kuhn_munkres_correct` — assemblage : dual réalisable + arêtes toutes d'égalité ⇒ optimal (invariant de sortie de l'algorithme).
- `dualFeasible_tighten` — le resserrement `u += δ` / `v -= δ` (δ = min marge sur les arêtes sortantes) préserve la réalisabilité duale. C'est l'étape qui, répétée, fait croître le graphe d'égalité jusqu'à l'augmentation.

## Hors scope (délibéré)

Preuve de terminaison et complexité O(n³) (Edmonds-Karp/Tomizawa) — la correction structurelle par dualité suffit au propos (cf issue). Le pont Shapley-Shubik (cœur = polytope dual) est traité numériquement dans le notebook ; sa formalisation coopérative vivrait dans `game_theory_lean/CooperativeGames/`.

## Build

Toolchain v4.32.1, Mathlib v4.32.1 (cache). `lake build Assignment` (WSL + elan, cf `docs/reference/kernels-runtime.md`).
