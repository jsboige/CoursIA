---
title: Lean i18n policy — harmonisation FR/EN des docstrings et commentaires
status: proposed (See #4980)
owner: po-2026
date: 2026-07-03
---

# Lean i18n policy — harmonisation FR/EN des docstrings et commentaires

**Statut : proposition (work in progress, scope #4980).**
**Périmètre : `MyIA.AI.Notebooks/**/*.lean` (hors vendored `.lake/packages/**`).**

Cette politique couvre uniquement les **prolégomènes textuels** des fichiers Lean
(docstrings `/-- ... -/` et commentaires de ligne `-- ...`). Elle ne touche PAS :
le code Lean (qui est par construction agnostique à la langue),
les `lakefile.lean` (infra), ni les README de lake (régis par `readme-french-first.md`).

---

## 1. État des lieux (inventaire FR/EN par lake)

**Méthode.** Heuristique lexicale (`/tmp/lean_fr_en_3level.py`) sur 27 sub-lakes
du repo, 207 fichiers `.lean` au total, hors `.lake/`. Pour chaque docstring et
commentaire de ligne de plus de 3 caractères, on calcule un score FR et EN
pondéré : accents (5 pts), mots lourds FR/EN (3 pts), stop-words (1 pt).
Le pourcentage `%FR = 100 * score_FR / (score_FR + score_EN)`.

> **Verdict par lake** : FR-majeure (≥80 %), mixte-FR+ (≥50 %), mixte-EN (≤50 %),
> EN-majeure (≤20 %). Le seuil 50 % départage « cible atteinte » vs « cible ouverte ».

### 1.1 Sub-lakes déjà FR-majeures (12 sur 27) — cible atteinte

| Sub-lake | Files | %FR | Verdict |
|----------|------:|----:|---------|
| `GameTheory/minimax_lean` | 5 | 100% | FR-majeure |
| `GameTheory/repeated_games_lean` | 6 | 86% | FR-majeure |
| `ML/learning_theory_lean` | 19 | 99% | FR-majeure |
| `Probas/decision_theory_lean` | 13 | 73% | mixte-FR+ |
| `QuantConnect/kelly_lean` | 4 | 100% | FR-majeure |
| `Search/astar_lean` | 6 | 100% | FR-majeure |
| `Sudoku/sudoku_lean` | 4 | 100% | FR-majeure |
| `SymbolicAI/Lean/finiteness_lean` | 3 | 100% | FR-majeure |
| `SymbolicAI/Lean/mathlib_examples` | 3 | 100% | FR-majeure |
| `SymbolicAI/Planners` | 4 | 99% | FR-majeure |
| `SymbolicAI/SmartContracts` | 5 | 100% | FR-majeure |
| `SymbolicAI/Tweety` | 7 | 97% | FR-majeure |

Ces lakes **ne nécessitent pas d'harmonisation** : ils suivent déjà la convention
FR. Pas d'action recommandée sauf régression ponctuelle.

### 1.2 Sub-lakes EN-majeures (15 sur 27) — harmonisation requise

| Sub-lake | Files | %FR | Verdict |
|----------|------:|----:|---------|
| `GameTheory/cooperative_games_lean` | 5 | 15% | EN-majeure |
| `GameTheory/examples` | 1 | 16% | EN-majeure |
| `GameTheory/lean_game_defs` | 6 | 28% | mixte-EN |
| `GameTheory/lean_game_defs_ext` | 11 | 10% | EN-majeure |
| `GameTheory/social_choice_lean` | 10 | 23% | mixte-EN |
| `GameTheory/social_choice_lean_peters` | 2 | 0% | EN-majeure (vendored) |
| `GameTheory/stable_marriage_lean` | 7 | 10% | EN-majeure |
| `GameTheory/conway_cgt_lean` | 2 | 7% | EN-majeure |
| `SymbolicAI/Lean/agent_tests` | 10 | 17% | EN-majeure |
| `SymbolicAI/Lean/calibration_lean` | 5 | 20% | EN-majeure |
| `SymbolicAI/Lean/conway_lean` | 25 | 15% | EN-majeure |
| `SymbolicAI/Lean/grothendieck_lean` | 25 | 17% | EN-majeure |
| `SymbolicAI/Lean/knot_lean` | 8 | 16% | EN-majeure |
| `SymbolicAI/Lean/sensitivity_lean` | 6 | 8% | EN-majeure |
| `SymbolicAI/Lean/examples` | 5 | 77% | mixte-FR+ |

**Total :** 119 fichiers sur 207 (57 %) nécessitent une harmonisation.

### 1.3 Échantillons de docstrings EN-majeures (à traduire)

Ces exemples illustrent la convention actuelle — anglais mathématique académique,
parfaitement lisible mais hétérogène avec le reste du repo.

```lean
-- CooperativeGames/Shapley.lean
/--
A solution concept assigns to each game a payoff vector
-/
```

```lean
-- StableMarriage/Lattice.lean
/--
Man-preference ordering on matchings: μ ≤ ν iff every man prefers
his partner in μ at least as much as in ν (i.e., menPref m (μ m) ≤ menPref m (ν m)).
Lower rank = more preferred, so μ ≤ ν means μ is man-preferred over ν.
-/
```

```lean
-- StableMarriage/GaleShapley.lean
/--
The Gale-Shapley algorithm terminates.
At most n^2 proposals can occur (each man proposes to each woman at most once).

TODO: formalize the algorithm as a step relation and prove termination.
-/
```

```lean
-- SocialChoice/Arrow.lean
/--
b is strictly best in individual i's ordering over X
-/
```

```lean
-- SocialChoice/Voting.lean
/--
The margin of x over y in a profile:
    |{voters strictly preferring x to y}| - |{voters strictly preferring y to x}|
    Positive margin means x beats y in pairwise comparison.
-/
```

```lean
-- Bayesian/Reputation.lean
/--
Period-1 response encoded in an incumbent plan
    (0 = Accommodate, 1 = Fight).
-/
```

```lean
-- Conway/Life/MacroCell.lean
/--
A quadtree cell.
    - `leaf b` is a single cell that is alive (`b = true`) or dead (`b = false`).
    - `node nw ne sw se` is a 2x2 block of subtrees, all required (by convention,
      but not enforced by the type) to have the same level.
-/
```

---

## 2. Convention proposée

### 2.1 Principe directeur (HARD)

**Les docstrings et commentaires des `.lean` du repo CoursIA sont en français.**

Exception 1 : les noms de lemmes/théorèmes restent en anglais
(`theorem gale_shapley_terminates : ...`), comme dans toute littérature
mathématique formalisée (Mathlib convention).
Exception 2 : les `lakefile.lean` restent en anglais (infra, pas de prose).
Exception 3 : les citations textuelles de résultats publiés (e.g. Arrow's
impossibility theorem) peuvent conserver la formulation anglaise originale entre
guillemets.

### 2.2 Option A (recommandée) — Docstring bilingue dans le même bloc

**Format :**

```lean
/--
Résumé court en français (≤ 1 ligne).

Explication complémentaire en français. Détails techniques, références,
conditions d'application.

EN: Short English summary for international readers. (Optional, ≤ 2 lignes.
Encouragé pour les lakes partagés avec une audience anglophone : Search,
QuantConnect, ML, GameTheory/lean_game_defs.)
-/
theorem mon_theoreme : ... := by
  -- Commentaire de preuve en français (imperatif / indicatif présent)
  ...
```

**Avantages :**
- Une seule source de vérité (pas de risque de drift entre `.lean` et `.en.lean`).
- Pas d'outillage supplémentaire.
- Lecture native possible pour les deux audiences via le même fichier.
- Pattern déjà pratiqué dans `learning_theory_lean` (qui mixe FR + mots-clés EN
  pour les termes techniques).

**Inconvénients :**
- Docstrings plus longues (≈ +30 % de caractères).
- Traduction approximative possible (les agents IA ne sont pas des traducteurs
  professionnels ; rester humble sur la qualité littéraire).

### 2.3 Option B — Fichier compagnon `.en.lean`

**Format :**

```
CooperativeGames/Shapley.lean        ← FR uniquement
CooperativeGames/Shapley.en.lean     ← EN, build conditionnel
```

`lakefile.lean` ne compile que les fichiers primaires ; les `.en.lean` sont
chargés comme documentation externe (par exemple via un module `Shapleyl10n`
qui ré-exporte les signatures).

**Avantages :**
- Séparation propre des sources.
- Pas de pollution visuelle du `.lean` principal.

**Inconvénients :**
- Risque de **drift** : deux fichiers à maintenir en parallèle.
- Outillage requis (script de cohérence, hooks CI).
- Coût d'outillage disproportionné pour un repo éducatif.

### 2.4 Option C — Extraction en `.md` par module

Les docstrings restent FR uniquement dans `.lean`. Les traductions EN sont
stockées dans `<lake>/<module>.md` (par exemple `CooperativeGames/Shapley.md`).

**Avantages :**
- Aucune pollution du `.lean`.
- Markdown plus lisible que les blocs `/-- -/`.

**Inconvénients :**
- Outillage pour garder la cohérence (doc-gen maison ou extraction manuelle).
- Documentation déconnectée du code (un `.lean` modifié sans mise à jour du `.md`
  devient silencieusement obsolète).

### 2.5 Recommandation

**Option A** (docstring bilingue dans le même bloc) pour les raisons suivantes :

1. **Cohérence avec l'
