# mimo_lean — Détection MIMO par descente à flips (Lean 4)

Port formel de l'algorithme de détection MIMO par flips de coordonnées
(Papailiopoulos, 2026 — issue #10984). Le lake naît directement sur
`v4.32.0` (migration #10986 terminée) et suit la convention i18n #4980
(docstrings FR par défaut, sibling `_en` avec namespace `Mimo_en`).

## Phases

| Phase | Livrable | Statut |
|-------|----------|--------|
| 1 | `Descent.lean` — squelette abstrait de la Proposition 9.1, **sans dépendance** (cœur Lean) | livré |
| 2 | `Objective.lean` — fonction objectif avec Mathlib : Lemme 11.1 (coût d'un flip `4·(ρ/N·‖hᵢ‖² + √(ρ/N)·hᵢᵀw)`), Lemme 5.1 (erreur LMMSE `E‖b − x*‖² = E tr(B_ρ)`) | à venir |
| 3 | Converse §11 via le lake externe [YuanheZ/lean-stat-learning-theory](https://github.com/YuanheZ/lean-stat-learning-theory) (v4.32.0, Apache 2.0, 0 sorry) : Hanson-Wright, concentration LSI, RMT | à venir |

## Phase 1 — ce qui est prouvé

Le théorème phare `Mimo.descent_target_before_ceiling` est la forme abstraite
de la Proposition 9.1 : sous (i) stricte décroissance du coût à chaque flip
accepté, (ii) confinement du coût sous une barrière `B`, (iii) absence de
point bloquant hors cible, tout run **terminal** atteint la cible en
**strictement moins de `M_N` flips** (plafond).

Quatre lemmes intermédiaires, chacun autonome :

1. `run_tail_cost_lt` — la décroissance stricte se propage à toute la queue ;
2. `run_nodup` — un run ne revisite jamais un état ;
3. `run_length_le_cost` — le nombre de flips est majoré par le coût initial
   (le « budget de descente ») ;
4. `descent_flips_le_barrier` — sous la barrière `B`, flips ≤ `B < M_N`.

Le fichier est volontairement **sans `require`** : build en quelques secondes,
sans téléchargement de Mathlib. Les hypothèses `accept` / `cost` / `target`
sont abstraites ; la Phase 2 instancie `cost` par la fonction objectif du
papier (où seuls les flips diminuant l'objectif sont acceptés, ce qui donne
`hstrict`).

## Build

```bash
cd MyIA.AI.Notebooks/SymbolicAI/Lean/mimo_lean
lake build   # cœur seul : quelques secondes, zéro dépendance
```

CI : `lean-mimo.yml` (baseline sorry = 0, filtre standalone-tactic — cf les
autres lakes du dépôt).

## Voir aussi

- Issue #10984 — spécification et découpage en phases
- Lakes frères : `learning_theory_lean` (v4.32.0), `kelly_lean`
- Convention i18n #4980 — `Descent.lean` (FR) / `Descent_en.lean` (EN)
