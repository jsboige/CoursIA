# mimo_lean — Détection MIMO par descente à flips (Lean 4)

Port formel de l'algorithme de détection MIMO par flips de coordonnées
(Papailiopoulos, 2026 — issue #10984). Le lake naît directement sur
`v4.32.0` (migration #10986 terminée) et suit la convention i18n #4980
(docstrings FR par défaut, sibling `_en` avec namespace `Mimo_en`).

## Phases

| Phase | Livrable | Statut |
|-------|----------|--------|
| 1 | `Descent.lean` — squelette abstrait de la Proposition 9.1, **sans dépendance** (cœur Lean) | livré |
| 2 | `Objective.lean` — fonction objectif au carré avec Mathlib : Lemme 11.1 (coût d'un flip `4·(s·‖hᵢ‖² + √s·⟪hᵢ,w⟫)`) + boucle de contrôle `flip_accepted_iff` | livré |
| 3a | `Lmmse.lean` — **Lemme 5.1** (erreur LMMSE) : `E‖b − x*‖² = tr(B_ρ)`, `B_ρ = (I + s·HᵀH)⁻¹` — formule de la trace gaussienne + transport de loi | livré |
| 3b | `Converse.lean` — converse §11 : briques probabilistes via le lake externe [YuanheZ/lean-stat-learning-theory](https://github.com/YuanheZ/lean-stat-learning-theory) (v4.32.0, Apache 2.0) : intervalles gaussiens + union bound + Hanson–Wright + assemblage | livré |

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

## Phase 2 — ce qui est prouvé

`Objective.lean` (twin `Objective_en.lean`, code byte-identique hors
docstrings) instancie la géométrie du détecteur sur Mathlib :

1. `norm_add_sq_two` — Pythagore réel `‖x + y‖² = ‖x‖² + 2⟪x,y⟫ + ‖y‖²`,
   redérivé des lemmes fondamentaux ;
2. `flip_cost` — cœur géométrique **générique** (tout Hilbert réel) :
   `‖w + 2√s•h‖² − ‖w‖² = 4·(s·‖h‖² + √s·⟪h,w⟫)` ;
3. `mimoObj` / `flipAt` — l'objectif concret `‖w + √s•A u‖²` (canal :
   application linéaire de l'espace signal `(Fin N → ℝ)` vers l'espace de
   mesure `EuclideanSpace ℝ (Fin M)`) et le vecteur de déviation `2·eᵢ` ;
4. `mimo_flip_cost` — **Lemme 11.1** (Papailiopoulos 2026) : forme fermée
   exacte du coût d'un flip ;
5. `flip_accepted_iff` — la boucle de contrôle : un flip est accepté ssi le
   score `s·‖hᵢ‖² + √s·⟪hᵢ,w⟫` est strictement négatif — exactement
   l'hypothèse `hstrict` que consomme la Proposition 9.1 (Phase 1).

Axiomes : `propext`, `Classical.choice`, `Quot.sound` (les trois standards
de Mathlib) — zéro sorry.

## Phase 3a — ce qui est prouvé

`Lmmse.lean` (twin `Lmmse_en.lean`) prouve le **Lemme 5.1** sur Mathlib :

1. `integral_norm_sq_eq_trace` — **formule de la trace gaussienne** : pour
   une gaussienne centrée de covariance PSD `B`, `E‖x‖² = tr B` (chaque
   coordonnée contribue sa variance `B i i`, via les marginales
   `gaussianReal` et `variance_eq_integral`) ;
2. `B_ρ` / `B_ρ_posSemidef` — la matrice d'erreur LMMSE `(I + s·HᴴH)⁻¹`
   est PSD dès `s ≥ 0` (`posSemidef_conjTranspose_mul_self` + inverse) ;
3. `lmmse_error_eq_trace` — **Lemme 5.1** : `E‖b − x*‖² = tr(B_ρ)` par
   transport de la loi de l'erreur.

Axiomes : les trois standards de Mathlib — zéro sorry.

## Phase 3b — ce qui est prouvé

`Converse.lean` (twin `Converse_en.lean`) pose les briques probabilistes du
converse §11 (impossibilité sous `2 log N − log log N − s_N`), en s'appuyant
sur le lake externe SLT (pinned `d0f506f0` — mêmes toolchain et Mathlib que
mimo, zéro re-téléchargement) :

1. `gaussianPDFReal_lower_two` / `gaussian_interval_mass_lower` — **Brique 1** :
   la densité `φ ≥ e⁻²/√(2π)` sur `[−2,2]`, donc tout intervalle inclus dans
   `[−2,2]` porte une masse `≥ largeur·φ(2)` (mécanisme des « intervalles de
   largeur `1/√ρ₀` » du §11) — domination d'indicateurs + `lintegral_mono` ;
2. `one_sub_pow_le_exp_mul` — **Brique 2** : union bound complémentaire
   `(1−p)^n ≤ e^{−np}` (instance de `one_sub_div_pow_le_exp_neg`) ;
3. `hasSubgaussianMGF_eval_stdGaussianPi` / `hanson_wright_noise` — **Brique 3** :
   les coordonnées de `stdGaussianPi n` sont sous-gaussiennes de paramètre `1`
   (transport du certificat `N(0,1)` via `map_eval_stdGaussianPi`), puis
   **Hanson–Wright** cas `K = 1` : queue de la forme quadratique centrée
   `|XᵀAX − E XᵀAX|` (théorème du lake SLT) — la queue chi-square de `‖w‖²`
   et des formes `hᵢᵀ w` du §11 ;
4. `gaussian_coordinate_escape_bound` — **assemblage** : par indépendance des
   coordonnées (`Measure.pi_pi`), `P(w échappe aux n intervalles) = ∏ᵢ(1−mᵢ)
   ≤ (1−p)^n ≤ e^{−np}` avec `p = ε·φ(2)` — le squelette complet de l'argument
   d'impossibilité du §11.

Axiomes : les trois standards de Mathlib — zéro sorry.

## Build

```bash
cd MyIA.AI.Notebooks/SymbolicAI/Lean/mimo_lean
lake build   # Descent (cœur, instantané) + Objective/Lmmse/Converse (Mathlib requis)
```

CI : `lean-mimo.yml` (baseline sorry = 0, filtre standalone-tactic — cf les
autres lakes du dépôt).

## Voir aussi

- Issue #10984 — spécification et découpage en phases
- Lakes frères : `learning_theory_lean` (v4.32.0), `kelly_lean`
- Convention i18n #4980 — `Descent.lean`/`Descent_en.lean`, `Objective.lean`/`Objective_en.lean`, `Lmmse.lean`/`Lmmse_en.lean`, `Converse.lean`/`Converse_en.lean`
