# mimo_lean — Détection MIMO par descente à flips (Lean 4)

Port formel de l'algorithme de détection MIMO par flips de coordonnées
(Papailiopoulos, 2026 — issue #10984). Le lake naît directement sur
`v4.32.1` (Mathlib résolu à `520045ab14e26149ee970e2e617ca04b09bde5d6`,
fin de la migration #10986) et suit la convention i18n #4980
(docstrings FR par défaut, sibling `_en` avec namespace `Mimo_en`).

## Phases et libs compilées

Six `lean_lib` déclarées dans `lakefile.lean`, chacune avec son sibling EN
et associée à une phase du papier §11 :

| Phase | Lib              | Livrable                                                              | Statut |
|-------|------------------|-----------------------------------------------------------------------|--------|
| 1     | `Descent`        | Proposition 9.1 abstraite — descente à flips, sans dépendance         | livré  |
| 2     | `Objective`      | Lemme 11.1 — forme fermée du coût d'un flip + boucle `flip_accepted_iff` | livré  |
| 3a    | `Lmmse`          | Lemme 5.1 — erreur LMMSE `E‖b − x*‖² = tr B_ρ`                         | livré  |
| 3b    | `Converse`       | Converse §11 — Hanson–Wright + union bound + gaussian PDF            | livré  |
| 4     | `Bridge`         | Pont ML ↔ converse — identité de différence de coût (`cost_diff`)     | livré  |
| 5     | `NormTails`      | Queues de normes `‖w‖`, `‖hᵢ‖` — concentration 1-Lipschitz gaussienne | livré  |

Les Phases 4 et 5 sont les grains à grignoter de l'issue **#11148** (suite
de #10984) — modules portant une **substance propre** mais hors-périmètre
du premier découpage.

## Build

```bash
cd MyIA.AI.Notebooks/SymbolicAI/Lean/mimo_lean
lake build   # 6 libs × 2 namespaces (Mimo + Mimo_en) — Descent (cœur,
             # instantané) + Objective/Lmmse/Converse/Bridge/NormTails
             # (Mathlib + SLT requis)
```

CI : `lean-mimo.yml` (baseline sorry = 0, filtre standalone-tactic — cf les
autres lakes du dépôt).

## Dépendances externes

| Lake           | Source                                                                  | Pin                                       | Consommé par                       |
|----------------|-------------------------------------------------------------------------|-------------------------------------------|------------------------------------|
| **mathlib4**   | github.com/leanprover-community/mathlib4.git                            | `v4.32.1` (résolu `520045ab…`)            | Objective, Lmmse, Converse, Bridge, NormTails |
| **slt**        | github.com/YuanheZ/lean-stat-learning-theory.git (Apache 2.0)           | `d0f506f0a695018265dccb33bcb05e2f5ca1c876` | Converse (Hanson–Wright), NormTails (Lipschitz) |

Le pin SLT est **identique** à `lake-manifest.json` — la `require` ne dérive
pas. Aucune mise à jour de SLT n'est prévue sans revue dédiée (sécurité de
la frontière formelle).

## Inventaire détaillé des phases

### Phase 1 — `Descent.lean` (sans dépendance, instantané)

Le théorème phare `Mimo.descent_target_before_ceiling` est la forme abstraite
de la Proposition 9.1 : sous (i) stricte décroissance du coût à chaque flip
accepté, (ii) confinement du coût sous une barrière `B`, (iii) absence de
point bloquant hors cible, tout run **terminal** atteint la cible en
**strictement moins de `M_N` flips** (plafond).

Quatre lemmes intermédiaires :

1. `run_tail_cost_lt` — la décroissance stricte se propage à toute la queue ;
2. `run_nodup` — un run ne revisite jamais un état ;
3. `run_length_le_cost` — le nombre de flips est majoré par le coût initial
   (« budget de descente ») ;
4. `descent_flips_le_barrier` — sous la barrière `B`, flips ≤ `B < M_N`.

Pas de `require` : build en quelques secondes, pas de téléchargement Mathlib.
Les hypothèses `accept` / `cost` / `target` sont abstraites ; Phase 2 les
instancie sur la fonction objectif du papier.

### Phase 2 — `Objective.lean` (Mathlib)

Instancie la géométrie du détecteur :

1. `norm_add_sq_two` — Pythagore réel `‖x + y‖² = ‖x‖² + 2⟪x,y⟫ + ‖y‖²` ;
2. `flip_cost` — cœur géométrique **générique** (tout Hilbert réel) :
   `‖w + 2√s•h‖² − ‖w‖² = 4·(s·‖h‖² + √s·⟪h,w⟫)` ;
3. `mimoObj` / `flipAt` — l'objectif concret `‖w + √s•A u‖²` (canal :
   application linéaire `Fin N → ℝ → EuclideanSpace ℝ (Fin M)`) ;
4. `mimo_flip_cost` — **Lemme 11.1** : forme fermée exacte du coût d'un flip ;
5. `flip_accepted_iff` — la boucle de contrôle : un flip est accepté ssi le
   score `s·‖hᵢ‖² + √s·⟪hᵢ,w⟫` est strictement négatif — l'hypothèse
   `hstrict` que consomme la Proposition 9.1 (Phase 1).

### Phase 3a — `Lmmse.lean` (Mathlib)

Prouve le **Lemme 5.1** :

1. `integral_norm_sq_eq_trace` — **formule de la trace gaussienne** :
   `E‖x‖² = tr B` pour gaussienne centrée de covariance PSD `B` ;
2. `B_ρ` / `B_ρ_posSemidef` — la matrice d'erreur LMMSE
   `(I + s·HᴴH)⁻¹` est PSD dès `s ≥ 0` ;
3. `lmmse_error_eq_trace` — **Lemme 5.1** : `E‖b − x*‖² = tr(B_ρ)`.

### Phase 3b — `Converse.lean` (Mathlib + SLT)

Briques probabilistes du converse §11, sur le lake externe SLT pinned
`d0f506f0a695018265dccb33bcb05e2f5ca1c876` :

1. `gaussianPDFReal_lower_two` / `gaussian_interval_mass_lower` —
   **Brique 1** : densité `φ ≥ e⁻²/√(2π)` sur `[−2,2]`, donc tout
   intervalle inclus porte une masse `≥ largeur·φ(2)` ;
2. `one_sub_pow_le_exp_mul` — **Brique 2** : union bound complémentaire
   `(1−p)^n ≤ e^{−np}` ;
3. `hasSubgaussianMGF_eval_stdGaussianPi` / `hanson_wright_noise` —
   **Brique 3** : coordonnées de `stdGaussianPi n` sont sous-gaussiennes
   de paramètre `1`, puis **Hanson–Wright** cas `K = 1` : queue de la forme
   quadratique centrée `|XᵀAX − E XᵀAX|` (transport depuis le certificat SLT) ;
4. `gaussian_coordinate_escape_bound` — **assemblage** : par indépendance,
   `P(w échappe aux n intervalles) = ∏ᵢ(1−mᵢ) ≤ (1−p)^n ≤ e^{−np}` avec
   `p = ε·φ(2)` — le squelette complet du §11.

### Phase 4 — `Bridge.lean` (Mathlib + Phase 2 + Phase 3b)

Pont entre `mimoObj` (Phase 2) et converse (Phase 3b). Résultats phares :

1. `cost_diff` — forme **générique** : dans tout Hilbert réel,
   `‖w + √s•z + √s•v‖² − ‖w + √s•z‖² = s·‖v‖² + 2√s·⟪w,v⟫ + 2s·⟪z,v⟫` ;
2. (grain suivant, à livrer) : fragment de converse connecté au décodeur ML.

### Phase 5 — `NormTails.lean` (Mathlib + SLT)

Concentration de Lipschitz gaussienne (`gaussian_lipschitz_concentration`
du lake SLT, transporté en dépendance pinnée) — pour tout `t > 0` :

```
P(|‖X‖ − E‖X‖| ≥ t) ≤ 2·exp(−t²/2)
```

La norme euclidienne est 1-Lipschitz sur un vecteur gaussien standard.
C'est la **queue de norme** du §11 : elle borne `‖w‖` et `‖hᵢ‖` qui
apparaissent dans le score de flip de Phase 2 — les grains suivants
combinent ces queues par union bound sur les `N` colonnes du canal.

## Frontière formelle : prouvé localement vs emprunté

- **Prouvé localement** (CoursIA) : tout ce qui vit dans les six fichiers
  `.lean` — Descent, Objective, Lmmse, Converse, Bridge, NormTails —
  axiomes : `propext`, `Classical.choice`, `Quot.sound` (les trois
  standards de Mathlib) ;
- **Emprunté** (SLT) :
  - `gaussian_lipschitz_concentration` (lake SLT, NormTails) ;
  - `hanson_wright` (lake SLT, transporté dans `Converse.lean`).
- **Pas de claim axiomatique nouveau** — tout axiome hors ces deux
  emprunts doit faire l'objet d'une PR dédiée avec `#print axioms` et
  revue de la frontière.

## Companion canonique

Le compagnon natif est **[Lean-22b-MIMO-Converse-Native.ipynb](../../../../Lean-22b-MIMO-Converse-Native.ipynb)**
(kernel `lean4-wsl`) — il visite les 35 déclarations de `NormTails` /
`Converse` / `Bridge`, chacune interrogée par `#check` et sondée par
`#print axioms` sur les théorèmes clés. Trois axiomes standards, zéro
`sorry`, zéro axiome non standard.

Lean-22b **distingue** le prouvé localement (les énoncés de ce lake) de
l'emprunté (les deux théorèmes SLT rappelés explicitement) — la lecture
est self-contained, sans confusion de frontière.

## Voir aussi

- Issue #10984 — spécification initiale et découpage en phases 1–3
- Issue #11148 — grains à grignoter 4–5 (Bridge, NormTails)
- Issue #13121 — passe 1 d'audit CoursIA : `mimo_lean` est **PROPRE
  COURSIA** (preuve propre, différent d'un portage amont) ;
  Mathlib 4.32.1 résolu, SLT pinné, `distinct_code_sorry=0`.
- Lakes frères : `learning_theory_lean` (v4.32.1), `kelly_lean`
- Convention i18n #4980 — sibling `_en` par fichier,
  namespace `Mimo_en` côté anglais, byte-identity hors docstrings
