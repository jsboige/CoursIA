# Inventaire des projets Lean 4 — `ML`

Inventaire transverse des projets de formalisation Lean 4 sous `ML/`, sur le modèle de
[`GameTheory/LEAN_INVENTORY.md`](../GameTheory/LEAN_INVENTORY.md) et
[`SymbolicAI/Lean/LEAN_INVENTORY.md`](../SymbolicAI/Lean/LEAN_INVENTORY.md). Source de
vérité : corps de l'Epic
[#4038](https://github.com/jsboige/CoursIA/issues/4038) + vérification `firsthand`. Colonne
*Sorry (production)* = métrique CI `standalone-tactic` (les mentions prose « 0 sorry »
n'entrent pas dans ce compte ; cf.
`lean-ci-sorry-filter`).

## Résumé

| Lake | Toolchain | sorry (production) | Modules | Notebook câblé | Classe | Suivi |
|------|-----------|--------------------:|--------:|---------------:|--------|-------|
| `learning_theory_lean` | v4.31.0-rc1 | 0 | 5 | 0¹ | PEDA/REF | #4051, #4301, #4038 |
| **Total** | — | **0** | **5** | — | — | — |

¹ Aucun notebook Lean dédié. Companion conceptuel = la série **ML.NET** (classification
linéaire, le perceptron comme ancêtre) — convention sibling-lake (le lake est le livrable
formel, le notebook compagnon revient au propriétaire de la série ML).

---

## Par lake

### learning_theory_lean — PEDAGOGIQUE / REFERENCE

**Objectif** : théorème de convergence du Perceptron (Novikoff, 1962) — données
linéairement séparables de marge γ et rayon R ⟹ au plus `(R/γ)²` mises à jour. Premier lake
Lean de la série ML (roadmap #4038 Tier 2).

- **Toolchain** : v4.31.0-rc1 · **Dépendance** : Mathlib4
- **lib** : `Perceptron` (`globs := #[.submodules \`Perceptron]`)
- **Modules** : `Perceptron/Data.lean`, `Perceptron/Perceptron.lean`,
  `Perceptron/Convergence.lean`, `Perceptron/Tightness.lean` + umbrella `Perceptron.lean`
- **sorry (production)** : **0**. `lake build Perceptron` SUCCESS (8497 jobs, 0 warning).

#### Théorèmes prouvés (0 sorry)

- **`PerceptronRun.novikoff_mistake_bound`** (flagship Convergence, #4140) : `n·γ² ≤ R²` —
  la borne de Novikoff sur le nombre de mises à jour.
- **`novikoff_bound_is_sharp`** (flagship Tightness, #4301) :
  `∃ run : PerceptronRun ℂ, (run.n : ℝ) * run.γ^2 = run.R^2` — un témoin concret sur `ℂ`
  (deux points `1±I`, séparateur `u=1`, marge `γ=1`, rayon `R=√2`, `n=2`) sature la borne
  avec **égalité** `n·γ² = R²`. L'inégalité universelle `≤ R²` (`novikoff_mistake_bound`) et
  l'égalité du témoin coexistent ⟹ aucune borne `n·γ² ≤ c·R²` avec `c < 1` n'est universelle :
  la constante `1` (devant `(R/γ)²`) est **optimale**.
- `PerceptronRun.align_growth` (Lemme A) : `⟪wₖ, u⟫ ≥ k·γ` — croissance de l'alignement
  avec le vecteur séparateur `u`.
- `PerceptronRun.norm_bound` (Lemme B) : `‖wₖ‖² ≤ k·R²` — borne quadratique sur la norme
  des poids.
- Support IPS (espace préhilbertien réel) : `norm_sq_eq_inner_self`, `norm_add_sq_eq`,
  `perceptronWeights_zero`/`_succ` (suite de récurrence `w₀=0`, `w_{k+1}=wₖ+yₖ•xₖ`).
- Support Tightness (witness `ℂ`) : `complex_inner_re` (produit scalaire réel sur `ℂ` en
  coordonnées `w.re·z.re + w.im·z.im`), `witnessPts_norm_sq` (`‖xₖ‖² = 2`),
  `witness_margin_inner`, `witness_cross_inner` (orthogonalité `⟨1+I, 1−I⟩ = 0`),
  `witness_w1`, `witness_lbl`, `witness_rad`, `witness_margin`, `witness_mistake`,
  `tightnessRun_saturates` (égalité `2·1² = (√2)²`).

#### Honnêteté du périmètre (G.3/G.9)

La borne de Novikoff **complète** (alignement + norme + Cauchy–Schwarz `real_inner_le_norm`)
est prouvée 0 sorry, **et sa sharpness est établie** (`novikoff_bound_is_sharp`, #4301) —
le lac ne se contente pas de la borne universelle, il prouve son optimalité. Aucun jalon
laissé en `sorry`. Axiomes `[propext, Classical.choice, Quot.sound]` (Mathlib standard,
**pas de `sorryAx`**).

## Notes transverses

- **WDAC workaround** (RECOVERABLE-LOCAL) : `lake exe cache get` bloqué (err 4551) → réutilise
  les oleans `.lake/packages/` d'un lake frère binairement compatible (`astar_lean`, même
  toolchain `v4.31.0-rc1` + même révision Mathlib). Cf.
  `lean-wdac-olean-wholesale-copy`.
- **Mathlib v4.31.0-rc1 IPS-API renames** (documentés durably) : `InnerProductSpace ℝ V`
  exige `[SeminormedAddCommGroup V]` param-class ; `norm_sq_eq_inner`→`real_inner_self_eq_norm_sq` ;
  `abs_inner_le_norm`→`real_inner_le_norm` ; `inner_comm`→`real_inner_comm` ;
  `inner_add_add`→`real_inner_add_add_self` ; `inner_smul_*`→`real_inner_smul_*` ;
  `sq_le_sq` (devenu iff)→`sq_le_sq₀` ; `linarith` aveugle aux produits Nat-cast→`nlinarith [sq_nonneg R]`.
- CI : `.github/workflows/lean-perceptron.yml` (`sorry-filter-mode: standalone-tactic`,
  baseline `"0"`).
