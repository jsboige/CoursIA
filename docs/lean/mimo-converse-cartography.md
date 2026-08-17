# Cartographie converse MIMO (#11152) — brique → source

**Mesuré le 2026-08-16** sur le Mathlib et le SLT du manifest `mimo_lean` courant :
Mathlib `v4.32.0` (rev résolue par `lake-manifest.json`) et `YuanheZ/lean-stat-learning-theory` @ `d0f506f0a695018265dccb33bcb05e2f5ca1c876` (pin #11099).

Cette cartographie remplace la liste du 2026-08-14 portée par le body de #11152 : **deux briques jugées manquantes sont désormais sourcées dans Mathlib**, et une seule reste à formaliser.

## Tableau brique → source

| # | Brique | Verdict | Source (mesurée, `file:line`) |
|---|--------|---------|-------------------------------|
| 0 | Hanson-Wright | **SOURCÉ (SLT)** | `slt/SLT/HansonWright.lean:4356` `hanson_wright_inequality` — P(\|`centeredQuadraticForm μ A X`\| ≥ t) ≤ 2·exp(−(1/(4C))·min(t²/(K⁴·‖A‖²_F), t/(K²·‖A‖_op))) pour coordonnées indépendantes sous-gaussiennes. Variantes : `:4448` `hanson_wright_inequality_hdp_explicit`, `:4482` `hanson_wright_inequality_hdp`, MGF `:3996` `hasHansonWrightMGF_of_subgaussian`, `:4164` `hasHansonWrightMGF_of_bounded`, `:4300` `two_sided_tail_of_cgf_bound` |
| 1 | Queues chi-squared sur `‖w‖²` / `‖h‖²` | **À FORMALISER** | χ² **absent de Mathlib v4.32.0** : 0 hit pour `ChiSquared` / `chiSquared` / `chiSquare` / `ChiSq` / `chi2` sur les 8795 fichiers `Mathlib/**/*.lean`. Chemins possibles : (a) forme quadratique `A = I` via Hanson-Wright (Frobenius = op = √n, K = 1 pour gaussien standard) — borne en min(t²/n, t/√n) ; (b) loi χ² dédiée (somme de carrés) comme définition propre |
| 2 | Bornes de queue gaussiennes explicites | **SOURCÉ (assemblage de 2 lemmes Mathlib)** | `Mathlib/Probability/Moments/SubGaussian.lean:334` `measure_ge_le` : pour `HasSubgaussianMGF X c`, P(X ≥ ε) ≤ exp(−ε²/(2c)). Pont gaussien → sous-gaussien dérivable de `Mathlib/Probability/Distributions/Gaussian/Real.lean:494` `mgf_gaussianReal` (mgf = exp(μt + vt²/2), donc `HasSubgaussianMGF` avec c = v pour la loi centrée). Pont court à écrire une fois dans mimo_lean (2 lignes depuis `mgf_gaussianReal`) |
| 3 | Concentration de norme | **SOURCÉ (SLT)** | `slt/SLT/GaussianLipConcen.lean:493` `cgf_bound` — borne de CGF pour fonction Lipschitz d'un vecteur gaussien (via LSI). `x ↦ ‖x‖` est 1-Lipschitz : la concentration de la norme s'obtient par application directe. Auxiliaires dans le même fichier (`lipschitz_gradNormSq_bound:30`, `entropy_bound_exp_scaled:330`) |
| 4 | Woodbury / Sherman-Morrison | **SOURCÉ (Mathlib)** — la liste du 08-14 était périmée | `Mathlib/LinearAlgebra/Matrix/Invertible.lean:199` `Matrix.invOf_add_mul_mul` (identité de Woodbury, version `⅟`) ; `Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:604` `Matrix.add_mul_mul_inv_eq_sub` (version `⁻¹` avec hypothèses `IsUnit`), `:621` `add_mul_mul_inv_eq_sub'` (théorème inverse binomial, variante de Woodbury) |

## Deltas vs la liste du 2026-08-14

- **Woodbury** : réputé manquant → **présent** dans Mathlib v4.32.0 (les deux formes `⅟` et `⁻¹`).
- **Bornes de queue gaussiennes** : réputées manquantes → **couvertes par assemblage** (`measure_ge_le` + `mgf_gaussianReal`), le pont à écrire est de l'ordre de 2 lignes.
- **Chi-squared** : confirmé **toujours absent** (toutes orthographes testées). C'est la seule brique réellement à formaliser — le grain 2 de #11152 reste valide.
- **Hanson-Wright** : confirmé complet dans le SLT (3 formes de borne + 2 certificats MGF).

## Conséquences pour les grains 2-4 de #11152

- **Grain 2 (queues chi-squared)** : seule brique à formaliser. Voie recommandée : HW avec `A = I` donne directement la borne quadratique/linéaire sur `‖w‖²` (avec K = 1 par `mgf_gaussianReal`), sans avoir à définir la loi χ² au complet.
- **Grain 3 (coordonnée → union)** : s'appuiera sur `measure_ge_le` (Mathlib) — sourcé.
- **Grain 4 (assemblage)** : l'inversion de `(I + γ·h·h᙮)` nécessaire au LMMSE passe par Woodbury (`Matrix.add_mul_mul_inv_eq_sub`) — sourcé.

## Méthode

Greps sur les sources vendored du donateur local (`CoursIA-10984-mimo/.../mimo_lean/.lake/packages/`), revs vérifiées dans `lake-manifest.json` (mathlib `v4.32.0`, slt `d0f506f`). Lecture des énoncés (`sed`) pour chaque hit retenu — aucune ligne de ce tableau n'est estimée.
