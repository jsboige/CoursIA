import Mathlib
import GradientFlow.Plain_en
import GradientFlow.Residual_en

/-!
# GradientFlow — formal digestion: why the gradient survives residual blocks

English mirror of `GradientFlow.lean` (FR-first canonical), EPIC #4980 (i18n
Lean). Convention ratified 2026-07-04 (issue #4980): namespace
`GradientFlow_en`; cross-module `_en` imports `_en`.

A tranche of the digestion EPIC **#13106** (formalization form, like the CHSH
pilot #14858 by po-2025 and the PFR grid #14566 by ai-01). The digestion
protocol (Tao, ICM 2026 — the *digest* operation) requires a 10-point grid per
child grain; it is rolled out in the FR canonical header. Summary:

1. **Exact statement.** Plain stack of `n` blocks each contracting the
   derivative (`|f'_k| ≤ c`): `|(f_{n-1} ∘ … ∘ f_0)'| ≤ c ^ n`
   (`abs_deriv_plainStack_le`), and for `c < 1` the bound tends to `0`
   (`plainStack_gradient_vanishes`). Stack of residual blocks `h ↦ h + f h`
   with `c ≤ 1`: `(1 - c) ^ n ≤ |(g_{n-1} ∘ … ∘ g_0)'|`
   (`abs_deriv_residualStack_ge`) — the gradient survives geometrically.
2. **Provenance.** The identity shortcut: He, Zhang, Ren & Sun, *Deep
   Residual Learning for Image Recognition*, arXiv:1512.03385 (2015); the
   ensemble view: Veit, Wilber & Belongie, arXiv:1605.06431 (2016). The
   digested content is **our own notebook**
   `DataScienceWithAgents/04-Vision/4.2-ConvNet-Profonde-Residuelles.ipynb`
   (§3: measured factor ≈ 0.4/block; §6: plain 43.1% vs prenorm 58.4%
   pairwise accuracy over 3 seeds).
3. **Real novelty.** First module of the lake (and of the repo, empty grep)
   formalizing deep-gradient mechanics: the upper/lower bound pair above
   existed in no form; the siblings `Perceptron` (Novikoff) and `PacLearning`
   (Valiant) cover algorithmic convergence and generalization, not
   optimization.
4. **Dependency map.** Mathlib only (`HasDerivAt.comp`, `HasDerivAt.add`,
   `abs_mul`, `abs_sub_abs_le_abs_add`,
   `Real.tendsto_pow_atTop_nhds_0_nat`, `norm_num`); no dependency on the
   lake's sibling modules.
5. **Condensed trivial vs newly developed.** The bricks are honest
   condensates (chain rule + induction + product monotonicity); what is
   **new** is the pair of statements and the coupling to the course's
   numeric anchors (`0.4 ^ 20 < 1e-7` plain-side, `3e-5 < 0.6 ^ 20`
   residual-side).
6. **Natural friction.** Navigating the `Deriv`/`HasDerivAt` API (argument
   order of `.comp`, exact shape of the abs lemmas); keeping 0-sorry on
   syntactic recursions (the derivative value carried by `HasDerivAt`).
7. **Discovery path.** The 4.2-ConvNet notebook measures first (straight
   line on a semilog scale: factor ~0.4/block, `0.4 ^ 20 ≈ 1e-8`), the lake
   proves second: measurement precedes proof — exactly the order the
   digestion protocol wants to institutionalize.
8. **Limits.** 1-D toy model over `ℝ`: no Jacobians, no eigenvalues, no
   pre-norm/LayerNorm. The formalization captures survival by identity
   shortcut, **not** repair by normalization (the notebook distinguishes
   both; the lake covers only the first).
9. **Corpus connection.** Notebook `4.2-ConvNet-Profonde-Residuelles`
   (§3, §6); lake `learning_theory_lean` (siblings `Perceptron`,
   `PacLearning`); lake README updated.
10. **Transmission.** FR docstrings (canonical) + EN siblings
    (`GradientFlow_en`, convention #4980); grid summarized in the README;
    numeric anchors checked by `norm_num`.

## Status

Tranche 1 **delivered**: `Plain.lean` (upper bound `c ^ n` + vanishing +
anchor `0.4 ^ 20`), `Residual.lean` (lower bound `(1-c) ^ n` + anchor
`0.6 ^ 20`), both 0-sorry. Natural extensions (out of scope for this
tranche): the matrix model (Jacobians, spectral radius) and the pre-norm.
-/

namespace GradientFlow_en

/-- Status: tranche 1 delivered (digestion #13106) — plain stack bounded above
by `c ^ n` (`abs_deriv_plainStack_le`, vanishing
`plainStack_gradient_vanishes`), residual stack bounded below by `(1-c) ^ n`
(`abs_deriv_residualStack_ge`), numeric anchors of the 4.2-ConvNet notebook
(`two_fifths_pow_twenty_lt`, `three_fifths_pow_twenty_gt`). Open extensions
out of scope: matrix model (Jacobians/spectral), pre-norm. -/
abbrev Status : Prop := True

end GradientFlow_en
