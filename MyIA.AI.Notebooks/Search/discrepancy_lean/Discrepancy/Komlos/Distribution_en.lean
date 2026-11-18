/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapted for `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979): toolchain v4.33.0, Mathlib `db584cd6`, i18n convention #4980.

The original Dahia source lives in the `gdahia/Komlos` repository (module
`Komlos/Distribution.lean`, toolchain v4.34.0, `Finsupp` framework over
`E →₀ ℝ`). The adaptation carries the module over **name for name**.

**Scope of this commit** (brick k2.5, `lake build SUCCESS` required, 0 `sorry`):

The oracle module carries a whole `Finsupp` infrastructure — `mass`, `mean`,
`IsDist`, additivity lemmas (`mass_add`, `mass_smul`, `mean_smul`),
monotonicity (`mass_nonneg`, `mass_mono`), sup/inf support accounts and the
identities `mass_sup_add_mass_inf` / `mean_sup_add_mean_inf` — of which
**only the conclusion** has a measured consumer in our chain:

`mean_mem_convexHull` (l.105) is the **base case `n = 0`** of the k1.7
assembly (`SignedSums.lean` l.42: `simpa using mean_mem_convexHull hP le_rfl`).
This brick delivers this pendant alone: the barycenter of a positive
distribution of mass 1 over its support `S` belongs to the convex hull of
the **transported** support (k2.3: `S.map ⟨toReal, toReal_injective⟩`).

**In the oracle the proof is a one-liner**: the weights that
`Finset.mem_convexHull'` asks for are the `Finsupp` itself, zero outside the
support **by construction** (`Finsupp` = function zero outside a finite
support). This is exactly the work that the lake's explicit `Finset` framing
asks for again — and the k2.3 organ `push` provides it: `push toReal P` is
the pushed distribution on the real grid, reading `P` on the image
(`push_apply`) and zero off the image (`push_eq_zero`). The proof becomes
the oracle one-liner again, its three components reading off the k2.3
organs: `push_apply` (positivity of the transported weights), `push_mass`
(mass, the oracle's `mass_push`), `coordMoment_toReal` (the product point,
the oracle's `mean_push` — the barycenter asserted into the hull is exactly
the one the k2.0 coordinate moments compute).

**Arbitrated framing gaps** (same family as k2.4):

1. **the `mean` is read coordinate-wise** — the base `Fin d → ℤ` is not an
   `ℝ`-module (blocker measured in k2.2); the point is
   `fun i => coordMoment P S i` (k2.0), living in `Fin d → ℝ` where
   `convexHull ℝ` is expressible (k2.2/k2.3);
2. **`IsDist` becomes two hypotheses** (`hP`: pointwise positivity, `hmass`:
   mass 1 over `S`) — the `Finsupp` structure carried these facts by
   construction; the lake takes them as hypotheses, like `hSQ`/`hPsupp` in
   k2.4;
3. **the support of the statement is `S` itself** — the oracle concludes on
   an arbitrary `s ⊇ support`; here the lake concludes on the exact
   transported support `S.map ⟨toReal, _⟩`, the same shape as the `pullback`
   conclusion (k2.4).

**Deferred with a measured consumer**:

- the sup/inf infrastructure of the oracle module (`mass_sup_add_mass_inf`,
  `mean_sup_add_mean_inf`, `support_inf_subset`, `support_sup_subset`) has no
  consumer in our framing — mass preservation under splitting is already
  `split_mass` (k1.2), which the assembly will consume as a chained
  hypothesis;
- `sum_smul_inl` (deferred in k2.4 as "no measured consumer") **gains a
  measured consumer** through the k1.7 reading of the step
  (`SignedSums.lean` l.53: `rw [mean_split, sum_smul_inl, Prod.mk_add_mk,
  add_zero] at hmem`) — it will be delivered with the k2.6 assembly, where
  its exact shape gets fixed.
-/

import Discrepancy.Basic_en
import Discrepancy.Komlos.MeanSplit_en
import Discrepancy.Komlos.Transport_en

namespace Discrepancy.Komlos_en

/-- **`mean_mem_convexHull`** (lake form of the oracle's l.105): the
barycenter — read coordinate-wise, `fun i => coordMoment P S i` (k2.0) — of
a positive distribution of mass 1 over its support `S` belongs to the convex
hull of the **transported** support on the real grid. This is the base case
`n = 0` of the Lemma 1.4 assembly (k1.7, `SignedSums.lean` l.42).

The proof is the oracle's — `Finset.mem_convexHull'` with the distribution
itself as weights — **provided** the required weight function on the real
grid exists: this is `push toReal P` (k2.3, the lake's `Finsupp.embDomain`
organ), zero off the image by construction. The three components read off
the k2.3 organs: `push_apply` (positivity), `push_mass` (mass),
`coordMoment_toReal` (the point). -/
theorem mean_mem_convexHull {d : ℕ} {P : (Fin d → ℤ) → ℝ}
    {S : Finset (Fin d → ℤ)}
    (hP : ∀ x, 0 ≤ P x) (hmass : ∑ x ∈ S, P x = 1) :
    (fun i => coordMoment P S i) ∈ convexHull ℝ
      ↑(S.map (⟨⇑toReal, toReal_injective⟩ : (Fin d → ℤ) ↪ (Fin d → ℝ))) := by
  refine Finset.mem_convexHull'.2 ⟨push toReal P, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, -, hxy⟩ := Finset.mem_map.1 hy
    have hval : push toReal P y = P x := by
      rw [← hxy]
      exact push_apply toReal toReal_injective P x
    rw [hval]
    exact hP x
  · rw [push_mass toReal toReal_injective P S]
    exact hmass
  · funext i
    rw [← coordMoment_toReal P S i]
    simp only [Finset.sum_apply, coordMomentReal, Pi.smul_apply, smul_eq_mul]

end Discrepancy.Komlos_en
