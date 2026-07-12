import Lake
open Lake DSL

/-! # Mini-projet Lean pédagogique : dérivées symboliques de Brzozowski

Projet **autonome, sans dépendance Mathlib**, illustrant le concept de dérivée
symbolique d'une expression régulière et le théorème de finitude de Brzozowski
(1964) — la base théorique de la terminaison des reconnaisseurs non-backtracking
(RE#, .NET `RegexOptions.NonBacktracking`).

La formalisation constructive *complète* en Lean 4 est due à Zhuchko, Maarand,
Veanes, Ebner (ITP 2025) — dépôt `ezhuchko/finiteness-derivatives`. Sa licence
amont n'étant pas confirmée, ce projet **ne vendore pas** leur code : il en
illustre l'intuition par des définitions et exemples originaux. Voir le notebook
[`Lean-14-Finiteness-Derivatives.ipynb`](../Lean-14-Finiteness-Derivatives.ipynb)
pour la présentation pédagogique complète, et l'issue #2978 (livrable C). -/

package «finiteness» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «Finiteness» where
  -- `Finiteness.Basic` : inductive Regex minimale + dérivée de Brzozowski +
  -- exemples illustrant la finitude de l'espace des dérivées.
  -- `globs` (not default roots) so `lake build` auto-discovers `*_en` siblings (#4980).
  globs := #[.submodules `Finiteness]
