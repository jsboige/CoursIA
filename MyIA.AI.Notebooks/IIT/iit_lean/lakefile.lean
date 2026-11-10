import Lake
open Lake DSL

/-! # Premier lake Lean de la série IIT — intégration par coupes (proxy relationnel, Phase 1)

Formalisation Lean 4 **sans dépendance Mathlib** du proxy relationnel de
décomposition par coupe figé dans l'issue #18599 (Epic Aaronson #16781,
veine 5) : systèmes déterministes sur `n` bits, coupes non triviales,
indépendance d'une coupe, et le couple de théorèmes qui fait de la critique
d'Aaronson un objet formel — les systèmes à dynamiques latérales
indépendantes sont décomposables (`cutIndep_of_sides_independent`), le
broadcast-parité est intégré pour toute coupe (`broadcast_integrated`) avec
dynamique triviale (`broadcast_two_cycle`).

**Pas de dépendance Mathlib** : `Fin`, `Bool`, `xor` et des témoins
constructifs suffisent — le lake se construit en secondes, sans `lake exe
cache get`. `globs` (not default roots) pour que `lake build` découvre les
jumeaux `*_en` (#4980). -/

package «iit» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «IIT» where
  -- `IIT.Integration` : defs coupe/indépendance/décomposabilité + les trois
  -- théorèmes figés de la Phase 1 ; `IIT.Integration_en` : jumeau EN
  -- (docstrings seules diffèrent, namespace `IIT_en`, #4980 pattern A).
  globs := #[.submodules `IIT]
