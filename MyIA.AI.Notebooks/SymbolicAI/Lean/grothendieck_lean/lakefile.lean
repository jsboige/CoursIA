import Lake
open Lake DSL

package «grothendieck» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

-- Convention i18n EPIC #4980 (ratifiée user 04/07, finding 2 ai-01) :
-- `globs` (et non `roots`) pour que `lake build` auto-découvre les siblings
-- `_en` (miroir EN, namespace `<Lib>_en`). Avec `roots := #\[`<Lib>\]`, le root
-- n'importe que ses deps transitives — le sibling `_en` (namespace distinct)
-- n'est PAS built par défaut, seulement via `lake build <Lib>.*_en` explicite.
-- `globs := #\[`<Lib>.*\]` couvre TOUS les modules sous `<Lib>/`, `_en` inclus →
-- la CI drift-detection voit les deux langues. Zéro toucher aux fichiers .lean.
--
-- NOTE technique (validated firsthand po-2026 sur decision_theory_lean, à propager) :
-- la forme bare `globs := #\[`<Lib>\]` NE fonctionne PAS — elle ne matche que le
-- module root, pas les enfants. Il FAUT le suffixe `.*` : `globs := #\[`<Lib>.*\]`.
-- Migration c.398 : grothendieck_lean rejoint le pattern sibling pair ratifié (#6154).

@[default_target]
lean_lib «Grothendieck» where
  globs := #[`Grothendieck.*]
