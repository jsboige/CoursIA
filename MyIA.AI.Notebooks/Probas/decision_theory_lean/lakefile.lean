import Lake
open Lake DSL

package decision_theory_lean where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`pp.unicode.fun, true⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0-rc2"

-- Convention i18n EPIC #4980 (ratifiée user 04/07, finding 2 ai-01) :
-- `globs` (et non `roots`) pour que `lake build` auto-découvre les siblings
-- `_en` (miroir EN, namespace `<Lib>_en`). Avec `roots := #[`<Lib>]`, le root
-- n'importe que ses deps transitives — le sibling `_en` (namespace distinct)
-- n'est PAS built par défaut, seulement via `lake build <Lib>.*_en` explicite.
-- `globs := #[`<Lib>.*]` couvre TOUS les modules sous `<Lib>/`, `_en` inclus →
-- la CI drift-detection voit les deux langues. Zéro toucher aux fichiers .lean.
--
-- NOTE technique (validated firsthand po-2026, à propager à la fleet) :
-- la forme bare `globs := #[`<Lib>]` NE fonctionne PAS — elle ne matche que le
-- module root, pas les enfants. Il FAUT le suffixe `.*` : `globs := #[`<Lib>.*]`.
-- Test firsthand sur decision_theory_lean (Utility.Basic_en/Axioms_en) :
--   bare `Utility`  → 8497 jobs, _en NON built
--   `Utility.*`     → 8499 jobs, _en built (Basic_en 16s + Axioms_en 15s)
@[default_target]
lean_lib Gittins where
  globs := #[`Gittins.*]

@[default_target]
lean_lib Utility where
  globs := #[`Utility.*]

@[default_target]
lean_lib Coherence where
  globs := #[`Coherence.*]
