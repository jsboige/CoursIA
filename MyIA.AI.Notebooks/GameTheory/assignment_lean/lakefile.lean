import Lake
open Lake DSL

-- Hommage James R. Munkres (1930-2026), issue #12598 (1/3) :
-- lake compagnon du notebook GameTheory-27-Munkres-Assignment.ipynb.
-- Kuhn (1955) / Munkres (1957), methode hongroise pour le probleme
-- d'affectation. Le lake formalise la charpente de correction :
-- dualite faible LP, certificat d'optimalite a gap nul, et preservation
-- de la realisabilite duale par le resserrement hongrois.
--
-- Convention i18n EPIC #4980 (cf game_theory_lean) :
-- `globs` avec suffixe `.*` pour auto-decouvrir les siblings `_en`.
package «assignment_lean» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, true⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.1"

@[default_target]
lean_lib Assignment where
  globs := #[`Assignment.*, `Assignment_en]
