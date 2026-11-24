import Lake
open Lake DSL

package «linear_lean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.0"

-- Marche Axler (Epic Origami #24838, Fille 3.1) : le socle d'algebre lineaire
-- d'Axler (*Linear Algebra Done Right*, 4e ed., CC BY-NC 4.0) ecrit en marches
-- `.lean` avant Lean-12/13. Aucune ligne recopiee des compagnons (rkirov/
-- linear-algebra-done-right-lean, Apache-2.0 declare dans son README amont ;
-- blanketism/Axler-Solutions, sans licence declaree) : leur progression est
-- comparee, jamais vendue. Cette tranche (marche 1) est FR seule ; les
-- jumeaux `_en` #4980 sont une tranche suivante.

@[default_target]
lean_lib «Linear» where
  globs := #[.andSubmodules `Linear]
