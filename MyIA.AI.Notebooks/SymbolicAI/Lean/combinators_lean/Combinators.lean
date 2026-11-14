/-
# Combinators — confluence formelle du systeme S/K/I

Pli 4 de l'Epic Origami #19742 (grain B, #25061). Modules :

- `Combinators.Term` — termes S/K/I, taille, reduction a un pas `step` ;
- `Combinators.Parallel` — reduction parallele `par`, lemmes de forme,
  lemme du losange par induction forte sur la taille ;
- `Combinators.Confluence` — invocation de l'organe Mathlib
  `Relation.church_rosser`, confluence de `step*`, unicite de la forme
  normale.
-/

import Combinators.Term
import Combinators.Parallel
import Combinators.Confluence
