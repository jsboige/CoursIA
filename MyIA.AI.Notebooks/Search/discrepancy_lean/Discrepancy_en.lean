import Discrepancy.Basic_en
import Discrepancy.Komlos_en

/-!
# i18n convention: EN sibling file

i18n convention ratified for this repository (EPIC #4980): for each canonical
FR file `Foo.lean`, an EN sibling `Foo_en.lean` mirrors it with translated
docstrings and comments ONLY — signatures, definitions, proofs and tactics
are byte-identical; the namespace carries the `_en` suffix to avoid name
clashes. The FR file remains the canonical teaching source.
-/

/-!
# Root aggregator of the `discrepancy_lean` lake (EN mirror)

Imports the two modules of tier P0 (issue #12823):

- `Discrepancy.Basic_en`: definitions (`IsColoring`, `discrepancy`,
  `degree`, `maxDegree`), elementary lemmas, Beck–Fiala conjecture and
  target statement `BeckFialaClassic` (`disc ≤ 2k − 1`);
- `Discrepancy.Komlos_en`: Komlós conjecture and Bansal–Jiang 2025 forms
  (arXiv:2508.03961).

State of the proofs and brick breakdown: `FORMAL_STATUS.md`. Companion
notebook (deliverable A of issue #12823): delivered, then renumbered --
see #13771 for its canonical number. The name
`Search-15-*` was an opportunistic number never retained
(`Search-15` denotes the NetworkX notebooks).
-/
