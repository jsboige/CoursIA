import Discrepancy.Basic
import Discrepancy.Komlos

/-!
# Agrégateur racine du lake `discrepancy_lean`

Importe les deux modules du palier P0 (issue #12823) :

- `Discrepancy.Basic` : définitions (`IsColoring`, `discrepancy`, `degree`,
  `maxDegree`), lemmes élémentaires, conjecture de Beck–Fiala et énoncé
  cible `BeckFialaClassic` (`disc ≤ 2k − 1`) ;
- `Discrepancy.Komlos` : conjecture de Komlós et formes Bansal–Jiang 2025
  (arXiv:2508.03961).

État des preuves et découpage en boutes : `FORMAL_STATUS.md`. Notebook
compagnon prévu : `Search-15-CombinatorialDiscrepancy` (livrable A de
l'issue #12823).
-/
