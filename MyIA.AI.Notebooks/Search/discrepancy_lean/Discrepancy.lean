import Discrepancy.Basic
import Discrepancy.Kernel
import Discrepancy.Partial
import Discrepancy.Komlos

/-!
# Agrégateur racine du lake `discrepancy_lean`

Importe les deux modules du palier P0 (issue #12823) :

- `Discrepancy.Basic` : définitions (`IsColoring`, `discrepancy`, `degree`,
  `maxDegree`), lemmes élémentaires, conjecture de Beck–Fiala et énoncé
  cible `BeckFialaClassic` (`disc ≤ 2k − 1`) ;
- `Discrepancy.Kernel` : boute b1 — double comptage dimensionnel et vecteur de noyau (P1 de #12823) ;
- `Discrepancy.Partial` : boute b2 — invariant de coloration partielle, lignes figées à `2k−1` (P1 de #12823) ;
- `Discrepancy.Partial` : boute b2 — invariant de coloration partielle, lignes figées à `2k−1` (P1 de #12823) ;
- `Discrepancy.Komlos` : conjecture de Komlós et formes Bansal–Jiang 2025
  (arXiv:2508.03961).

État des preuves et découpage en boutes : `FORMAL_STATUS.md`. Notebook
compagnon prévu : `Search-15-CombinatorialDiscrepancy` (livrable A de
l'issue #12823).
-/
