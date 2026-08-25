import Discrepancy.Basic
import Discrepancy.Kernel
import Discrepancy.Partial
import Discrepancy.Progress
import Discrepancy.BeckFiala
import Discrepancy.Komlos
import Discrepancy.ErdosSpencer

/-!
# Agrégateur racine du lake `discrepancy_lean`

Importe les modules des paliers P0 et P1 (issue #12823) :

- `Discrepancy.Basic` : définitions (`IsColoring`, `discrepancy`, `degree`,
  `maxDegree`), lemmes élémentaires, conjecture de Beck–Fiala et énoncé
  cible `BeckFialaClassic` (`disc ≤ 2k − 1`) ;
- `Discrepancy.Kernel` : boute b1 — double comptage dimensionnel et vecteur de noyau (P1 de #12823) ;
- `Discrepancy.Partial` : boute b2 — invariant de coloration partielle, lignes figées à `2k−1` (P1 de #12823) ;
- `Discrepancy.Progress` : boute b3 — lemme de progrès, pas minimal atteignant la frontière (P1 de #12823) ;
- `Discrepancy.BeckFiala` : boute b4 — terminaison et assemblage, `theorem beck_fiala_classic` (P1 de #12823) ;
- `Discrepancy.Komlos` : conjecture de Komlós et formes Bansal–Jiang 2025
  (arXiv:2508.03961) ;
- `Discrepancy.ErdosSpencer` : boute P2 — borne inférieure Erdős–Spencer
  `√k/2` (méthode probabiliste, kernel `PacLearning.Hoeffding` importé).

État des preuves et découpage en boutes : `FORMAL_STATUS.md`. Notebook
compagnon prévu : `Search-15-CombinatorialDiscrepancy` (livrable A de
l'issue #12823).
-/
