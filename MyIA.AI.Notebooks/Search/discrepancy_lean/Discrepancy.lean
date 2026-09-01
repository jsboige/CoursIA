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
  **prouvée à constante explicite `√k/14`** (`erdos_spencer_lb_explicit`,
  méthode probabiliste, kernel `PacLearning.Hoeffding` importé) ; la forme
  optimiste `√k/2` (`ErdosSpencerLB`) reste une `Prop` ouverte. Découpé en
  sous-modules (#13508 Volet 2) : `ErdosSpencer.Moments` (boute p1 — moments
  de la somme de Rademacher colorée) et `ErdosSpencer.LB` (boutes p2–p4 et
  le théorème final) ; `ErdosSpencer.lean` est l'agrégateur qui re-exporte
  les deux.

État des preuves et découpage en boutes : `FORMAL_STATUS.md`. Notebook
compagnon (livrable A de l'issue #12823) : livré, puis renuméroté —
voir #13771 pour sa numérotation canonique. Le nom
`Search-15-*` était une numérotation d'opportunité jamais retenue
(`Search-15` désigne les cahiers NetworkX).
-/
