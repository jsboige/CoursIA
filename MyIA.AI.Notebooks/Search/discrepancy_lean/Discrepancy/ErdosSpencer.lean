import Discrepancy.ErdosSpencer.Moments
import Discrepancy.ErdosSpencer.LB

/-!
# Agrégateur Erdős–Spencer — re-export Moments + LB

Découpage de l'ancien monolithe de 1 827 lignes (issue #13508, Volet 2) :
déplacements byte-identiques, aucun énoncé réécrit.

- `Discrepancy.ErdosSpencer.Moments` : boute p1 — moments de la somme de
  Rademacher colorée, Paley–Zygmund, minoration de queue ;
- `Discrepancy.ErdosSpencer.LB` : bouts p2–p4 — familles aléatoires, union
  bound sur les colorations, contrôle du degré, et le théorème final
  `erdos_spencer_lb_explicit` (√k/14, prouvé). La forme optimiste
  `ErdosSpencerLB` (√k/2) reste une `Prop` ouverte.
-/
