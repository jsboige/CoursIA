import Sensitivity.MainTheorem
import Sensitivity.Sens2026

/-!
# Point d'entree de verification pour le carnet ANALYSE-06

Ce fichier n'est PAS compile par `lake build` (hors globs de la lib) : il sert
au carnet `../ANALYSE/ANALYSE-06-Sensibilite-2026-Lean-Python.ipynb`, qui
l'execute via `lake env lean Check.lean` pour afficher les signatures reelles
du socle et de l'ajout 2026, et prouver l'integrite des theoremes (aucun
axiome au-dela des trois standards, aucun sorry).

Statut epistemique (Epic Origami #19898, Pli 2) : les enonces 127/132/186/192
du depot openai/math sont cites par le carnet AVEC leur statut — formalises
en amont (squelette Lean publie), non re-prouves ici. Ce qui est verifie
ci-dessous est a NOUS : les definitions de `Separations`, le temoin `tribes32`
de `Sens2026`, et le theoreme de Huang porte par le lac.
-/

#check @Sensitivity.sensitivity
#check @Sensitivity.blockSensitivity
#check @Sensitivity.tribes32
#check @Sensitivity.tribes32_sensitivity_zero
#check @Sensitivity.tribes32_sensitivity_eq_three
#check @Sensitivity.tribes32_blockSensitivity_ge_three
#check @Sensitivity.tribes32_local_separation
#check @Sensitivity.or3_blockSensitivity
#check @Sensitivity.orOfAnds_strict_separation
#check @Sensitivity.huang_degree_theorem

#print axioms Sensitivity.huang_degree_theorem
#print axioms Sensitivity.tribes32_sensitivity_zero
#print axioms Sensitivity.tribes32_sensitivity_eq_three
#print axioms Sensitivity.tribes32_blockSensitivity_ge_three
#print axioms Sensitivity.tribes32_local_separation
#print axioms Sensitivity.or3_blockSensitivity
#print axioms Sensitivity.orOfAnds_strict_separation
