import KLS.Defs

/-!
# Point d'entree de verification pour le carnet ANALYSE-05

Ce fichier n'est PAS compile par `lake build` (hors globs de la lib) : il sert
au carnet `../ANALYSE-05-KLS-Lean-Python.ipynb`, qui l'execute via
`lake env lean Check.lean` pour afficher les declarations du socle et prouver
l'integrite des deux theoremes (aucun axiome, aucun sorry).
-/

open KLS

#check @KLS.IsLogConcaveFun
#check @KLS.IsLogConcaveMeasure
#check @KLS.IsIsotropicMeasure
#check @KLS.poincareConstant
#check @KLS.cheegerConstant
#check @KLS.convexOn_half_sq
#check @KLS.gaussProfile_logConcave

#print axioms KLS.convexOn_half_sq
#print axioms KLS.gaussProfile_logConcave
