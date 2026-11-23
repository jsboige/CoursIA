/-
  Linear — racine du lake `linear_lean` (Fille 3.1, Epic Origami #24838)
  ============================================

  Série des marches d'Axler (*Linear Algebra Done Right*, 4e éd., CC BY-NC
  4.0, copie archivée — chemin dans `Linear/EspacesVectoriels.lean`) :
  - `Linear.EspacesVectoriels` — chapitre 1 (1.A-1.C) : scalaires, vecteur
    nul, sommes et sommes directes ;
  - `Linear.DimensionFinie` — chapitre 2 (2.A-2.C) : familles libres,
    bases, dimension finie, formule de Grassmann ;
  - `Linear.ApplicationsLineaires` — chapitre 3, sections 3.A, 3.B et 3.D :
    applications linéaires, noyau, image, théorème fondamental (3.21),
    inversibilité et isomorphismes.

  Chaque module porte l'ordre d'Axler et délègue les résultats à Mathlib.
  Cette tranche est FR seule ; les jumeaux `_en` (convention #4980) sont une
  tranche suivante documentée au `README.md §i18n`.
-/
import Linear.EspacesVectoriels
import Linear.DimensionFinie
import Linear.ApplicationsLineaires
