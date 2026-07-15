/-
Copyright (c) 2019 Reid Barton, Johan Commelin, Jesse Michael Han, Chris Hughes, Robert Y. Lewis,
Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Johan Commelin, Jesse Michael Han, Chris Hughes, Robert Y. Lewis,
  Patrick Massot

Portage de mathlib4/Archive/Sensitivity.lean vers un workspace Lake autonome.
Théorème de sensibilité de Huang : dans l'hypercube de dimension n ≥ 1, si l'on
colorie plus de la moitié des sommets, alors au moins un sommet possède au moins
√n voisins coloriés.

Convention i18n #4980 (sibling pair) : cette racine est FR-seule canonique,
le jumeau anglais agrégateur est `Sensitivity_en.lean`.
-/
import Sensitivity.Hypercube
import Sensitivity.VectorSpace
import Sensitivity.Operator
import Sensitivity.MainTheorem
