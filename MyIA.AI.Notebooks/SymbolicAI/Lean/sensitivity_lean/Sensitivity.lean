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

---
English:
Port of mathlib4/Archive/Sensitivity.lean to standalone Lake workspace.
Huang's sensitivity theorem: in the hypercube of dimension n >= 1, if one
colors more than half the vertices then at least one vertex has at least
sqrt(n) colored neighbors.
-/
import Sensitivity.Hypercube
import Sensitivity.VectorSpace
import Sensitivity.Operator
import Sensitivity.MainTheorem
