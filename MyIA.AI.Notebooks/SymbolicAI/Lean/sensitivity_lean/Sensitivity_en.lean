/-
Copyright (c) 2019 Reid Barton, Johan Commelin, Jesse Michael Han, Chris Hughes, Robert Y. Lewis,
Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Johan Commelin, Jesse Michael Han, Chris Hughes, Robert Y. Lewis,
  Patrick Massot

Port of mathlib4/Archive/Sensitivity.lean to standalone Lake workspace.
Huang's sensitivity theorem: in the hypercube of dimension n >= 1, if one
colors more than half the vertices then at least one vertex has at least
sqrt(n) colored neighbors.

i18n convention #4980 (sibling pair): this root is EN-only, the canonical
French aggregator twin is `Sensitivity.lean`.
-/
import Sensitivity.Hypercube_en
import Sensitivity.VectorSpace_en
import Sensitivity.Operator_en
import Sensitivity.MainTheorem_en
