# Applications — Probas

Applications autonomes de la série Probas : des notebooks qui utilisent la
programmation probabiliste ou la formalisation Lean sur un problème complet,
sans appartenir à une progression numérotée. Chacun est lisible seul ; les
progressions vivent dans [`../Infer/`](../Infer/README.md),
[`../PyMC/`](../PyMC/README.md) et [`../DecisionTheory/`](../DecisionTheory/README.md).

| Notebook | Kernel | Sujet |
|---|---|---|
| [`Pyro_RSA_Hyperbole.ipynb`](Pyro_RSA_Hyperbole.ipynb) | Python 3 | Rational Speech Acts bayésien en Pyro — pragmatique linguistique, implicatures scalaires, hyperboles |
| [`Percolation/Percolation-Supercritique.ipynb`](Percolation/Percolation-Supercritique.ipynb) | Python 3 | Percolation de liens sur tore fini — simulation, trois régimes mesurés |
| [`Percolation/Percolation-Lean.ipynb`](Percolation/Percolation-Lean.ipynb) | Lean 4 (WSL) | Compagnon exécutable du lake `percolation_lean` — noyau fini prouvé sans `sorry` |

Le dossier [`Percolation/`](Percolation/README.md) a son README détaillé (duo
simulation + formalisation, adossé à [l'issue #14871](https://github.com/jsboige/CoursIA/issues/14871)).
