# Applications — Probas

Applications autonomes de la série Probas : des notebooks qui utilisent la
programmation probabiliste ou la formalisation Lean sur un problème complet,
sans appartenir à une progression numérotée. Chacun est lisible seul ; les
progressions vivent dans [`../Infer/`](../Infer/README.md),
[`../PyMC/`](../PyMC/README.md) et [`../DecisionTheory/`](../DecisionTheory/README.md).

| Notebook | Kernel | Sujet |
|---|---|---|
| [`Pyro_RSA_Hyperbole.ipynb`](Pyro_RSA_Hyperbole.ipynb) | Python 3 | Rational Speech Acts bayésien en Pyro — pragmatique linguistique, implicatures scalaires, hyperboles |
| [`Percolation/Percolation-01-Supercritique-Python.ipynb`](Percolation/Percolation-01-Supercritique-Python.ipynb) | Python 3 | Percolation de liens sur tore fini — simulation, trois régimes mesurés |
| [`Percolation/Percolation-02-Lean.ipynb`](Percolation/Percolation-02-Lean.ipynb) | Lean 4 (WSL) | Compagnon exécutable du lake `percolation_lean` — noyau fini prouvé sans `sorry` |
| [`Marches/Marches-01-Retour-Polya-Watson-Python.ipynb`](Marches/Marches-01-Retour-Polya-Watson-Python.ipynb) | Python 3 | Le retour de Pólya au « problème final » de Watson — série génératrice, intégrale de Watson contre forme fermée, anisotrope haute précision + Monte-Carlo |

Le dossier [`Percolation/`](Percolation/README.md) a son README détaillé (duo
simulation + formalisation, adossé à [l'issue #14871](https://github.com/jsboige/CoursIA/issues/14871)),
ainsi que [`Marches/`](Marches/README.md) (veine V1 de la distillation
Schwartz/BootLoops, [issue #20428](https://github.com/jsboige/CoursIA/issues/20428)).
