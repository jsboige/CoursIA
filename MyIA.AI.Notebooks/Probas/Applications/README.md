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
| [`Integrales/Integrales-01-Triangle-Scalaire-Python.ipynb`](Integrales/Integrales-01-Triangle-Scalaire-Python.ipynb) | Python 3 | Le triangle scalaire à une boucle — trois voies de calcul (Feynman 2D, rectangle $(u,v)$, intégrale exacte en $v$), contrôles mordants, forme fermée $J = 2\,\mathrm{Cl}_2(\psi)/\sin\psi$ identifiée à anneau déclaré |
| [`Integrales/Integrales-02-Sunrise-Masses-Egales-Python.ipynb`](Integrales/Integrales-02-Sunrise-Masses-Egales-Python.ipynb) | Python 3 | Le sunrise à masses égales en $d = 2$ — quatre voies accordées, ancre exacte sur le carnet 01, intégrande elliptique exhibée, refus documenté de forme fermée |

Le dossier [`Percolation/`](Percolation/README.md) a son README détaillé (duo
simulation + formalisation, adossé à [l'issue #14871](https://github.com/jsboige/CoursIA/issues/14871)),
ainsi que [`Marches/`](Marches/README.md) (veine V1 de la distillation
Schwartz/BootLoops, [issue #20428](https://github.com/jsboige/CoursIA/issues/20428))
et [`Integrales/`](Integrales/README.md) (veine V3 de la même distillation — du
triangle scalaire au diagramme sunrise).
