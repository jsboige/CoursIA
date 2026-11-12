# Fondations — Probas

[← Série Probas](../README.md)

Socle mathématique **commun** aux deux stacks de la série : le corpus bayésien
[`../Infer/`](../Infer/README.md) et le port [`../PyMC/`](../PyMC/README.md)
présupposent tous deux le théorème central limite et l'échantillonnage MCMC
qu'il rend possible. Ces carnets n'appartiennent ni à l'un ni à l'autre — c'est
la raison de niveau qui les réunit ici (section B de
[#24197](https://github.com/jsboige/CoursIA/issues/24197)) : un carnet qui
mesure **l'outil** que les deux stacks utilisent en boîte noire n'est pas un
carnet de moteur.

| Notebook | Kernel | Sujet | Durée |
|---|---|---|---|
| [`Probas-CLT-Theoreme-Central-Limite.ipynb`](Probas-CLT-Theoreme-Central-Limite.ipynb) | Python 3 | Le TCL mesuré : le taux `1/√n` comme borne (Berry–Esseen), l'hypothèse de variance finie porteuse | 15 min |
| [`Probas-CLT-Theoreme-Central-Limite-CSharp.ipynb`](Probas-CLT-Theoreme-Central-Limite-CSharp.ipynb) | .NET C# | Le même protocole avec MathNet.Numerics 5.0.0, distance d'ECDF et échelle robuste de Lomax | 20 min |
| [`Probas-MCMC-Echantillonnage-Metropolis-Python.ipynb`](Probas-MCMC-Echantillonnage-Metropolis-Python.ipynb) | Python 3 | Metropolis–Hastings et Gibbs from-scratch, diagnostics `ESS`/`R-hat`, là où l'approximation naïve échoue | 30 min |

L'ordre de lecture suit la table : le TCL d'abord (pourquoi la gaussienne est
partout), l'échantillonnage ensuite (comment l'interroger quand l'intégrale
n'a pas de forme fermée). La documentation détaillée de chaque carnet vit dans
le [README de la série](../README.md#fondations-dossier-fondations) ; les
applications autonomes sont dans [`../Applications/`](../Applications/README.md).
