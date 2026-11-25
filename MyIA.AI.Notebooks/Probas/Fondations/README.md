# Fondations — quand peut-on croire une approximation ?

[↑ Série Probas](../README.md)

Une moyenne de mesures indépendantes et une moyenne de tirages successifs d'une chaîne ne s'interprètent pas de la même façon. Ici, on connaît la loi cible : on peut donc mesurer l'erreur au lieu de se fier à la forme d'un histogramme. Il suffit de connaître la moyenne, la variance et les probabilités conditionnelles. Choisissez Python ou C# ; les deux versions posent les mêmes questions, sans exiger les mêmes trajectoires aléatoires.

## Comment lire ce README — découverte

[Choisir sa vitesse de lecture](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) : suivez une expérience avant de comparer les moteurs.

- Vous découvrez : commencez par la somme de variables indépendantes.
- Vous creusez un palier : confrontez la variance groupée aux moyennes de chaque chaîne.
- Vous cherchez la recherche en cours : passez du mélange bimodal au problème inverse de percolation.

## Parcours principal — licence et master

| Expérience | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| Sommes indépendantes | [Python](Probas-CLT-Theoreme-Central-Limite.ipynb) · [C#](Probas-CLT-Theoreme-Central-Limite-CSharp.ipynb) | Comparer une fonction de répartition empirique à la gaussienne par leur écart maximal, puis changer la loi des termes de la somme. | Licence | Que devient la normalisation si la variance est infinie ? |
| Tirages dépendants | [Python](Probas-MCMC-Echantillonnage-Metropolis-Python.ipynb) · [C#](Probas-MCMC-Echantillonnage-Metropolis-CSharp.ipynb) | Construire un pas d'acceptation de Metropolis–Hastings et un échantillonneur de Gibbs ; mesurer corrélation et taille effective d'échantillon. | Licence avancée | Pourquoi plusieurs chaînes sont-elles nécessaires ? |

## Approfondissements — master

**Autour du théorème central limite.** La borne de Berry–Esseen en `1/√n` suppose un troisième moment absolu fini ; elle ne promet pas une vitesse identique pour toutes les lois. Avec la loi de Lomax de paramètre 1,5, même la variance n'existe pas. Dans l'expérience Python, la médiane de la valeur absolue de la somme centrée divisée par `√n` passe de 2,94 à 6,75 entre `n = 10` et `640`. Pour la loi uniforme, elle reste proche de 0,39. Une médiane permet ici de comparer les échelles sans estimer une variance inexistante.

**Autour de Metropolis.** Sur la gaussienne de corrélation 0,8, la version Python obtient 0,801 par Metropolis et 0,799 par Gibbs ; l'approximation à composantes indépendantes donne −0,014. Les chaînes de Metropolis y donnent `R-hat = 1,0030` : proche de 1, c'est un signal de cohérence, pas une preuve de convergence. Sur le mélange bimodal, la variance groupée de 6,359 semble proche de la cible 6,5. Pourtant `R-hat = 2,272` : des chaînes restent dans des modes différents. Le jumeau C# donne lui aussi l'alerte (`R-hat = 5,122`), sans reproduire la même variance groupée. Le diagnostic à retrouver est le désaccord entre chaînes, pas la décimale d'une trajectoire.

## Installation et prolongements — pratique

Les noyaux sont `python3` et `.net-csharp` ; les versions C# épinglent `MathNet.Numerics 5.0.0`. Voir les [dépendances Python](../requirements.txt) et le [guide des noyaux](../../../docs/reference/kernels-runtime.md).

Pour distinguer convergence en loi et concentration en grande dimension, poursuivre avec [Concentration de la mesure](../Applications/Probas-KLS-Concentration.ipynb). Le [projet de synthèse sur la percolation](../Probas-Capstone-Percolation-Bayesienne-Python.ipynb) réutilise Metropolis sur une cible dont on cherche cette fois à apprendre les paramètres.
