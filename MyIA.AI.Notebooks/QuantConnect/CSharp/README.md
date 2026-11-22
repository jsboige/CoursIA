# QuantConnect — jumeaux C#

Les carnets de cette section sont les **jumeaux .NET** des carnets Python de
[QuantConnect](../Python/README.md) : même contrat, mêmes chiffres, même
pédagogie — écrits en **C# / .NET Interactive**, BCL pur, sans package externe.

Chaque jumeau est enregistré au registre des parités
(`scripts/notebook_tools/twin_pairs.d/`), qui porte son niveau de parité et
les différences connues entre les deux côtés.

## Comment lire ce README

| Carnet | Ce qu'on y apprend |
|--------|--------------------|
| [QC-06b-Valorisation-Derives-CSharp](QC-06b-Valorisation-Derives-CSharp.ipynb) | Les trois moteurs de valorisation d'un dérivé (Black-Scholes en forme fermée, arbre binomial CRR, Monte-Carlo) reconduits en C# : fonction normale implémentée depuis le bas, convergence oscillante de l'arbre, put américain et prime d'exercice anticipé, intervalle de confiance de la simulation — **les mêmes chiffres que le jumeau Python** |

## Approfondissements

| Carnet | Rattaché à | Ce qu'on y apprend |
|--------|------------|--------------------|
| [QC-06b-Valorisation-Derives-CSharp](QC-06b-Valorisation-Derives-CSharp.ipynb) | [06b Python](../Python/QC-Py-06b-Derivatives-Valuation-From-Scratch.ipynb) | Le port C# du carnet de valorisation from-scratch : mêmes moteurs, mêmes verdicts, en .NET |

Le jumeau Python se lit d'abord : la version C# en reprend le contrat et les
mesures, et n'y ajoute que le langage d'exécution.
