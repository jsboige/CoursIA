# Marches aléatoires : le retour

[← Série Probas](../../README.md) · [← Applications](../README.md)

La question de Pólya (1921) — « la marche revient-elle jamais ? » — suivie
jusqu'au « **problème final de Watson** » : la probabilité de retour **exacte**
d'une marche 3D à trois taux de saut inégaux, posée en 1939 et fermée en 2026
par un harnais d'agents de calcul (projet BootLoops, rapporté par M. Schwartz,
essai *Claude-shaped science*). Ce dossier en est la veine V1 de la distillation
[issue #20428](https://github.com/jsboige/CoursIA/issues/20428).

| Composant | Notebook | Stack | Ce qu'il apporte |
|-----------|----------|-------|------------------|
| [Marches-01-Retour-Polya-Watson](Marches-01-Retour-Polya-Watson-Python.ipynb) | 1 (Python) | Python 3 + `mpmath` + `numpy` | Théorème de Pólya par série génératrice ($G_d(\beta)$, divergence $d \leq 2$) et simulation ; intégrale de Watson isotrope à haute précision contre forme fermée en fonctions $\Gamma$ (22 chiffres de coïncidence) ; marche anisotrope $(1/2, 1/3, 1/6)$ — $R \approx 0{,}3790736$ — contre-vérifiée par Monte-Carlo multi-graine avec biais d'horizon quantifié en $n^{-1/2}$ |

Deux protocoles du harnais BootLoops y sont pratiqués sur un cas où ils
mordent : **planted-truth** (chaque constante est vérifiée numériquement *avant*
d'être confrontée à sa forme fermée — y compris un piège d'annulation
d'exposant attrapé en construisant le carnet) et **acceptance-gate** (le
résultat exact est retrouvé par une route indépendante — simulation — dont le
biais systématique est mesuré, pas ignoré).

## Ponts vers le reste du dépôt

- **Percolation** ([../Percolation/](../Percolation/README.md)) : même famille
  de questions — que fait le hasard sur un réseau $\mathbb{Z}^d$ à la limite
  $d = 2/3$ — vue du côté de la connectivité (seuil $p_c$) plutôt que du retour.
- **Distillation Schwartz** ([issue #20428](https://github.com/jsboige/CoursIA/issues/20428)) :
  ce carnet est la veine V1 ; les protocoles `bootloops/skills` (V2) et la
  reproductibilité NBER (V4) sont d'autres veines de la même issue.

## Sources

- G. Pólya, *Mathematische Annalen* **84**, 149–160 (1921).
- G. N. Watson, « Three Triple Integrals », *Q. J. Math.* **10**(1), 266–276
  (1939), doi:10.1093/qmath/os-10.1.266 — non disponible en accès ouvert
  (citation bibliographique seule).
- M. D. Schwartz, *Vibe physics* et *Claude-shaped science* (Anthropic, 2025),
  arXiv:2601.02484 (2026) — archivés au gisement
  `G:\Mon Drive\MyIA\IA\Bibliographie IA\Physics\` (rayon Physics).
