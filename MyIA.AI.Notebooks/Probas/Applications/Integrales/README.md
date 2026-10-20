# Intégrales de Feynman : le triangle scalaire à une boucle

[← Série Probas](../../README.md) · [← Applications](../README.md)

Le **triangle scalaire** à une boucle — trois propagateurs sans masse, un moment
externe par sommet — en dimension 4 euclidienne : l'une des briques de base des
corrections radiatives, et l'un des objets de la famille « 30 intégrales de
Feynman » du harnais [BootLoops](https://github.com/BootLoops-ai) (MIT), rapportée
par M. Schwartz dans *Claude-shaped science* (2025). Ce dossier en est la **veine
V3** de la distillation [issue #20428](https://github.com/jsboige/CoursIA/issues/20428),
après la veine V1 (marches aléatoires).

| Composant | Notebook | Stack | Ce qu'il apporte |
|-----------|----------|-------|------------------|
| [Integrales-01-Triangle-Scalaire](Integrales-01-Triangle-Scalaire-Python.ipynb) | 1 (Python) | Python 3 + `mpmath` + `numpy` + `matplotlib` | Représentation de Feynman du triangle ($\Delta = \alpha x_1x_2 + \gamma x_1x_3 + \beta x_2x_3$, $C_0 = J/16\pi^2$) dérivée au §1 ; **trois voies** de calcul de $J$ (quadrature 2D imbriquée, substitution homogène $(u,v)$, intégrale exacte en $v$) accordées à plus de 20 chiffres sur quatre cinématiques, dont un point de stress et un point non isocèle ; forme fermée $J(1,1,2-2\cos\psi) = 2\,\mathrm{Cl}_2(\psi)/\sin\psi$ certifiée à ~38 chiffres sur six angles, avec les cas exacts $2G$ (Catalan) et $\frac{4}{\sqrt{3}}\,\mathrm{Cl}_2(\pi/3)$ |

Trois protocoles du harnais BootLoops y sont pratiqués sur un cas où ils
mordent : **planted-truth** (l'outil d'identification de constantes est validé
contre des valeurs connues *avant* usage — le piège `clsin(1,·)`/`clcos(2,·)` de
`mpmath` est montré et attrapé) ; **constant-recognition** (l'anneau de recherche
est *déclaré avant* la recherche, et un échec se conclut « pas de forme fermée
identifiée », jamais une constante inventée) ; **acceptance-gate** (un contrôle
négatif *mord* — écarts relatifs $1/3$ et $1/2$ — et son point aveugle est nommé :
à l'angle autodual $\psi = 90°$ les deux appariements coïncident, un contrôle à un
seul point serait passé). Le carnet porte aussi son **périmètre honnête** (§7) :
précision ≠ bornes certifiées, identifiée ≠ dérivée.

## Ponts vers le reste du dépôt

- **Marches** ([../Marches/](../Marches/README.md)) : les deux carnets calculent
  des fonctions de Green — l'une sur $\mathbb{Z}^d$ discret, l'autre sur une
  boucle continue — et les mêmes protocoles les traversent.
- **Distillation Schwartz** ([issue #20428](https://github.com/jsboige/CoursIA/issues/20428)) :
  ce carnet est la veine V3 ; les veines V2 (protocoles `bootloops/skills`) et V4
  (reproductibilité NBER) restent ouvertes sur la même issue.

## Sources

- G. 't Hooft, M. Veltman, *Scalar one-loop integrals*, Nucl. Phys. B **153**,
  365 (1979).
- G. Passarino, M. Veltman, *One-loop corrections for $e^+e^-$ annihilation into
  $\mu^+\mu^-$ in the Weinberg model*, Nucl. Phys. B **160**, 151 (1979).
- L. Lewin, *Polylogarithms and Associated Functions*, North-Holland (1981) —
  fonction de Clausen $\mathrm{Cl}_2$.
- M. D. Schwartz, *Vibe physics* et *Claude-shaped science* (Anthropic, 2025),
  arXiv:2601.02484 (2026) — archivés au gisement
  `G:\Mon Drive\MyIA\IA\Bibliographie IA\Physics\`.
- *BootLoops* (MIT / CC-BY-4.0) — harnais d'intégrales certifiées et protocoles ;
  `kira` (GPL-3.0) cité sans réutilisation.