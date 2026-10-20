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

## Feuille de route

La série n'est pas née d'un carnet isolé : elle est la **veine V3** de la
distillation [#20428](https://github.com/jsboige/CoursIA/issues/20428), son aînée
V1 ([Marches](../Marches/README.md)) est déjà fusionnée, et son fil directeur est
la classification du harnais BootLoops — polylogarithmes → elliptique → K3 →
Calabi-Yau. Les carnets suivants sont des **candidats bornés**, arbitrés à
l'usage — aucun n'est promis :

- **Integrales-02 — Le diagramme sunrise à masses égales : la sortie des
  polylogarithmes** (candidat) : un tour de boucle de plus que le triangle, le
  même polynôme de Symanzik $U = x_1x_2 + x_1x_3 + x_2x_3$ — et en $d = 2$
  l'objet devient elliptique. (Le triangle *massif* à une boucle, lui, reste
  dilogarithmique — 't Hooft–Veltman : le saut de classe se produit ici, pas
  là.) À $q^2 = 0$ le sunrise retombe exactement sur $J(1,1,1)$ du carnet 01 :
  l'ancre entre les deux carnets est mathématiquement exacte.
- **Integrales-03 — La bulle et la première divergence** (candidat) : deux
  propagateurs en $d = 4$, la divergence logarithmique UV, et la régularisation
  introduite comme le carnet 01 traite ses limites — un paramètre, une échelle,
  une limite finie exhibée.

Le nom et le toit définitifs de la série restent un **point de décision ouvert**
(#20428, point de décision 1 : la « série de physique numérique », question
partagée avec [#19741](https://github.com/jsboige/CoursIA/issues/19741)) ;
`Probas/Applications/Integrales/` est l'hôte intérimaire, cohérent avec l'aînée
V1 dans `Applications/Marches/`.

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