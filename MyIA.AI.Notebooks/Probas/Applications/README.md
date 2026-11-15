# Applications — Probas

[← Série Probas](../README.md)

Applications autonomes de la série Probas : des notebooks qui utilisent la
programmation probabiliste ou la formalisation Lean sur un problème complet,
sans appartenir à une progression numérotée. Chacun est lisible seul ; les
progressions vivent dans [`../Infer/`](../Infer/README.md),
[`../PyMC/`](../PyMC/README.md) et [`../DecisionTheory/`](../DecisionTheory/README.md).

| Notebook | Kernel | Sujet |
|---|---|---|
| [`Pyro_RSA_Hyperbole.ipynb`](Pyro_RSA_Hyperbole.ipynb) | Python 3 | Rational Speech Acts bayésien en Pyro — pragmatique linguistique, implicatures scalaires, hyperboles |
| [`Quotients-Fibres-Recollement-Python.ipynb`](Quotients-Fibres-Recollement-Python.ipynb) | Python 3 | Quotients, fibres et recollement : ce qui survit à la projection (ex-Infer-20) |
| [`Probas-KLS-Concentration.ipynb`](Probas-KLS-Concentration.ipynb) | Python 3 | Gap spectral, constante de Cheeger et thin-shell en dimension croissante — contrepoint non-bayésien de la série |
| [`Percolation/Percolation-01-Supercritique-Python.ipynb`](Percolation/Percolation-01-Supercritique-Python.ipynb) | Python 3 | Percolation de liens sur tore fini — simulation, trois régimes mesurés |
| [`Percolation/Percolation-02-Lean.ipynb`](Percolation/Percolation-02-Lean.ipynb) | Lean 4 (WSL) | Compagnon exécutable du lake `percolation_lean` — noyau fini prouvé sans `sorry` |
| [`Marches-01-Retour-Polya-Watson-Python.ipynb`](Marches-01-Retour-Polya-Watson-Python.ipynb) | Python 3 | Le retour de Pólya au « problème final » de Watson — série génératrice, intégrale de Watson contre forme fermée, anisotrope haute précision + Monte-Carlo |

Le dossier [`Percolation/`](Percolation/README.md) a son README détaillé (duo
simulation + formalisation, adossé à [l'issue #14871](https://github.com/jsboige/CoursIA/issues/14871)).

Le carnet [`Probas-KLS-Concentration.ipynb`](Probas-KLS-Concentration.ipynb) —
ex-carnet transverse de la racine de la série — s'est replié ici comme
**application autonome de la géométrie log-concave** (section B de
[#24197](https://github.com/jsboige/CoursIA/issues/24197)) : ses prérequis
(`Infer-03`, `PyMC-14`) en font un carnet d'application, pas un socle. Sa
documentation détaillée vit dans le [README de la série](../README.md#probas-kls-concentrationipynb).

Le carnet [`Marches-01-Retour-Polya-Watson-Python.ipynb`](Marches-01-Retour-Polya-Watson-Python.ipynb)
est la veine V1 de la distillation Schwartz/BootLoops
([issue #20428](https://github.com/jsboige/CoursIA/issues/20428)) : la question
de Pólya (1921) — « la marche revient-elle jamais ? » — suivie jusqu'au
« **problème final de Watson** », la probabilité de retour **exacte** d'une
marche 3D à trois taux de saut inégaux, posée en 1939 et fermée en 2026 par un
harnais d'agents de calcul (projet BootLoops, rapporté par M. Schwartz, essai
*Claude-shaped science*).

Deux protocoles du harnais BootLoops y sont pratiqués sur un cas où ils
mordent : **planted-truth** (chaque constante est vérifiée numériquement *avant*
d'être confrontée à sa forme fermée — y compris un piège d'annulation
d'exposant attrapé en construisant le carnet) et **acceptance-gate** (le
résultat exact est retrouvé par une route indépendante — simulation — dont le
biais systématique est mesuré, pas ignoré).

Son pont vers le reste du dépôt : **Percolation** ([`Percolation/`](Percolation/README.md)),
même famille de questions — que fait le hasard sur un réseau $\mathbb{Z}^d$ à
la limite $d = 2/3$ — vue du côté de la connectivité (seuil $p_c$) plutôt que
du retour.

La veine V3 de la même distillation — du triangle scalaire au rung elliptique du
sunrise — a quitté `Applications/` : les intégrales de Feynman ne sont pas des
objets probabilistes, et la série [`Physique/Integrales/`](../../Physique/Integrales/README.md)
est le toit commun des distillations de physique numérique
([EPIC #23161](https://github.com/jsboige/CoursIA/issues/23161)).

## Sources

Références du carnet `Marches-01` (la liste complète, avec Joyce et les trois
pièces de Schwartz, est dans sa section « Références ») :

- G. Pólya, *Mathematische Annalen* **84**, 149–160 (1921).
- G. N. Watson, « Three Triple Integrals », *Q. J. Math.* **10**(1), 266–276
  (1939), doi:10.1093/qmath/os-10.1.266 — non disponible en accès ouvert
  (citation bibliographique seule).
- G. S. Joyce, « On the simple cubic lattice Green function », *Phil. Trans.
  R. Soc. Lond. A* **273**, 583–610 (1973) — la forme fermée de $G_3(1)$, dont
  la valeur $1{,}5164$ est reprise par le carnet.
- M. D. Schwartz, *Vibe physics* et *Claude-shaped science* (Anthropic, 2025),
  arXiv:2601.02484 (2026) — archivés au gisement
  `G:\Mon Drive\MyIA\IA\Bibliographie IA\Physics\` (rayon Physics).
