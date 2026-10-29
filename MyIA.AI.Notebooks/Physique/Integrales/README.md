# Intégrales de Feynman : du triangle scalaire au sunrise

[← Racine des carnets](../../README.md) · [← Applications (Probas)](../../Probas/Applications/README.md)

Le **triangle scalaire** à une boucle — trois propagateurs sans masse, un moment
externe par sommet — en dimension 4 euclidienne, le **diagramme sunrise** à
masses égales en dimension 2, puis la **bulle** — deux propagateurs en $d = 4$,
la première divergence de la série — et le **rung elliptique** du sunrise, sa
courbe exhibée par le calcul : quatre briques des corrections radiatives, issues de
la famille « 30 intégrales de Feynman » du harnais
[BootLoops](https://github.com/BootLoops-ai) (MIT), rapportée par M. Schwartz dans
*Claude-shaped science* (2025). Ce dossier en est la **veine V3** de la
distillation [issue #20428](https://github.com/jsboige/CoursIA/issues/20428),
après la veine V1 (marches aléatoires).

| Composant | Notebook | Stack | Ce qu'il apporte |
|-----------|----------|-------|------------------|
| [Integrales-01-Triangle-Scalaire](Integrales-01-Triangle-Scalaire-Python.ipynb) | 1 (Python) | Python 3 + `mpmath` + `numpy` + `matplotlib` | Représentation de Feynman du triangle ($\Delta = \alpha x_1x_2 + \gamma x_1x_3 + \beta x_2x_3$, $C_0 = J/16\pi^2$) dérivée au §1 ; **trois voies** de calcul de $J$ (quadrature 2D imbriquée, substitution homogène $(u,v)$, intégrale exacte en $v$) accordées à plus de 20 chiffres sur quatre cinématiques, dont un point de stress et un point non isocèle ; forme fermée $J(1,1,2-2\cos\psi) = 2\,\mathrm{Cl}_2(\psi)/\sin\psi$ certifiée à ~38 chiffres sur six angles, avec les cas exacts $2G$ (Catalan) et $\frac{4}{\sqrt{3}}\,\mathrm{Cl}_2(\pi/3)$ |
| [Integrales-02-Sunrise-Masses-Egales](Integrales-02-Sunrise-Masses-Egales-Python.ipynb) | 2 (Python) | Python 3 + `mpmath` | Le sunrise à masses égales en $d = 2$ — même polynôme $U$ que le triangle, deux boucles : **quatre voies** (simplexe, rectangle $(u,v)$, Cheng–Wu, hyperbolique) accordées (A = B exact, CW à $10^{-20}$, hyperbolique à $10^{-15}$) ; ancre exacte $I(0) = J(1,1,1) = \frac{4}{\sqrt 3}\mathrm{Cl}_2(\pi/3)$ contre le carnet 01 ; intégrande elliptique de troisième espèce exhibée par $t = \cosh\theta$ ; piège du facteur 2 attrapé en direct ; deux identifications fermées **refusées** sur mesure (anneau déclaré avant recherche) |
| [Integrales-03-Bulle-Premiere-Divergence](Integrales-03-Bulle-Premiere-Divergence-Python.ipynb) | 3 (Python) | Python 3 + `mpmath` | La première divergence de la série : $B(\Lambda) = \pi^2(\ln\Lambda^2 + 1) + o(1)$, **coefficient $\pi^2$ mesuré à $7\times10^{-14}$** (différence $B(10\Lambda)-B(\Lambda)$, planted truth n° 1) et **constante finie $F = \pi^2$ ancrée dans $\int_0^1\ln\frac{1}{x(1-x)}dx = 2$** — calculable à la main, mesurée à $3\times10^{-25}$ (n° 2) et à $3\times10^{-29}$ par la **voie directe stabilisée**, laquelle n'a **aucun résidu** ; mesure de $S^3$ vérifiée avant usage (une première écriture rendait la moitié de l'intégrale) ; écart $\bar\Delta/\Lambda^2$ boule dure vs décalage **mesuré, pas masqué** (3,3 % à $\Lambda = 2$), de coefficient $\pi^2/3$ relevé ; **quadrature appliquée sur le coin $k = p$** diagnostiquée par un contrôle à quatre cases — artefact **constant** de $2\times10^{-4}$ en $\Lambda$, distinct du résidu réel en $1/\Lambda^2$ ; régularisation soustractive $B_R(\mu^2) = \pi^2(1+\ln\mu^2)$, premier « running » de la série ; refus documentés (pas de $\gamma_E$ ni $\ln 4\pi$ dans la boule dure — différence de schème, pas contradiction) |
| [Integrales-04-Sunrise-Courbe-Elliptique](Integrales-04-Sunrise-Courbe-Elliptique-Python.ipynb) | 4 (Python) | Python 3 + `mpmath` | Le rung elliptique du sunrise — **la courbe sort du calcul** : l'intégrale interne en $x$ est élémentaire (un `artanh`, coefficient $4$ et jacobien $(1-\chi)$ qui s'annule — deux erreurs de facteur attrapées par planted truth avant commit), il reste $y^2 = b(\chi)c(\chi)$, quartique de genre 1 aux racines $\{1, -1/s, r_\pm\}$ explicites, et $I(s) = \int 4\,\mathrm{artanh}\sqrt{b/c}\;d\chi/y$ — un dilogarithme elliptique en formation ; **périodes mesurées** sous $\chi = m + h\sin\theta$ (la substitution tue la singularité $1/\sqrt{\ }$ : de $10^{-9}$ à $10^{-18}$–$10^{-30}$) et **réduction de Legendre** $\psi_1/\psi_2 = K(1-k^2)/K(k^2)$ vérifiée sur trois points, module $k^2$ par birapport des racines ; $\tau(s)$ **court** — non constant, contrairement aux carnets 01-02 ; dégénérescences bornantes : $s\to0$ (une racine s'échappe, ancre $I(0)$ retrouvée à $O(s)$) et $s\to\infty$ (collision de racines, $k^2 \sim 16/s^3$ mesuré) ; module « naïf » du carnet 02 **mesuré comme différent** du module de la quartique (familles isogènes) ; ABW cité sans reproduction |

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
V1 ([Marches](../../Probas/Applications/Marches/README.md)) est déjà fusionnée, et son fil directeur est
la classification du harnais BootLoops — polylogarithmes → elliptique → K3 →
Calabi-Yau. Les carnets de la série ont été livrés comme des **candidats
bornés**, arbitrés à l'usage — aucun n'était promis :

- **Integrales-02 — Le diagramme sunrise à masses égales : la sortie des
  polylogarithmes** (livré — [carnet 02](Integrales-02-Sunrise-Masses-Egales-Python.ipynb)) :
  un tour de boucle de plus que le triangle, le
  même polynôme de Symanzik $U = x_1x_2 + x_1x_3 + x_2x_3$ — et en $d = 2$
  l'objet devient elliptique. (Le triangle *massif* à une boucle, lui, reste
  dilogarithmique — 't Hooft–Veltman : le saut de classe se produit ici, pas
  là.) À $q^2 = 0$ le sunrise retombe exactement sur $J(1,1,1)$ du carnet 01 :
  l'ancre entre les deux carnets est mathématiquement exacte.
- **Integrales-03 — La bulle et la première divergence** (livré —
  [carnet 03](Integrales-03-Bulle-Premiere-Divergence-Python.ipynb)) : deux
  propagateurs en $d = 4$, la divergence logarithmique UV, et la régularisation
  introduite comme le carnet 01 traite ses limites — un paramètre, une échelle,
  une limite finie exhibée. La constante finie $F = \pi^2$ y est ancrée dans une
  intégrale calculable à la main, et trois leçons de méthode (la mesure $S^3$
  vérifiée avant usage ; l'écart $\bar\Delta/\Lambda^2$ mesuré, pas masqué ; la
  quadrature appliquée sur le coin $k = p$, diagnostiquée par un contrôle à
  quatre cases plutôt que rafistolée) restent exposées dans le carnet.
- **Integrales-04 — Le rung elliptique du sunrise** (livré —
  [carnet 04](Integrales-04-Sunrise-Courbe-Elliptique-Python.ipynb)) : la courbe
  elliptique **exhibée par le calcul** plutôt que recopiée d'une référence —
  l'intégrale interne se fait en fonctions élémentaires et le reste vit sur la
  quartique $y^2 = bc$, dont les racines sont explicites. Périodes mesurées puis
  réduites à $K$ (module par birapport des racines, deux voies indépendantes),
  $\tau(s)$ non constant, et les deux dégénérescences qui bornent la famille
  ($s \to 0$ : une racine s'échappe, retour au monde $\mathrm{Cl}_2$ ; $s \to
  \infty$ : collision, pointe). La comparaison à la forme fermée d'Adams–Bogner–
  Weinzierl reste **citée sans être reproduite**, et le module « naïf » testé au
  carnet 02 y est mesuré comme n'étant pas celui de la quartique — une mesure,
  pas une correction. L'étage suivant du classement (K3, Calabi–Yau) demanderait
  des graphes à trois boucles, hors du périmètre arbitré de la série.

**Le toit `Physique/` se monte par tranches, et cette sous-série en est la
première.** Cette veine est la tranche **T1** de l'EPIC
[#23161](https://github.com/jsboige/CoursIA/issues/23161) ; les tranches
voisines sont **T2** `Jauge/` (théorème de Noether en sympy,
[PR #23169](https://github.com/jsboige/CoursIA/pull/23169)) et **T3**
`Numerique/` (Burgers, volumes finis, solveur de Riemann,
[PR #23172](https://github.com/jsboige/CoursIA/pull/23172)) — toutes deux encore
ouvertes au moment de cette livraison. Le **T0** (README de série
`Physique/README.md`, `Physique/index.qmd`, les listes codées en dur du
catalogue) appartient à l'EPIC et n'est **pas** dans cette tranche : l'ordre
prévu est **T1 → T0**, et le T0 devra donc énumérer les trois sous-séries
(`Integrales/`, `Jauge/`, `Numerique/`) pour que le toit ne reste pas dispersé.
En attendant, les seuls liens de voisinage sont donc ceux qui existent déjà :
les carnets voisins de `Integrales/` sont listés ci-dessus, et `Jauge/` comme
`Numerique/` n'apparaissent ici que comme tranches annoncées, sans lien vers
un dossier qui n'existe pas encore.

Le carnet habite désormais la série `Physique/` (EPIC
[#23161](https://github.com/jsboige/CoursIA/issues/23161)) : les intégrales de
Feynman ne sont pas des objets probabilistes, et `MyIA.AI.Notebooks/Physique/`
est le toit commun des distillations de physique numérique
([#19741](https://github.com/jsboige/CoursIA/issues/19741),
[#20428](https://github.com/jsboige/CoursIA/issues/20428)). L'aînée V1 reste dans
`Probas/Applications/Marches/` — la récurrence de Pólya est probabiliste native
— mais les deux séries se touchent par les fonctions de Green.

## Ponts vers le reste du dépôt

- **Marches** ([../../Probas/Applications/Marches/](../../Probas/Applications/Marches/README.md)) : les deux séries calculent
  des fonctions de Green — sur $\mathbb{Z}^d$ discret chez Marches, sur des
  boucles continues ici — et les mêmes protocoles les traversent.
- **Distillation Schwartz** ([issue #20428](https://github.com/jsboige/CoursIA/issues/20428)) :
  cette série est la veine V3 ; les veines V2 (protocoles `bootloops/skills`) et V4
  (reproductibilité NBER) restent ouvertes sur la même issue.

## Sources

- G. 't Hooft, M. Veltman, *Scalar one-loop integrals*, Nucl. Phys. B **153**,
  365 (1979).
- G. Passarino, M. Veltman, *One-loop corrections for $e^+e^-$ annihilation into
  $\mu^+\mu^-$ in the Weinberg model*, Nucl. Phys. B **160**, 151 (1979).
- L. Lewin, *Polylogarithms and Associated Functions*, North-Holland (1981) —
  fonction de Clausen $\mathrm{Cl}_2$.
- L. Adams, C. Bogner, S. Weinzierl, *The two-loop sunrise graph with arbitrary
  masses*, arXiv:1302.7004 (v1 seule) ; *The two-loop sunrise graph in two
  space-time dimensions with arbitrary masses in terms of elliptic dilogarithms*,
  arXiv:1405.5640 — la forme fermée du sunrise en intégrales elliptiques multiples
  (citée sans être reproduite aux carnets 02 et 04).
- M. D. Schwartz, *Vibe physics* (Anthropic, 2025) — le livrable de la
  collaboration qu'il raconte est arXiv:2601.02484 (2026), *Resummation of the
  C-Parameter Sudakov Shoulder Using Effective Field Theory* ; *Claude-shaped
  science* (Anthropic, 2025) — la thèse des problèmes « claude-formes », d'où sort
  le harnais BootLoops. Les trois pièces sont archivées au gisement
  `G:\Mon Drive\MyIA\IA\Bibliographie IA\Physics\`.
- *BootLoops* (MIT / CC-BY-4.0) — harnais d'intégrales certifiées et protocoles ;
  `kira` (GPL-3.0) cité sans réutilisation.