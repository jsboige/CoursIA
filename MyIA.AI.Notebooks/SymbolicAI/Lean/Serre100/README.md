# Serre 100 — Distillations

Série née du centenaire de Jean-Pierre Serre (conférence [Serre 100](https://serre100.sciencesconf.org/resource/page/id/1), 15-16 septembre 2026) — EPIC [#16334](https://github.com/jsboige/CoursIA/issues/16334).

Le geste « distillation » : prendre un énoncé ou une construction centrale de Serre et le rendre **calculé dans une sortie** — l'énoncé devient une expérience numérique vérifiable, démontrable en Lean quand Mathlib le permet, et exerçable (≥ 3 exercices par notebook).

## Notebooks

| # | Notebook | Source / écho | Outil |
|---|----------|---------------|-------|
| 01 | [01-corps-finis-borne-hasse.ipynb](01-corps-finis-borne-hasse.ipynb) | *A Course in Arithmetic* ch. 1-2 (et en fond, la borne de Hasse-Weil que Serre a tant maniée) | Python stdlib + matplotlib |
| 02 | [02-valeurs-zeta-multiples-finies.ipynb](02-valeurs-zeta-multiples-finies.ipynb) | Adèles et valeurs zêta multiples finies | Python stdlib |
| 03 | [03-cohomologie-cech-espaces-finis.ipynb](03-cohomologie-cech-espaces-finis.ipynb) | Pont Serre–Grothendieck : cohomologie de Čech calculée sur espaces finis | Python stdlib |
| 04 | [04-lemme-yoneda-categories-finies.ipynb](04-lemme-yoneda-categories-finies.ipynb) | Lemme de Yoneda calculé sur catégories finies | Python stdlib |
| 05 | [05-table-de-caracteres.ipynb](05-table-de-caracteres.ipynb) | Tables de caractères — squelette combinatoire des groupes finis | Python stdlib |
| 06 | [06-bulles-minkowski.ipynb](06-bulles-minkowski.ipynb) | Les bulles diaboliques de Minkowski — géométrie des nombres | Python stdlib |
| 07 | [07-zeros-fonctions-l-gaps-gue.ipynb](07-zeros-fonctions-l-gaps-gue.ipynb) | Zéros de fonctions L, gaps et statistique GUE — l'autre versant de l'œuvre (contre-exemple de Terjanian cité) | Python stdlib |
| 08 | [08-serre-dans-mathlib-Lean.ipynb](08-serre-dans-mathlib-Lean.ipynb) | Tour des cinq « Serre » de Mathlib — le versant preuves du diptyque (index : grain 9 #16374) | Lean 4 (kernel `lean4-wsl`, lake [`serre100_lean/`](serre100_lean/)) |
| 09 | [09-congruences-tau-lacunarite-delta.ipynb](09-congruences-tau-lacunarite-delta.ipynb) | τ de Ramanujan — congruence mod 691, borne de Deligne, lacunarité des puissances de η (Euler, Jacobi, Serre) | Python stdlib + matplotlib |
| 10 | [10-empilements-borne-lp-cohn-elkies.ipynb](10-empilements-borne-lp-cohn-elkies.ipynb) | Bornes d'empilements de sphères par LP (Cohn–Elkies, lignée Odlyzko–Serre) — Poisson mesuré, LP naïf autopsié, LP certifié par intervalles | numpy + scipy (HiGHS) + matplotlib |
| 11 | [11-corps-quadratiques-reciprocite-quadratique.ipynb](11-corps-quadratiques-reciprocite-quadratique.ipynb) | Corps quadratiques imaginaires — réciprocité quadratique, Fermat des deux carrés / deux triangulaires, densités de Chebotarev via symbole de Kronecker, conjecture de Stark-Heegner (neuf nombres) | Python stdlib |
| 12 | [12-formes-quadratiques-binaires-nombre-classes.ipynb](12-formes-quadratiques-binaires-nombre-classes.ipynb) | Formes quadratiques binaires $ax^2 + bxy + cy^2$, conditions de réduction, bijection classes d'idéaux $\\leftrightarrow$ formes réduites, formule analytique $h(D) = \\frac{w\\sqrt{\|D\|}}{2\\pi} L(1, \\chi_D)$, théorème de Stark-Heegner ($h = 1$ pour les 9 discriminants fondamentaux) | Python stdlib |
| 13 | [13-jacobi-kronecker-reciprocite-II.ipynb](13-jacobi-kronecker-reciprocite-II.ipynb) | Loi de réciprocité quadratique II — symbole de Jacobi `(d/n)` (n impair) et extension Kronecker `(d/n)` ; algorithme d'Euler-Legendre O(log n) ; conducteur des corps quadratiques de Heegner | Python stdlib (math.isqrt) |
| 14 | [14-formes-quadratiques-composition-gauss.ipynb](14-formes-quadratiques-composition-gauss.ipynb) | Composition des formes quadratiques binaires (Gauss) — réduction, énumération des formes réduites, calcul de h(D), vérification du théorème de Stark–Heegner sur les 9 corps de Heegner | Python stdlib (math.isqrt) |
| 15 | [15-quatre-carres-lagrange.ipynb](15-quatre-carres-lagrange.ipynb) | Théorème de Lagrange — tout entier est somme de quatre carrés ; algorithme de Lagrange/Jacobi, formule de Jacobi pour r₄(n), identité de Brahmagupta–Fibonacci (quaternions) | Python stdlib (math.isqrt) |
| 16 | [16-fonctions-l-dirichlet-progression-premiers.ipynb](16-fonctions-l-dirichlet-progression-premiers.ipynb) | *Cours d'arithmétique* ch. VI — caractères de Dirichlet énumérés, séries L et produits eulériens, sommes de Gauss τ(χ) (réduction aux primitifs), non-annulation L(1,χ) ≠ 0 par formules fermées (π/4, 2log(1+√2)/√8, 2log φ/√5), biais de Tchebychev mesuré | Python stdlib (cmath) + matplotlib |
| 17 | [17-chebotarev-frobenius-types-cycles.ipynb](17-chebotarev-frobenius-types-cycles.ipynb) | Théorème de densité de Chebotarev (Serre, « Chebotarev and his density theorem », 1998) — correspondance de Dedekind (type de factorisation ↔ cycles du Frobenius), x³-2 sur S₃ : densités 1/6, 1/2, 1/3 comptées à 10⁶, cas quadratique (réciprocité retrouvée) et cyclotomique Φ₅/Φ₇ (Chebotarev = Dirichlet) | Python stdlib + matplotlib |
| 18 | [18-discriminant-ramification-critere-dedekind.ipynb](18-discriminant-ramification-critere-dedekind.ipynb) | *Corps locaux* ch. III — critère de Dedekind : disc(x³−2) = −108 par résultant de Sylvester/Bareiss, ramifiés ↔ diviseurs du discriminant, décompositions à multiplicités (e = 3 en 2 et 3), idéaux (2) = (α)³ et (3) = (α+1)³, contraste disc(f) ≠ disc(K) sur x²−5 (indice 2), finitude de la ramification | Python stdlib + matplotlib |
| 19 | [19-arbres-ping-pong-sl2.ipynb](19-arbres-ping-pong-sl2.ipynb) | *Arbres, amalgames et SL₂* (1977) — signature $SL_2(\mathbb{Z}) \cong C_4 *_{C_2} C_6$ mesurée, transitivité constructive sur $P^1(\mathbb{Q})$ par descente de Stern-Brocot (1958/1958 rationnels), arbre de Farey mesuré arbre (birégulier (2,3), acyclique à quatre rayons), théorème de Sanov par ping-pong exact (liberté : 39364/39364 mots réduits), contrepoint de tresses $TLT = LTL$ | Python stdlib |
| 20 | [20-sylow-p-sous-groupes.ipynb](20-sylow-p-sous-groupes.ipynb) | Théorèmes de Sylow calculés (*Cours d'arithmétique* ch. I) — groupes de permutations reconstruits par clôture, treillis des sous-groupes énuméré, $n_p$ comptés et confrontés à $n_p \equiv 1 \pmod p$ et $n_p \mid \|G\|/p^a$, conjugaison et indice du normalisateur mesurés par deux chemins indépendants, non-simplicité de l'ordre $30$ par comptage d'éléments ($24 + 20 = 44 > 30$) | Python stdlib + matplotlib |
| 20c | [20c-cohomologie-groupe-calculee.ipynb](20c-cohomologie-groupe-calculee.ipynb) | *Cohomologie des groupes discrets* (Serre, 1958) — H¹ et H² calculés par énumération exhaustive sur C₂, C₃, C₄, V₄ et S₃ ; contrôle négatif (H²(C₃, Z/2) trivial, H²(V₄, Z/2) d'ordre 8) ; extensions centrales de C₂ classées par les 2-cocycles (C₄ ou C₂ × C₂, distingués par la mesure de l'ordre des éléments) ; H¹ confronté au nombre de sous-groupes d'indice 2 et à la suite universelle de coefficients | Python stdlib + matplotlib |
| 21 | [21-operateurs-hecke-formes-modulaires.ipynb](21-operateurs-hecke-formes-modulaires.ipynb) | Opérateurs de Hecke calculés en arithmétique exacte — E₄/E₆ par séries de diviseurs, Δ par deux routes indépendantes `(E₄³−E₆²)/1728` et `q∏(1−qⁿ)²⁴`, `T_p(E_k) = (1+p^{k−1})E_k` et `T_p(Δ) = τ(p)Δ`, algèbre de Hecke sur S₂₄ en matrices entières (`[T_p,T_q]=0`, `T_pq = T_pT_q`, `T_{p²} = T_p² − p²³`), borne de Deligne mesurée sur 139 premiers, angles de Sato–Tate confrontés à l'uniforme | Python stdlib + matplotlib |
| 22 | [22-vecteurs-witt-frobenius.ipynb](22-vecteurs-witt-frobenius.ipynb) | Vecteurs de Witt (Serre, *Corps locaux* ch. II ; ouverture d'Illusie vers le complexe de de Rham–Witt) — échec du relèvement naïf mesuré sur deux contre-exemples et un contrôle positif, composantes fantômes, inversion triangulaire à division **exacte et vérifiée**, axiomes testés exhaustivement sur $W_2(\\mathbb{F}_3)$, $W_3(\\mathbb{F}_2)$, $W_4(\\mathbb{F}_2)$, Frobenius / Verschiebung / élévation de Teichmüller, $W_n(\\mathbb{F}_p) \\cong \\mathbb{Z}/p^n$ établi par contrôle croisé de deux constructions indépendantes | Python stdlib |
| 25 | [25-groupe-galois-calcule.ipynb](25-groupe-galois-calcule.ipynb) | Le groupe de Galois calculé (*Topics in Galois Theory*, leçon 1) — types de décomposition (Dedekind, prolonge 17), discriminant exact (Sylvester/Bareiss) et $G \subseteq A_n$, étau de sous-groupes transitifs : neuf groupes identifiés ($C_3$ à $S_5$), leçon mesurée de la transitivité ($V_4$ contre un pseudo-$C_2$), résolvante cubique concordante, série dérivée calculée (Abel-Ruffini exécuté, $A_5$ parfait), Cardano vérifié contre Durand-Kerner, pont Lean-22/$M_{23}$ | Python stdlib + matplotlib |

## Conventions

- Français d'abord, arithmétique en stdlib pur (aucune dépendance au-delà de matplotlib pour les figures) ; le versant **preuves** Lean (08) vit dans le lake compagnon [`serre100_lean/`](serre100_lean/), mêmes pins Mathlib que `hecke_lean`. Exception assumée : le carnet 10 invoque `scipy.optimize.linprog` — le vrai solveur LP est l'outil du sujet (verdict SOTA-OK).
- ≥ 3 exercices C.1 par notebook (convention #2161), exécution complète commitée (C.2).
- Verdict SOTA écrit au body de chaque PR (#3801).

## Voie décorélée

L'EPIC #16334 comporte aussi une voie décorélée du programme de l'anniversaire (pont Serre–Grothendieck avec le lake `SymbolicAI/Lean/grothendieck_lean`) : cohomologie de Čech calculée, Yoneda calculé, `SerreMap.lean`.


## Sources primaires

Deux témoignages filmés de J.-P. Serre, transcrits intégralement (Whisper large-v3-turbo, transcription automatique — noms propres corrigés dans les citations : Artin, Weil, Bombieri, Cartier), alimentent les carnets 03, 04 et 07 :

- **« Plaisir des mathématiques »** — J.-P. Serre, Institut Henri Poincaré, 2026 (YouTube `tNtoTzGltak`) — le contre-exemple de Terjanian à la conjecture d'Artin (11:05), cité dans 07.
- **« À propos de la correspondance Grothendieck-Serre »** — dialogue J.-P. Serre / Alain Connes, Fondation Hugot du Collège de France, 2019 (YouTube `pOv-ygSynRI`) — Tohoku et les axiomes (07:05), la montée H0-H1-H2 (12:36), le conducteur (17:57), citées dans 03, 04 et 07.

Transcriptions complètes (timestampées) : `G:\Mon Drive\MyIA\IA\Bibliographie IA\NumberTheory\` — hors dépôt, conformément à la convention bibliographique.
