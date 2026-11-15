# Langlands — formes modulaires et ponts

Série née de l'EPIC [#17969](https://github.com/jsboige/CoursIA/issues/17969) : donner aux formes modulaires la place pédagogique réfléchie qu'elles méritent, et tisser les ponts — forme modulaire ↔ courbe elliptique, Moonshine ↔ groupe Monstre — que le programme de Langlands articule. C'est la direction que Serre décrivait comme **orthogonale** à la marée montante de Grothendieck : des voies surprenantes où il ne suffit pas de laisser monter la mer (entretien Serre–Connes, distillé dans `../GROTH/GROTH-02-Tribut-Python.ipynb`, section « Les limites de la marée »).

Le geste de la série : rendre chaque identité **calculée dans une sortie** — q-expansions exactes à coefficients entiers, valeurs propres de Hecke, tables de coefficients vérifiées premier par premier — en miroir du socle formel [`hecke_lean/`](hecke_lean/README.md) qui démontre ce que les carnets calculent.

## Notebooks

| # | Notebook | Source / écho | Outil |
|---|----------|---------------|-------|
| 01 | [01-formes-modulaires-sl2z-hecke.ipynb](01-formes-modulaires-sl2z-hecke.ipynb) | *A Course in Arithmetic* ch. VII ; pont Γ₀(11) courbe 11a1 ↔ η²η₁₁² ; formule `coeffHeckeT` du lake | Python stdlib |
| 02 | [02-monstrous-moonshine-invariant-j.ipynb](02-monstrous-moonshine-invariant-j.ipynb) | Conway & Norton *Monstrous Moonshine* (1979) ; invariant $j$ et groupe Monstre ; récit cp4space/Wertheim | Python stdlib |
| 03 | [03-chaine-de-modularite-vers-fermat.ipynb](03-chaine-de-modularite-vers-fermat.ipynb) | Frey, Serre–Ribet, Wiles — la chaîne de modularité qui prouve Fermat ; miroir calculé de [`hecke_lean/Hecke/FltRoute.lean`](hecke_lean/Hecke/FltRoute.lean) | Python stdlib |
| 04 | [04-umbral-moonshine-reseaux-niemeier.ipynb](04-umbral-moonshine-reseaux-niemeier.ipynb) | Cheng, Duncan & Harvey *Umbral Moonshine* (2013) — les 24 réseaux de Niemeier et leurs systèmes de racines ADE ; le réseau de Leech, rang 24 et racines nulles ; 10 458 combinaisons ADE de rang 24 énumérées | Python stdlib |
| 05 | [05-szpiro-pasten-2026.ipynb](05-szpiro-pasten-2026.ipynb) | Pasten, *Improved Bounds for Szpiro's Conjecture* (arXiv 2609.17390, #16549) ; factorisations admissibles `N=DM`, proxy `log\|Δ\|/log rad(\|Δ\|)` des courbes `y²=x³+ax+b` ; arrivé de la série Search (carte #19253, ligne 15) | Python + sympy |
| 06 | [06-operateurs-de-hecke-natif.ipynb](06-operateurs-de-hecke-natif.ipynb) | Les opérateurs $T_p$/$U_p$ **exécutés au noyau** `lean4-wsl` — compagnon natif du lake, seule marche qui interroge in-kernel les trois PID (7, 11, 13) et la route de Fermat (`#check`/`#print axioms`, 0 erreur) ; ex-Lean-29, descendu de la racine (gradation #17545) | Lean 4 (WSL) |

## Route d'entrée

Pour suivre les liens mathématiques déjà calculés dans le dépôt, commencer par [01 — Formes modulaires et opérateurs de Hecke](01-formes-modulaires-sl2z-hecke.ipynb) : les q-expansions et le pont vers la courbe elliptique 11a1 donnent le vocabulaire nécessaire. Enchaîner avec [02 — Monstrous Moonshine](02-monstrous-moonshine-invariant-j.ipynb), qui met en regard les coefficients de l'invariant $j$ et les dimensions de représentations du groupe Monstre. Ce carnet évoque les algèbres vertex comme contexte de la preuve de Borcherds ; il ne constitue pas un cours sur les algèbres vertex.

Depuis 02, deux prolongements répondent à des questions différentes : [04 — Umbral Moonshine](04-umbral-moonshine-reseaux-niemeier.ipynb) élargit la piste Moonshine aux réseaux de Niemeier ; [03 — la chaîne de modularité vers Fermat](03-chaine-de-modularite-vers-fermat.ipynb) revient aux formes modulaires pour suivre le pont entre courbes elliptiques et théorème de Fermat. Le [compagnon Lean 06](06-operateurs-de-hecke-natif.ipynb) reprend ensuite les opérateurs de Hecke dans le noyau Lean et le lake [`hecke_lean/`](hecke_lean/README.md). Le carnet [05 — Szpiro–Pasten](05-szpiro-pasten-2026.ipynb) est une lecture complémentaire sur une conjecture voisine, non un prérequis à cette route.

## Cours filmés de Borcherds — inventaire et correspondance

L'œuvre pédagogique de Richard Borcherds — ses cours filmés, publics — est l'entrée naturelle vers cette série et ses voisines. [Sa chaîne](https://www.youtube.com/channel/UCIyDqfi_cbkp-RU20aBF-MQ) publie **21 séries, 470 épisodes, ≈196 h** (mesuré le 2026-11-13, [#23989](https://github.com/jsboige/CoursIA/issues/23989) : durées sommées épisode par épisode depuis les pages de playlist ; années dérivées de l'ancienneté affichée, granularité de l'année).

| Série (playlist) | Épisodes | Durée | Années | Carnets du dépôt |
|---|---|---|---|---|
| [Modular forms](https://www.youtube.com/playlist?list=PL8yHsr3EFj51HisRtNyzHX-Xyg6I3Wl2F) | 13 | 4 h 16 | 2021 | [01](01-formes-modulaires-sl2z-hecke.ipynb) (q-expansions, SL₂(ℤ), courbe 11a1) · [06](06-operateurs-de-hecke-natif.ipynb) (T_p au noyau) · [../Serre100/21](../Serre100/21-operateurs-hecke-formes-modulaires.ipynb) |
| [Elliptic functions](https://www.youtube.com/playlist?list=PL8yHsr3EFj50t6hrPaJ0GruNrN-xPcFTI) | 4 | 2 h 05 | 2024 | [01](01-formes-modulaires-sl2z-hecke.ipynb) (η-produits, courbe 11a1) · [02](02-monstrous-moonshine-invariant-j.ipynb) (invariant $j$) · écho périodes : [../Physique/Integrales/04](../../../Physique/Integrales/Integrales-04-Sunrise-Courbe-Elliptique-Python.ipynb) |
| [Introduction to number theory (Berkeley Math 115)](https://www.youtube.com/playlist?list=PL8yHsr3EFj53L8sMbzIhhXSAOpuZ1Fov8) | 53 | 26 h 12 | 2022 | [../Serre100/](../Serre100/README.md) (corps finis, valeurs zêta, bulles de Minkowski, Pell, partitions) · [03](03-chaine-de-modularite-vers-fermat.ipynb) |
| [Theory of numbers](https://www.youtube.com/playlist?list=PL8yHsr3EFj52Qf7lc3HHvHRdIysxEcj1H) | 20 | 9 h 24 | 2021 | [../Serre100/29](../Serre100/29-reciprocite-quadratique-legendre.ipynb) · [11](../Serre100/11-corps-quadratiques-reciprocite-quadratique.ipynb)–[14](../Serre100/14-formes-quadratiques-composition-gauss.ipynb) · [16](../Serre100/16-fonctions-l-dirichlet-progression-premiers.ipynb) |
| [Galois theory](https://www.youtube.com/playlist?list=PL8yHsr3EFj53Zxu3iRGMYL_89GDMvdkgt) | 25 | 9 h 42 | 2021 | [../GALOIS/01](../GALOIS/GALOIS-01-Probleme-Inverse-M23-Python.ipynb) (problème inverse M23) · [../Serre100/25](../Serre100/25-groupe-galois-calcule.ipynb) · [17](../Serre100/17-chebotarev-frobenius-types-cycles.ipynb) · [18](../Serre100/18-discriminant-ramification-critere-dedekind.ipynb) |
| [Group theory](https://www.youtube.com/playlist?list=PL8yHsr3EFj51pjBvvCPipgAT3SYpIiIsJ) | 32 | 11 h 48 | 2020 | [../Serre100/20](../Serre100/20-sylow-p-sous-groupes.ipynb) · [20b](../Serre100/20b-groupes-abeliens-finis.ipynb) · [02](02-monstrous-moonshine-invariant-j.ipynb) (groupe Monstre) |
| [Representation theory](https://www.youtube.com/playlist?list=PL8yHsr3EFj51AM_VmB0VygPIzcUCH_jUG) | 10 | 4 h 00 | 2020-2024 | [../Serre100/05](../Serre100/05-table-de-caracteres.ipynb) (table de caractères) · [02](02-monstrous-moonshine-invariant-j.ipynb) (dimensions de représentations du Monstre) |
| [Lie groups](https://www.youtube.com/playlist?list=PL8yHsr3EFj53RWBkiHKoOsTw-dGHAoJ-h) | 12 | 5 h 36 | 2021 | [01](01-formes-modulaires-sl2z-hecke.ipynb) (SL₂(ℤ) sur le demi-plan) · [../Serre100/19](../Serre100/19-arbres-ping-pong-sl2.ipynb) |
| [Algebraic topology](https://www.youtube.com/playlist?list=PL8yHsr3EFj52yxQGxQoxwOtjIEtxE2BWx) | 4 | 1 h 48 | 2021 | [../KNOTS/](../KNOTS/README.md) (invariants 02, géométrie hyperbolique 04, tresses 05) |
| [Complex analysis](https://www.youtube.com/playlist?list=PL8yHsr3EFj537_iYA5QrvwhvMlpkJ1yGN) | 21 | 8 h 48 | 2021-2024 | aucune série dédiée ; le demi-plan supérieur est calculé dans [01](01-formes-modulaires-sl2z-hecke.ipynb), écho zéros de polynômes : [../ANALYSE/01](../ANALYSE/ANALYSE-01-Sendov-Lean-Python.ipynb) |
| [Algebraic geometry I: Varieties](https://www.youtube.com/playlist?list=PL8yHsr3EFj53j51FG6wCbQKjBgpjKa5PX) | 51 | 17 h 24 | 2020 | [../Lean-15](../Lean-15-Grothendieck-Tribute.ipynb) · [15b](../Lean-15b-Lean-Grothendieck.ipynb) · [15c](../Lean-15c-Lean-Grothendieck-Companion.ipynb) (digestions EGA/SGA) |
| [Algebraic geometry II: Schemes](https://www.youtube.com/playlist?list=PL8yHsr3EFj50Un2NpfPySgXctRQK7CLG-) | 48 | 20 h 42 | 2020 | [../GROTH/](../GROTH/README.md) (carte #17545) · lake `grothendieck_lean` (catégories, sites, topologies) |
| [Commutative algebra](https://www.youtube.com/playlist?list=PL8yHsr3EFj53rSexSz7vsYt-3rpHPR3HB) | 76 | 30 h 12 | 2020-2021 | [../GROTH/05](../GROTH/GROTH-05-MvPowerSeries-Lean.ipynb) (anneau des séries formelles exécuté) ; aucune série dédiée |
| [Rings and modules](https://www.youtube.com/playlist?list=PL8yHsr3EFj52XDLrmvrFDgwcf6XOm2TEE) | 22 | 10 h 24 | 2021 | aucune cible |
| [Introduction to homological algebra](https://www.youtube.com/playlist?list=PL8yHsr3EFj53tlhAM-Zf0pRKNB541ZTi2) | 6 | 2 h 42 | 2020 | [../Serre100/03](../Serre100/03-cohomologie-cech-espaces-finis.ipynb) (Čech) · [20c](../Serre100/20c-cohomologie-groupe-calculee.ipynb) · lake `grothendieck_lean` |
| [Categories for the idle mathematician](https://www.youtube.com/playlist?list=PL8yHsr3EFj51F9XZ_Ka4bLnQoxTdMx0AL) | 7 | 2 h 36 | 2021 | [../GROTH/01](../GROTH/GROTH-01-Categories-Mathlib-Lean.ipynb) (catégories, foncteurs, adjonctions natifs) · [../Serre100/04](../Serre100/04-lemme-yoneda-categories-finies.ipynb) (Yoneda) |
| [Algebraic geometry: extra topics](https://www.youtube.com/playlist?list=PL8yHsr3EFj53Rwr6ly1oUasJXR2Qerwgj) | 24 | 10 h 42 | 2020-2021 | aucune cible |
| [Zermelo Fraenkel axioms](https://www.youtube.com/playlist?list=PL8yHsr3EFj52EKVgPi-p50fRP2_SbG2oi) | 8 | 2 h 24 | 2022 | aucune cible (voisin : [../Lean-03b](../Lean-03b-Formalized-Formal-Logic-Lean-Python.ipynb), logique formelle — pas ZF) |
| [Vinberg lecture](https://www.youtube.com/playlist?list=PL8yHsr3EFj50MVfqGTj4VF3CBS-bJeal3) | 4 | 3 h 30 | 2024 | aucune cible |
| [Math talks](https://www.youtube.com/playlist?list=PL8yHsr3EFj53y6T5Qc0uq_VTJ_gXyIBMY) | 23 | 10 h 30 | 2020-2024 | aucune cible (conférences, pas un cours) |
| [History of science](https://www.youtube.com/playlist?list=PL8yHsr3EFj52w1KAe998NwDus_hva63fc) | 7 | 1 h 24 | 2020 | aucune cible |

**Route depuis les cours.** Un lecteur qui sort du cours *Modular forms* entre dans la série par [01](01-formes-modulaires-sl2z-hecke.ipynb) puis [06](06-operateurs-de-hecke-natif.ipynb) — le cours donne les définitions, les carnets les exécutent. Les cours de théorie des nombres mènent à [../Serre100/](../Serre100/README.md), la géométrie algébrique et les schémas à l'îlot [../GROTH/](../GROTH/README.md) dont la carte nomme explicitement les prérequis jamais préparés. Deux trous restent déclarés : les **algèbres vertex** (aucun carnet — cf. la route d'entrée ci-dessus) et l'**analyse complexe** (aucune série dédiée).

## Conventions

- Français d'abord, arithmétique en stdlib pur (aucune dépendance au-delà de la bibliothèque standard) ; exception : `05` recourt à `sympy` (`factorint`, `totient`) pour les factorisations admissibles `N = DM`.
- ≥ 3 exercices C.1 par notebook (convention #2161), exécution complète commitée (C.2).
- Verdict SOTA écrit au body de chaque PR (#3801).
- Le versant formel vit dans le lake compagnon [`hecke_lean/`](hecke_lean/README.md) (opérateurs de Hecke, courbe de Frey), descendu avec la sous-série (gradation #17545).

## Sources primaires

- **« Plaisir des mathématiques »** — J.-P. Serre, Institut Henri Poincaré, 2026 (YouTube `tNtoTzGltak`) — la culture du contre-exemple qui ouvre la série.
- **« À propos de la correspondance Grothendieck-Serre »** — dialogue J.-P. Serre / Alain Connes, Fondation Hugot du Collège de France, 2019 (YouTube `pOv-ygSynRI`) — l'orthogonalité Langlands/Grothendieck.
- **« The most magical subject in math (modular forms) »** — Richard Borcherds, The Mansions of Science, 2026 (YouTube `lhE4DZWFQ1U`) — la « cinquième opération arithmétique » d'Eichler [00:00], la construction du Monstre par Griess racontée par son prouveur [01:30], et la ligne de conduite de la série : *« the logical way to teach a subject and the best psychological way to teach it are usually different »* [02:25].

Transcriptions complètes (timestampées) : `G:\Mon Drive\MyIA\IA\Bibliographie IA\NumberTheory\` — hors dépôt, conformément à la convention bibliographique. À archiver pour la suite : Diamond & Shurman, *A First Course in Modular Forms*.
