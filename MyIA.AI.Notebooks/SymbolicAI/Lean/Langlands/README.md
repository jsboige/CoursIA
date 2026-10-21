# Langlands — formes modulaires et ponts

Série née de l'EPIC [#17969](https://github.com/jsboige/CoursIA/issues/17969) : donner aux formes modulaires la place pédagogique réfléchie qu'elles méritent, et tisser les ponts — forme modulaire ↔ courbe elliptique, Moonshine ↔ groupe Monstre — que le programme de Langlands articule. C'est la direction que Serre décrivait comme **orthogonale** à la marée montante de Grothendieck : des voies surprenantes où il ne suffit pas de laisser monter la mer (entretien Serre–Connes, distillé dans `../Lean-15-Grothendieck-Tribute.ipynb`, section « Les limites de la marée »).

Le geste de la série : rendre chaque identité **calculée dans une sortie** — q-expansions exactes à coefficients entiers, valeurs propres de Hecke, tables de coefficients vérifiées premier par premier — en miroir du socle formel [`hecke_lean/`](../hecke_lean/README.md) qui démontre ce que les carnets calculent.

## Notebooks

| # | Notebook | Source / écho | Outil |
|---|----------|---------------|-------|
| 01 | [01-formes-modulaires-sl2z-hecke.ipynb](01-formes-modulaires-sl2z-hecke.ipynb) | *A Course in Arithmetic* ch. VII ; pont Γ₀(11) courbe 11a1 ↔ η²η₁₁² ; formule `coeffHeckeT` du lake | Python stdlib |
| 02 | [02-monstrous-moonshine-invariant-j.ipynb](02-monstrous-moonshine-invariant-j.ipynb) | Conway & Norton *Monstrous Moonshine* (1979) ; invariant $j$ et groupe Monstre ; récit cp4space/Wertheim | Python stdlib |
| 03 | [03-szpiro-pasten-2026.ipynb](03-szpiro-pasten-2026.ipynb) | Pasten, *Improved Bounds for Szpiro's Conjecture* (arXiv 2609.17390, #16549) ; factorisations admissibles `N=DM`, proxy `log\|Δ\|/log rad(\|Δ\|)` des courbes `y²=x³+ax+b` ; arrivé de la série Search (carte #19253, ligne 15) | Python + sympy |
| 04 | [04-umbral-moonshine-reseaux-niemeier.ipynb](04-umbral-moonshine-reseaux-niemeier.ipynb) | Cheng, Duncan & Harvey *Umbral Moonshine* (2013) — les 24 réseaux de Niemeier et leurs systèmes de racines ADE ; le réseau de Leech, rang 24 et racines nulles ; 10 458 combinaisons ADE de rang 24 énumérées | Python stdlib |

## Conventions

- Français d'abord, arithmétique en stdlib pur (aucune dépendance au-delà de la bibliothèque standard) ; exception : `03` recourt à `sympy` (`factorint`, `totient`) pour les factorisations admissibles `N = DM`.
- ≥ 3 exercices C.1 par notebook (convention #2161), exécution complète commitée (C.2).
- Verdict SOTA écrit au body de chaque PR (#3801).
- Le versant formel vit dans le lake compagnon [`hecke_lean/`](../hecke_lean/README.md) (opérateurs de Hecke, courbe de Frey).

## Sources primaires

- **« Plaisir des mathématiques »** — J.-P. Serre, Institut Henri Poincaré, 2026 (YouTube `tNtoTzGltak`) — la culture du contre-exemple qui ouvre la série.
- **« À propos de la correspondance Grothendieck-Serre »** — dialogue J.-P. Serre / Alain Connes, Fondation Hugot du Collège de France, 2019 (YouTube `pOv-ygSynRI`) — l'orthogonalité Langlands/Grothendieck.
- **« The most magical subject in math (modular forms) »** — Richard Borcherds, The Mansions of Science, 2026 (YouTube `lhE4DZWFQ1U`) — la « cinquième opération arithmétique » d'Eichler [00:00], la construction du Monstre par Griess racontée par son prouveur [01:30], et la ligne de conduite de la série : *« the logical way to teach a subject and the best psychological way to teach it are usually different »* [02:25].

Transcriptions complètes (timestampées) : `G:\Mon Drive\MyIA\IA\Bibliographie IA\NumberTheory\` — hors dépôt, conformément à la convention bibliographique. À archiver pour la suite : Diamond & Shurman, *A First Course in Modular Forms*.
