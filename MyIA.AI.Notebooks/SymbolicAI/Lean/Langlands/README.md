# Langlands — formes modulaires et ponts

Série née de l'EPIC [#17969](https://github.com/jsboige/CoursIA/issues/17969) : donner aux formes modulaires la place pédagogique réfléchie qu'elles méritent, et tisser les ponts — forme modulaire ↔ courbe elliptique, Moonshine ↔ groupe Monstre — que le programme de Langlands articule. C'est la direction que Serre décrivait comme **orthogonale** à la marée montante de Grothendieck : des voies surprenantes où il ne suffit pas de laisser monter la mer (entretien Serre–Connes, distillé dans `../Lean-15-Grothendieck-Tribute.ipynb`, section « Les limites de la marée »).

Le geste de la série : rendre chaque identité **calculée dans une sortie** — q-expansions exactes à coefficients entiers, valeurs propres de Hecke, tables de coefficients vérifiées premier par premier — en miroir du socle formel [`hecke_lean/`](../hecke_lean/README.md) qui démontre ce que les carnets calculent.

## Notebooks

| # | Notebook | Source / écho | Outil |
|---|----------|---------------|-------|
| 01 | [01-formes-modulaires-sl2z-hecke.ipynb](01-formes-modulaires-sl2z-hecke.ipynb) | *A Course in Arithmetic* ch. VII ; pont Γ₀(11) courbe 11a1 ↔ η²η₁₁² ; formule `coeffHeckeT` du lake | Python stdlib |

## Conventions

- Français d'abord, arithmétique en stdlib pur (aucune dépendance au-delà de la bibliothèque standard).
- ≥ 3 exercices C.1 par notebook (convention #2161), exécution complète commitée (C.2).
- Verdict SOTA écrit au body de chaque PR (#3801).
- Le versant formel vit dans le lake compagnon [`hecke_lean/`](../hecke_lean/README.md) (opérateurs de Hecke, courbe de Frey).

## Sources primaires

- **« Plaisir des mathématiques »** — J.-P. Serre, Institut Henri Poincaré, 2026 (YouTube `tNtoTzGltak`) — la culture du contre-exemple qui ouvre la série.
- **« À propos de la correspondance Grothendieck-Serre »** — dialogue J.-P. Serre / Alain Connes, Fondation Hugot du Collège de France, 2019 (YouTube `pOv-ygSynRI`) — l'orthogonalité Langlands/Grothendieck.

Transcriptions complètes (timestampées) : `G:\Mon Drive\MyIA\IA\Bibliographie IA\NumberTheory\` — hors dépôt, conformément à la convention bibliographique. À archiver pour la suite : Diamond & Shurman, *A First Course in Modular Forms*.
