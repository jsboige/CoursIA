# Langlands — formes modulaires et ponts

Série née de l'EPIC [#17969](https://github.com/jsboige/CoursIA/issues/17969) : donner aux formes modulaires la place pédagogique réfléchie qu'elles méritent, et tisser les ponts — forme modulaire ↔ courbe elliptique, Moonshine ↔ groupe Monstre — que le programme de Langlands articule. C'est la direction que Serre décrivait comme **orthogonale** à la marée montante de Grothendieck : des voies surprenantes où il ne suffit pas de laisser monter la mer (entretien Serre–Connes, distillé dans `../Lean-15-Grothendieck-Tribute.ipynb`, section « Les limites de la marée »).

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

## Cours filmés de Borcherds : inventaire non mesurable

Au 8 novembre 2026, le proxy HTTP refuse le tunnel HTTPS vers `www.youtube.com:443` (`HTTP/1.1 403 Forbidden`, `curl: (56) CONNECT tunnel failed, response 403`) pour la [page des playlists de la chaîne](https://www.youtube.com/channel/UCIyDqfi_cbkp-RU20aBF-MQ/playlists) comme pour son [flux RSS](https://www.youtube.com/feeds/videos.xml?channel_id=UCIyDqfi_cbkp-RU20aBF-MQ) ; aucun contenu HTML de ces pages n'est reçu. Le profil officiel de [Richard E. Borcherds à Berkeley](https://math.berkeley.edu/people/faculty/richard-e-borcherds) et son [site personnel hébergé par Berkeley](https://math.berkeley.edu/~reb/) sont accessibles, mais ne donnent ni index de playlists ni métadonnées d'épisodes. Le profil indique ses domaines de recherche (algèbres de Lie et vertex, formes automorphes) ; ces sources ne permettent pas de mesurer ses cours filmés.

| Série de cours | Épisodes | Durée totale | Année | URL interrogée | Cible dans le dépôt |
|---|---:|---:|---:|---|---|
| Aucune ligne exploitable : le contenu de la page des playlists n'a pas été reçu | non mesuré | non mesurée | non mesurée | [Page des playlists interrogée](https://www.youtube.com/channel/UCIyDqfi_cbkp-RU20aBF-MQ/playlists) | Aucune cible attribuable sans titre ni contenu de playlist vérifiables |

Cette ligne décrit une limite d'accès, pas un inventaire négatif : elle ne prouve ni l'absence de cours ni leur redondance avec les carnets. Aucun titre, total d'épisodes, durée ou année n'est déduit du profil ou du nom de la chaîne. La route ci-dessus guide vers les carnets existants à partir de leurs contenus vérifiés ; elle ne prétend pas les faire correspondre à des cours dont les playlists n'ont pas pu être observées.

## Conventions

- Français d'abord, arithmétique en stdlib pur (aucune dépendance au-delà de la bibliothèque standard) ; exception : `03` recourt à `sympy` (`factorint`, `totient`) pour les factorisations admissibles `N = DM`.
- ≥ 3 exercices C.1 par notebook (convention #2161), exécution complète commitée (C.2).
- Verdict SOTA écrit au body de chaque PR (#3801).
- Le versant formel vit dans le lake compagnon [`hecke_lean/`](hecke_lean/README.md) (opérateurs de Hecke, courbe de Frey), descendu avec la sous-série (gradation #17545).

## Sources primaires

- **« Plaisir des mathématiques »** — J.-P. Serre, Institut Henri Poincaré, 2026 (YouTube `tNtoTzGltak`) — la culture du contre-exemple qui ouvre la série.
- **« À propos de la correspondance Grothendieck-Serre »** — dialogue J.-P. Serre / Alain Connes, Fondation Hugot du Collège de France, 2019 (YouTube `pOv-ygSynRI`) — l'orthogonalité Langlands/Grothendieck.
- **« The most magical subject in math (modular forms) »** — Richard Borcherds, The Mansions of Science, 2026 (YouTube `lhE4DZWFQ1U`) — la « cinquième opération arithmétique » d'Eichler [00:00], la construction du Monstre par Griess racontée par son prouveur [01:30], et la ligne de conduite de la série : *« the logical way to teach a subject and the best psychological way to teach it are usually different »* [02:25].

Transcriptions complètes (timestampées) : `G:\Mon Drive\MyIA\IA\Bibliographie IA\NumberTheory\` — hors dépôt, conformément à la convention bibliographique. À archiver pour la suite : Diamond & Shurman, *A First Course in Modular Forms*.
