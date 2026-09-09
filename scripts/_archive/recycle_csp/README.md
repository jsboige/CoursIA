# Scripts de recyclage CSP archivés

Ce dossier conserve les sept scripts one-shot qui ont transformé les notebooks
`CSP-3-Advanced` à `CSP-9-Distributed` pour l’issue #463. Leur mission a été
livrée par les PR #469 à #475, puis les scripts ont été archivés par la PR
#9575 le 6 août 2026.

Ils ne constituent plus des outils actifs : aucun autre script ne les importe,
et leurs notebooks cibles existent sur `main`. Ils restent ici pour préserver
la provenance exacte des transformations historiques.

## Registre de disposition

| Script | Verdict | Superseded by | Verdict recorded in |
|---|---|---|---|
| `recycle_csp3.py` | OBSOLETE — transformation livrée, puis état des labels remanié | `MyIA.AI.Notebooks/Search/Part2-CSP/CSP-3-Advanced.ipynb` : livraison PR #469, remaniement issue #464 (commit `171e7862a`), restauration des labels d’exercice par le TP étudiant PR #601 | PR #469 ; issue #464 / commit `171e7862a` ; PR #601 ; archivage PR #9575 |
| `recycle_csp4.py` | OBSOLETE — mission de migration remplie | `MyIA.AI.Notebooks/Search/Part2-CSP/CSP-4-Scheduling.ipynb` (PR #470) | PR #470 ; archivage #9575 |
| `recycle_csp5.py` | OBSOLETE — mission de migration remplie | `MyIA.AI.Notebooks/Search/Part2-CSP/CSP-5-Optimization.ipynb` (PR #471) | PR #471 ; archivage #9575 |
| `recycle_csp6.py` | OBSOLETE — transformation livrée et raffinée | `MyIA.AI.Notebooks/Search/Part2-CSP/CSP-6-Hybridization.ipynb` : livraison PR #472, remaniement issue #464 (commit `171e7862a`), correction de label PR #9171 | PR #472 ; issue #464 / commit `171e7862a` ; PR #9171 ; archivage PR #9575 |
| `recycle_csp7.py` | OBSOLETE — mission de migration remplie | `MyIA.AI.Notebooks/Search/Part2-CSP/CSP-7-Soft.ipynb` (PR #473) | PR #473 ; archivage #9575 |
| `recycle_csp8.py` | OBSOLETE — mission de migration remplie | `MyIA.AI.Notebooks/Search/Part2-CSP/CSP-8-Temporal.ipynb` (PR #474) | PR #474 ; archivage #9575 |
| `recycle_csp9.py` | OBSOLETE — mission de migration remplie | `MyIA.AI.Notebooks/Search/Part2-CSP/CSP-9-Distributed.ipynb` (PR #475) | PR #475 ; archivage #9575 |

## Analyse et préservation

Chaque fichier possède une seule entrée top-level : le corps de module pour
CSP-3 et CSP-4, puis `main()` pour CSP-5 à CSP-9. Les en-têtes de disposition
dans les scripts rendent cette entrée explicite et renvoient vers le notebook
qui porte désormais le contenu.

La préservation a été vérifiée par l’historique Git : chaque PR #469 à #475 a
livré le script et la transformation de son notebook dans le même commit. Les
cas qui ont évolué ensuite sont documentés sans les masquer :

- CSP-3 suit la chaîne PR #469 → issue #464 / commit `171e7862a` → PR #601 ;
  le contenu CSP demeure dans le notebook courant, mais les labels posés par le
  one-shot ne sont plus son état final.
- CSP-6 suit la chaîne PR #472 → issue #464 / commit `171e7862a` → PR #9171.
- CSP-4, CSP-5, CSP-7, CSP-8 et CSP-9 conservent les exemples et variantes
  livrés par leurs PR respectives.

## Pourquoi conserver ces fichiers

La suppression ferait perdre le source exact des transformations de 2026.
L’archive locale au domaine garde cette provenance consultable sans présenter
les scripts comme des outils réutilisables. Toute nouvelle évolution des
notebooks doit modifier directement les notebooks ou un outil actif de
`scripts/notebook_tools/`, jamais rejouer ces one-shots indexés par cellules.

## Références

- Issue source : #463
- Archivage initial : PR #9575
- Standard appliqué : `docs/reference/_archive-convention.md`
- Suivi de standardisation : #13749
