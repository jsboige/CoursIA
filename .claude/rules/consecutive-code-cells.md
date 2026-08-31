# Cellules code consécutives — markdown intermédiaire ou fusion (advisory)

S'applique à **tous les agents** qui éditent des notebooks pédagogiques (`MyIA.AI.Notebooks/**/*.ipynb`). Source : mandat user 2026-08-24, issue **#12797**.

## Règle

Deux cellules code qui **se suivent** (aucune cellule markdown entre elles) sont **quasiment toujours** soit l'opportunité de proposer une cellule de markdown intermédiaire (interprétation / transition), soit un motif de **fusion** (les deux cellules n'ont pas lieu d'être séparées).

| Résolution | Quand |
|------------|-------|
| **Cellule markdown intermédiaire** | Les deux cellules sont des étapes logiquement distinctes (ex. pipeline ML : data → features → grid search). Ajouter une cellule de transition/interprétation. |
| **Fusion** | Les deux cellules sont étroitement couplées (imports, `x = load()` + `x.head()`, préparation en 2 fragments). Fusionner en une cellule. |

## Détection

`scripts/notebook_tools/detect_consecutive_code_cells.py` mesure les runs de **≥2** cellules code consécutives. ADVISORY (sortie 0 toujours) ; le signal est le label `consecutive-code-cells` posé par `.github/workflows/consecutive-code-cells-advisory.yml` sur les PRs touchant un notebook concerné. La classification corpus/kind est consommée depuis `count_exercises.py` (out-of-corpus + setup exempts) — jamais réimplémentée.

## Réflexe

Quand une PR touche un notebook portant `consecutive-code-cells`, l'agent d'enrichissement (enricher/iterative-builder) ou l'auteur **choisit** l'une des deux résolutions. Ne jamais laisser une série de ≥3 cellules code sans prose ni fusion (mesure : 132 notebooks à run ≥3, 37 à ≥4 — de vrais gaps). Donner la priorité aux runs les plus longs.

## Interdits

- **Ne pas re-balayer ni réimplémenter** la classification corpus/kind : l'utiliser via `detect_consecutive_code_cells.py`.
- **Ne pas confondre** avec `check_interp_positioning.py` (placement d'une interp vs la section à laquelle elle appartient) ni avec `pedagogy_density.py` (densité chars/cellule) — trois règles complémentaires, trois rationales.
- **Ne pas statuer** sur un notebook que l'outil n'a pas pu lire (`unmeasured`) : le noter, ne pas prétendre la conformité (#8819).

## Voir aussi

- [notebook-conventions.md](notebook-conventions.md) — C.1 stubs, C.2 outputs
- [cell-interpretation-ordering.md](cell-interpretation-ordering.md) — placement des cellules d'interprétation
- [docs/reference/subagents-reference.md](../../docs/reference/subagents-reference.md) — agents d'enrichissement
