# _archive/c8257-lean18-enrichment — scripts archivés

Helpers one-shot utilisés pour l'enrichissement initial du notebook `Lean-18-Search-AStar-Optimality.ipynb` durant le cycle c.8257. Le notebook a depuis été :

1. **déplacé** sous `MyIA.AI.Notebooks/Search/Part1-Foundations/` (PR #13685, "descent" Lean-18 → Search),
2. **renommé** `Search-03e-AStar-Optimality.ipynb` (PR #14250).

Ces deux helpers référencent l'ancien chemin `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-18-Search-AStar-Optimality.ipynb` (cf. `NB_PATH = Path(...)` en tête de chaque script), qui **n'existe plus** sur main. Une fois l'enrichissement terminé (c.8257), ils sont devenus **historiques** mais n'avaient pas été archivés — Tell c.853-L2 ★★ comble ce gap.

## Contenu

- `enrich_lean18.py` — script d'enrichissement (squelette markdown pédagogique ajouté au notebook)
- `verify_lean18.py` — script de vérification (lecture du notebook enrichi, contrôle des invariants)

Aucun des deux n'est **plus utilisé** sur main : 0 référence dans le repo (`grep -rln "enrich_lean18\|verify_lean18"` retourne vide).

## Pourquoi archivés plutôt que supprimés

- Préservation de la preuve de travail (cf. CLAUDE.md global « Consolider != Archiver »).
- Restauration possible si le contenu revient dans un autre cycle.
- Conformité au pattern `scripts/_archive/` (cf. `docs/reference/_archive-convention.md`).

## Ticket lié

- Issue #14251 (chore d'archivage)
- Refs : #13841 (issue parent), #13685 (descent), #14250 (rename minimal)

— lane `myia-po-2024:CoursIA-2`, cycle c.867 (2026-09-02).