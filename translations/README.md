# CSV de synchro traduction — source de vérité multilingue

**Statut** : POC T1 (Epic #4957 / #1650). Arborescence des CSV source de vérité pour la synchronisation traduction des notebooks pédagogiques.

## Structure

```
translations/
├── README.md           ← ce fichier
└── symbolicai/
    ├── README.md
    └── argument_analysis.csv
```

Convention : `translations/<famille>/<série>.csv`, une ligne par cellule de notebook. Cf. `scripts/translation/README.md` pour le schéma détaillé.

## Familles couverte (POC)

- **`symbolicai/`** — Série `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/` (16 notebooks, 395 cellules)

## Workflow (T1 → T2 → T3)

| T# | Script | Statut |
|----|--------|--------|
| **T1** | `scripts/translation/extract_cells_to_csv.py` | **Livré** (Phase 1 INFRA, PR #5657) |
| **T2** | `scripts/translation/check_translation_sync.py` | **Livré**, CI non-bloquante `.github/workflows/translation-drift.yml` |
| **T3** | Moteur Argumentum `datasetupdater` (8 langues) | À venir (gated #1650 Phase 1 connecteur) |

## Voir aussi

- Issue #4957 — design infrastructure
- Epic #1650 — traduction multilingue du dépôt
- `scripts/translation/README.md`