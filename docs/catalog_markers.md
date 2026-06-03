# Catalog Markers - README Auto-Update System

Source-of-truth counts driven by `COURSE_CATALOG.generated.json`. Markers in README files are expanded by `scripts/notebook_tools/expand_catalog_markers.py` and verified by CI on every PR.

## Overview

Instead of hardcoding notebook counts in README files, the project uses **catalog markers** — special HTML comments that get their values from the generated catalog. This ensures READMEs stay in sync with the actual notebook inventory automatically.

**Data flow:**

```
generate_catalog.py → COURSE_CATALOG.generated.json → expand_catalog_markers.py → README files
                                                                       ↑
                                                          CI checks for drift (catalog-drift.yml)
```

## Marker Types

### CATALOG-STATUS (multi-line block)

The primary marker. A multi-line HTML comment block placed near the top of a README.

**Root README** (`MyIA.AI.Notebooks/README.md`):

```html
<!-- CATALOG-STATUS
series: ALL
total: 448
breakdown: GenAI=99, QuantConnect=93, SymbolicAI=90, ...
maturity: ALPHA=232, DRAFT=126, BETA=61, PRODUCTION=29
updated: 2026-05-02
-->
```

**Series README** (e.g., `MyIA.AI.Notebooks/ML/README.md`):

```html
<!-- CATALOG-STATUS
series: ML
pedagogical_count: 30
breakdown: _root=30
maturity: ALPHA=30
updated: 2026-05-02
-->
```

**Fields:**

| Field | Root README | Series README |
|-------|-------------|---------------|
| `series` | `ALL` | Serie name (e.g., `ML`, `GenAI`) |
| `total` | Total notebook count | — |
| `pedagogical_count` | — | Notebooks in this serie |
| `breakdown` | Per-serie counts | Per-sous_serie counts |
| `maturity` | Global maturity distribution | Serie maturity distribution |
| `updated` | Last expansion date | Last expansion date |

### CATALOG:counter (inline)

Inline markers for embedding counts in prose or tables. Not yet used in current READMEs but supported by the expand script.

```html
<!-- CATALOG:counter:total -->                 → total notebooks
<!-- CATALOG:counter:serie=ML -->              → ML notebooks
<!-- CATALOG:counter:serie=ML;status=READY --> → ML notebooks with status READY
<!-- CATALOG:counter:serie=ML;maturity=PRODUCTION --> → PRODUCTION ML notebooks
```

## Script Usage

```bash
# Expand all READMEs (idempotent)
python scripts/notebook_tools/expand_catalog_markers.py

# Dry-run (show what would change)
python scripts/notebook_tools/expand_catalog_markers.py --dry-run

# Check for drift (exit 1 if stale, used by CI)
python scripts/notebook_tools/expand_catalog_markers.py --check

# Expand a specific file
python scripts/notebook_tools/expand_catalog_markers.py --file MyIA.AI.Notebooks/ML/README.md

# Use a different catalog file
python scripts/notebook_tools/expand_catalog_markers.py --catalog /path/to/catalog.json
```

The script is idempotent: running it twice produces identical output. It reads the catalog, regenerates each CATALOG-STATUS block, and only writes if the content differs.

## CI Integration

The `catalog-drift.yml` workflow runs on PRs that touch notebooks or the catalog:

```yaml
on:
  pull_request:
    paths:
      - 'MyIA.AI.Notebooks/**/*.ipynb'
      - 'MyIA.AI.Notebooks/**/README.md'
      - 'COURSE_CATALOG.generated.json'
```

Two checks run in sequence:

1. **CATALOG-STATUS marker drift** — `expand_catalog_markers.py --check` verifies all markers match the catalog
2. **Notebook catalog drift** — `verify_catalog_readme.py` checks declared counts vs actual notebooks on disk

If either check fails, the PR is blocked until markers are updated.

## Adding Markers to a New README

1. Add a `<!-- CATALOG-STATUS ... -->` block near the top of the README
2. Set the `series:` field to the serie name (use `ALL` for root)
3. Run `python scripts/notebook_tools/expand_catalog_markers.py` to populate values
4. Commit the updated README

## Regenerating the Catalog

If notebook counts change (new notebooks added/removed):

```bash
python scripts/notebook_tools/generate_catalog.py
python scripts/notebook_tools/expand_catalog_markers.py
git add COURSE_CATALOG.generated.json MyIA.AI.Notebooks/*/README.md
git commit -m "feat(catalog): regenerate catalog and update markers"
```
