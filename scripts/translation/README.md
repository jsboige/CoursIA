# Scripts de synchro traduction (Epic #4957 / #1650)

Infrastructure de synchronisation multilingue pour les notebooks pédagogiques. Le moteur de traduction (datasetupdater Argumentum, v0.9.0, 8 langues) n'est PAS réécrit ici — ces scripts en sont la couche d'**alignement** : ils maintiennent le CSV source de vérité et détectent le drift.

## Workflow en 3 couches (T1 → T2 → T3)

| Couche | Script | Rôle | Statut |
|--------|--------|------|--------|
| **T1** | `extract_cells_to_csv.py` | Extrait les cellules des notebooks vers le CSV (langue pivot `fr`) | Livré |
| **T2** | `check_translation_sync.py` | Détecte le drift (source modifiée / trad éditée / cellule supprimée) | Livré (non-bloquant, CI) |
| **T3** | moteur Argumentum | Resync des langues cibles sur les lignes flaggées | À venir (gated #1650 Phase 1) |

## Schéma CSV (ratified #4957 §1)

`translations/<famille>/<série>.csv` — une ligne par cellule de notebook :

```
notebook, cell_id, cell_type, src_lang, src_hash,
text_fr, text_en, text_es, text_ar, text_fa, text_zh, text_ru, text_pt,
hash_fr, hash_en, hash_es, hash_ar, hash_fa, hash_zh, hash_ru, hash_pt
```

- `cell_id` = id nbformat stable (cellules sans id sont ignorées)
- `src_hash` = sha256(16) du texte normalisé (rstrip/ligne + strip newline terminal → pas de faux-drift cosmétique)
- Colonnes pivot (`fr`) remplies à l'extraction T1 ; colonnes cibles remplies par le moteur Argumentum en T3
- Le couple `(src_hash, hash_<lang>)` détecte le drift dans les **deux sens**

## extract_cells_to_csv.py (T1)

```bash
# Extraire le CSV initial d'une série (langue pivot fr, #1650 Phase 0.5)
python scripts/translation/extract_cells_to_csv.py MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/ \
    -o translations/symbolicai/argument_analysis.csv

# Un seul notebook (POC / review du schéma)
python scripts/translation/extract_cells_to_csv.py notebook.ipynb -o poc.csv
```

Exclut `_output.ipynb` (sorties Papermill) et `_agent.ipynb` (auto-générées). Déterministe (re-extract byte-identique).

## check_translation_sync.py (T2)

Détecte le drift entre les notebooks courants et le CSV. **Non-bloquant** (mode CI `--check` : exit 0 même si drift ; le rapport va sur stderr + JSON stdout). Verdicts :

| Verdict | Sens |
|---------|------|
| `IN_SYNC` | src_hash et hash_<lang> matchent les notebooks courants |
| `SRC_DRIFT` | le notebook source a bougé depuis la dernière synchro → retraduction requise |
| `TRAD_DRIFT` | une traduction a été éditée à la main sans repercussion sur le CSV |
| `MISSING_LANG` | le notebook `xxx_<lang>.ipynb` n'existe plus alors qu'un hash était déposé |
| `ORPHAN_ROW` | la ligne CSV référence un `cell_id` absent du notebook source (cellule supprimée) |

```bash
# Vérifier un CSV (exit 1 si drift)
python scripts/translation/check_translation_sync.py translations/symbolicai/argument_analysis.csv

# Vérifier tous les CSV (mode CI non-bloquant, exit 0)
python scripts/translation/check_translation_sync.py translations/ --check
```

En phase POC (T1, seule la colonne pivot est remplie), le script ne remonte que du `SRC_DRIFT` éventuel ; l'absence de traductions déposées n'est pas un drift (c'est l'état attendu pré-T3). Le pivot (`fr`) étant le notebook source lui-même, sa cohérence est couverte par `SRC_DRIFT` — pas de faux `MISSING_LANG` sur le pivot.

## CI

Le workflow `.github/workflows/translation-drift.yml` tourne sur les PR touchant les notebooks ou `translations/` : il exécute `check_translation_sync.py --check` et surface le drift sous forme d'annotation `notice` (non-bloquant, read-only — même philosophie que `catalog-drift.yml`). La resync elle-même (T3) n'est JAMAIS auto-commitée en CI : elle est proposée par la détection et exécutée manuellement par un agent (moteur Argumentum, #4957 §3).

## Voir aussi

- Issue [#4957](../../../issues/4957) — design de l'infrastructure (schéma, sémantique drift, séquencement T0→T3)
- Epic [#1650](../../../issues/1650) — traduction multilingue du dépôt
