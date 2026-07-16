# CSV de synchro traduction — famille SymbolicAI/SMT

**Statut** : Phase 2 rollout (Epic #4957 / #1650). Famille SMT couverte par l'infrastructure i18n, deux séries indépendantes.

## Couvert

| Fichier | Série | Notebooks | Cellules |
|---------|-------|-----------|----------|
| [`z3-api.csv`](z3-api.csv) | `SymbolicAI/SMT/Z3-API/` | 24 (`Z3-Python-01-Introduction` → `Z3-Python-24`, parité Python ⇄ C# `-Csharp`) | 541 (315 markdown + 226 code, 20 colonnes) |
| [`z3-linq2z3.csv`](z3-linq2z3.csv) | `SymbolicAI/SMT/Z3-Linq2Z3/` | 18 (`01_Linq2Z3_Intro` → `18_Einsteins_Riddle`, C# LINQ-to-Z3 déclaratif) | 525 (323 markdown + 202 code, 20 colonnes) |

**Schéma** : 20 colonnes (#4957 §1). `src_lang=fr`, `src_hash` (sha256-16) + `text_fr` remplies ; colonnes cibles (`text_en/es/ar/...`) vides pour le moteur T3 Argumentum (#1650 Phase 1).

**Note cross-language** : Z3-API est parité Python ⇄ C# (`-Csharp`) via `Microsoft.Z3`. Z3-Linq2Z3 est C# natif (LINQ-to-Z3 déclaratif). Les deux CSV prennent chaque notebook verbatim (cellule source indépendante). La traduction future T3 (moteur Argumentum) appliquera les deux langages.

**Note owner-floue** : SMT = SymbolicAI, partition po-2023 côté .NET (`-Csharp` + Z3-Linq2Z3) / po-2025 côté Python (Z3-API Python). L'extraction i18n est **safe cross-owner** (artefacts dérivés = CSV de cellules upstream en lecture seule, pas de modification des notebooks — cf note identique dans `translations/smartcontracts/README.md`).

## Régénération

```bash
# Depuis la racine du dépôt :
python scripts/translation/extract_cells_to_csv.py \
    MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-API/ \
    -o translations/smt/z3-api.csv
python scripts/translation/extract_cells_to_csv.py \
    MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-Linq2Z3/ \
    -o translations/smt/z3-linq2z3.csv
```

L'extraction est **déterministe byte-identique** (même ordre de notebooks, mêmes hash sha256-16 sur texte normalisé) — re-exécuter produit le même CSV.

## Vérification de drift (T2)

```bash
python scripts/translation/check_translation_sync.py translations/smt/
```

## Hors scope

- `SymbolicAI/SMT/Z3.Linq/` — submodule vendored (hors dépôt pédagogique, `polyglot-repro`).
- `SymbolicAI/SMT/Automata/`, `SymbolicAI/SMT/Resharp/` — pas de notebooks pédagogiques FR-first détectés.
