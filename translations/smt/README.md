# CSV de synchro traduction — série SymbolicAI/SMT/Z3-API

**Statut** : Phase 2 rollout (Epic #4957 / #1650). Première série SMT couverte par l'infrastructure i18n.

## Couvert

| Fichier | Série | Notebooks | Cellules |
|---------|-------|-----------|----------|
| [`z3-api.csv`](z3-api.csv) | `SymbolicAI/SMT/Z3-API/` | 24 (`Z3-Python-01-Introduction` → `Z3-Python-24`, parité Python ⇄ C# `-Csharp`) | 541 (315 markdown + 226 code, 20 colonnes) |

**Note cross-language** : la série Z3-API est cross-language — chaque notebook Python a un jumeau .NET (`-Csharp`) via le binding `Microsoft.Z3`. Le script d'extraction prend les deux verbatim (chaque notebook est une cellule source indépendante). La traduction future T3 (moteur Argumentum) appliquera les deux langages.

**Note owner-floue** : SMT = SymbolicAI, partition po-2023 côté .NET (`-Csharp`) / po-2025 côté Python (cf partition language-based). L'extraction i18n est **safe cross-owner** (artefacts dérivés = CSV de cellules upstream en lecture seule, pas de modification des notebooks — cf note identique dans `translations/smartcontracts/README.md`).

## Régénération

```bash
# Depuis la racine du dépôt :
python scripts/translation/extract_cells_to_csv.py \
    MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-API/ \
    -o translations/smt/z3-api.csv
```

L'extraction est **déterministe byte-identique** (même ordre de notebooks, mêmes hash sha256-16 sur texte normalisé) — re-exécuter produit le même CSV.

## Vérification de drift (T2)

```bash
python scripts/translation/check_translation_sync.py translations/smt/z3-api.csv
```

## Hors scope

- `SymbolicAI/SMT/Z3-Linq2Z3/` (18 notebooks) — série distincte, sera un CSV séparé (`z3-linq2z3.csv`) si couverte.
- `SymbolicAI/SMT/Z3.Linq/` — submodule vendored (hors dépôt pédagogique).
