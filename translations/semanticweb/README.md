# CSV de synchro traduction — série SymbolicAI/SemanticWeb

**Statut** : Phase 2 rollout (Epic #4957 / #1650). Série SemanticWeb couverte par l'infrastructure i18n.

## Couvert

| Fichier | Série | Notebooks | Cellules |
|---------|-------|-----------|----------|
| [`semanticweb.csv`](semanticweb.csv) | `SymbolicAI/SemanticWeb/` (top-level) | 24 (`SW-1` → `SW-13`, parité Python ⇄ C# : `-Csharp` / `b-Python`) | 1193 (758 markdown + 435 code, 20 colonnes) |

**Schéma** : 20 colonnes (#4957 §1). `src_lang=fr`, `src_hash` (sha256-16) + `text_fr` remplies ; colonnes cibles (`text_en/es/ar/...`) vides pour le moteur T3 Argumentum (#1650 Phase 1).

**Note cross-language** : la série SemanticWeb est cross-language — chaque concept a un jumeau Python (`SW-Nb-Python`) et C# (`SW-NC-Csharp`), plus la couverture RDF/SPARQL/OWL/SHACL/JSON-LD/RDFStar/KnowledgeGraphs/GraphRAG/Reasoners. Le script d'extraction prend les deux langages verbatim (chaque notebook est une cellule source indépendante). La traduction future T3 (moteur Argumentum) appliquera les deux familles.

**Note owner-floue** : SemanticWeb = SymbolicAI, partition po-2023 côté .NET (`-Csharp` via dotNetRDF) / po-2025 côté Python (`rdflib`). L'extraction i18n est **safe cross-owner** (artefacts dérivés = CSV de cellules upstream en lecture seule, pas de modification des notebooks — cf note identique dans `translations/smartcontracts/README.md`).

## Régénération

```bash
# Depuis la racine du dépôt :
python scripts/translation/extract_cells_to_csv.py \
    MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/SW-*.ipynb \
    -o translations/semanticweb/semanticweb.csv
```

L'extraction est **déterministe byte-identique** (même ordre de notebooks, mêmes hash sha256-16 sur texte normalisé) — re-exécuter produit le même CSV.

## Vérification de drift (T2)

```bash
python scripts/translation/check_translation_sync.py translations/semanticweb/semanticweb.csv
```

## Hors scope

- `SymbolicAI/SemanticWeb/RDF.Net-Legacy/RDF.Net.ipynb` — notebook legacy non pédagogique (exclu par le glob `SW-*`).
