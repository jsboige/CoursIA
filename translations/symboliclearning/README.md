# CSV de synchro traduction — série SymbolicAI/SymbolicLearning

**Statut** : Phase 2 rollout (Epic #4957 / #1650). Série SymbolicLearning couverte par l'infrastructure i18n.

## Couvert

| Fichier | Série | Notebooks | Cellules |
|---------|-------|-----------|----------|
| [`symboliclearning.csv`](symboliclearning.csv) | `SymbolicAI/SymbolicLearning/` (top-level) | 20 (`SL-1-LogicalLearning` → `SL-12-DifferentiableLogicGateNetworks`, parité Python ⇄ C# `-Csharp`) | 738 (444 markdown + 294 code, 20 colonnes) |

**Schéma** : 20 colonnes (#4957 §1). `src_lang=fr`, `src_hash` (sha256-16) + `text_fr` remplies ; colonnes cibles (`text_en/es/ar/...`) vides pour le moteur T3 Argumentum (#1650 Phase 1).

**Note cross-language** : la série SymbolicLearning est cross-language — chaque concept a un notebook Python et un jumeau C# .NET (`-Csharp`) couvrant l'apprentissage symbolique : CBH Search & Version Space, EBL & RBL, pertinence (RBL), programmation logique inductive (ILP — FOIL, Progol, Metagol, Popper, dILP), résolution inverse, ILP moderne récursif, apprentissage actif d'automates (L* d'Angluin), intégration neuro-symbolique, ILP & knowledge graphs, LLMs & apprentissage symbolique, capstone neuro-symbolique, Differentiable Logic Gate Networks. Le script d'extraction prend les deux langages verbatim (chaque notebook est une cellule source indépendante). La traduction future T3 (moteur Argumentum) appliquera les deux familles.

**Note owner-floue** : SymbolicLearning = SymbolicAI, partition po-2023 côté .NET (`-Csharp`) / po-2025 côté Python. L'extraction i18n est **safe cross-owner** (artefact dérivé = CSV de cellules upstream en lecture seule, pas de modification des notebooks — cf note identique dans `translations/smartcontracts/README.md`).

## Régénération

```bash
# Depuis la racine du dépôt :
python scripts/translation/extract_cells_to_csv.py \
    MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/SL-*.ipynb \
    -o translations/symboliclearning/symboliclearning.csv
```

L'extraction est **déterministe byte-identique** (même ordre de notebooks, mêmes hash sha256-16 sur texte normalisé) — re-exécuter produit le même CSV.

## Vérification de drift (T2)

```bash
python scripts/translation/check_translation_sync.py translations/symboliclearning/symboliclearning.csv
```

## Hors scope

- `SymbolicAI/SymbolicLearning/_archives/`, `assets/`, `reference/`, `tests/`, `vendor/` — supports non pédagogiques (exclus par le glob `SL-*.ipynb` top-level).
