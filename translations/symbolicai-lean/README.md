# CSV de synchro traduction — série SymbolicAI/Lean

**Statut** : Phase 0.5 backfill (Epic #4957 / #1650). Série SymbolicAI/Lean couverte par l'infrastructure i18n.

## Couvert

| Fichier | Série | Notebooks | Cellules |
|---------|-------|-----------|----------|
| [`symbolicai-lean.csv`](symbolicai-lean.csv) | `SymbolicAI/Lean/` (série numérotée Lean-1 à Lean-18, avec sous-niveaux a/b/c/d/e/f) | 28 | 1178 (21 colonnes) |

**Note owner-lane** : l'extraction i18n est **safe owner-lane** (artefacts dérivés = CSV de cellules upstream, pas de modification de code des notebooks). Les cellules `code` (Lean 4) et `markdown` (prose pédagogique FR) sont toutes indexées ; les T3 (colonnes cibles `text_en`/`hash_en`/…) restent vides en attente du run moteur Argumentum (gated #1650 Phase 1).

**Périmètre fonctionnel** : la série couvre la preuve formelle en Lean 4 — types dépendants et tactiques (Lean-1 à Lean-6), recherche A* et optimalité, LeanDojo et TorchLean (pont Python), puis les hommages-mathématiciens (Sensitivity, Kochen-Specker, Finiteness, Grothendieck, Conway : Game of Life, FRACTRAN, Free Will Theorem, Knots/invariants). Le fil rouge « hommages » traverse la seconde moitié de la série.

## Décision Lean (#4957 question ouverte)

Conformément à l'option (a) de la question ouverte #4957 — « la pédagogie FR vivant dans les notebooks compagnons [est traduite par] le pipeline standard » — cette série de **notebooks** entre dans le périmètre CSV standard. La traduction des fichiers **`.lean`** (preuves formelles, docstrings) est traitée séparément par l'Epic #4980 (paires sibling FR/`_en`), hors de ce CSV.

## Régénération

```bash
# Depuis la racine du dépôt :
python scripts/translation/extract_cells_to_csv.py \
    MyIA.AI.Notebooks/SymbolicAI/Lean/ \
    --src-lang fr \
    -o translations/symbolicai-lean/symbolicai-lean.csv
```

L'extraction est **déterministe byte-identique** (même ordre de notebooks, mêmes hash sha256-16 sur texte normalisé) — re-exécuter produit le même CSV (vérifié : SHA256 `e6e5f3cb…` reproductible).

## Vérification de drift (T2)

```bash
python scripts/translation/check_translation_sync.py translations/symbolicai-lean/
```

Résultat attendu : `csvs_checked: 1, anomaly_count: 0` (IN_SYNC by construction pour un seed frais).
