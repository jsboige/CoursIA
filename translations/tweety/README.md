# CSV de synchro traduction — série SymbolicAI/Tweety

**Statut** : Phase 2 rollout (Epic #4957 / #1650). Série Tweety couverte par l'infrastructure i18n.

## Couvert

| Fichier | Série | Notebooks | Cellules |
|---------|-------|-----------|----------|
| [`tweety.csv`](tweety.csv) | `SymbolicAI/Tweety/` (top-level) | 31 (`Tweety-1-Setup` → `Tweety-11-Causal`, parité Python ⇄ C# `-Csharp`, + branches `2b/2c/3-*/4/5b/7a/7b`) | 864 (517 markdown + 347 code, 20 colonnes) |

**Schéma** : 20 colonnes (#4957 §1). `src_lang=fr`, `src_hash` (sha256-16) + `text_fr` remplies ; colonnes cibles (`text_en/es/ar/...`) vides pour le moteur T3 Argumentum (#1650 Phase 1).

**Note cross-language** : la série Tweety est cross-language — chaque notebook Python a un jumeau .NET (`-Csharp`) via le bridge IKVM + Tweety jars Java (logique propositionnelle/FOL, Dung, ASPIC+, révision de croyances, argumentation structurée, dialogues d'agents, préférences, MLN, causalité). Le script d'extraction prend les deux langages verbatim (chaque notebook est une cellule source indépendante). La traduction future T3 (moteur Argumentum) appliquera les deux familles.

**Note owner-floue** : Tweety = SymbolicAI, partition po-2023 côté .NET (`-Csharp` via IKVM + Tweety jars) / po-2025 côté Python (TweetyJPype). L'extraction i18n est **safe cross-owner** (artefacts dérivés = CSV de cellules upstream en lecture seule, pas de modification des notebooks — cf note identique dans `translations/smartcontracts/README.md`).

## Régénération

```bash
# Depuis la racine du dépôt :
python scripts/translation/extract_cells_to_csv.py \
    MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-*.ipynb \
    -o translations/tweety/tweety.csv
```

L'extraction est **déterministe byte-identique** (même ordre de notebooks, mêmes hash sha256-16 sur texte normalisé) — re-exécuter produit le même CSV.

## Vérification de drift (T2)

```bash
python scripts/translation/check_translation_sync.py translations/tweety/tweety.csv
```

## Hors scope

- `SymbolicAI/Tweety/_probes/Tweety-IKVM-Init-Probe.ipynb` — probe de diagnostic non pédagogique (exclu par le glob `Tweety-*.ipynb` top-level).
