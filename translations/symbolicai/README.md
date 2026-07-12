# CSV de synchro traduction — série SymbolicAI

**Statut** : POC T1 (Epic #4957 / #1650). Source de vérité de l'alignement multilingue pour les séries `SymbolicAI/`.

## Couvert

| Fichier | Série | Notebooks | Cellules |
|---------|-------|-----------|----------|
| [`argument_analysis.csv`](argument_analysis.csv) | `SymbolicAI/Argument_Analysis/` | 16 (20 au total, 4 `_agent.ipynb` auto-générés exclus) | 395 (cf. en-tête) |

## Régénération

```bash
# Depuis la racine du dépôt :
python scripts/translation/extract_cells_to_csv.py \
    MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/ \
    -o translations/symbolicai/argument_analysis.csv
```

L'extraction est **déterministe byte-identique** (même ordre de notebooks, mêmes hash sha256-16 sur texte normalisé) — re-exécuter produit le même CSV, ce qui rend le diff lisible et la CI capable de détecter un drift réel (≠ cosmétique).

## Vérification de drift (T2)

```bash
python scripts/translation/check_translation_sync.py translations/symbolicai/
```

Sortie = JSON (`anomaly_count`, `verdicts`) + rapport lisible sur stderr. En POC (T1), seule la colonne pivot `fr` est remplie → 0 drift attendu (le pivot EST la source). Les drifts apparaîtront en T3 quand le moteur Argumentum déposera les colonnes cibles.

## Acceptance #4957 T1

- [x] Schéma CSV validé par le user (ratifié dans `scripts/translation/README.md`)
- [x] T1 POC livré : CSV initial d'une série + script d'extraction + CI drift-flag existant
- [ ] T3 : premier run moteur Argumentum (gated #1650 Phase 1 connecteur) → `xxx_<lang>.ipynb` pour la série Argument_Analysis

## Voir aussi

- Issue #4957 — design de l'infrastructure de synchronisation traduction
- Epic #1650 — traduction multilingue du dépôt
- `scripts/translation/README.md` — scripts T1+T2
- `.github/workflows/translation-drift.yml` — CI non-bloquante (read-only)