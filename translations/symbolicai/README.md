# CSV de synchro traduction — série SymbolicAI

**Statut** : POC T1 (Epic #4957 / #1650). Source de vérité de l'alignement multilingue pour les séries `SymbolicAI/`.

## Couvert

| Fichier | Série | Notebooks | Cellules |
|---------|-------|-----------|----------|
| [`argumentanalysis.csv`](argumentanalysis.csv) | `SymbolicAI/ArgumentAnalysis/` | 16 au 2026-07-09, resync OWL #5799 (14 + 4 `_agent.ipynb` exclus au seed initial 2026-07-05, 20 au total à l'époque — le compte courant vit dans le CSV) | 395 au 2026-07-09 (cf. en-tête — compte courant mesurable dans le CSV) |

## Régénération

```bash
# Depuis la racine du dépôt :
python scripts/translation/extract_cells_to_csv.py \
    MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis/ \
    -o translations/symbolicai/argumentanalysis.csv
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
- [ ] T3 : premier run moteur Argumentum (gated #1650 Phase 1 connecteur) → `xxx_<lang>.ipynb` pour la série ArgumentAnalysis

## Voir aussi

- Issue #4957 — design de l'infrastructure de synchronisation traduction
- Epic #1650 — traduction multilingue du dépôt
- `scripts/translation/README.md` — scripts T1+T2
- `.github/workflows/translation-drift.yml` — CI non-bloquante (read-only)