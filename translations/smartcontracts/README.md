# CSV de synchro traduction — série SmartContracts

**Statut** : Phase 2 rollout (Epic #4957 / #1650). 5ᵉ série couverte par l'infrastructure i18n, après `SymbolicAI/Argument_Analysis/` (PR #5799), `Probas/Infer/` (PR #5801), `ML/ML.Net/` (PR #5805) et `SymbolicAI/Planners/` (PR #5806).

## Couvert

| Fichier | Série | Notebooks | Cellules |
|---------|-------|-----------|----------|
| [`smartcontracts.csv`](smartcontracts.csv) | `SymbolicAI/SmartContracts/` | 27 (SC-0-Cypherpunk-Origins → SC-26-Final-Project, parité Solidity/Foundry/Vyper/Solana/Move + Python tutorials) | 956 (header + 21 990 lignes CSV-escaped, 20 colonnes) |

**Note cross-language** : la série SmartContracts est cross-language (Solidity, Vyper, Move/Sui, Anchor/Solana, Bitcoin Scripting, EVM) avec jumeaux Python (web3.py, pytest, etc.). Le script d'extraction prend **les deux familles** verbatim (chaque notebook est une cellule source indépendante). La traduction future T3 (moteur Argumentum) appliquera les deux familles.

**Note owner-floue** : la série SmartContracts = SymbolicAI = owner po-2025 (cf c.371-372 Argumentum = AIF OWL + crossLinks CSV owner-floue, partition SymbolicAI swepté par po-2025 via c.371-c.372 + sweep #5780 SymbolicLearning c.373). L'extraction i18n est **safe cross-owner** (L143 SAFE : artefacts dérivés = CSV de cellules upstream, pas de modification de code des notebooks).

## Régénération

```bash
# Depuis la racine du dépôt :
python scripts/translation/extract_cells_to_csv.py \
    MyIA.AI.Notebooks/SymbolicAI/SmartContracts/ \
    -o translations/smartcontracts/smartcontracts.csv
```

L'extraction est **déterministe byte-identique** (même ordre de notebooks, mêmes hash sha256-16 sur texte normalisé) — re-exécuter produit le même CSV.

## Vérification de drift (T2)

```bash
python scripts/translation/check_translation_sync.py translations/smartcontracts/
```

Sortie = JSON `{"csvs_checked": 1, "anomalies": [], "anomaly_count": 0}` (IN_SYNC). Les drifts apparaîtront en T3 quand le moteur Argumentum déposera les colonnes cibles `text_en/es/ar/fa/zh/ru/pt` (les colonnes `hash_*` correspondantes seront alors remplies).

## Acceptance #4957 Phase 2

- [x] T1 extraction OK : 956 cellules / 27 notebooks SmartContracts (Solidity/Foundry/Vyper/Solana/Move + Python tutorials)
- [x] T2 round-trip IN_SYNC : 0 anomaly
- [x] Script T1+T2 inchangés (Phase 1 INFRA #5657 réutilisée telle quelle)
- [x] Workflow CI `.github/workflows/translation-drift.yml` non touché
- [ ] T3 (run moteur Argumentum #1650 Phase 1 connecteur) : gated owner po-2025 c.371-372

## Voir aussi

- Issue #4957 — design infrastructure synchronisation traduction
- Epic #1650 — traduction multilingue du dépôt
- `translations/symbolicai/README.md` — 1ère série (Argument_Analysis)
- `translations/probas-infer/README.md` — 2ᵉ série (Probas/Infer)
- `translations/mlnet/README.md` — 3ᵉ série (ML/ML.Net)
- `translations/planners/README.md` — 4ᵉ série (Planners)
- `scripts/translation/README.md` — scripts T1+T2
- `.github/workflows/translation-drift.yml` — CI non-bloquante
