# QuantBooks Execution Status — LIVE POINTER

> **Statut : LIVE POINTER (2026-07-21)** — fichier rafraîchi post-cure **#7575**
> (c.728y+16). La **source de vérité** sur l'état d'exécution des quantbooks
> est l'outil programmé ci-dessous, **pas ce document**. Ce fichier sert de
> carte de navigation + table récapitulative des 9 quantbooks PREEXISTING_UNEXEC
> (bug-class #7575) avec leur statut post-cure.

## Source de vérité (audit script — toujours à jour)

```bash
python scripts/quantconnect/audit_quantbooks_unexec.py
```

Sortie : classification `HEALTHY` / `STOP_REPAIR_STRIPPED` / `PREEXISTING_UNEXEC`
par projet, cross-référencée avec `config.json` (cloud-id `ALIVE` / `MISSING` /
`DEAD`). Référence complète + tests hermétiques :
[`scripts/quantconnect/tests/test_audit_quantbooks_unexec.py`](tests/test_audit_quantbooks_unexec.py).

Issue parente de l'outil : **#6891** (corps — 8 quantbooks avec FABRICATION
dégénérée, sweep strip en #7447 + #7462). Issue sœur **#7575** (c.728y+16 —
9 quantbooks PREEXISTING_UNEXEC **non couverts par le corps #6891**).

---

## Table récapitulative des 9 quantbooks PREEXISTING_UNEXEC (c.728y+16)

Issued #7575 (corps) liste 9 quantbooks avec cellules code jamais exécutées
(`execution_count: null`, `outputs: []`) **sans marqueur strip** — bug-class
distinct de #6891 (qui était FABRICATION puis strippée). État post-cure
(rafraîchi `git show` 2026-07-21) :

| Projet | Cells unexec | `config.json` | Cloud ID | Marqueur `QC-UNEXEC-TRIAGED` | `ARCHIVE.md` | PR cure | Statut post-cure |
|--------|--------------|---------------|----------|------------------------------|--------------|---------|------------------|
| `BTC-ML` | 8/11 | absent | n/a | présent (PR #7681) | **présent** (PR #7792) | #7681 + #7792 | **ARCHIVÉ** (projet mort) |
| `DL-LSTM` | 2/12 | absent | n/a | présent | **présent** | #7681 + #7792 | **ARCHIVÉ** (INTRINSIC — pas de QC) |
| `ML-DeepLearning` | 2/12 | absent | n/a | présent | **présent** | #7681 + #7792 | **ARCHIVÉ** (Ridge proxy) |
| `ML-TextClassification` | 10/14 | absent | n/a | présent | **présent** | #7681 + #7792 | **ARCHIVÉ** (sentiment simulé) |
| `PairsTrading` | 4/7 | absent | n/a | présent | **présent** | #7681 + #7792 | **ARCHIVÉ** (BROKEN — cointégration instable) |
| `RL-Portfolio` | 7/10 | absent | n/a | présent | **présent** | #7681 + #7792 | **ARCHIVÉ** (Q-Learning template) |
| `VIX-TermStructure` | 8/10 | absent | n/a | présent | **présent** (c.728f L873 ★) | #7652 | **ARCHIVÉ** (avant #7575, predecessor) |
| `Crypto-MultiCanal` | 8/10 | **présent** | 30750734 | présent | n/a | #7681 | **GARDÉ** (cloud-id ALIVE, re-exec RECOVERABLE-MACHINE) |
| `ML-XGBoost` | 10/11 | **présent** | 29434753 | présent | n/a | #7681 | **GARDÉ** (cloud-id ALIVE, re-exec RECOVERABLE-MACHINE) |

**Résultat post-cure** : 7/9 ARCHIVÉS (projets morts sans `config.json`),
2/9 GARDÉS (avec `config.json` live — `Crypto-MultiCanal` et `ML-XGBoost`,
re-exécution différée sur QC Cloud, RECOVERABLE-MACHINE).

### PRs de la cure #7575

| PR | Statut | Commit | Livrable |
|----|--------|--------|----------|
| **#7569** | MERGED 2026-07-20 | `c2f29631f` | Outil d'audit `audit_quantbooks_unexec.py` + classification 3 états |
| **#7652** | MERGED 2026-07-21 | `15e825d55` | `VIX-TermStructure/ARCHIVE.md` (predecessor, c.728f L873 ★) |
| **#7681** | MERGED 2026-07-21 | `c15de838e` | Marqueurs `QC-UNEXEC-TRIAGED` dans les 9 + classe dédiée |
| **#7792** | OPEN 2026-07-21 | `624319e86` | 6 `ARCHIVE.md` pour dead quantbooks (BTC-ML, DL-LSTM, ML-DeepLearning, ML-TextClassification, PairsTrading, RL-Portfolio) |

### Bug-class distincte (cf #7575)

- **#6891 (corps)** : FABRICATION dégénérée (1×1 PNG, `Row N` placeholders,
  blank 70B outputs). Strip sweep #7447 + #7462 a ajouté le marqueur
  `STOP_REPAIR_STRIPPED`. **Re-execution gated** sur QC Cloud (RECOVERABLE-MACHINE).
- **#7575 (sœur)** : PREEXISTING_UNEXEC = `execution_count: null` dès l'origine,
  **PAS de fabrication**. La strip sweep #7447+#7462 ne pouvait pas les marquer
  (`STOP_REPAIR_STRIPPED` requiert un marqueur strip pré-existant). La cure a
  introduit le marqueur dédié `QC-UNEXEC-TRIAGED` + classe `STOP_REPAIR_UNEXEC`
  dans l'audit tool (PR #7681).

### Issue parente et clôture

- **#6891** OPEN — fix partiel (strip sweep fait, re-exécution à faire
  en QC Cloud). À clore une fois la re-exécution des 8 STRIPPED effective.
- **#7575** OPEN — cure complète livrée (PR #7569 + #7652 + #7681 + #7792).
  Restant = 2 re-exécutions QC Cloud (Crypto-MultiCanal, ML-XGBoost) gated sur
  infra QC + clôture définitive après merge #7792.

---

## Snapshot historique DEPRECATED (2026-05-04 → 2026-07-20)

> **Historique préservé tel quel pour mémoire uniquement**, **PAS comme source
> de vérité**. Le snapshot ci-dessous prétendait classifier 45 quantbooks
> (8 done + 37 « pending ») mais 37 étaient des **placeholders fabriqués** (N/A).
> L'audit initial était fallacieux. Source : note d'origine du fichier.

### DEPRECATED — snapshot 2026-05-04 (préservé pour mémoire)

| # | Project | Cloud ID | Cells | Outputs | Status |
|---|---------|----------|-------|---------|--------|
| 1 | AllWeather | 28657833 | 8 | 8/8 | DONE |
| 2 | DualMomentum | 28692516 | 9 | 9/9 | DONE |
| 3 | EMA-Cross-Alpha | 28885488 | 9 | 9/9 | DONE |
| 4 | FuturesTrend | 28657834 | 8 | 8/8 | DONE |
| 5 | MomentumStrategy | 28657837 | 8 | 8/8 | DONE |
| 6 | RiskParity | 28652653 | 8 | 8/8 | DONE |
| 7 | SectorMomentum | 28433643 | 7 | 7/7 | DONE |
| 8 | TurnOfMonth | 28657905 | 9 | 9/9 | DONE |

### DEPRECATED — Pending (QC Cloud execution required)

(37 lignes placeholder historique — non reproduites ici, **PAS** source de
vérité. Voir `git log -p -- scripts/quantconnect/quantbooks_execution_status.md`
pour le snapshot complet 2026-05-04.)

**Note d'origine (préservée)** : « Previous version falsely reported 45/45
DONE. 37 had fabricated outputs (N/A placeholders) which were reverted.
Real execution requires QC Cloud research nodes via MCP qc-mcp or Playwright. »

---

## Liens utiles

- [`scripts/quantconnect/audit_quantbooks_unexec.py`](audit_quantbooks_unexec.py) — source de vérité (TOUJOURS à jour)
- [`scripts/quantconnect/tests/test_audit_quantbooks_unexec.py`](tests/test_audit_quantbooks_unexec.py) — tests hermétiques
- Issue **#6891** — parent (corps : fabrication dégénérée)
- Issue **#7575** — sœur (c.728y+16 : PREEXISTING_UNEXEC)
- PR **#7569** (MERGED) — audit tool
- PR **#7652** (MERGED) — VIX archive predecessor
- PR **#7681** (MERGED) — marqueurs `QC-UNEXEC-TRIAGED` + classe dédiée
- PR **#7792** (OPEN) — 6 `ARCHIVE.md` pour dead quantbooks
