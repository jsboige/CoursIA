# EPIC #3801 — Ledger axe-2 SOTA (substance owner po-2025 strict)

**Statut** : Entry de ledger cumulatif. Format = table audit SOTA par famille, 5 verdicts SOTA-OK / RECOVERABLE-{LOCAL,MACHINE,USER-HAND} / INTRINSIC.

**Source** : EPIC #3801 axe-2 SOTA ledger, mandat user 2026-06-21, règle SOTA-not-workaround (5 verdicts).

## Convention d'entrée

Chaque entry = 1 audit de famille/source, avec :

- **Famille / source** : nom canonique + owner-lane + nb_count
- **Date audit** + **auditeur** (machine:workspace)
- **Verdict agrégé** : SOTA-OK / RECOVERABLE-LOCAL / RECOVERABLE-MACHINE / RECOVERABLE-USER-HAND / INTRINSIC
- **Findings** : nb total / EXEC_PROVED / erreurs / stubs C.1 / vrais outils SOTA invoqués / workarounds dégradés
- **PRs liées** : liens vers PRs de fix si verdict != SOTA-OK

## Entry #001 — ML/ML.Net (owner po-2025 strict, c.388)

| Métrique | Valeur |
|----------|--------|
| Famille | `MyIA.AI.Notebooks/ML/ML.Net/` (19 .ipynb) |
| Owner-lane | **po-2025 strict** (PRs récentes #5787 sweep figures, #5745 Twin C# parity #4956, #5746 Twin parity) |
| Date audit | 2026-07-09 (c.388) |
| Auditeur | `myia-po-2025:CoursIA-2` |
| Verdict agrégé | **SOTA-OK** (19/19 SOTA-OK) |

### Findings détaillés

| Nb | Cells | Code | EXEC | Err | Stubs C.1 | Kernel | ML.NET refs | SOTA verdict |
|----|-------|------|------|-----|-----------|--------|-------------|--------------|
| ML-1-Introduction | 40 | 16 | 16/16 | 0 | 0 | .net-csharp | 54 | **SOTA-OK** |
| ML-1-Introduction-Python | 36 | 13 | 13/13 | 0 | 0 | python3 | 10 | **SOTA-OK** |
| ML-2-Data&Features | 28 | 12 | 12/12 | 0 | 0 | .net-csharp | 29 | **SOTA-OK** |
| ML-2-Data&Features-Python | 19 | 9 | 9/9 | 0 | 0 | python3 | 29 | **SOTA-OK** |
| ML-3-Entrainement&AutoML | 20 | 8 | 8/8 | 0 | 0 | .net-csharp | 28 | **SOTA-OK** |
| ML-3-Entrainement-Python | 20 | 8 | 8/8 | 0 | 0 | python3 | 12 | **SOTA-OK** |
| ML-4-Evaluation | 85 | 40 | 40/40 | 0 | 0 | .net-csharp | 68 | **SOTA-OK** |
| ML-4-Evaluation-Python | 21 | 10 | 10/10 | 0 | 0 | python3 | 16 | **SOTA-OK** |
| ML-5-TimeSeries | 40 | 15 | 15/15 | 0 | 0 | .net-csharp | 19 | **SOTA-OK** |
| ML-5-TimeSeries-Python | 30 | 12 | 12/12 | 0 | 0 (FP hash) | python3 | 6 | **SOTA-OK** |
| ML-6-ONNX | 28 | 12 | 12/12 | 0 | 0 | .net-csharp | 52 | **SOTA-OK** |
| ML-6-ONNX-Python | 28 | 10 | 10/10 | 0 | 0 | coursia-ml-training | 8 | **SOTA-OK** |
| ML-7-Recommendation | 34 | 16 | 16/16 | 0 | 0 | .net-csharp | 34 | **SOTA-OK** |
| ML-7-Recommendation-Python | 24 | 10 | 10/10 | 0 | 0 | python3 | 5 | **SOTA-OK** |
| ML-8-Clustering | 34 | 14 | 14/14 | 0 | 0 | .net-csharp | 20 | **SOTA-OK** |
| ML-8-Clustering-Python | 26 | 11 | 11/11 | 0 | 0 | python3 | 10 | **SOTA-OK** |
| ML-9-Anomaly-Detection | 34 | 14 | 14/14 | 0 | 0 | .net-csharp | 19 | **SOTA-OK** |
| ML-9-Anomaly-Detection-Python | 29 | 12 | 12/12 | 0 | 0 | python3 | 6 | **SOTA-OK** |
| TP-prevision-ventes | 24 | 9 | 9/9 | 0 | 0 | .net-csharp | 30 | **SOTA-OK** |

### Synthèse

- **EXEC_PROVED global** : 19/19 (100%) — tous kernels exécutés, `execution_count != null`, `outputs: [...]` cohérents.
- **Erreurs runtime** : 0/19.
- **Violations C.1** : 0/19 (1 faux positif initial sur hash base64 confirmé nettoyé par lecture directe G.1).
- **Vrais outils SOTA invoqués** :
  - ML.NET 4.x/5.x via .NET Interactive (10 nb .net-csharp) — kernelspec `.net-csharp`
  - scikit-learn/Pandas via Python (8 nb python3) — kernelspec `python3`
  - coursia-ml-training env pour ML-6 ONNX Python — kernelspec `coursia-ml-training`
- **Workaround dégradé** : 0/19 (pas d'ASCII art, pas de stub à la place de ML.NET, pas de réimplémentation jouet).
- **Problème non-trivial** (Prong B) : 19/19 OK — chaque notebook pose un problème ML.Net réel (classification binaire, régression, clustering K-Means, time series forecasting SSA, recommandation, détection d'anomalies) qui exerce la capacité distinctive du moteur ML.NET (vs. baselines triviales).

### Conclusions audit

- **Substance owner po-2025 strict ML/ML.Net = propre**, conforme aux règles SOTA-not-workaround (5 verdicts) + C.1/C.2 notebook-conventions + Stop & Repair.
- **Pas de fix nécessaire** : audit = SOTA-OK 19/19, aucun PR de substance.
- **Continuité c.388** : pivot légitime post-i18n monotone c.380-c.387 (10ᵉ série PR #5813) — registre varié owner po-2025 strict, axe-2 SOTA ledger entry, **L335 anti-monoculture respecté** (substance NEUVE ≠ 11ᵉ PR i18n monotone, ≠ clôture admin #5661, ≠ re-sweep monotone figures).

## Cumul entries

| # | Entry | Owner | Date | Verdict | PR |
|---|-------|-------|------|---------|-----|
| 1 | ML/ML.Net (19 nb) | po-2025 strict | 2026-07-09 | SOTA-OK 19/19 | THIS |

## Voir aussi

- EPIC #3801 — registre axe-2 SOTA (mandat user 2026-06-21)
- `.claude/rules/sota-not-workaround.md` — 5 verdicts + Prong A/B
- `docs/lean/sota-2026-analysis.md` — entry Lean existante (format de référence)
- PR #5787 — sweep figures ML.Net (c.374, owner po-2025 strict, MERGED)