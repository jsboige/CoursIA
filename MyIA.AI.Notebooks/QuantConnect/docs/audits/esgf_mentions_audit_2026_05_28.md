# ESGF Mentions Audit — 2026-05-28

**Scope**: All files under `MyIA.AI.Notebooks/QuantConnect/` containing "ESGF".
**Source**: Epic #1621, sub-issue #1625.
**Total**: 165 occurrences across 55 files.

## Classification

### Category 1: Already De-genericized (partner-course-quant-trading/)

po-2024 Phase 2 (PR #1638 merged) renamed `ESGF-2026/` to `partner-course-quant-trading/`. These files still have ESGF mentions in research notebook outputs (cell outputs from previous runs).

| File | Occurrences | Nature |
|------|-------------|--------|
| partner-course-quant-trading/kit-transitoire/01-ML-RandomForest/research.ipynb | 1 | Cell output (project name) |
| partner-course-quant-trading/kit-transitoire/02-ML-XGBoost/research.ipynb | 1 | Cell output |
| partner-course-quant-trading/kit-transitoire/03-Framework-Composite/research.ipynb | 1 | Cell output |
| partner-course-quant-trading/examples/Sector-Momentum/research_robustness.ipynb | 2 | Cell output |
| partner-course-quant-tracking/examples/Sector-Momentum/deep_research_optimization.ipynb | 2 | Cell output |

**Action**: Re-execute notebooks to refresh outputs with new project names (po-2024 Phase 3b scope).

### Category 2: Pedagogical Notebooks (Python/)

Each QC-Py-XX notebook has 1 mention of ESGF in a context like "Ce notebook est utilisé dans le cours ESGF" or similar. These are **reference mentions**, not branding.

| Files | Count | Nature |
|-------|-------|--------|
| QC-Py-01 through QC-Py-17 (14 notebooks) | 14 | Single mention each, pedagogical context |

**Action**: No action needed — these are factual references to a course that uses the material. Could optionally replace with generic "ce cours" if user mandates full debranding.

### Category 3: ML-Training-Pipeline Docs

Technical documentation referencing ESGF-derived strategies (HAR-RV-Kelly, ensemble experiments).

| File | Occurrences | Nature |
|------|-------------|--------|
| ML-Training-Pipeline/README.md | 1 | Reference to ESGF course context |
| ML-Training-Pipeline/docs/M3_HAR_LONG_HORIZON.md | 3 | Strategy context |
| ML-Training-Pipeline/docs/M11b_HAR_KELLY_LONG_HORIZONS.md | 3 | Strategy context |
| ML-Training-Pipeline/docs/M11c_DM_SIGNIFICANCE.md | 1 | Strategy context |
| ML-Training-Pipeline/docs/M11e_ENSEMBLE.md | 2 | Strategy context |
| ML-Training-Pipeline/docs/M11f_TX_COST_SWEEP.md | 2 | Strategy context |
| ML-Training-Pipeline/docs/M11g_FEE_AWARE_KELLY.md | 1 | Strategy context |
| ML-Training-Pipeline/docs/M12_M11EF_QC_MIGRATION_PLAN.md | 1 | Migration plan reference |
| ML-Training-Pipeline/research_what_dl_can_predict.ipynb | 2 | Research notebook output |

**Action**: Replace "ESGF" with generic context in docs (8 .md files). Research notebook outputs can be refreshed on next execution.

### Category 4: Projects Research Notebooks

Research notebooks with ESGF mentions in cell outputs or metadata.

| File | Occurrences | Nature |
|------|-------------|--------|
| projects/ForexCarry/research.ipynb | 2 | Cell output |
| projects/HAR-RV-Kelly/research.ipynb | 2 | Cell output |
| projects/TurnOfMonth/research.ipynb | 1 | Cell output |
| projects/TurnOfMonth/ARCHIVE.md | 3 | Archive documentation |
| projects/Vol-GARCH-Target/research.ipynb | 2 | Cell output |
| projects/Vol-Ensemble-Conservative/research.ipynb | 3 | Cell output |

**Action**: Re-execute notebooks to refresh outputs. ARCHIVE.md can be updated manually.

### Category 5: Project READMEs

| File | Occurrences | Nature |
|------|-------------|--------|
| projects/Corrective-AI/README.md | 1 | Chapter reference |
| projects/RL-Options-Hedging/README.md | 1 | Chapter reference |
| projects/CSharp-BTC-MACD-ADX/README.md | 1 | Course context |
| projects/CSharp-BTC-MACD-ADX/RESEARCH_SUMMARY.md | 1 | Research context |
| projects/CSharp-BTC-EMA-Cross/RESEARCH_INSTRUCTIONS.md | 2 | Instructions |
| projects/CSharp-CTG-Momentum/RESEARCH_SUMMARY.md | 1 | Research context |

**Action**: Replace ESGF references with generic "course" or "training program" text.

### Category 6: Documentation & Audit Files

| File | Occurrences | Nature |
|------|-------------|--------|
| docs/audits/AUDIT_QC_CLOUD.md | 28 | Historical audit |
| docs/audits/AUDIT_QC_ORG_2026-04.md | 4 | Historical audit |
| docs/audits/AUDIT_RAPPORT_2026-03-22.md | 11 | Historical audit |
| docs/audits/VALIDATION-REPORT.md | 3 | Historical validation |
| docs/audit_consolidation_qc.md | 13 | Consolidation audit |
| docs/qc_strategies_catalog.md | 15 | Strategy catalog |
| docs/HANDSON_AI_TRADING_MAPPING.md | 8 | Book mapping |
| docs/HANDSON_DATA_REQUIREMENTS.md | 2 | Data requirements |
| GETTING-STARTED.md | 1 | Getting started guide |
| projects/_docs/QUANTCONNECT_PROJECTS_AUDIT.md | 1 | Project audit |
| projects/_docs/SESSION5_PATTERNS.md | 1 | Session patterns |
| scripts/audit_readme.py | 9 | Audit script |
| shared/data_cache.py | 3 | Data cache module |

**Action**: Historical audits (docs/audits/) — **keep as-is** (historical records). Other docs can be debranded.

### Category 7: README.md (Main)

| File | Occurrences | Nature |
|------|-------------|--------|
| README.md | 7 | ESGF-2026 section, transient dirs |

**Action**: Update ESGF-2026 section to reference `partner-course-quant-trading/` instead. Transient dirs section already updated (PR #1635).

### Category 8: New audit file (this file)

| File | Occurrences | Nature |
|------|-------------|--------|
| docs/audits/qc_projects_audit_2026_05_28.md | 2 | Self-reference |

**Action**: N/A (this audit document).

## Migration Plan

### Phase 1: Already done (po-2024)
- `ESGF-2026/` → `partner-course-quant-trading/` (PR #1638)
- ESGF branding removed from QC project main.py files (PR #1640)

### Phase 2: Debrand documentation (po-2023, this PR)
- [ ] Replace ESGF with generic text in 6 project READMEs (Category 5)
- [ ] Replace ESGF with generic text in ML-Training-Pipeline docs (Category 3, 8 .md files)
- [ ] Update main README.md ESGF-2026 section (Category 7)
- [ ] Replace ESGF in scripts/audit_readme.py and shared/data_cache.py (Category 6)

### Phase 3: Refresh notebook outputs (future)
- [ ] Re-execute 5 partner-course notebooks (Category 1)
- [ ] Re-execute 5 project research notebooks (Category 4)
- [ ] Re-execute ML-Training-Pipeline research notebook (Category 3)

### Phase 4: No action needed
- [x] Historical audits (docs/audits/) — preserved as historical records
- [x] Pedagogical notebooks (Python/) — factual references, acceptable
