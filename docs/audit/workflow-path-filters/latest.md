# Audit workflow paths-filters (issue #10600)

Total workflows: **150** | pull_request: **86** | avec paths: **79** | label-posing: **6** | required: **1** | avec filtre effectif PR→main: **80** | exemptions documentees: **6** | sans-filtre eligible: **0**

| Workflow | pull_request | paths | target-filter excl. main | label-posing | exemption doc. |
|----------|--------------|-------|--------------------------|--------------|----------------|
| `.github\workflows\always-on-guards.yml` | oui | (none) | non | oui | #13234 |
| `.github\workflows\always-on-metadata-guards.yml` | oui | (none) | non | oui | #13234 |
| `.github\workflows\arxiv-attributions-guard.yml` | oui | arxiv_attributions_registry.yaml, scripts/check_arxiv_attributions.py, scripts/t | non | non |  |
| `.github\workflows\banner-guard.yml` | oui | **.ipynb, scripts/notebook_tools/strip_probe_banner.py, .github/workflows/banner | non | non |  |
| `.github\workflows\bare-cross-dir-load-gate.yml` | oui | MyIA.AI.Notebooks/**/*.ipynb, scripts/notebook_tools/detect_bare_cross_dir_load. | non | non |  |
| `.github\workflows\bash-syntax-advisory.yml` | oui | **/*.sh, .github/workflows/bash-syntax-advisory.yml | non | non |  |
| `.github\workflows\catalog-drift.yml` | oui | MyIA.AI.Notebooks/**/*.ipynb, MyIA.AI.Notebooks/**/README.md, scripts/notebook_t | non | non |  |
| `.github\workflows\cell-order-gate.yml` | oui | MyIA.AI.Notebooks/**/*.ipynb, scripts/notebook_tools/scan_cell_ordering.py, scri | non | non |  |
| `.github\workflows\consecutive-code-cells-advisory.yml` | oui | **/*.ipynb, .github/workflows/consecutive-code-cells-advisory.yml | non | oui |  |
| `.github\workflows\dotnet-AgentSafetyAnalyzer.yml` | oui | MyIA.AI.Notebooks/GenAI/Vibe-Coding/analyzers/**, .github/workflows/dotnet-Agent | non | non |  |
| `.github\workflows\dotnet-ArgumentAnalysis.yml` | oui | MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/**, .github/workflows/dotnet-Argu | non | non |  |
| `.github\workflows\dotnet-OrphanApps.yml` | oui | MyIA.AI.Notebooks/GenAI/Integrations-DotNet/**, MyIA.AI.Notebooks/GenAI/Vibe-Cod | non | non |  |
| `.github\workflows\dotnet-Shared.Tests.yml` | oui | MyIA.AI.Shared/**, MyIA.AI.Shared.Tests/**, .github/workflows/dotnet-Shared.Test | non | non |  |
| `.github\workflows\enrich-quality-gate.yml` | oui | MyIA.AI.Notebooks/**/*.ipynb, scripts/notebook_tools/scan_enrich_quality.py, scr | non | non |  |
| `.github\workflows\gametheory-tests.yml` | oui | MyIA.AI.Notebooks/GameTheory/**, .github/workflows/gametheory-tests.yml | non | non |  |
| `.github\workflows\harness-coauthor-guard.yml` | oui | .claude/skills/**, .claude/agents/**, .claude/commands/**, .claude/rules/**, .gi | non | non |  |
| `.github\workflows\hooks-parity.yml` | oui | .pre-commit-config.yaml, .github/workflows/hooks-parity.yml, scripts/check_hooks | non | non |  |
| `.github\workflows\ict-tests.yml` | oui | MyIA.AI.Notebooks/IIT/ICT-Series/**, .github/workflows/ict-tests.yml | non | non |  |
| `.github\workflows\label-paths-guard.yml` | oui | .github/workflows/**, scripts/check_workflow_label_paths.py, scripts/tests/test_ | non | oui |  |
| `.github\workflows\lean-argumentation.yml` | oui | MyIA.AI.Notebooks/SymbolicAI/Tweety/argumentation_lean/**.lean, MyIA.AI.Notebook | non | non |  |
| `.github\workflows\lean-assignment.yml` | oui | MyIA.AI.Notebooks/GameTheory/assignment_lean/**.lean, MyIA.AI.Notebooks/GameTheo | non | non |  |
| `.github\workflows\lean-asymmetric-information.yml` | oui | MyIA.AI.Notebooks/GameTheory/asymmetric_information_lean/**.lean, MyIA.AI.Notebo | non | non |  |
| `.github\workflows\lean-calibration.yml` | oui | MyIA.AI.Notebooks/SymbolicAI/Lean/calibration_lean/**.lean, MyIA.AI.Notebooks/Sy | non | non |  |
| `.github\workflows\lean-conway-cgt.yml` | oui | MyIA.AI.Notebooks/GameTheory/conway_cgt_lean/**.lean, MyIA.AI.Notebooks/GameTheo | non | non |  |
| `.github\workflows\lean-conway.yml` | oui | MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean/**.lean, MyIA.AI.Notebooks/Symboli | non | non |  |
| `.github\workflows\lean-decision-theory.yml` | oui | MyIA.AI.Notebooks/Probas/decision_theory_lean/**.lean, MyIA.AI.Notebooks/Probas/ | non | non |  |
| `.github\workflows\lean-discrepancy.yml` | oui | MyIA.AI.Notebooks/Search/discrepancy_lean/**.lean, MyIA.AI.Notebooks/Search/disc | non | non |  |
| `.github\workflows\lean-erc20.yml` | oui | MyIA.AI.Notebooks/SymbolicAI/SmartContracts/erc20_lean/**.lean, MyIA.AI.Notebook | non | non |  |
| `.github\workflows\lean-finiteness.yml` | oui | MyIA.AI.Notebooks/SymbolicAI/Lean/finiteness_lean/**.lean, MyIA.AI.Notebooks/Sym | non | non |  |
| `.github\workflows\lean-formal-groups.yml` | oui | MyIA.AI.Notebooks/SymbolicAI/Lean/formal_groups_lean/**.lean, MyIA.AI.Notebooks/ | non | non |  |
| `.github\workflows\lean-galois.yml` | oui | MyIA.AI.Notebooks/SymbolicAI/Lean/galois_lean/**.lean, MyIA.AI.Notebooks/Symboli | non | non |  |
| `.github\workflows\lean-game-defs-ext.yml` | oui | MyIA.AI.Notebooks/GameTheory/lean_game_defs_ext/**.lean, MyIA.AI.Notebooks/GameT | non | non |  |
| `.github\workflows\lean-game-defs.yml` | oui | MyIA.AI.Notebooks/GameTheory/lean_game_defs/**.lean, MyIA.AI.Notebooks/GameTheor | non | non |  |
| `.github\workflows\lean-game-theory.yml` | oui | MyIA.AI.Notebooks/GameTheory/game_theory_lean/**.lean, MyIA.AI.Notebooks/GameThe | non | non |  |
| `.github\workflows\lean-grothendieck.yml` | oui | MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean/**.lean, MyIA.AI.Notebooks/S | non | non |  |
| `.github\workflows\lean-hecke.yml` | oui | MyIA.AI.Notebooks/SymbolicAI/Lean/hecke_lean/**.lean, MyIA.AI.Notebooks/Symbolic | non | non |  |
| `.github\workflows\lean-i18n-drift.yml` | oui | **/*.lean, scripts/lean/check_i18n_siblings.py, .github/workflows/lean-i18n-drif | non | non |  |
| `.github\workflows\lean-kelly.yml` | oui | MyIA.AI.Notebooks/QuantConnect/kelly_lean/**.lean, MyIA.AI.Notebooks/QuantConnec | non | non |  |
| `.github\workflows\lean-knot.yml` | oui | MyIA.AI.Notebooks/SymbolicAI/Lean/knot_lean/**.lean, MyIA.AI.Notebooks/SymbolicA | non | non |  |
| `.github\workflows\lean-learning-theory.yml` | oui | MyIA.AI.Notebooks/ML/learning_theory_lean/**.lean, MyIA.AI.Notebooks/ML/learning | non | non |  |
| `.github\workflows\lean-mathlib-examples.yml` | oui | MyIA.AI.Notebooks/SymbolicAI/Lean/mathlib_examples/**.lean, MyIA.AI.Notebooks/Sy | non | non |  |
| `.github\workflows\lean-mimo.yml` | oui | MyIA.AI.Notebooks/SymbolicAI/Lean/mimo_lean/**.lean, MyIA.AI.Notebooks/SymbolicA | non | non |  |
| `.github\workflows\lean-minimax.yml` | oui | MyIA.AI.Notebooks/GameTheory/minimax_lean/**.lean, MyIA.AI.Notebooks/GameTheory/ | non | non |  |
| `.github\workflows\lean-percolation.yml` | oui | MyIA.AI.Notebooks/Probas/Applications/Percolation/percolation_lean/**.lean, MyIA | non | non |  |
| `.github\workflows\lean-planning.yml` | oui | MyIA.AI.Notebooks/SymbolicAI/Planners/planning_lean/**.lean, MyIA.AI.Notebooks/S | non | non |  |
| `.github\workflows\lean-search.yml` | oui | MyIA.AI.Notebooks/Search/search_lean/**.lean, MyIA.AI.Notebooks/Search/search_le | non | non |  |
| `.github\workflows\lean-sensitivity.yml` | oui | MyIA.AI.Notebooks/SymbolicAI/Lean/sensitivity_lean/**.lean, MyIA.AI.Notebooks/Sy | non | non |  |
| `.github\workflows\lean-social-choice-peters.yml` | oui | MyIA.AI.Notebooks/GameTheory/social_choice_lean_peters/**.lean, MyIA.AI.Notebook | non | non |  |
| `.github\workflows\lean-social-choice.yml` | oui | MyIA.AI.Notebooks/GameTheory/game_theory_lean/SocialChoice/**.lean, MyIA.AI.Note | non | non |  |
| `.github\workflows\lean-sudoku.yml` | oui | MyIA.AI.Notebooks/Sudoku/sudoku_lean/**.lean, MyIA.AI.Notebooks/Sudoku/sudoku_le | non | non |  |
| `.github\workflows\lean-visibility-advisory.yml` | oui | **/*_lean/**/*.lean, .github/workflows/lean-visibility-advisory.yml | non | oui |  |
| `.github\workflows\manifest-description-visuelle-gate.yml` | oui | MyIA.AI.Notebooks/**/assets/readme/MANIFEST.md, scripts/notebook_tools/detect_ma | non | non |  |
| `.github\workflows\markdown-claims-output-advisory.yml` | oui | MyIA.AI.Notebooks/**/*.ipynb, scripts/check_markdown_claims_output.py, scripts/t | non | non |  |
| `.github\workflows\markdown-rendering-guard.yml` | oui | **.ipynb, _quarto.yml, scripts/notebook_tools/detect_markdown_rendering.py, scri | non | non |  |
| `.github\workflows\ml-tests.yml` | oui | MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/scripts/**, tests/**, pytest | non | non |  |
| `.github\workflows\notebook-cell-source-parses.yml` | oui | **.ipynb, scripts/notebook_tools/check_cell_source_parses.py, .github/workflows/ | non | non |  |
| `.github\workflows\notebook-exec-sequence-ratchet.yml` | oui | **.ipynb, scripts/notebook_tools/check_exec_sequence.py, scripts/notebook_tools/ | non | non |  |
| `.github\workflows\notebook-execution-required.yml` | oui | **.ipynb, scripts/notebook_tools/golden_set.yml, scripts/notebook_tools/golden_s | non | non |  |
| `.github\workflows\notebook-interp-positioning.yml` | oui | MyIA.AI.Notebooks/**/*.ipynb, scripts/notebook_tools/check_interp_positioning.py | non | non |  |
| `.github\workflows\notebook-latex-control-chars.yml` | oui | **.ipynb, scripts/notebook_tools/check_latex_control_chars.py, .github/workflows | non | non |  |
| `.github\workflows\notebook-link-render-check.yml` | oui | MyIA.AI.Notebooks/**/README.md, scripts/notebook_tools/check_notebook_link_rende | non | non |  |
| `.github\workflows\notebook-navlink-check.yml` | oui | **/*.ipynb, scripts/notebook_tools/check_notebook_navlinks.py, scripts/tests/bas | non | non |  |
| `.github\workflows\notebook-papermill-ratchet.yml` | oui | **.ipynb, scripts/notebook_tools/check_papermill_ratchet.py, .github/workflows/n | non | non |  |
| `.github\workflows\notebook-plan-loss-gate.yml` | oui | (none) | non | non | #14391/#14429 |
| `.github\workflows\notebook-validation.yml` | oui | **.ipynb | non | non |  |
| `.github\workflows\orphaned-delivery-scan.yml` | oui | (none) | oui | non |  |
| `.github\workflows\owui-playwright-check.yml` | oui | MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/Open-WebUI/Playwright-OWU | non | non |  |
| `.github\workflows\pedagogy-density-advisory.yml` | oui | scripts/notebook_tools/pedagogy_density_baseline.json, MyIA.AI.Notebooks/**, .gi | non | oui |  |
| `.github\workflows\perimeter-review-guard.yml` | oui | (none) | non | non | #11268 |
| `.github\workflows\pip-leak-guard.yml` | oui | **.ipynb, scripts/notebook_tools/audit_pip_install_cells.py, scripts/notebook_to | non | non |  |
| `.github\workflows\pr-gate.yml` | oui | (none) | non | non | #10600 |
| `.github\workflows\prose-counts-guard.yml` | oui | **/*.ipynb, **/*.md | non | non |  |
| `.github\workflows\quantconnect-notebook-freshness.yml` | oui | MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/**/*.ipynb, scripts/check_qu | non | non |  |
| `.github\workflows\quarto-pages-deploy.yml` | oui | _quarto.yml, **.qmd, MyIA.AI.Notebooks/**/index.qmd, MyIA.AI.Notebooks/**/*.ipyn | non | non |  |
| `.github\workflows\scan-md-hierarchy-drift.yml` | oui | MyIA.AI.Notebooks/**/*.ipynb, scripts/notebook_tools/scan_md_hierarchy.py, scrip | non | non |  |
| `.github\workflows\scripts-tests.yml` | oui | scripts/**, tests/**, pytest.ini, .github/workflows/scripts-tests.yml, .github/w | non | non |  |
| `.github\workflows\secret-scan.yml` | oui | (none) | non | non | #10600 |
| `.github\workflows\slides-composition-pr-relay.yml` | oui | slides/** | non | non |  |
| `.github\workflows\solution-leak-guard.yml` | oui | **.ipynb, scripts/notebook_tools/audit_solution_leaks.py, scripts/notebook_tools | non | non |  |
| `.github\workflows\source-output-ratchet.yml` | oui | **/*.ipynb, scripts/notebook_tools/check_source_output_ratchet.py, .github/workf | non | non |  |
| `.github\workflows\translation-drift.yml` | oui | MyIA.AI.Notebooks/**/*.ipynb, translations/**, scripts/translation/** | non | non |  |
| `.github\workflows\translation-guard.yml` | oui | .github/workflows/translation-guard.yml, scripts/ci/translation_override_require | non | non |  |
| `.github\workflows\twin-attestation-name-guard.yml` | oui | scripts/notebook_tools/twin_pairs.d/** | non | non |  |
| `.github\workflows\twin-parity.yml` | oui | scripts/notebook_tools/twin_pairs.d/**, scripts/notebook_tools/check_twin_parity | non | non |  |
| `.github\workflows\unique-check-run-names-guard.yml` | oui | .github/workflows/**, scripts/ci/check_unique_check_run_names.py, scripts/pr_gat | non | non |  |
| `.github\workflows\validation-matrix.yml` | oui | **.ipynb, scripts/validation/** | non | non |  |

## Fan-out estime par type de PR

| Type de PR | Workflows declenches | Reduction vs SANS paths |
|------------|---------------------|--------------------------|
| markdown-only | **8** | reduction vs total pulls |
| notebook-only | **22** | reduction vs total pulls |
| scripts-only | **8** | reduction vs total pulls |
| workflows-only | **10** | reduction vs total pulls |
| docs-only | **8** | reduction vs total pulls |
| pr-target-main | **85** | reduction vs total pulls |
