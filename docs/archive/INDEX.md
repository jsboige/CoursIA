# INDEX — Archives docs/

**Archive le** : 2026-06 (docs-reorg S3, See #2456).
**Theme** : Documents archives du repertoire `docs/` — investigations closes, audits datats, references historiques.

Ces documents sont conserves pour reference mais ne sont plus actifs. Ne pas modifier sans justification.

## Fichiers racine

| Fichier | Resume |
|---------|--------|
| 01-cartographie-initiale.md | Cartographie initiale du projet CoursIA |
| 02-etude-adk-deepmind.md | Etude DeepMind ADK |
| 03-plan-formation-datascience-agentique.md | Plan formation data science agentique |
| GROTHENDIECK_MATHLIB_MAP.md | Map Mathlib pour le projet Grothendieck |
| H7_P2_DOCKER_ERROR_CATALOG.md | Catalog erreurs Docker H7/P2 |
| NOTEBOOK_ENV_COVERAGE.md | Couverture environnements notebooks |
| REVERSE_PROXY_CIRCUIT.md | Reverse proxy circuit |
| dette-branches-audit-2026-05-27.md | Audit dette branches (mai 2026) |
| env-audit-cluster-2026-05-10.md | Audit environnements cluster (mai 2026) |
| epf-universalisation-design.md | Design universalisation EPF |
| epic-1028-audiobook-postmortem.md | Postmortem audiobook (Epic #1028) |
| genai-images-mission-complete.md | Mission complete images GenAI |
| genai-services-inventory-2026-05.md | Inventory services GenAI (mai 2026) |
| genai-stack-audit-2026-05-10.md | Audit stack GenAI (mai 2026) |
| handson-book-mapping.md | Cartographie du livre Hands-On AI Trading (Jared Broad) |
| integration-roadmap.md | Roadmap integration |
| qc-broken-strategies-audit.md | Audit strategies QuantConnect broken |
| qc-league-ece.md | League ECE QuantConnect |
| qc-stabilization-phase2.md | Stabilisation QC phase 2 |
| slides-refonte-procedure.md | Procedure refonte slides |
| stabilization-phase1-matrix.md | Matrice stabilization phase 1 |

## Sous-repertoires

| Repertoire | Contenu | INDEX |
|-------------|---------|-------|
| investigation-mcp-nuget/ | 26 fichiers d'investigation MCP Jupyter / NuGet / .NET Interactive | [INDEX.md](investigation-mcp-nuget/INDEX.md) |
| genai/ | 13+ fichiers infrastructure GenAI detaillee | [README.md](genai/README.md) |
| suivis/genai-image/ | 8 fichiers + 4 repertoires de phases (ComfyUI/Qwen) | [INDEX.md](suivis/genai-image/INDEX.md) |
| curriculum-renumbering-phase1/ | 6 fichiers (Texte, Video, Infer, PyMC, Search, Planners) — analyses phase-1 #5081 verdict NO-RENUMBER archivées 2026-07-19 (c.676 GenAI Texte+Video) + 2026-07-20 (c.748 Probas/Infer, Probas/PyMC, Search) + 2026-07-20 (c.695 Planners, dernier dispatch phase-1, owner-dispatch po-2026 anti-contamination L420) | — |
| lean-intractable-diagnosis/ | 1 fichier (stable-marriage.md) — diagnostic daté 2026-05-18 des 6 sorrys intractables post-rural-hospitals-formalization, archivé 2026-07-20 (c.696, owner-dispatch po-2026 Lean core, superseded-by absorption StableMarriage dans game_theory_lean/ #4365, KB prover `intractable_targets.json` mise à jour) | — |
| ledgers-reviews/ | 54 fichiers sweeps §H.4/B/D datés PM transiente (juillet 2026) — verdicts EXEC_PROVED datés préservés verbatim, archivés 2026-07-19 (c.736) | — |
| po2026-local-build-troubleshooting.md | 1 fichier (102 lignes) — diagnostic daté 2026-07-16 des 4 modes d'échec `lake build` po-2026 + recette de récupération (c.466-c.469, c.473 validée knot_lean), **1 inbound reference** sur `origin/main` (`docs/reference/scripts-reference.md` L158 mise à jour c.700). **Procédure codifiée** dans `scripts/lean/po2026_recover_build.py` (309 lignes, idempotent, recette canonique B). Leçon durable dans `MEMORY.md` L502. Archivé 2026-07-20 (c.700, owner-dispatch po-2026 anti-contamination L420, See #7422 triage) | — |

## Issue de reference

Part of #1925 (EPIC refonte docs/). See #2456 (S3 archivage).
