---
name: Infer.NET notebook series structure
description: Pedagogical structure and quality status of all 20 Infer.NET notebooks
type: project
---

All 20 notebooks in the series are at `D:\dev\CoursIA\MyIA.AI.Notebooks\Probas\Infer\`.

**Structure verified:** All 20 notebooks have the required pedagogical elements:
- Navigation header (title, Serie X/20, Duree, Prerequis)
- Objectifs section
- Navigation table (Precedent / Suivant)
- Resume section at end of major sections
- Section introductions before code cells
- Result interpretation cells after inference outputs

**Numbering fix:** DONE as of 2026-03-16 (all now show X/20, not X/13)

**Series structure:**
- Notebooks 1-13: Core probabilistic programming concepts
- Notebooks 14-20: Decision theory (already had correct X/20 from creation)

**Key technical notes:**
- These are C# .NET Interactive notebooks (kernel: polyglot-notebook)
- Must use `CompilerChoice.Roslyn` in all InferenceEngine instances
- FactorGraphHelper.cs is loaded via `#load "FactorGraphHelper.cs"` for visualization
- Infer-13 uses older cell ID format (cell-0, cell-1, ...) instead of UUID format
- Infer-12 and several others exceed 25000 tokens - use Grep to inspect rather than Read

**Quality status after 2026-03-16 review:**
- No emojis found anywhere in the series
- No unresolved TODOs (2 intentional exercise placeholders in Infer-17 and Infer-19)
- All notebooks have correct pedagogical structure
- Main fix needed was the series numbering (X/13 -> X/20)

**Remaining work (as of 2026-03-16):**
- Git commit with message `fix(probas): corriger numerotation serie (X/13 -> X/20) dans Infer-1 a Infer-13`
- Consider deeper review of code quality in each notebook
