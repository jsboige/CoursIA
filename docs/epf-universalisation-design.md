# EPF Universalisation Design — Phase 1

**Status**: DESIGN (doc-only, no code changes)
**Author**: po-2023 (Cycle 17, T21.13)
**Date**: 2026-05-10
**Directive**: User 2026-05-10 — "Le repertoire Notebooks/EPF n'a pas pas vocation a rester. Hormis la session ESGF 2026 en cours, le reste doit devenir universel, sans particularites d'ecoles."

## 1. Inventaire complet

### 1.1 MyIA.AI.Notebooks/EPF/ (4 notebooks, 2 projects)

| # | Current path | Type | Content | Tech |
|---|-------------|------|---------|------|
| 1 | `EPF/IA101-Devoirs/CC1-Exploratoire-Symbolique/CC1-Diagnostic-Medical.ipynb` | Student skeleton | Diagnostic medical: A* search, genetic algorithm, Z3 validation | Python, z3-solver, heapq |
| 2 | `EPF/IA101-Devoirs/CC1-Exploratoire-Symbolique/CC1-Diagnostic-Medical-corrigé.ipynb` | Solution | Same, completed | Python, z3-solver |
| 3 | `EPF/IA101-Devoirs/CC2-Symbolique-Probabiliste/enonce/CC2_OncoPlan_Squelette.ipynb` | Student skeleton | Oncology planning: CSP/OR-Tools, Pyro probabilistic, RDF ontology | Python, pyro-ppl, ortools |
| 4 | `EPF/IA101-Devoirs/CC2-Symbolique-Probabiliste/corrige/CC2_OncoPlan_Corrige.ipynb` | Solution | Same, completed | Python, pyro-ppl, ortools |

**Supporting files**:
- `EPF/IA101-Devoirs/CC1-Exploratoire-Symbolique/data/patients.csv`
- `EPF/IA101-Devoirs/CC1-Exploratoire-Symbolique/enonce/sujet.md`
- `EPF/IA101-Devoirs/CC1-Exploratoire-Symbolique/README.md`
- `EPF/IA101-Devoirs/CC2-Symbolique-Probabiliste/enonce/sujet.md`
- `EPF/IA101-Devoirs/CC2-Symbolique-Probabiliste/enonce/ressources/patients_oncology.csv`
- `EPF/IA101-Devoirs/CC2-Symbolique-Probabiliste/README.md`
- `EPF/requirements.txt`
- `EPF/README.md` (CATALOG-STATUS marker: series=EPF, pedagogical_count=4)

### 1.2 MyIA.AI.Notebooks/GenAI/EPF/ (4 notebooks, 4 projects)

| # | Current path | Type | Content | Tech |
|---|-------------|------|---------|------|
| 5 | `GenAI/EPF/Carole & Cléo/barbie-schreck.ipynb` | Student showcase | Barbie/Shrek hybrid image generation | OpenAI DALL-E, PIL |
| 6 | `GenAI/EPF/Dorian & Bastien/cuisine/receipe_maker.ipynb` | Student showcase | Recipe generator with SK agents | Semantic Kernel, OpenAI |
| 7 | `GenAI/EPF/Dorian & Bastien/cuisine/receipe_maker_output.ipynb` | Exec output | Papermill execution output | — |
| 8 | `GenAI/EPF/Louise et Jeanne Céline/medical_chatbot.ipynb` | Student showcase | Medical chatbot with SK agents | Semantic Kernel, OpenAI |
| 9 | `GenAI/EPF/Louise et Jeanne Céline/medical_chatbot_output.ipynb` | Exec output | Papermill execution output | — |
| 10 | `GenAI/EPF/fort-boyard-python.ipynb` | Student showcase | Fort Boyard interactive game | OpenAI GPT |

**Supporting files**:
- `GenAI/EPF/Carole & Cléo/README.md`
- `GenAI/EPF/Dorian & Bastien/cuisine/README.md`
- `GenAI/EPF/Louise et Jeanne Céline/README.md`
- `GenAI/EPF/README.md`

### 1.3 Total

- **10 notebooks** (4 exam + 4 showcases + 2 output files)
- **10 supporting files** (data, subjects, READMEs, requirements)
- **2 top-level READMEs** with CATALOG-STATUS markers

## 2. Mapping migration

### 2.1 EPF/IA101-Devoirs → CaseStudies/

Both CC1 and CC2 are cross-cutting case studies that span Search, SymbolicAI, and Probas. They don't belong under a single thematic series. A top-level `CaseStudies/` directory groups interdisciplinary projects.

| # | Current path | Target path |
|---|-------------|-------------|
| - | `EPF/IA101-Devoirs/CC1-Exploratoire-Symbolique/` | `CaseStudies/Diagnostic-Medical/` |
| 1 | `CC1-Diagnostic-Medical.ipynb` | `student/Diagnostic-Medical.ipynb` |
| 2 | `CC1-Diagnostic-Medical-corrigé.ipynb` | `solution/Diagnostic-Medical.ipynb` |
| - | `data/patients.csv` | `data/patients.csv` |
| - | `enonce/sujet.md` | `subject.md` |
| - | `README.md` | `README.md` (updated) |
| - | `EPF/IA101-Devoirs/CC2-Symbolique-Probabiliste/` | `CaseStudies/Oncology-Planning/` |
| 3 | `enonce/CC2_OncoPlan_Squelette.ipynb` | `student/Oncology-Planning.ipynb` |
| 4 | `corrige/CC2_OncoPlan_Corrige.ipynb` | `solution/Oncology-Planning.ipynb` |
| - | `enonce/sujet.md` | `subject.md` |
| - | `enonce/ressources/patients_oncology.csv` | `data/patients_oncology.csv` |
| - | `README.md` | `README.md` (updated) |
| - | `EPF/requirements.txt` | `CaseStudies/requirements.txt` |

**Naming decisions**:
- `enonce/` → `student/` (universal English term)
- `corrige/` → `solution/` (universal English term)
- `CC1-Diagnostic-Medical` → `Diagnostic-Medical` (drop exam prefix)
- `CC2_OncoPlan` → `Oncology-Planning` (descriptive, drop exam prefix)
- `sujet.md` → `subject.md` (English)

### 2.2 GenAI/EPF/ → GenAI/CaseStudies/

GenAI student projects stay under GenAI but move to a neutral `CaseStudies/` subdirectory. Author names are preserved as attribution (showcase, not exam).

| # | Current path | Target path |
|---|-------------|-------------|
| 5 | `GenAI/EPF/Carole & Cléo/barbie-schreck.ipynb` | `GenAI/CaseStudies/Barbie-Schreck/barbie-schreck.ipynb` |
| 6 | `GenAI/EPF/Dorian & Bastien/cuisine/receipe_maker.ipynb` | `GenAI/CaseStudies/Recipe-Maker/receipe_maker.ipynb` |
| 7 | `GenAI/EPF/Dorian & Bastien/cuisine/receipe_maker_output.ipynb` | `GenAI/CaseStudies/Recipe-Maker/receipe_maker_output.ipynb` |
| 8 | `GenAI/EPF/Louise et Jeanne Céline/medical_chatbot.ipynb` | `GenAI/CaseStudies/Medical-Chatbot/medical_chatbot.ipynb` |
| 9 | `GenAI/EPF/Louise et Jeanne Céline/medical_chatbot_output.ipynb` | `GenAI/CaseStudies/Medical-Chatbot/medical_chatbot_output.ipynb` |
| 10 | `GenAI/EPF/fort-boyard-python.ipynb` | `GenAI/CaseStudies/Fort-Boyard/fort-boyard-python.ipynb` |

**Naming decisions**:
- Drop student name directories (Carole & Cléo → Barbie-Schreck)
- Use descriptive project name as directory (Recipe-Maker, Medical-Chatbot)
- Preserve author attribution in README.md and notebook headers
- `fort-boyard-python.ipynb` gets its own directory for consistency

### 2.3 Directories to remove after migration

| Path | Action |
|------|--------|
| `EPF/IA101-Devoirs/` | Remove (recursively, after git mv) |
| `EPF/` | Remove entirely |
| `GenAI/EPF/` | Remove entirely |

### 2.4 Preserve (no changes)

| Path | Reason |
|------|--------|
| `GradeBookApp/` | EPF grading configs are grading-specific, not notebook paths |
| `slides/` | EPF school mentions in slide attributions are contextual |
| `QuantConnect/ESGF-2026/` | Active session, user directive: never touch |
| `MyIA.AI.Notebooks/Search/` | EPF references in README are attributions ("adapted from EPF 2025"), not path references |

## 3. README updates

### 3.1 Files to create

| Path | Content |
|------|---------|
| `CaseStudies/README.md` | New series README with CATALOG-STATUS marker (series: CaseStudies) |
| `GenAI/CaseStudies/README.md` | New sub-series README |

### 3.2 Files to modify

| File | Changes |
|------|---------|
| `MyIA.AI.Notebooks/README.md` | Replace `EPF/ (4)` row with `CaseStudies/ (4)`, update structure tree |
| `MyIA.AI.Notebooks/GenAI/README.md` | Replace EPF section with CaseStudies, update CATALOG breakdown |
| `CaseStudies/Diagnostic-Medical/README.md` | Renamed from CC1 README, remove CC1/EPF/IA101 references, keep pedagogical content |
| `CaseStudies/Oncology-Planning/README.md` | Renamed from CC2 README, remove CC2/EPF/IA101 references, keep pedagogical content |
| `GenAI/CaseStudies/Barbie-Schreck/README.md` | Updated from Carole & Cléo README |
| `GenAI/CaseStudies/Recipe-Maker/README.md` | Updated from Dorian & Bastien cuisine README |
| `GenAI/CaseStudies/Medical-Chatbot/README.md` | Updated from Louise et Jeanne Céline README |

### 3.3 Files to leave as-is

| File | Reason |
|------|--------|
| `GradeBookApp/README.md` | Grading system references EPF as school, not path |
| `GradeBookApp/configs/README.md` | Same |
| `slides/README.md` | School attributions in pedagogical slides |
| `MyIA.AI.Notebooks/Search/README.md` | Attribution ("EPF 2025"), not path references |

## 4. Git strategy

All moves use `git mv` to preserve file history.

```
Phase 2 commit sequence (single PR):

1. Create target directories
   mkdir -p CaseStudies/Diagnostic-Medical/{student,solution,data}
   mkdir -p CaseStudies/Oncology-Planning/{student,solution,data}
   mkdir -p GenAI/CaseStudies/{Barbie-Schreck,Recipe-Maker,Medical-Chatbot,Fort-Boyard}

2. git mv EPF content → CaseStudies/
   git mv EPF/IA101-Devoirs/CC1-Exploratoire-Symbolique/CC1-Diagnostic-Medical.ipynb \
          CaseStudies/Diagnostic-Medical/student/Diagnostic-Medical.ipynb
   git mv EPF/IA101-Devoirs/CC1-Exploratoire-Symbolique/CC1-Diagnostic-Medical-corrigé.ipynb \
          CaseStudies/Diagnostic-Medical/solution/Diagnostic-Medical.ipynb
   git mv EPF/IA101-Devoirs/CC1-Exploratoire-Symbolique/data/patients.csv \
          CaseStudies/Diagnostic-Medical/data/patients.csv
   git mv EPF/IA101-Devoirs/CC1-Exploratoire-Symbolique/enonce/sujet.md \
          CaseStudies/Diagnostic-Medical/subject.md
   # ... (same pattern for CC2 and all GenAI/EPF projects)

3. Update READMEs
   # Rewrite READMEs with neutral naming
   # Update MyIA.AI.Notebooks/README.md
   # Update MyIA.AI.Notebooks/GenAI/README.md

4. Remove empty EPF directories
   git rm EPF/README.md EPF/requirements.txt
   git rm GenAI/EPF/README.md
   # rmdir remaining empty dirs

5. Regenerate CATALOG
   python scripts/notebook_tools/expand_catalog_markers.py --check
```

## 5. CATALOG-STATUS updates

| Marker location | Current | After migration |
|----------------|---------|-----------------|
| `EPF/README.md` | `series: EPF, count: 4` | REMOVED |
| `GenAI/EPF/README.md` | (part of GenAI breakdown) | REMOVED |
| `CaseStudies/README.md` | N/A | `series: CaseStudies, count: 4` (new) |
| `GenAI/README.md` breakdown | `EPF=4` | `CaseStudies=4` |
| `MyIA.AI.Notebooks/README.md` breakdown | `EPF=4` | `CaseStudies=4` |
| `COURSE_CATALOG.generated.json` | EPF entries | CaseStudies entries (auto-regenerated) |

## 6. Validation checklist (Phase 2 — pre-merge)

- [ ] `git log --follow CaseStudies/Diagnostic-Medical/student/Diagnostic-Medical.ipynb` shows original history
- [ ] `git log --follow CaseStudies/Oncology-Planning/student/Oncology-Planning.ipynb` shows original history
- [ ] `grep -r "EPF" MyIA.AI.Notebooks/ --include="*.md"` returns 0 matches in notebook READMEs
- [ ] `grep -r "CC1\|CC2" MyIA.AI.Notebooks/ --include="*.md"` returns 0 in CaseStudies paths (attribution in Search README is OK)
- [ ] `grep -r "IA101-Devoirs" MyIA.AI.Notebooks/` returns 0 matches
- [ ] All READMEs have correct relative links to new paths
- [ ] `COURSE_CATALOG.generated.json` regenerated via `expand_catalog_markers.py`
- [ ] `COURSE_CATALOG.generated.md` regenerated
- [ ] GradeBookApp configs still reference correct notebook paths (or document the discrepancy)
- [ ] Notebook internal cross-references updated (e.g., `../../EPF/` links in markdown cells)
- [ ] `find MyIA.AI.Notebooks/EPF -type f` returns 0 (directory fully removed)

## 7. Risk assessment

| Risk | Mitigation |
|------|-----------|
| Broken cross-references in notebooks | Grep for `../../EPF/`, `../EPF/`, `EPF/` in all .ipynb before commit |
| GradeBookApp path mismatch | GradeBookApp references grading configs, not notebook paths directly — verify |
| CATALOG drift | Run `expand_catalog_markers.py --check` after all moves |
| Large diff (git mv = delete + add) | `git log --follow` confirms history preserved — explain in PR body |
| Student attribution lost | README files preserve author names; notebooks unchanged internally |

## 8. Scope boundaries

**In scope (Phase 2 — po-2025)**:
- Physical `git mv` of all files listed in Section 2
- README updates listed in Section 3
- CATALOG regeneration
- Validation checklist Section 6

**Out of scope**:
- GradeBookApp config changes (grading system, separate concern)
- Slides updates (pedagogical context, not notebook paths)
- Search README attribution changes ("EPF 2025" is historical context, not path reference)
- Any notebook content changes (source code, markdown cells inside notebooks)
- ESGF-2026 content (user directive: preserve)
