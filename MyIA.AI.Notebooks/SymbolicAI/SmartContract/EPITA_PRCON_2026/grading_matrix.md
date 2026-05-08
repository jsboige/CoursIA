# EPITA PrCon 2026 — Grading Matrix

**Course**: SCIA Programmation par Contraintes
**Soutenances**: 18 mai + 22 mai 2026
**Repo**: `jsboigeEpita/2026-Epita-Programmation-par-Contraintes`
**Evaluation**: collegiale (pairs + enseignants), 4 criteres x 0-10, somme/2 = /20

---

## Group Overview

| Group | Topic | Sujet # | Members | Size Bonus | Files in Repo | PRs Merged | Last Activity |
|-------|-------|---------|---------|------------|---------------|------------|---------------|
| E4 | Allocation de validateurs PoS (Bin Packing) | E4 | Evariste BALVAY | +3 (solo) | README.md only | 1 PR (README init) | 22/04 |
| H1 | Composition Musicale Assistee par Contraintes | H1 | Louis Parmentier, Marianne Proux, Ethan Girard | 0 (trio) | README.md only | 1 PR (README) | 22/04 |
| H2 | Procedural Generation (WFC + CP-SAT) | H2 | Martin Couturier | +3 (solo) | wfc_cpsat.py, notebook.ipynb, tileset.json, tileset_cave.json | 2 PRs (WFC + cave tileset) | 21-22/04 |
| J1 | Allocation multicritere de candidats | J1 | Alexandre Bodin, Mark Delaloy (+?) | -1/+0? | FastAPI app, scoring, embedding, UI | 1 PR (full app) | 28/04-04/05 |
| I2 | Angles/Geometrie (CSP notebooks) | I2 | ANGLES, DEGUEST, HIEGEL | 0 (trio) | 4 notebooks in src/, demo/slides/resources = .gitkeep only | 1 PR (scaffolding) | 22/04 |

---

## Pre-Soutenance Assessment (as of 08/05/2026)

### Group E4 — Evariste BALVAY (solo, +3 bonus)

**Sujet**: E4 — Allocation de validateurs PoS en comites (Bin Packing + anti-affinite + dynamique temporelle)

| Dimension | Status | Observations |
|-----------|--------|-------------|
| **README quality** | EXCELLENT | Detailed formulation: variables, constraints (5 families), objective function (multi-criteria weighted), baselines (Ethereum random + PLNE), metrics, extensions. Most thorough README of all groups. |
| **CP modeling** | THEORETICAL ONLY | Full mathematical formulation present in README but no code committed. No CP-SAT implementation, no solver call, no results. |
| **Code** | ABSENT | Only README.md in folder. No Python files, no notebook, no solver code. |
| **Git activity** | MINIMAL | 1 commit (Ristoufe, 22/04). 21 days of inactivity since. |
| **Livrables** | MISSING | No notebook, no UI/demo, no slides, no code. |

**Risk**: SOLO project with zero code after 3 weeks. README quality suggests the student understands the theory but has not started implementation. Needs urgent delivery before soutenance.

---

### Group H1 — Composition Musicale (trio)

**Sujet**: H1 — Generation de partitions musicales via contraintes harmoniques, contrepoint et rythme

| Dimension | Status | Observations |
|-----------|--------|-------------|
| **README quality** | EXCELLENT | Full architecture (core/, constraints/, soft_constraints/, export/), music theory encoding (pitch/duration/voice as CP-SAT vars), harmonic representation (root/quality/degree), search space estimation (10^180), style variants (baroque/jazz/contemporary), MIDI export. Very well structured. |
| **CP modeling** | THEORETICAL ONLY | Complete modeling description in README but no code committed. No CP-SAT model, no constraint implementations. |
| **Code** | ABSENT | Only README.md in folder. No core/, no constraints/, no export/. Architecture described but not built. |
| **Git activity** | MINIMAL | 1 commit (Louis Parmentier, 22/04). No subsequent activity. |
| **Livrables** | MISSING | No notebook, no UI, no MIDI export, no slides. |

**Risk**: Trio with excellent theoretical groundwork but zero implementation. Architecture design is promising but requires substantial coding effort.

---

### Group H2 — Procedural Generation WFC (solo, +3 bonus)

**Sujet**: H2 — Wave Function Collapse as CP-SAT constraint satisfaction

| Dimension | Status | Observations |
|-----------|--------|-------------|
| **README quality** | N/A (no separate README) | Code + notebook serve as documentation. |
| **CP modeling** | IMPLEMENTED | `wfc_cpsat.py`: CP-SAT model with adjacency constraints, floor ratio bounds, object placement (enemies/keys/chests), difficulty proportional to area, connectivity via flow/reachability booleans. Also implements pure WFC (AC-3 propagation + entropy collapse + backtracking) and random baseline for comparison. |
| **Code quality** | GOOD | Clean Python, well-structured (tileset loading, 3 generation modes), proper type hints, OR-Tools CP-SAT usage. ~400+ lines. Two tilesets (dungeon + cave). |
| **Notebook** | PRESENT | 387KB notebook.ipynb with visualizations and analysis. |
| **Git activity** | MODERATE | 2 student commits (21/04), 1 teacher fix (22/04). Commits show iterative development (base WFC, then cave tileset + global constraints). |

**Assessment**: Most advanced group. Solo student with working CP-SAT implementation, multiple generation modes, and a substantial notebook. The connectivity constraint via flow modeling is particularly noteworthy.

---

### Group J1 — Allocation multicritere de candidats

**Sujet**: J1 — Matching candidats/postes avec scoring multicritere

| Dimension | Status | Observations |
|-----------|--------|-------------|
| **Code quality** | GOOD (for what it is) | FastAPI app with Pydantic models, embedding-based scoring, static UI, JSON storage. Clean structure (models, scoring, storage, embedding_client). |
| **CP solver usage** | ABSENT | No CP-SAT, no OR-Tools, no constraint solver. Uses weighted cosine similarity + lexical overlap for scoring. This is an **embedding/ML matching system**, not a constraint programming project. |
| **Git activity** | MODERATE | 3 commits (22/04, 28/04, 28/04), showing iterative development. |
| **Tech stack** | FastAPI + uvicorn + embeddings | Modern web stack but fundamentally wrong approach for a CP course project. |

**Critical Issue**: This group built a web app with embedding-based scoring but **did not use any constraint solver**. The project subject was "Allocation multicritere de candidats" which should involve CP-SAT or SAT-based matching with hard/soft constraints. The current implementation is a weighted scoring system, not a constraint satisfaction problem. This is a **fundamental misalignment** with the course requirements.

---

### Group I2 — ANGLES, DEGUEST, HIEGEL (trio)

**Sujet**: I2 — CSP notebooks (Fundamentals, Optimization, Hybridization, Soft Constraints)

| Dimension | Status | Observations |
|-----------|--------|-------------|
| **File structure** | SCAFFOLDING ONLY | 4 notebooks listed in src/ (CSP-1, CSP-5, CSP-6, CSP-7) but `demo/`, `slides/`, `resources/` contain only `.gitkeep`. The src/ directory also shows `.gitkeep` as the only file with content. Notebooks may be empty or template copies from the course material. |
| **CP modeling** | UNCLEAR | Cannot verify notebook content via API. Names suggest they follow the course notebook structure (CSP-1 Fundamentals through CSP-7 Soft). |
| **Code** | MINIMAL/TEMPLATE | If notebooks are copies of course templates without substantial additions, this counts as minimal work. |
| **Git activity** | MINIMAL | 1 scaffolding commit (22/04, cherry-picked from PR #13). No student commits visible. |
| **Livrables** | INCOMPLETE | No demo, no slides, no original code visible. |

**Risk**: Trio with scaffolding only. The notebook names match existing course material (Search/Part2-CSP/), suggesting possible reuse without original contribution. Needs verification during soutenance.

---

## Evaluation Criteria (per README)

| Criteres | Points | Description |
|----------|--------|-------------|
| Qualite de la presentation | 0-10 | Communication, clarte, pedagogie, slides, demonstrations |
| Qualite theorique | 0-10 | Principes CP/CSP utilises, classes d'algorithmes, contexte historique, explication des performances et limitations |
| Qualite technique | 0-10 | Livrables (code, notebook, UI), qualite du code, commits Git, demonstrations, resultats, perspectives |
| Organisation | 0-10 | Planning, repartition des taches, collaboration, activite Git, documentation |

**Note finale = somme / 2** (echelle /20), ajustee des bonus/malus taille + bonus TP.

---

## Grading Matrix (Pre-Soutenance Estimates)

> These are **provisional** assessments based on repository state as of 08/05/2026.
> Final grades determined during soutenance (18+22 mai) by collegial evaluation.

| Group | Presentation | Theorique | Technique | Organisation | Raw Score | Size Adj. | Est. /20 |
|-------|-------------|-----------|-----------|-------------|-----------|-----------|----------|
| **E4** (solo) | ? | 7-8 (README excellent) | 1-2 (no code) | 2-3 (1 commit, 21d inactive) | 10-13 | +3 | ~8-10/20 |
| **H1** (trio) | ? | 7-8 (README excellent) | 1-2 (no code) | 2-3 (1 commit, inactive) | 10-13 | 0 | ~5-7/20 |
| **H2** (solo) | ? | 6-7 (CP-SAT + WFC theory) | 7-8 (working code + notebook) | 5-6 (2 commits, iterative) | 18-21 | +3 | ~12-12.5/20 |
| **J1** | ? | 2-3 (no CP theory used) | 6-7 (good web app) | 5-6 (3 commits, iterative) | 13-16 | 0 | ~6.5-8/20 |
| **I2** (trio) | ? | ? (unverifiable) | 2-3 (scaffolding only) | 2-3 (no student commits) | ? | 0 | ~2-5/20 |

### Key Concerns for Soutenance

1. **E4, H1**: Excellent theoretical understanding (README quality) but zero implementation. The soutenance must demonstrate whether code was developed locally but not pushed, or if the groups are genuinely behind.

2. **J1**: Fundamental misalignment — web app with embedding scoring instead of CP solver. Must explain during soutenance why no constraint programming was used and whether they understand the difference.

3. **I2**: No visible original work. Trio with scaffolding only. Must demonstrate actual contributions during soutenance.

4. **H2**: Clear frontrunner. Working CP-SAT implementation with multiple generation modes, connectivity constraint, and notebook. The soutenance should validate theoretical depth.

---

## Bonus/Malus Reference

| Group | Size | Bonus/Malus | TP Bonus (max) | Total Possible Adj. |
|-------|------|-------------|----------------|---------------------|
| E4 | Solo (1) | +3 | +2 | +5 |
| H1 | Trio (3) | 0 | +2 | +2 |
| H2 | Solo (1) | +3 | +2 | +5 |
| J1 | Duo/Trio? | 0/-1 | +2 | +1/+2 |
| I2 | Trio (3) | 0 | +2 | +2 |

---

## Soutenance Checklist (per group)

### For Each Group

- [ ] Code runs (demo live or recorded)
- [ ] Notebook demonstrates CP concepts (not just narrative)
- [ ] CP-SAT or equivalent solver is actually used in the code
- [ ] Hard constraints vs soft constraints clearly explained
- [ ] Search space reduction techniques discussed
- [ ] Performance comparison (baseline vs optimized) shown
- [ ] Git history shows meaningful contributions from all members
- [ ] Slides cover theoretical background (not just demo)
- [ ] Limitations and future work discussed honestly

### Red Flags to Watch

- J1: No CP solver in code (embedding scoring is NOT constraint programming)
- E4/H1: No code in repo — was it developed locally and not pushed?
- I2: Are the notebooks original work or copies of course templates?
- All groups: Can they explain CP-SAT concepts (propagation, branching, nogoods) when questioned?
