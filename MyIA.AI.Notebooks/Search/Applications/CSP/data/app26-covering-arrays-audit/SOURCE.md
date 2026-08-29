# Source and reproduction — App-26 Covering Arrays

## Student source

- **Author:** Valérian Pichot ([Valhallave](https://github.com/Valhallave))
- **Project:** H4 — Covering Arrays, EPITA SCIA *Programmation par Contraintes* 2026
- **Repository:** [jsboigeEpita/2026-Epita-Programmation-par-Contraintes](https://github.com/jsboigeEpita/2026-Epita-Programmation-par-Contraintes/tree/main/H4-Covering-Arrays)
- **Pull request:** [#58](https://github.com/jsboigeEpita/2026-Epita-Programmation-par-Contraintes/pull/58)
- **Source commit:** `75000d6d7f81039db00871485576ebb4290e1188`
- **License:** MIT (repository root)

The student project provides a CP-SAT covering-array generator, IPOG and AETG comparators, a constraint-aware generation example, a notebook, and presentation slides. App-26 attributes that apparatus and its experimental question, but does **not** copy its Python modules, notebook cells, prose, or figures.

## Fresh reproduction used for distillation

The source notebook was rerun independently before App-26 was authored. The following observations guided the reconstruction:

- the core CP-SAT generation cells execute;
- the benchmark cells fail because `itertooCPSATGeneratorls` is called instead of `itertools.product`;
- a focused 12-case rerun (four parameter/level configurations across CP-SAT, IPOG, and AETG) reproduced 10 stored suite sizes exactly;
- within that focused subset, AETG `(k=4, v=3)` produced 28 rows instead of the stored 29 because the source does not fix a seed;
- within that focused subset, CP-SAT `(k=5, v=3)` found an incumbent of 35 instead of the stored 36 under the time limit;
- the constrained example produced 32 rows and zero semantic violations, but the source validator reported 38 missing interactions; inspection showed those interactions had no extension satisfying the semantic constraints;
- the source does not distinguish `FEASIBLE` from `OPTIMAL` in its result narrative.

These are reproduction observations, not copied data dependencies. App-26 reconstructs smaller instances so every claim can be rerun quickly inside CoursIA.

## Independent CoursIA apparatus

App-26 implements from scratch:

1. a Cartesian interaction enumerator and independent coverage oracle;
2. an interaction-feasibility filter based on admissible full rows;
3. an exact set-cover CP-SAT model over admissible candidate rows;
4. deterministic and seeded greedy constructions labelled `IPOG-like` and `AETG-like`, explicitly not industrial implementations;
5. a constraint-aware validator that separates impossible from uncovered interactions;
6. status/incumbent/bound reporting and three safe exercise stubs.

No source data files are required at runtime. The notebook generates all instances locally and executes with one CP-SAT worker. The randomised baseline uses seed 42.

## App-26 verification environment

Initial full execution:

- **Date:** 2026-08-29
- **Python:** 3.13.14
- **OR-Tools:** 9.15.6755
- **pandas:** 2.3.3
- **Command:**

```bash
python scripts/notebook_tools/notebook_tools.py execute \
  MyIA.AI.Notebooks/Search/Applications/CSP/App-26-CoveringArrays-Guarantee-Audit.ipynb \
  --timeout 180
```

Key independently generated outputs:

- `CA(N;2,4,2)`: `N=5`, status `OPTIMAL`, best bound `5`, oracle `24/24`;
- `CA(N;3,4,2)`: `N=8`, status `OPTIMAL`, best bound `8`;
- constrained binary example: 9/16 admissible rows, 22/24 feasible pairwise interactions, exact `N=5`;
- naïve validator: invalid with 2 alleged missing interactions;
- constraint-aware validator: valid with 0 missing interaction;
- deterministic and seeded greedy baselines: valid suites, audited against the same independent oracle;
- ternary `(k=4, t=2, v=3)` benchmark run: incumbent `N=9`, status `FEASIBLE`, best bound `0` at the 15-second limit — a valid suite, not a certified optimum.

Execution times are machine-dependent. Optimality statements are limited to finite instances for which CP-SAT returns `OPTIMAL` with a closed bound.
