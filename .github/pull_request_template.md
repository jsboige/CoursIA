## Summary

<!-- 1-3 bullet points describing what this PR does -->

-

## Changes

<!-- List the main changes: files added/modified, features, fixes -->

-

## Review Checklist

<!-- 5-point review system (CLAUDE.md section B) -->

- [ ] **1. Scope** — PR does exactly what it announces, nothing more, nothing less
- [ ] **2. Post-fix validation** — Automated script ran AFTER the last commit on the deliverable (not just source code)
- [ ] **3. Pedagogical coherence** — Exercises aligned with taught content, no redundancy, TODO stubs consistent, logical cell order
- [ ] **4. Real execution** — Notebooks executed with outputs (Papermill/Jupyter), Slidev `?clicks=99` for slides
- [ ] **5. Regression check** — Grep touched symbols in the rest of the repo; no unintended side effects

## Anti-regression

<!-- For PRs touching production code (Lean/Coq, business logic, tests, libraries) -->

- [ ] No `sorry` introduced in Lean/Coq certified modules (run: `grep -c sorry` on touched `.lean` files)
- [ ] No `@pytest.skip` or `assert True` added to bypass failing tests
- [ ] Deletions on production code justified (ratio insertions/deletions reasonable)

## Notebook-specific

<!-- For PRs modifying .ipynb files — skip if not applicable -->

- [ ] No `raise NotImplementedError` / `assert False` / `1/0` in any cell (use `pass` or `print("Exercice a completer")`)
- [ ] All code cells have `execution_count: <int>` + coherent `outputs`
- [ ] Only notebooks with source changes are committed (rule C.3)

## Test plan

<!-- How to verify this PR works -->

-
