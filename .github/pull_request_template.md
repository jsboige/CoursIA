<!-- ETUDIANTS (PR de TP) : remplissez seulement la section Summary ci-dessous. Laissez les checklists telles quelles — votre encadrant s'en charge. Une CI rouge ne bloque pas votre TP. -->

> **Etudiants (PR de TP)** : remplissez seulement **Summary**. Les checklists de review sont pour l'encadrant — laissez-les telles quelles. Une CI rouge ne bloque pas le merge de votre TP.

<!-- AGENTS INTERNES (workers po-*, ai-01) : la PREMIERE LIGNE du body doit porter le tag variation-protocol. ETUDIANTS : ignorez ce bloc. -->

**Grain (agents internes — [variation-protocol](../.claude/rules/variation-protocol.md))** — premiere ligne du body, format :

`Grain: <TIER>/<GENRE> — lane <machine:workspace> — prev: <TIER>/<GENRE>`

<!--
TIER (test objectif, detail dans .claude/rules/variation-protocol.md) :
  DEEP  = main gagne un resultat/capacite inexistant, produit par du raisonnement de domaine
          (sorry Lean retire + lake build OK, backtest/training multi-seed, notebook execute >=3 exos, moteur SOTA branche verdict SOTA-OK).
  MED   = etend de la substance existante avec re-exec/verif ET change quelque chose
          (enrichissement + re-exec, audit borne qui change une decision, refactor + tests verts, README fichier-entier corrigeant un drift structurel reel).
  LIGHT = generable en serie par scan (guard-tranche, path-fix, doc-resync +1/-1, ledger append, fix accent/leak/FP).
          Litmus : « pourrais-je en generer une douzaine a la chaine en scannant l'instance d'a-cote ? » -> oui = LIGHT, quel que soit le label.
GENRE : lean . qc . training . genai . notebook-python . notebook-dotnet . docs . guard . refactor . ledger . readme . test
Gates durs : plancher du cycle = DEEP ou MED (G-VAR-1) ; <=1 LIGHT/lane/jour, agrege (G-VAR-2) ; pas 2x le meme genre LIGHT consecutif (G-VAR-3).
-->

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
