# Verify Before Claiming

Source : incidents 2026-05-07 (faux claim "MultiAgentSorryProver doesn't exist" alors qu'implemente dans `prover/agents.py`, `prover/workflow.py`, etc.) + 2026-04-24 (commit "Mathlib compilation fixes" remplace 9 preuves par `sorry`). Voir aussi [pr-review-discipline.md](pr-review-discipline.md), [anti-regression.md](anti-regression.md).

## Regles HARD

1. **VERIFY avant de diagnostiquer "X is missing"** : `grep -r "X"` ou `Read` le source AVANT. Dashboard reports doivent inclure : "I verified the code and [feature] exists at [file:line] / does not exist (grep returned 0 results)". Pas de claim non-verifie sur architecture/library/function/config.

2. **No inflated DONE** : sorry 8→7 = "1/8 elimine, 87% restant", PAS "DONE". Metrics (PR count, commit count) != progres. PR sans changement sorry count = 0 proof progress.

3. **Doubt self before blaming the tool** : "le LLM ne peut pas X" / "l'outil est insuffisant" → ai-je utilise la MEILLEURE architecture (multi-agent vs single) ? Ai-je grep le codebase pour features existantes ? Ai-je liste ce que je n'ai PAS tente ?

4. **Coordinator merge scrutiny** : pour toute PR claim de progres technique, verifier (a) evidence verifiable (sorry diff, test output, exec log), (b) description match le diff (`git diff --stat`), (c) si "missing features" claimed : verifie par lecture code. Vague claims = request proof avant merge.
