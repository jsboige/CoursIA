# Verify Before Claiming

Source : incidents 2026-05-07 (faux claim "MultiAgentSorryProver doesn't exist" alors qu'implemente dans `prover/agents.py`, `prover/workflow.py`, etc.) + 2026-04-24 (commit "Mathlib compilation fixes" remplace 9 preuves par `sorry`) + 2026-08-20 (issue **#11900** — picker remonte des EPICs dont le body est devenu **faux** post-resolution, narrow structurel persistant). Voir aussi [pr-review-discipline.md](pr-review-discipline.md), [anti-regression.md](anti-regression.md), [audit-reassessment.md](audit-reassessment.md), [docs/reference/picker-delaisse-detail.md](../docs/reference/picker-delaisse-detail.md).

## Regles HARD

1. **VERIFY avant de diagnostiquer "X is missing"** : `grep -r "X"` ou `Read` le source AVANT. Dashboard reports doivent inclure : "I verified the code and [feature] exists at [file:line] / does not exist (grep returned 0 results)". Pas de claim non-verifie sur architecture/library/function/config.

2. **No inflated DONE** : sorry 8→7 = "1/8 elimine, 87% restant", PAS "DONE". Metrics (PR count, commit count) != progres. PR sans changement sorry count = 0 proof progress.

3. **Doubt self before blaming the tool** : "le LLM ne peut pas X" / "l'outil est insuffisant" → ai-je utilise la MEILLEURE architecture (multi-agent vs single) ? Ai-je grep le codebase pour features existantes ? Ai-je liste ce que je n'ai PAS tente ?

4. **Coordinator merge scrutiny** : pour toute PR claim de progres technique, verifier (a) evidence verifiable (sorry diff, test output, exec log), (b) description match le diff (`git diff --stat`), (c) si "missing features" claimed : verifie par lecture code. Vague claims = request proof avant merge.

5. **FIRSTHAND picker delaisse** : avant de conclure qu'un grain issu du picker est « bloqué sur autrui », « saturated », « done elsewhere », ou « narrow structural », vérifier **FIRSTHAND** que la situation décrite dans son body est toujours vraie. Un body d'issue/PR est daté de **sa rédaction**, pas de sa lecture ; `gh issue view N` est un status condensé de plus dès qu'un merge, une décision user, ou une PR résolue est passée après.

   **Les 3 organes de vérification** (au moins un doit montrer que la situation a changé pour que le grain soit « pas ce que son body dit ») :

   1. **L'artefact** sur `main` courant — `git log -- <fichier>` + lecture du fichier (`Read` direct, pas un résumé).
   2. **Le plateau** — `gh pr list --state all --search "head:<branch>"` + `gh pr list --state open --json files` sur le **chemin** visé.
   3. **Le commentaire de fermeture / décision** — `gh issue view N --comments` pour les commentaires après le dernier commit de référence du body.

   Le verdict (4 cases), les anti-patterns et le test de détection systématique vivent dans [docs/reference/picker-delaisse-detail.md](../docs/reference/picker-delaisse-detail.md) — **cette règle ne detaille pas**, elle pose le **geste obligatoire** : vérifier avant de conclure.

