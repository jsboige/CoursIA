# Lean coordinator workflow (ai-01)

Detail des deux disciplines coordinateur sur le projet Lean : Lake build pre-merge + BG iter prover systematique. Les regles HARD correspondantes sont dans :
- [.claude/rules/lean-lake-build-required.md](../../.claude/rules/lean-lake-build-required.md)
- [.claude/rules/lean-prover-bg-systematic.md](../../.claude/rules/lean-prover-bg-systematic.md)

## 1. Lake build SUCCESS local avant merge

### Incident 2026-05-10

Merge de #866 (`median_voter_theorem` sorry 1->0) a 00:50Z en confiance sur le claim "lake build SUCCESS 124.6s WSL" du body. po-2026 audit a 07:38Z trouve :
- Build FAIL avec 2 type errors
- `single_peaked` def changee globally = breaking pour autres theoremes
- `split_cycle_defeats` gutted a `True`
- `hcount` = sorry deguise

Revert PR #885 ouverte. Section H.4 violee, repair coute 1 cycle.

Corollaire : revert #885 a remis Voting.lean dans baseline... lui-meme casse depuis `592147a4` (indentation L242/L246, deux `simp` un-indents apres `have ... := by`). Bug a survecu a 6+ PRs parce que le CI ne testait pas Voting.lean. Fix PR #886 (4 lignes diff).

**Lecon** : ENV LEAN LOCAL = preuve > CI claims. **Le claim "lake build SUCCESS Xs" dans le body PR n'est PAS suffisant.**

### Workflow build local (ai-01 Windows)

```bash
cd D:/CoursIA/MyIA.AI.Notebooks/GameTheory/social_choice_lean
lake build SocialChoice.Voting   # ou autre module touche
```

Lake = elan installe sous `C:\Users\MYIA\.elan\bin\`. Lean v4.29.1 OK.

Si "no such file or directory" sur des oleans Mathlib (cache corrompu) :
```bash
lake exe cache get   # ~3min, 8232 oleans pre-builts depuis Azure
```

Toujours `cache get` AVANT un build neuf, pas apres.

### CI != Lake build local

`lean-social-choice.yml` ne build PAS Voting.lean (juste Arrow/Sen/Framework/Basic pour no-sorry check). **CI SUCCESS != Voting.lean compile**.

### Si pas d'env Lean local

- Ne pas merger seul
- Dispatcher po-2026 avec criteres :
  1. Build log complet colle (pas extrait)
  2. `grep -c sorry` avant/apres par fichier
  3. Diff sur defs partagees (signatures, instances)

### Discipline temporelle

- Dashboard `[DEFER]` AVANT le merge, pas apres
- Pour PRs strict-vs-weak preferences ou def globale : demander la liste des theoremes downstream qui dependent de la def

---

## 2. BG iter prover systematique post-PR/msg po-2026

### Source user 2026-05-16

Apres reply Decision A po-2026 sur gale_shapley, ~13:55Z :

> "Pour gale shapley, stp fais une iteration de ton cote en BG (ca devrait etre systematique apres chaque PR ou message de po-2026). Visiblement le script n'est toujours pas bon, car avec la correction sous les yeux, ca devrait etre plie depuis longtemps"

### Diagnostic double

1. **Comparaison parallele** ai-01 BG + po-2026 manual = 2 paths convergents (ou divergents)
2. **Forensic actif** : si le BG re-echoue malgre nouveau contexte (upstream PR #1181 mergee donnant acces `Properties.lean:48-120` upstream), c'est que SearchAgent/CoordinatorAgent n'utilisent pas effectivement le repo upstream comme RAG. **Bug script**.

### Action immediate ai-01

```bash
cd /d/CoursIA/MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests
"C:/Users/MYIA/miniconda3/envs/coursia-ml-training/python.exe" -u run_prover_bg.py \
    <DEMO_ID> --provider zai --director-provider openrouter \
    --max-iter 20 --workflow-timeout 2400 2>&1 | tee bg_logs/ai01_demo<N>_cycle<NN>_$(date +%s).log
```

`DEMO_ID` (index dans `prover/config.py` `DEMOS` dict) :

| DEMO | Cible |
|------|-------|
| 6 | shapley |
| 9 | median_voter |
| 13 | banks_set |
| 14 | median_voter GT |
| 15 | gale_shapley_stable |

`--provider zai` (GLM-5.1) + `--director-provider openrouter` (Opus 4.7 strategic guidance, cher mais necessaire pour very_hard).

Lancer avec `Bash run_in_background=true`. Sauvegarder `bash_id` + path `.output`. Continuer FG work (min 2 tracks, cf CLAUDE.md "Productivite operations longues" HARD 2026-05-11).

### Forensic interpretation guide

| Outcome BG ai-01 | Outcome manual po-2026 | Diagnostic |
|------------------|------------------------|------------|
| FAIL (sorry inchange) | FAIL (sorry inchange) | Sorry vraiment **intractable** (Mathlib gaps, formalisation incomplete). Defer ou bouger contexte. |
| FAIL (sorry inchange) | SUCCESS (sorry elimine) | **Script defectueux** : prover ne fait pas ce qu'humain/agent expert fait. Forensic POSTMORTEM. |
| SUCCESS (sorry elimine) | FAIL (sorry inchange) | Script meilleur que manual sur ce point — incident a investiguer. |
| SUCCESS | SUCCESS | Convergence — verifier que les 2 preuves coincident (ou different mais valides). |

### Forensic capture sur echec N iter

- Issue `prover/script-defect-<n>` OU tracking `agent_tests/prover/POSTMORTEM.md`
- Logs `bg_logs/ai01_demo<N>_*.log` = source forensic primary
- Croiser avec [prover_iteration_history.md](prover_iteration_history.md) sections "BUILD-FAIL Pattern Categories" et "Architecture Evolution"

### Anti-pattern et verification fin de cycle

- **Anti-pattern interdit** : "Le BG a deja FAILED hier, pas la peine de relancer". Le contexte change a chaque iteration manual po-2026.
- **Reporting** : status BG (DELTA sorry, RESULT_SUCCESS, elapsed) dans dashboard cycle suivant. Ne PAS reporter "BG running, voila".
- **Fin de cycle** : avant `[DONE]`, repondre "Est-ce qu'il y a eu un PR ou msg po-2026 ce cycle ? Si oui, BG iter a-t-il ete lance ?".
