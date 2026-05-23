---
name: train-model
description: Train an ML model in the QuantConnect ML-Training-Pipeline with thermal-safe GPU usage and rigorous validation. Arguments: <architecture|script> [--dry-run] [--seeds 0,1,7,42,99] [--folds 5] [--bg]
---

# Train Model

Entrainer un modele ML du pipeline `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/` avec securite thermique GPU et validation rigoureuse. Couvre l'Epic #1454 (Training & Post-Training : RL/PPO, Decision Transformer, GenAI fine-tuning/LoRA).

Pour les cycles longs/batch, deleguer a l'agent `training-specialist` en async (`run_in_background: true`).

## Arguments

- `<architecture|script>` : nom court (`lstm`, `transformer`, `mamba`, `patchtst`, `itransformer`, `moe`, `gnn`, `dqn-rl`, `decision-transformer`) ou nom de script `train_*.py`.
- `--dry-run` : smoke test CPU via `validate_training_package.py --dry-run`, sans GPU. **Toujours commencer par la.**
- `--seeds 0,1,7,42,99` : seeds pour le multi-seed (defaut >=4 parmi 0/1/7/42/99).
- `--folds 5` : walk-forward folds (defaut 5).
- `--bg` : lancer le training en background (recommande pour les longs runs).

## Process

### Phase 0 — Environnement + grounding
1. Activer l'env : `& "C:\Users\MYIA\miniconda3\envs\coursia-ml-training\python.exe"`.
2. Lire `REGISTRY.md` + `CURRICULUM.md` : le modele est-il deja un keeper valide ? deprecated ? Ne pas refaire.

### Phase 1 — Dry-run CPU (HARD avant tout GPU)
```
python validate_training_package.py --dry-run   # smoke test, pas de GPU
```
Si le dry-run echoue : reparer (pas contourner). Ne pas passer en GPU sur un package casse.

### Phase 2 — Verifier le watchdog thermique (HARD)
```
python -c "from gpu_training import batch_thermal_check, get_gpu_temp; print('temp:', get_gpu_temp())"
```
- Temperature non nulle => watchdog actif (MAX_TEMP=80C, `cool_sleep=30`, AMP).
- `ImportError` ou temp 0 => **protection thermique en no-op silencieux** (`gpu_training.py` absent). NE PAS lancer un long run GPU sans protection : restaurer le module ou monitorer `nvidia-smi` manuellement. Documenter.

### Phase 3 — Training
- Lancer `python scripts/train_<arch>.py` (via env coursia-ml-training), en `--bg` pour les longs runs.
- Noter l'ID du BG + nature attendue. **Pendant le run, avancer une 2e track** (2 tracks min, cf CLAUDE.md operations longues).
- Check a intervalles utiles : `tail -50 <log> | grep -E "FINAL|RESULT|ERROR|temp"`. Pas event-par-event.

### Phase 4 — Validation rigoureuse (gate PR)
- Walk-forward 5-fold (`WalkForwardSplitter`), pas single split.
- **>=4 seeds** ; edge >= 2sigma cross-seed, sinon flag "noise".
- DM significance (`dm_test.py` / `diebold_mariano.py`).
- Comparaison `majority_class_baseline` + couts de transaction (5bps SPY, 10bps crypto).
- **Pas de FAANG/Mag7** en training set.
- Verdict honnete : `BEATS` / `NO BEATS` / `INCONCLUSIVE`. Jamais "promising". Single-seed => `[POC]` explicite.

### Phase 5 — Registry + livrable
- `python registry_update.py` pour mettre a jour REGISTRY.md.
- Checkpoints `.pt` volumineux/transients : **ne pas stager** dans la PR.
- Rapport (metriques par seed/fold, verdict, DM p-value) sur le dashboard, pas dans un fichier du repo.
- PR : un sujet, body avec WF + seeds + edge + baseline + tx costs + verdict (sinon CHANGES_REQUESTED).

## Anti-patterns interdits

- Sauter le dry-run et lancer direct en GPU.
- Lancer un long run GPU sans verifier le watchdog importable (Phase 2).
- Claim "BEATS" sans multi-seed + DM significance.
- Python systeme au lieu de coursia-ml-training.
- Stager des `.pt` lourds.

## Voir aussi

- [.claude/agents/training-specialist.md](../../agents/training-specialist.md) — orchestrateur async
- [docs/ml-trading-state.md](../../../docs/ml-trading-state.md) — anti-FAANG, multi-seed, walk-forward
- [.claude/rules/pr-review-discipline.md](../../rules/pr-review-discipline.md) C — gate ML PR
