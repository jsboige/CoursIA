# hashlife -- instrumentation K_trajectory & Wolframe

Instrumentation pour mesurer la **complexite de trajectoire** (compression LZ fenetree) sur des automates cellulaires 2-D (Game of Life) et 1-D (regles elementaires de Wolframe).

## Modules

| Fichier | Role |
|---------|------|
| `k_trajectory.py` | CLI principal -- modes `measure`, `verify-corpus`, `bounds`, `wolfram`, `wolfram-4classes` |
| `wolfram_cross_classes_results.json` | Verbatim mesure 4 classes Wolframe (pli 4 c.110) |
| `wolfram_results.json` | Verbatim mesure Rule 30 / Rule 110 (pli 3 c.109) |
| `k_trajectory_results.json` | Mesure 2-D Game of Life (pli 1 c.103) |
| `WOLFRAM-VERDICT.md` | Falsifiable verdict R30 / R110 (pli 3 c.109) |
| `WOLFRAM-VERDICT-CROSS-CLASSES.md` | Falsifiable verdict 4 classes (pli 4 c.110) |
| `tests/` | Pytests (12 tests pli 4 + pli 3) |

## Modes CLI

| Mode | Mesure | Usage |
|------|--------|-------|
| `measure` | K_trajectory 2-D (Game of Life) sur seeds aleatoires | `python scripts/hashlife/k_trajectory.py --mode measure --n-cells 32 --n-steps 16` |
| `verify-corpus` | Verification reproductibilite d'un corpus de trajectoires | `python scripts/hashlife/k_trajectory.py --mode verify-corpus --corpus <path>` |
| `bounds` | Bornes theoriques (LZ vs entropie brute) | `python scripts/hashlife/k_trajectory.py --mode bounds --n-cells 64` |
| `wolfram` | K_trajectory sur Rule 30 / Rule 110 (1-D) | `python scripts/hashlife/k_trajectory.py --mode wolfram --rule 30 --n-cells 64 --n-steps 64` |
| `wolfram-4classes` | K_trajectory sur les 4 classes canoniques Wolframe (R0/R4/R30/R110) | `python scripts/hashlife/k_trajectory.py --mode wolfram-4classes --n-cells 64` |

## Reproduction

```bash
# PYTHONPATH necessaire pour ict.wolfram_step (pli 2 PR #19793)
export PYTHONPATH=MyIA.AI.Notebooks/IIT/ICT-Series

# Mesure 4 classes Wolframe (pli 4)
python scripts/hashlife/k_trajectory.py --mode wolfram-4classes --n-cells 64

# Sortie JSON
python scripts/hashlife/k_trajectory.py --mode wolfram-4classes --n-cells 64 \
    --json-out scripts/hashlife/wolfram_cross_classes_results.json

# Tests pytest
python -m pytest scripts/hashlife/tests/ -v
```

## Resultats notables

### Pli 1 (c.103) -- K_trajectory 2-D Game of Life
- 12 seeds aleatoires, n_cells=32, n_steps=16.
- Verdict : **DISCRIMINANT** -- K_trajectory distingue seed `soupe` (K eleve) vs seed `structure` (K collapse).

### Pli 3 (c.109) -- K_trajectory Rule 30 / Rule 110
- Mesure initiale a `n_cells = 64` : R30 (chaos) et R110 (Turing-complet) rendaient le **meme** ratio (0.510) -- un artefact de cadrage zlib (`K(W=64) = 523 = 512 + 11`, identique pour les deux regles), pas un resultat sur les regles.
- Hors saturation (`n_cells = 1024`) : R30 (frac 1.001, incompressible) et R110 (frac 0.429, compressible) **se separent**, dans le sens **inverse** de l'hypothese. Verdict : `WOLFRAM-CROSS-DIMENSION-REFUTED`. Cf. [WOLFRAM-VERDICT.md](WOLFRAM-VERDICT.md).

### Pli 4 (c.110) -- K_trajectory 4 classes Wolframe

Mesure canonique `n_cells = 1024` (hors saturation) :

| Regle | Classe | Ratio K(W=64)/K(W=1) | Verdict |
|-------|--------|----------------------|---------|
| 0     | I (uniforme) | 0.053 | CLASS-I-CONFIRMED (COLLAPSED) |
| 4     | II (periodique) | 0.023 | CLASS-II-CONFIRMED (COLLAPSED) |
| 30    | III (chaotique) | 0.922 | CLASS-III-CONFIRMED (WEAK-COLLAPSE) |
| 110   | IV (Turing-complet) | 0.571 | CLASS-IV-REFUTED (COLLAPSED alors qu'on attend entropie partielle) |

- Verdict final : `WOLFRAM-4CLASSES-III/IV-INVERSE` (1/4 contredisent -- faux negatif sur entropie).
- **Correction du 2026-10-09** : la mesure initiale a `n_cells = 64` publiait le **meme** ratio (0.510) pour R30 et R110 et un verdict « 2/4 contredisent » — un artefact de cadrage zlib (`K(W=64) = 523 = 512 + 11`, identique pour les deux regles). L'instrument declare desormais `WOLFRAM-SATURATED` sous `n_cells < 512`. Hors saturation, R30 et R110 se separent (0.922 vs 0.571).
- Conclusion : K_trajectory **separe** chaos et structure en 1-D des que la mesure sort du cadrage, mais ne mesure pas la **Turing-completude** (R110 est compressible parce que regulier). Instrument adequate pour discriminer *soupe vs programme* en 2-D.

## Origine

Suite Origami (EPIC #19742) -- plis 1 a 4 de l'instrumentation Hashlife / K_trajectory :
- **Pli 1** (c.103-c.104) : instrument K_trajectory 2-D, DELIVERED.
- **Pli 2** (c.108) : organe `ict.wolfram_step` (PR #19793 OPEN).
- **Pli 3** (c.109) : instrument 1-D Rule 30 / Rule 110 (PR #19815 OPEN).
- **Pli 4** (c.110) : extension 4 classes Wolframe (PR a ouvrir).

Suite prevue : pli 5 (hypergraphes), pli 6 (multiway), pli 7 (Kolmogorov structure function).