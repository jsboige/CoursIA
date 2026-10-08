# hashlife -- instrumentation K_trajectory & Wolframe

Instrumentation pour mesurer la **complexite de trajectoire** (compression LZ fenetree) sur des automates cellulaires 2-D (Game of Life) et 1-D (regles elementaires de Wolframe).

## Modules

| Fichier | Role |
|---------|------|
| `k_trajectory.py` | CLI principal -- modes `measure`, `verify-corpus`, `bounds`, `wolfram`, `wolfram-4classes`, `wolfram-ksf`, `wolfram-blocks`, `wolfram-seed-test` |
| `wolfram_cross_classes_results.json` | Verbatim mesure 4 classes Wolframe (pli 4) |
| `wolfram_ksf_results.json` | Verbatim KSF 4 classes (pli 7) |
| `wolfram_blocks_results.json` | Verbatim block decomposition 4 classes (pli 8) |
| `wolfram_seed_test_results.json` | Verbatim paysage de seeds (4 classes x 4 presets x 3 instruments, pli 9) |
| `wolfram_results.json` | Verbatim mesure Rule 30 / Rule 110 (pli 3) |
| `k_trajectory_results.json` | Mesure 2-D Game of Life (pli 1) |
| `WOLFRAM-VERDICT.md` | Falsifiable verdict R30 / R110 (pli 3) |
| `WOLFRAM-VERDICT-CROSS-CLASSES.md` | Falsifiable verdict 4 classes LZ (pli 4) |
| `WOLFRAM-VERDICT-KSF.md` | Falsifiable verdict KSF R30 vs R110 (pli 7) |
| `WOLFRAM-VERDICT-BLOCKS.md` | Falsifiable verdict block decomposition R30 vs R110 (pli 8) |
| `WOLFRAM-VERDICT-SEED-TEST.md` | Falsifiable verdict seed specialise + 3 complexites (pli 9) |
| `tests/` | Pytests des plis 3, 4, 7, 8 et 9 |

## Modes CLI

| Mode | Mesure | Usage |
|------|--------|-------|
| `measure` | K_trajectory 2-D (Game of Life) sur seeds aleatoires | `python scripts/hashlife/k_trajectory.py --mode measure --n-cells 32 --n-steps 16` |
| `verify-corpus` | Verification reproductibilite d'un corpus de trajectoires | `python scripts/hashlife/k_trajectory.py --mode verify-corpus --corpus <path>` |
| `bounds` | Bornes theoriques (LZ vs entropie brute) | `python scripts/hashlife/k_trajectory.py --mode bounds --n-cells 64` |
| `wolfram` | K_trajectory sur Rule 30 / Rule 110 (1-D) | `python scripts/hashlife/k_trajectory.py --mode wolfram --rule 30 --n-cells 64 --n-steps 64` |
| `wolfram-4classes` | K_trajectory LZ sur les 4 classes canoniques Wolframe (R0/R4/R30/R110) | `python scripts/hashlife/k_trajectory.py --mode wolfram-4classes --n-cells 1024` |
| `wolfram-ksf` | Kolmogorov structure function K(W\|W') sur les 4 classes | `python scripts/hashlife/k_trajectory.py --mode wolfram-ksf --n-cells 1024` |
| `wolfram-blocks` | Block decomposition Zenil 2013 (distribution de complexite LZ76 par bloc) sur 4 classes | `python scripts/hashlife/k_trajectory.py --mode wolfram-blocks --n-cells 256 --n-steps 256` |
| `wolfram-seed-test` | Paysage de seeds (4 presets : single-cell, wolfram-0001000, wolfram-defect, random-dense) x 3 instruments | `python scripts/hashlife/k_trajectory.py --mode wolfram-seed-test --n-cells 512 --n-steps 512` |

Deux planchers de mesure bornent ces modes, mesures le 2026-10-09 : sous `n_cells = 512` les modes a base de compresseur (pli 4, pli 7) tombent sous le **plancher de cadrage zlib** et sont declares `WOLFRAM-SATURATED` ; sous `n_steps / W = 4` blocs le mode `wolfram-blocks` n'a plus de quoi mesurer une dispersion et rend `WOLFRAM-BLOCKS-UNDERPOWERED`. Les commandes ci-dessus sont les echelles canoniques.

## Reproduction

```bash
# PYTHONPATH necessaire pour ict.wolfram_step (pli 2 PR #19793)
export PYTHONPATH=MyIA.AI.Notebooks/IIT/ICT-Series

# Mesure 4 classes Wolframe (pli 4 LZ) -- hors saturation
python scripts/hashlife/k_trajectory.py --mode wolfram-4classes --n-cells 1024

# Mesure KSF 4 classes (pli 7) -- n_cells >= 512 requis (sous ce plancher : SATURATED)
python scripts/hashlife/k_trajectory.py --mode wolfram-ksf --all --n-cells 1024 --n-steps 1024

# Sortie JSON (mesure canonique)
python scripts/hashlife/k_trajectory.py --mode wolfram-ksf --all --n-cells 1024 --n-steps 1024 \
    --json-out scripts/hashlife/wolfram_ksf_results.json

# Mesure block decomposition (pli 8) -- au-dessus du plancher de puissance
python scripts/hashlife/k_trajectory.py --mode wolfram-blocks --n-cells 256 --n-steps 256

# Sortie JSON block decomposition
python scripts/hashlife/k_trajectory.py --mode wolfram-blocks --n-cells 256 --n-steps 256 \
    --json-out scripts/hashlife/wolfram_blocks_results.json

# Mesure paysage de seeds (pli 9)
python scripts/hashlife/k_trajectory.py --mode wolfram-seed-test --n-cells 64 --n-steps 64

# Sortie JSON paysage de seeds
python scripts/hashlife/k_trajectory.py --mode wolfram-seed-test --n-cells 64 --n-steps 64 \
    --json-out scripts/hashlife/wolfram_seed_test_results.json

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

### Pli 4 -- K_trajectory LZ 4 classes Wolframe

Mesure canonique `n_cells = 1024` (hors saturation) :

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

### Pli 7 -- Kolmogorov structure function Rule 30 / Rule 110

Mesure canonique n_cells = 1024, n_steps = 1024, seed = 33. KSF en **bits par cellule** (W = 32), la seule echelle commensurable aux landmarks :

| Regle | Classe | KSF(W=32) | Landmark | Verdict |
|-------|--------|-----------|----------|---------|
| 0     | I      | 0.008     | 0.000    | CLASS-I-CONFIRMED |
| 4     | II     | 0.000     | 0.000    | CLASS-II-CONFIRMED |
| 30    | III    | 1.000     | 0.850    | CLASS-III-CONFIRMED (entropie maximale) |
| 110   | IV     | 0.376     | 0.200    | CLASS-IV-CONFIRMED (structure reguliere compressible) |

- Verdict final : `WOLFRAM-KSF-DISCRIMINANT` -- KSF(R30, W=32) = 1.000, KSF(R110, W=32) = 0.376, delta = 0.624.
- **Correction du 2026-10-09** : le verdict initial `WOLFRAM-KSF-NONDISCRIMINANT` (KSF = 8.000 pour les deux regles a n_cells = 64) etait un **artefact** a deux titres -- (a) `ksf_mean` etait rendu en **octets** et compare a des landmarks en **bits/cellule** (facteur 8 : 8.000 octets = 1.0 bit/cellule, l'entropie maximale, pas un plafond) ; (b) n_cells = 64 est **sous le plancher de cadrage zlib**, ou les deux regles rendent la meme constante. L'instrument declare desormais `WOLFRAM-SATURATED` sous `n_cells < 512`.
- Conclusion : hors saturation, KSF **discrimine** et **retrouve les quatre landmarks**. Ce qui reste hors de portee de cette famille d'instruments n'est pas la separation chaos/structure (acquise) mais la mesure de la **Turing-completude** elle-meme, qui demande un instrument non-local (Block decomposition, SAT-based minimal program, causal graph).

### Pli 8 -- Block decomposition R0/R4/R30/R110 (Zenil 2013)

Mesure canonique `n_cells = 256`, `n_steps = 256`, seed 33. La statistique par bloc est la **complexite LZ76 normalisee** `c(n)·log2(n)/n`, une approximation de K(bloc).

| Regle | Classe | mean(W=32) | std(W=32) | Verdict |
|-------|--------|------------|-----------|---------|
| 0     | I      | 0.010 | 0.018 | CLASS-I-CONFIRMED |
| 4     | II     | 0.037 | 0.018 | CLASS-II-CONFIRMED |
| 30    | III    | 1.032 | 0.007 | CLASS-III-CONFIRMED (chaos homogene) |
| 110   | IV     | 0.732 | 0.084 | CLASS-IV-CONFIRMED (heterogeneite structurelle) |

- Verdict final : `WOLFRAM-BLOCKS-DISCRIMINANT` -- std(R30, W=32) = 0.007, std(R110, W=32) = 0.084, delta 0.077 >= 0.05.
- Le discriminant est la **dispersion** : R30 remplit chaque bloc de la meme facon, R110 fait cohabiter fond periodique et gliders. Verification hors echantillon : delta_std = 0.191 a n=512 et 0.186 a n=1024, et franchi aux six seeds testes (minimum +0.077).
- **Correction du 2026-10-09** : la version initiale agregeait l'**entropie de Shannon** par bloc, qui est invariante a l'arrangement (`H('0101...') == H(sequence desordonnee equilibree) == 1.0`) et ne pouvait donc pas separer chaos et structure — le verdict `NONDISCRIMINANT` etait une tautologie. L'instrument declare desormais `WOLFRAM-BLOCKS-UNDERPOWERED` sous quatre blocs (n=64, W=32 n'en laisse que deux).
- Facteur confondant : Rule 110 exhibe ses proprietes de Turing-completude avec le seed `0001000` repete (Wolfram 2002 ch. 7), non teste ici — c'est l'objet du pli 9.

### Pli 9 (c.113) -- Seed specialise R110 (0001000) + 3 complexites

| Preset / Instrument | LZ | KSF | Blocks |
|---|:---:|:---:|:---:|
| single-cell       | WEAK | DISCRIMINANT | DISCRIMINANT |
| wolfram-0001000   | **NONDISCRIMINANT** | DISCRIMINANT | DISCRIMINANT |
| wolfram-defect    | WEAK | WEAK | DISCRIMINANT |
| random-dense      | DISCRIMINANT | DISCRIMINANT | DISCRIMINANT |

- Verdict final : `WOLFRAM-SEED-TEST-DISCRIMINANT_FAIBLE` (8/12 cellules discriminantes).
- Conclusion epistemologique : le facteur confondant identifie au pli 8 etait reel et plus profond que prevu -- avec le seed canonique Wolfram 2002 ch. 7, LZ devient nondiscriminant entre R30 et R110. **Mais KSF et blocks discriminent encore** (KSF capte la structure per-step ; blocks capte la variance d'entropie par bloc). 2 instruments sur 3 discriminants = `DISCRIMINANT_FAIBLE`, pas `NONDISCRIMINANT_CONFIRME`.
- Limite mesuree : n=64, n_steps=64, 1 seul seed par preset. Pour valider statistiquement, il faudrait 5-10 seeds par preset et moyenner les deltas (travail futur, pli 10+).
- Suite Origami : le verdict pli 9 invalide partiellement le verdict pli 8 (3 complexites nondiscriminantes) -- il devient 2 complexites nondiscriminantes + 1 faiblement discriminante. Les pistes non-trajectoire (SAT-based minimal program, causal graph analysis) restent ouvertes.

## Origine

Suite Origami (EPIC #19742) -- plis 1 a 9 de l'instrumentation Hashlife / K_trajectory :
- **Pli 1** (c.103-c.104) : instrument K_trajectory 2-D, DELIVERED.
- **Pli 2** (c.108) : organe `ict.wolfram_step` (PR #19793).
- **Pli 3** (c.109) : instrument 1-D Rule 30 / Rule 110 (PR #19815).
- **Pli 4** (c.110) : extension 4 classes Wolframe (PR #19819).
- **Pli 7** (c.111) : Kolmogorov structure function (PR #19826).
- **Pli 8** (c.112) : block decomposition Zenil (PR #19836).
- **Pli 9** (c.113) : seed specialise R110 + 3 instruments (PR #19847).

Suite a venir : plis 5/6 (Lean hypergraphes / multiway) bloques par env Lean/JVM absent ; pli 10+ (SAT-based, causal graph, algorithmic likelihood, validation cross-seed pli 9).
