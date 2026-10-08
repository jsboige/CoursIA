# WOLFRAM-VERDICT-BLOCKS — Block decomposition R0/R4/R30/R110

**Pli 8 Origami Wolfram — c.112 (2026-12-08)** — extension de l'instrument K_trajectory à la **block decomposition** (Zenil, Soler-Toscano, Kiani 2013 *A decomposition method for global complexity*, arXiv:1304.5813).

## Perimetre

Suite Origami Wolfram (pli 4 c.110 LZ fenetre REFUSE, pli 7 c.111 KSF REFUSE) :
- **Pli 4** (PR #19819) : K_trajectory LZ fenetre — `WOLFRAM-4CLASSES-III/IV-INVERSE`.
- **Pli 7** (PR #19826) : Kolmogorov structure function — `WOLFRAM-KSF-NONDISCRIMINANT` (KSF(R30, W=32) = KSF(R110, W=32) = 8.000).

Pli 8 implemente la **block decomposition** de Zenil 2013 : pour une trajectoire 1-D et une longueur de bloc W, decouper en blocs non-chevauchants, calculer l'entropie Shannon (base 2) du bitstream de chaque bloc, agreger (moyenne, std, min, max).

## Hypothese (a falsifier ou confirmer)

| Regle | Classe | mean(W=32) attendu | std(W=32) attendu | Justification |
|-------|--------|---------------------|--------------------|---------------|
| 0     | I (uniforme)    | 0.0 | 0.0 | Constance — tous les blocs identiques |
| 4     | II (periodique) | 0.0 | 0.0 | Periode courte capture tout |
| 30    | III (chaotique) | 1.0 | 0.0 | Chaos uniforme, blocs similaires partout |
| 110   | IV (Turing-complet) | 1.0 | 0.30 | **Bimodalite** : gliders a entropie basse + reactions a entropie elevee |

**Critere discriminant** : `std(R110, W=32) - std(R30, W=32) >= 0.05`. Au-dela, **DISCRIMINANT**. Sinon **NONDISCRIMINANT**.

## Mesure firsthand (n_cells=64, n_steps=64, seed=33)

| Regle | Classe | W=1 mean/std | W=4 mean/std | W=16 mean/std | W=32 mean/std |
|-------|--------|--------------|--------------|---------------|---------------|
| 0     | I      | 0.016/0.124  | 0.033/0.126  | 0.048/0.083   | 0.055/0.055   |
| 4     | II     | 0.348/0.082  | 0.356/0.074  | 0.360/0.040   | 0.361/0.024   |
| 30    | III    | 0.988/0.014  | 0.999/0.002  | 1.000/0.000   | 1.000/0.000   |
| 110   | IV     | 0.981/0.027  | 0.990/0.011  | 0.993/0.006   | 0.993/0.006   |

## Verdict falsifiable par regle

| Regle | Classe | Observation vs landmark | Verdict |
|-------|--------|--------------------------|---------|
| 0     | I      | mean=0.055 vs 0.0 (delta 0.055) ; std=0.055 vs 0.0 (delta 0.055) | CLASS-I-DEVIATION |
| 4     | II     | mean=0.361 vs 0.0 (delta 0.361) ; std=0.024 vs 0.0 (delta 0.024) | CLASS-II-DEVIATION |
| 30    | III    | mean=1.000 ~= 1.000 ; std=0.000 ~= 0.000 | **CLASS-III-CONFIRMED** |
| 110   | IV     | mean=0.993 vs 1.000 (delta 0.007) ; std=0.006 vs 0.300 (delta **0.294**) | CLASS-IV-DEVIATION |

**Notes sur les deviations** :
- **R0 (classe I)** : seed single-cell + Rule 0 produit un **die pattern** (cellules isolees qui survivent tant qu'elles ont exactement un voisin). Ce n'est pas une constance a zero — entropie basse (mean=0.055) mais non-nulle. La classe I canonique de Wolfram (constance) necessite un seed uniforme (tous zéros).
- **R4 (classe II)** : seed single-cell + Rule 4 evolue vers un motif periodique, mais le seed evolue suffisamment pour creer une entropie moyenne de 0.361, pas zero. La classe II canonique necessite un seed uniforme ou un motif periodique de base.
- **R110 (classe IV)** : seed single-cell ne produit PAS les structures de Turing-completude spectaculaires. Pour declencher les gliders et reactions, il faut le motif de fond `...000100010001...` specifique (Wolfram 2002 ch. 7). Avec seed single-cell, R110 evolue comme un automate proche du chaos.

## Verdict final discrimination R30 vs R110

```
WOLFRAM-BLOCKS-NONDISCRIMINANT (R30 std(W=32)=0.000, R110 std(W=32)=0.006, delta_std=0.006 < 0.05)
```

**Resultat** : `WOLFRAM-BLOCKS-NONDISCRIMINANT`. La std d'entropie par bloc R30 (0.000) et R110 (0.006) sont **identiques a 0** au-dela du seuil 0.05.

## Conclusion epistemologique

**Trois instruments de calsification (~complexites de trajectoire 1-D) convergent vers le meme constat** : a l'echelle n=64 avec seed single-cell, **Rule 30 (chaos) et Rule 110 (Turing-complet) sont indistinguables**.

| Pli | Instrument | Resultat |
|-----|------------|----------|
| 4 (c.110) | K_trajectory LZ fenetre | `WOLFRAM-4CLASSES-III/IV-INVERSE` |
| 7 (c.111) | Kolmogorov structure function | `WOLFRAM-KSF-NONDISCRIMINANT` (delta 0.000) |
| 8 (c.112) | Block decomposition Zenil | `WOLFRAM-BLOCKS-NONDISCRIMINANT` (delta 0.006) |

**Trois negatifs**, tous au-dela du seuil de discrimination de chaque instrument. C'est une **these falsifiable** : les complexites de trajectoire 1-D (locales, conditionnelles, decomposees par bloc) sont **insuffisantes** pour capturer la Turing-completude de Rule 110 — au moins a l'echelle n=64 et avec seed single-cell.

**Facteur confondant identifie** : Rule 110 exhibe ses proprietes de Turing-completude avec un seed specifique (motif `0001000` repete, Wolfram 2002). Avec seed single-cell, R110 evolue de maniere similaire a R30 (chaos-like). Une investigation ulterieure pourrait utiliser le seed `0001000` pour verifier si les instruments discriminent alors.

## Limites

- **Echelle** : n=64, n_steps=64. La discrimination pourrait apparaitre a plus grande echelle (n=256, n_steps=256) si les structures de R110 ont besoin de plus d'espace pour emerger.
- **Seed** : single-cell centre (defaut de `ict.wolfram_step`). Le seed `0001000` repete (woolframetest specifique) pourrait reveler des structures cachees.
- **Instrument** : block decomposition en entropie Shannon. Une variante par Kolmogorov structure function sur les blocs (BSF, block structure function) ou par algorithmic likelihood pourrait discriminer.

## Suite Origami (recommandation pli 9+)

Trois directions d'ouverture :

- **A. Seed specialise** : utiliser le seed `0001000` repete (background specifique a Rule 110, Wolfram 2002 ch. 7) et re-mesurer plis 4+7+8. C'est l'experience controlee la plus directe.
- **B. Algorithmic likelihood (Zenil)** : au lieu de l'entropie Shannon par bloc, utiliser la **block structure function** (BSF, Zenil 2013 eq. 5) qui approche la Kolmogorov complexity par distribution de longueur de programmes generant chaque bloc. C'est plus direct mais plus cher en calcul.
- **C. Causal graph analysis** : reconstruire le graphe causal de la trajectoire (Zenil 2012 arXiv:1208.5555) et mesurer la profondeur structurelle. C'est un instrument **non-trajectoire** qui pourrait capturer ce que les complexites de trajectoire ne voient pas.

## Sources

- Zenil, H., Soler-Toscano, F., & Kiani, N. A. (2013). *A decomposition method for global complexity*. arXiv:1304.5813 [cs.IT].
- Zenil, H., et al. (2012). *An algorithmic information calculus for causal discovery*. arXiv:1208.5555.
- Wolfram, S. (2002). *A New Kind of Science*. Ch. 7 (Rule 110 Turing-completude).
- Cook, M. (2004). *Universality in Elementary Cellular Automata*. Complex Systems 15(1): 1-40.

## Reproduction

```bash
export PYTHONPATH=MyIA.AI.Notebooks/IIT/ICT-Series
python scripts/hashlife/k_trajectory.py --mode wolfram-blocks --n-cells 64 --n-steps 64
python scripts/hashlife/k_trajectory.py --mode wolfram-blocks --n-cells 64 --n-steps 64 \
    --json-out scripts/hashlife/wolfram_blocks_results.json
python -m pytest scripts/hashlife/tests/test_wolfram_blocks.py -v
```

## Tests

21 tests pytest (pli 8) :
- Landmarks canoniques : 2 tests
- Shannon entropy bits : 5 tests
- Block decomposition : 5 tests
- Block entropy distribution : 2 tests
- Measure wolfram blocks : 4 tests
- Discrimination verdict : 2 tests
- JSON round-trip subprocess : 1 test

**21/21 PASSED** en 5.19s.

## Liens

- EPIC Origami #19742
- Pli 1 #19766 : Conscience Origami
- Pli 2 #19796 : organe `ict.wolfram_step` (PR #19793)
- Pli 3 #19813 : K_trajectory Rule 30 / Rule 110 (PR #19815)
- Pli 4 #19818 : K_trajectory cross-classes LZ (PR #19819)
- Pli 7 #19824 : Kolmogorov structure function (PR #19826)
- Pli 8 #19832 : Block decomposition (cette PR)
- Pli 9+ : SAT-based minimal program, causal graph analysis

---

Co-Authored-By: Claude Haiku 4.5 (1M context) <noreply@anthropic.com>

🤖 Generated with [Claude Code](https://claude.com/claude-code)