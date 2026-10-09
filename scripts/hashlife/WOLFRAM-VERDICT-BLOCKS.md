# WOLFRAM-VERDICT-BLOCKS — Block decomposition R0/R4/R30/R110

**Pli 8 Origami Wolfram.** Implementation de la **block decomposition** (Zenil, Soler-Toscano, Kiani 2013 *A decomposition method for global complexity*, arXiv:1304.5813).

**Correction du 2026-10-09** : le verdict initial (`WOLFRAM-BLOCKS-NONDISCRIMINANT`, delta 0.006) reposait sur deux defauts mesures — une **statistique insensible a l'arrangement** (entropie de Shannon) et une **echelle sous-alimentee** (2 blocs). Corriges, l'instrument **discrimine**.

## Les deux defauts de la version initiale

### (a) La statistique etait invariante a l'arrangement

La version initiale agregeait l'**entropie de Shannon** de chaque bloc. Or `H = -p0·log2(p0) - p1·log2(p1)` ne depend que du **nombre de 1**, jamais de leur position. Temoin negatif, mesure :

```
H('01010101...01')                 = 1.0     # trajectoire parfaitement periodique
H(sequence desordonnee equilibree) = 1.0
```

Une trajectoire periodique et une trajectoire chaotique equilibree y sont **indiscernables par construction**. Publier un verdict de non-discrimination sur cette statistique etait donc une **tautologie**, pas un resultat sur les automates.

C'est aussi ce qui produisait les verdicts `CLASS-II-DEVIATION` de la version initiale : R4 (classe II, periodique) y rendait `mean = 0.361` au lieu du landmark `0.0`, et la note l'expliquait par « le seed evolue suffisamment pour creer de l'entropie » — en realite l'instrument y lisait la **densite de 1**, pas la regularite.

Ce n'est pas la statistique de la methode citee : Zenil 2013 agrege une approximation de **K(bloc)**, pas une entropie marginale.

### (b) L'echelle sous-alimentait le test

A `n_steps = 64` et `W = 32` il ne reste que **2 blocs**. Un ecart-type sur 2 echantillons ne mesure rien, et c'est pourtant la quantite sur laquelle portait le verdict. L'instrument declare desormais `WOLFRAM-BLOCKS-UNDERPOWERED` sous `WOLFRAM_BLOCKS_MIN_N_BLOCKS = 4` : dans cette zone, aucune comparaison — confirmation comme refutation — n'est concluante.

## L'instrument corrige

La complexite par bloc est desormais la **complexite LZ76 normalisee** `c(n)·log2(n)/n` (Ziv & Lempel 1978 ; Li & Vitanyi 2019 ch. 6), une approximation de K(bloc) :

- **sensible a l'arrangement** — une chaine periodique se factorise en peu de phrases, une chaine chaotique en beaucoup ;
- **sans plancher de cadrage** — c'est un comptage entier, aucun compresseur n'est invoque. C'est precisement la propriete qui manquait aux plis 4 et 7, dont les mesures tombaient sous le plancher zlib aux petites fenetres.

L'entropie de Shannon reste calculee et committee (`entropy_*`) pour la tracabilite des mesures anterieures ; elle ne porte plus le verdict.

## Mesure canonique (n_cells = 256, n_steps = 256, seed = 33)

`wolfram_blocks_results.json` committe.

| Regle | Classe | W=8 mean/std | W=16 mean/std | W=32 mean/std | n_blocs (W=32) |
|-------|--------|--------------|---------------|---------------|----------------|
| 0     | I (uniforme)    | 0.017/0.033 | 0.012/0.025 | 0.010/0.018 | 8 |
| 4     | II (periodique) | 0.108/0.033 | 0.062/0.025 | 0.037/0.018 | 8 |
| 30    | III (chaotique) | 1.048/0.013 | 1.039/0.008 | 1.032/0.007 | 8 |
| 110   | IV (structure)  | 0.783/0.079 | 0.757/0.078 | 0.732/0.084 | 8 |

L'ordre des moyennes **suit la classe** : `R0 (0.010) < R4 (0.037) < R110 (0.732) < R30 (1.032)`. R30 — le chaos — est le plus incompressible, ce qui est le comportement attendu d'un estimateur de complexite, et que l'entropie de Shannon ne pouvait pas produire (elle rendait `1.000` pour R30 et `0.993` pour R110, soit un ecart de 0.007 qui ne mesurait rien).

## Verdict falsifiable par regle

| Regle | Classe | Observation vs landmark | Verdict |
|-------|--------|--------------------------|---------|
| 0     | I      | mean=0.010 ~= 0.010 ; std=0.018 ~= 0.020 | **CLASS-I-CONFIRMED** |
| 4     | II     | mean=0.037 ~= 0.040 ; std=0.018 ~= 0.020 | **CLASS-II-CONFIRMED** |
| 30    | III    | mean=1.032 ~= 1.030 ; std=0.007 ~= 0.010 | **CLASS-III-CONFIRMED** |
| 110   | IV     | mean=0.732 ~= 0.670 ; std=0.084 ~= 0.130 | **CLASS-IV-CONFIRMED** |

## Verdict final discrimination R30 vs R110

```
WOLFRAM-BLOCKS-DISCRIMINANT
(R30 mean/std = 1.032/0.007, R110 mean/std = 0.732/0.084, delta_std = 0.077 >= 0.05)
```

**Le discriminant est la dispersion, pas la moyenne.** R30 est **homogene** — le chaos remplit chaque bloc de la meme facon, `std ~ 0.007`. R110 est **heterogene** — fond periodique et gliders cohabitent, donc le contenu des blocs varie, `std = 0.084`. C'est exactement l'heterogeneite structurelle que la methode de decomposition cherche a capturer, et que l'entropie marginale ne pouvait pas voir.

Le seuil `0.05` est celui de la version initiale : il n'a **pas** ete deplace pour faire passer le resultat. Ce qui a change est l'instrument.

## Verification hors echantillon

Les landmarks sont calibres a `n = 256`. La verification se fait ailleurs — autres echelles, autres seeds.

**Autres echelles** (seed 33, W=32) :

| n_cells | n_blocs | R30 mean/std | R110 mean/std | delta_std | Verdict |
|---------|---------|--------------|---------------|-----------|---------|
| 512     | 16      | 1.024/0.005 | 0.483/0.196 | **0.191** | DISCRIMINANT |
| 1024    | 32      | 1.021/0.004 | 0.346/0.190 | **0.186** | DISCRIMINANT |

**Autres seeds** (n_cells = 256, W = 32) :

| seed | R30 mean/std | R110 mean/std | delta_std |
|------|--------------|---------------|-----------|
| 0    | 1.034/0.005 | 0.676/0.132 | +0.127 |
| 1    | 1.030/0.003 | 0.612/0.201 | +0.198 |
| 7    | 1.031/0.003 | 0.690/0.164 | +0.161 |
| 33   | 1.032/0.007 | 0.732/0.084 | +0.077 |
| 42   | 1.031/0.006 | 0.664/0.119 | +0.113 |
| 99   | 1.032/0.005 | 0.674/0.126 | +0.121 |

Le signe est stable et le seuil franchi aux **six** seeds (minimum `+0.077`, moyenne `+0.133`) ; la dispersion de R30 reste sous `0.007` partout, celle de R110 au-dessus de `0.084`. La discrimination ne depend ni du seed ni de l'echelle une fois la puissance atteinte.

## Ce que le resultat signifie — et ne signifie pas

**Signification.** Un instrument de decomposition par bloc **separe** le chaos de la structure en 1-D, des lors que la statistique par bloc est sensible a l'arrangement. Le negatif publie par la version initiale etait un artefact de l'instrument.

**Ce qu'il ne dit pas.** `WOLFRAM-BLOCKS-DISCRIMINANT` ne mesure **pas la Turing-completude**. L'instrument detecte l'**heterogeneite** d'une trajectoire : R110 est plus compressible que R30 parce que sa trajectoire est **reguliere** (fond periodique, gliders), et cette regularite est ce que la dispersion capte. Un automate regulier non universel produirait le meme profil. Discriminer la structure n'est pas mesurer l'universalite.

**Ce que cela change pour la these des « trois negatifs ».** La convergence publiee par la version initiale — plis 4, 7 et 8 tous `NONDISCRIMINANT` — est refutee pour **deux** de ses trois membres : les plis 4 et 7 etaient des artefacts de cadrage zlib (cf. `WOLFRAM-VERDICT-CROSS-CLASSES.md` et `WOLFRAM-VERDICT-KSF.md`), le pli 8 etait une statistique insensible a l'arrangement. Les « trois negatifs convergents » etaient trois defauts d'instrument distincts.

## Limites

- **Seed single pour la mesure canonique** : la robustesse multi-seed est rapportee ci-dessus mais n'est pas committee comme un mode de l'instrument. Un balayage systematique est l'objet du pli 9 (#19847).
- **Estimateur asymptotique** : `c(n)·log2(n)/n` peut depasser `1.0` de quelques centiemes sur les chaines courtes (R30 atteint `1.114` a `W=1`). Propriete connue de l'estimateur, pas une erreur — mais elle interdit de lire la moyenne comme une probabilite.
- **Un seul `W` porte le verdict** : `W=32`. Les autres longueurs de bloc sont mesurees et concordantes, mais le verdict ne teste pas leur accord formellement.
- **Seuil `0.05` non re-derive** : il vient de la version initiale et n'a pas ete recalibre pour l'instrument corrige. Sa valeur n'est pas critique ici (le minimum observe est `0.077`, soit 54 % au-dessus), mais il n'a pas ete choisi pour ce nouvel instrument.

## Reproduction

```bash
export PYTHONPATH=MyIA.AI.Notebooks/IIT/ICT-Series

# Mesure canonique (JSON committe)
python scripts/hashlife/k_trajectory.py --mode wolfram-blocks --n-cells 256 --n-steps 256 --seed 33 \
    --json-out scripts/hashlife/wolfram_blocks_results.json

# Zone sous-alimentee (verdict WOLFRAM-BLOCKS-UNDERPOWERED attendu)
python scripts/hashlife/k_trajectory.py --mode wolfram-blocks --n-cells 64 --n-steps 64 --seed 33

python -m pytest scripts/hashlife/tests/test_wolfram_blocks.py -v
```

## Sources

- Zenil, H., Soler-Toscano, F., & Kiani, N. A. (2013). *A decomposition method for global complexity*. arXiv:1304.5813 [cs.IT].
- Ziv, J. & Lempel, A. (1978). *Compression of individual sequences via variable-rate coding*. IEEE Trans. Info. Theory 24(5): 530-536.
- Li, M. & Vitanyi, P. (2019). *An Introduction to Kolmogorov Complexity and Its Applications*. Springer. 4th ed. Ch. 6 (estimateurs LZ).
- Wolfram, S. (2002). *A New Kind of Science*. Ch. 2-3 (classifications), ch. 7 (Rule 110).
- Cook, M. (2004). *Universality in Elementary Cellular Automata*. Complex Systems 15(1): 1-40.

## Liens

- EPIC Origami #19742
- Pli 1 #19766 : Conscience Origami
- Pli 2 #19796 : organe `ict.wolfram_step` (PR #19793)
- Pli 3 #19813 : K_trajectory Rule 30 / Rule 110 (PR #19815)
- Pli 4 #19818 : K_trajectory cross-classes LZ (PR #19819)
- Pli 7 #19824 : Kolmogorov structure function (PR #19826)
- Pli 8 #19832 : Block decomposition (cette PR)
- Pli 9 #19847 : seed specialise R110
