# Origami Wolfram — pli 9 : seed specialise R110 (0001000) + 3 complexites

**Verdict corrige (2026-10-09)** : `WOLFRAM-SEED-TEST-DISCRIMINANT_FAIBLE` —
9 verdicts DISCRIMINANT sur 12, controle `random-dense` NONDISCRIMINANT sur
les trois instruments.

**Correction du 2026-10-09** (reserve c.6078963240) : le verdict initial,
mesure a n=64 avec les instruments pre-correctif, **ne survivait pas a la
mesure**. Regeneres a n=512 avec les instruments corriges des plis freres,
les resultats s'inversent dans les deux sens :

- `wolfram-0001000` : `NONDISCRIMINANT` (LZ) -> `DISCRIMINANT` (trois
  instruments) ;
- `random-dense` : `DISCRIMINANT` x3 -> `NONDISCRIMINANT` x3.

**Conclusion honnete : le facteur confondant etait l'ECHELLE, pas le seed.**
Les verdicts de non-discrimination publies a n=64 etaient des artefacts de
saturation de l'instrument (fenetre packee sous le plancher de cadrage zlib),
pas une propriete des automates.

## Perimetre (premisse corrigee)

La premisse initiale du pli 9 etait : « pli 4 (LZ), pli 7 (KSF) et pli 8
(block decomposition) ont converge vers le meme verdict NONDISCRIMINANT a
n=64 avec seed single-cell ; tester le seed canonique avant d'ecarter la
discrimination ». Cette premisse est **fausse en son constat** : les trois
plis freres ont ete corriges sur leurs branches (corrections du 2026-10-09,
mesures firsthand) :

- pli 4 rend `WOLFRAM-4CLASSES-III/IV-INVERSE` a n=1024 (sortie de la zone
  de saturation zlib) ;
- pli 7 rend `WOLFRAM-KSF-DISCRIMINANT` a n_cells = 512 (unite corrigee :
  bits par cellule, facteur 8) ;
- pli 8 rend `WOLFRAM-BLOCKS-DISCRIMINANT` a n=256 (statistique corrigee :
  complexite LZ76, sensible a l'arrangement).

Ils ne convergent plus vers NONDISCRIMINANT. La question du pli 9 devient
donc : **le seed est-il un facteur confondant une fois l'echelle et les
instruments corriges ?**

## Corrections portees par ce pli

1. **KSF en bits par cellule** (port pli 7, correctif #19826) :
   `ksf_last_bits_per_cell = ksf_mean(octets) * 8 / n_cells`. La version
   initiale comparait des octets a des reperes en bits/cellule — facteur 8.
2. **Blocks en complexite LZ76 normalisee** (port pli 8, correctif #19836) :
   `normalized_lz76_complexity` = c(n)·log2(n)/n par bloc, sensible a
   l'arrangement. La version initiale agregeait l'entropie de Shannon,
   **invariante a l'arrangement** : H('0101...01') == H(desordre equilibre)
   — un verdict tire de cette statistique etait une tautologie
   d'instrument. L'entropie reste mesuree et commitee (`entropy_*`) pour
   tracabilite.
3. **Garde d'echelle** : `WOLFRAM_SEED_MIN_N_CELLS = 512`. Sous ce plancher,
   le verdict rend `WOLFRAM-SEED-SATURATED` sur toutes les cellules et le
   CLI **refuse** d'ecrire le JSON de resultats — un artefact de saturation
   ne se publie plus.
4. **Plancher absolu du verdict** : `WOLFRAM_SEED_ABS_DELTA_FLOOR = 0.05`.
   La version initiale normalisait par `max(abs(v30), abs(v110))` sans
   plancher : sur une paire de valeurs proches de zero, un delta de bruit
   (0.027) prend un ratio de 0.307 et un DISCRIMINANT se fabrique. Le delta
   absolu tranche **avant** le ratio. La valeur 0.05 est le seuil WEAK deja
   present dans le code avant correction ; les deltas mesures a n=512 sont
   >= 0.229 (signaux) et <= 0.027 (bruit) — le plancher ne deplace aucune
   frontiere contestee.

## Conditions de seed testees

| Preset | Pattern | Source |
|---|---|---|
| `single-cell` | cellule centrale unique allumee, reste eteint | baseline plis 4/7/8 |
| `wolfram-0001000` | pattern `0001000` repete (fond periodique 7-cell) | Wolfram 2002 ch. 7 (Turing-completude) |
| `wolfram-defect` | `0001000` repete sauf defaut local au centre | Cook 2004 (preuve d'universalite R110) |
| `random-dense` | pattern `10110011` repete | controle (les deux regles y sont periodiques) |

## Mesures verbatim (n_cells = 512, n_steps = 512)

Source : `wolfram_seed_test_results.json` regenere par le commit de
correction (pas de re-edition manuelle — les tables ci-dessous sont l'emission
directe du JSON).

### Preset = single-cell (baseline plis 4/7/8)

| Rule | Class | LZ ratio | KSF bits/cellule (W=32) | Blocks LZ76 std@W32 |
|---|---|---:|---:|---:|
| 0  | I   | 0.020 | 0.031 | 0.000 |
| 4  | II  | 0.026 | 0.000 | 0.000 |
| 30 | III | 0.747 | 0.691 | 0.308 |
| 110| IV  | 0.298 | 0.211 | 0.064 |

R30 vs R110 — LZ : abs 0.449, ratio 0.601 ; KSF : abs 0.479, ratio 0.694 ;
blocks : abs 0.244, ratio 0.792.

### Preset = wolfram-0001000 (seed canonique Wolfram 2002 ch. 7)

| Rule | Class | LZ ratio | KSF bits/cellule (W=32) | Blocks LZ76 std@W32 |
|---|---|---:|---:|---:|
| 0  | I   | 0.022 | 0.031 | 0.001 |
| 4  | II  | 0.024 | 0.000 | 0.000 |
| 30 | III | 0.752 | 0.585 | 0.287 |
| 110| IV  | 0.338 | 0.233 | 0.042 |

**C'est la refutation centrale.** La version initiale publiait « avec le seed
canonique, R30 et R110 sont indistinguables en LZ (0.584 vs 0.571, delta
0.013) ». A n=512, le meme seed donne **0.752 vs 0.338, delta absolu 0.414,
ratio 0.550** : l'instrument discrimine largement. Le seed canonique
**n'etait pas** le facteur confondant — c'etait la saturation a n=64.

### Preset = wolfram-defect (Cook 2004)

| Rule | Class | LZ ratio | KSF bits/cellule (W=32) | Blocks LZ76 std@W32 |
|---|---|---:|---:|---:|
| 0  | I   | 0.030 | 0.031 | 0.001 |
| 4  | II  | 0.013 | 0.000 | 0.000 |
| 30 | III | 0.909 | 0.993 | 0.303 |
| 110| IV  | 0.670 | 0.719 | 0.074 |

R30 vs R110 — LZ : abs 0.239, ratio 0.263 ; KSF : abs 0.274, ratio 0.276 ;
blocks : abs 0.229, ratio 0.755.

### Preset = random-dense (controle)

| Rule | Class | LZ ratio | KSF bits/cellule (W=32) | Blocks LZ76 std@W32 |
|---|---|---:|---:|---:|
| 0  | I   | 0.019 | 0.031 | 0.001 |
| 4  | II  | 0.019 | 0.031 | 0.001 |
| 30 | III | 0.088 | 0.019 | 0.005 |
| 110| IV  | 0.061 | 0.000 | 0.002 |

**La seconde refutation — le controle s'inverse.** La version initiale
publiait random-dense `DISCRIMINANT` x3 au motif d'un deraillement R110 (KSF
delta -3.000). A n=512, les deux regles y sont periodiques et **proches du
zero** : deltas absolus 0.027 / 0.019 / 0.003, tous sous le plancher —
NONDISCRIMINANT x3. Le plancher absolu joue ici son role exactement : les
ratios bruts (0.305 en LZ, 0.995 en KSF, 0.588 en blocks) auraient fabrique
trois DISCRIMINANT de bruit sous l'ancienne regle ratio-seule. L'ancienne
« curiosite » documentee etait un artefact d'echelle.

## Verdict discrimination R30 vs R110

| Preset / Instrument | LZ | KSF | Blocks |
|---|:---:|:---:|:---:|
| single-cell       | DISCRIMINANT | DISCRIMINANT | DISCRIMINANT |
| wolfram-0001000   | DISCRIMINANT | DISCRIMINANT | DISCRIMINANT |
| wolfram-defect    | DISCRIMINANT | DISCRIMINANT | DISCRIMINANT |
| random-dense      | NONDISCRIMINANT | NONDISCRIMINANT | NONDISCRIMINANT |

**Verdict global** : `DISCRIMINANT_FAIBLE` (9/12) — les trois instruments
discriminent R30 de R110 sur tous les presets **sauf le controle**, ou les
deux regles sont periodiques et indistinguables par construction.

## Conclusions epistemologiques (reecrites)

1. **Le facteur confondant etait l'echelle, pas le seed.** L'hypothese du
   pli 8 (c.112) — « le verdict NONDISCRIMINANT est conditionne au seed
   single-cell » — est refutee par la mesure : a n=512, le meme instrument
   discrimine sous **tous** les seeds testes, y compris single-cell. Ce qui
   manquait a n=64 n'etait pas le bon seed, c'etait la place pour que zlib
   distingue le contenu du cadrage.

2. **Le controle fait ce qu'un controle doit faire.** random-dense rend
   NONDISCRIMINANT x3 : deux regles periodiques y sont indistinguables, et
   le plancher absolu empeche le ratio de fabriquer du signal sur du bruit.
   La version initiale lisait l'inverse (DISCRIMINANT x3) — signe que
   l'instrument mesurait son propre artefact, pas les automates.

3. **Les trois instruments corriges convergent.** LZ, KSF (bits/cellule) et
   blocks (LZ76) donnent le meme verdict par preset pour la premiere fois de
   la serie : la coherence inter-instruments est le meilleur temoin que la
   correction d'unite/statistique a fait converger les instruments vers la
   meme grandeur physique.

4. **La discrimination ne depend pas du seed canonique.** La
   Turing-completude de R110 ne requiert pas le seed `0001000` pour etre
   **statistiquement** distinguee de R30 par complexite de trajectoire a
   cette echelle — la difference se lit dans la structure de la trajectoire
   (compressibilite, prediction par contexte, heterogeneite par bloc), pas
   dans le declencheur initial.

## Limites mesurees

- **n=512, n_steps=512** : plancher de la zone concluante (pli 7). Les
  mesures hors echantillon a plus grande echelle restent a verifier.
- **Un seul seed par preset** (patterns deterministes) — pas de mesure
  cross-seed statistique ; la validation 5-10 seeds par preset reste un
  travail futur (pli 10+).
- **Le verdict random-dense NONDISCRIMINANT est attendu par construction**
  (les deux regles y sont periodiques) : c'est un controle de bruit, pas un
  cas discriminant qui echoue.

## Livrables du pli 9 (corriges)

- `scripts/hashlife/k_trajectory.py` : mode `--wolfram-seed-test` avec
  `WOLFRAM_SEED_PRESETS`, `wolfram_seed_preset`,
  `wolfram_trajectory_from_state`, `measure_seed_instrument_landscape`,
  `seed_discrimination_verdict`, `cmd_wolfram_seed_test` ; garde
  `WOLFRAM_SEED_MIN_N_CELLS`, plancher `WOLFRAM_SEED_ABS_DELTA_FLOOR` ;
  ports byte-identiques de `lz76_factor_count`,
  `normalized_lz76_complexity`, `_bits_to_str`,
  `block_complexity_distribution` (correctifs plis 7/8, pour une rebase de
  pile sans conflit de contenu).
- `scripts/hashlife/wolfram_seed_test_results.json` : regenere a n=512 par
  execution reelle du mode (4 min de calcul, JSON ecrit par l'instrument).
- `scripts/hashlife/WOLFRAM-VERDICT-SEED-TEST.md` (ce document) : premisse,
  tables, verdict et conclusions reecrits sur la mesure corrigee.
- `scripts/hashlife/tests/test_wolfram_seed_test.py` : tests reecrits —
  gardes d'echelle, plancher absolu (controle du DISCRIMINANT fabrique),
  instruments portes, unites corrigees, JSON committe a n=512.
- `scripts/hashlife/README.md` : usage pli 9 a l'echelle canonique.

## References

- Wolfram, S. (2002). *A New Kind of Science*. Ch. 7, §7-9. Seed `0001000`
  background, demonstration de la machine de Turing par Rule 110.
- Cook, M. (2004). *Universality in Elementary Cellular Automata*. Complex
  Systems 15(1). Conditions de seed pour la preuve d'universalite R110.
- Zenil, H., et al. (2013). *A decomposition method for global complexity*.
  arXiv:1304.5813. Block decomposition (K(bloc), pas entropie marginale).
- Ziv, J. & Lempel, A. (1978) ; Li, M. & Vitanyi, P. (2019) ch. 6.
  Factorisation LZ76, estimateur normalise c(n)·log2(n)/n.
- Pli 4 #19819 — corrige : `WOLFRAM-4CLASSES-III/IV-INVERSE` a n=1024.
- Pli 7 #19826 — corrige : `WOLFRAM-KSF-DISCRIMINANT` a n_cells = 512
  (unite bits/cellule).
- Pli 8 #19836 — corrige : `WOLFRAM-BLOCKS-DISCRIMINANT` a n=256
  (statistique LZ76).
- Pli 9 = ce grain, corrige le 2026-10-09 (reserve c.6078963240) :
  `DISCRIMINANT_FAIBLE` (9/12) a n=512 — le facteur confondant etait
  l'echelle, pas le seed.
