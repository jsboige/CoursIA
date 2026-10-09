# WOLFRAM-VERDICT-KSF — Kolmogorov structure function Rule 30 vs Rule 110

**Suite Origami pli 7.** Constat : pli 4 (LZ fenetre, c.110) n'a pas discrimine Rule 30 (chaotique) de Rule 110 (Turing-complet). Ce pli etend le discriminant a K(W|W'), la **Kolmogorov structure function** (Vereshchagin & Vitanyi 2004) — l'instrument canonique pour discriminer entropie aleatoire d'entropie structuree.

**Correction du 2026-10-09** : le verdict initial (`WOLFRAM-KSF-NONDISCRIMINANT`) etait un **artefact d'echelle et d'unite**, pas un resultat de contenu. Les deux defauts sont mesures et corriges ci-dessous.

## Perimetre

Mesure `K_trajectory --mode wolfram-ksf` (pli 7, c.111) sur les 4 classes canoniques de Wolframe :

| Regle | Classe | Comportement attendu pour KSF |
|-------|--------|-------------------------------|
| 0     | I (uniforme) | 0 (deterministe, contexte capture tout) |
| 4     | II (periodique) | 0 (deterministe, contexte capture tout) |
| 30    | III (chaotique) | 1.0 bit/cellule (entropie maximale, contexte n'aide pas) |
| 110   | IV (Turing-complet) | intermediaire (contexte capture gliders et reactions) |

## Les deux defauts de la mesure initiale

### a) Unite : KSF etait rendue en octets, comparee a des landmarks en bits/cellule

`ksf_trajectory` rend `ksf_mean` en **octets** (difference de longueurs LZ). Les landmarks `WOLFRAM_KSF_LANDMARKS` sont des **bits par cellule**. Le verdict comparait donc directement des octets a des bits.

Pour une trajectoire incompressible, `ksf_mean` vaut `n_cells / 8` octets, c'est-a-dire **exactement 1.0 bit par cellule** — le plancher d'entropie, pas un plafond de compresseur. A n_cells = 64 : `ksf_mean = 8.000` octets, soit **1.0 bit/cellule**.

Le rapport initial lisait ces 8.000 comme des bits et concluait « 8/64 = 12.5 % de l'entropie maximale ». C'est un **facteur 8** : la valeur normalisee correcte est 100 %, et c'est precisement ce que predit la theorie pour Rule 30.

Le resultat porte desormais sa propre normalisation (`ksf_bits_per_cell = ksf_mean * 8 / n_cells`), seule echelle commensurable aux landmarks.

### b) Echelle : n_cells = 64 est sous le plancher de cadrage zlib

A n_cells = 64, chaque etat packe ne porte que 8 octets, sous le plancher de cadrage zlib (~11 octets par bloc stocke). La fenetre packee d'une mesure W reste trop courte pour que zlib distingue contenu et cadrage : **R30 et R110 rendent la meme constante**, et la « non-discrimination » mesuree n'etait que le cadrage de l'instrument.

Mesure firsthand (2026-10-09) : a n_cells = 64, R30 et R110 rendent tous deux `ksf_mean = 8.000` = `n_cells / 8`, a toutes les tailles de contexte W >= 8.

L'instrument declare donc desormais `WOLFRAM-SATURATED` sous `n_cells < 512` (constante `WOLFRAM_KSF_MIN_N_CELLS`) : dans cette zone, toute discrimination comme toute non-discrimination est un artefact.

## Mesure corrigee (hors saturation)

**n_cells = 1024, n_steps = 1024, seed = 33** (mesure canonique, `wolfram_ksf_results.json` committe). KSF en bits par cellule, W = 32 :

| Regle | Classe | KSF(W=1) | KSF(W=32) | Landmark | Verdict |
|-------|--------|----------|-----------|----------|---------|
| 0     | I      | 0.008    | 0.008     | 0.000    | CLASS-I-CONFIRMED (delta 0.008) |
| 4     | II     | 0.032    | 0.000     | 0.000    | CLASS-II-CONFIRMED (delta 0.000) |
| 30    | III    | 1.000    | **1.000** | 0.850    | CLASS-III-CONFIRMED (delta 0.150) |
| 110   | IV     | 0.751    | **0.376** | 0.200    | CLASS-IV-CONFIRMED (delta 0.176) |

**n_cells = 512, n_steps = 512, seed = 33** (plancher de la zone concluante) :

| Regle | Classe | KSF(W=32) | Landmark | Verdict |
|-------|--------|-----------|----------|---------|
| 0     | I      | 0.031     | 0.000    | CLASS-I-CONFIRMED |
| 4     | II     | -0.016    | 0.000    | CLASS-II-CONFIRMED |
| 30    | III    | 1.000     | 0.850    | CLASS-III-CONFIRMED |
| 110   | IV     | 0.507     | 0.200    | CLASS-IV-DEVIATION (delta 0.307) |

## Resultats falsifiables

### 1. Discrimination Rule 30 vs Rule 110 par KSF : **DISCRIMINANT**

A W = 32 (contexte maximal), hors saturation : KSF(R30) = **1.000** bit/cellule, KSF(R110) = **0.376** bit/cellule a n = 1024 ; **delta = 0.624**.

**Verdict final** : `WOLFRAM-KSF-DISCRIMINANT` — la Kolmogorov structure function **separe** le chaos de la structure Turing-complete des que la mesure sort de la zone saturee, contrairement a ce que concluait la mesure a n_cells = 64.

### 2. Les landmarks theoriques sont confirmes empiriquement

Les quatre classes tombent dans la fenetre de tolerance (0.20 bit/cellule) de leur landmark a n = 1024 : R0 et R4 sur 0.000, R30 sur 0.850 (observe 1.000), R110 sur 0.200 (observe 0.376). La ligne « landmarks non valides, a recalibrer » de la version precedente est levee : l'ecart venait de l'unite, pas du landmark.

### 3. Convergence en n — un plancher, pas une asymptote

R110 decroit vers son landmark avec la taille : 0.507 (n=512, deviation) puis 0.376 (n=1024, confirme). La convergence n'est pas encore asymptotique : la part de la structure de R110 que la fenetre W = 32 capture croit avec n. Rule 30 est insensible a n (1.000 a toutes les echelles mesurees : entropie maximale a chaque pas).

### 4. Ce que la mesure dit et ne dit pas

KSF(W) mesure la **redondance locale du dernier pas sachant une fenetre de W etats**. Elle discrimine R30 de R110 des que la fenetre est mesurable — mais elle ne mesure pas la **Turing-completude** elle-meme : R110 est compressible parce que sa trajectoire est **reguliere** (fond periodique, gliders), pas parce qu'elle est universelle. Un automate regulier non universel produirait le meme KSF. La lecture epistemique de la tranche 1 (« l'instrument detecte la regularite, pas l'auto-entretien ») tient donc, mais elle ne s'ecrit plus comme une **non-discrimination**.

## Conclusion epistemologique

**Pli 7 corrige pli 4 plutot qu'il ne le confirme.** La these « les complexites de trajectoire 1-D ne discriminent pas chaos et Turing-complet » etait portee par une mesure saturee. Hors saturation, KSF discrimine, et les landmarks de la theorie sont retrouves.

Ce qui reste vrai et non-trivial : KSF mesure une **regularite de trajectoire**, pas une **classe de computation**. Discriminer chaos et Turing-completude par une mesure de complexite demande un instrument qui capte la **structure non-locale** (le programme, pas la trajectoire) :

- **Block decomposition** (Zenil et al.) — pli 8, mesure deja instrumentee (#19836).
- **SAT-based minimal program** — mesure directe de Kolmogorov.
- **Causal graph analysis** (Zenil 2013) — profondeur du graphe causal.

## Sources

- Vereshchagin, N. & Vitanyi, P. (2004). *Kolmogorov structure functions and model selection*. IEEE Trans. Info. Theory 50(12): 3265-3290.
- Li, M. & Vitanyi, P. (2019). *An Introduction to Kolmogorov Complexity and Its Applications*. Springer. 4th ed. Ch. 6-7.
- Cook, M. (2004). *Universality in Elementary Cellular Automata*. Complex Systems 15(1): 1-40.
- Wolfram, S. (2002). *A New Kind of Science*. Ch. 7.

## Reproduction

```bash
export PYTHONPATH=MyIA.AI.Notebooks/IIT/ICT-Series

# Zone saturee (verdict WOLFRAM-KSF-SATURATED attendu)
python scripts/hashlife/k_trajectory.py --mode wolfram-ksf --all --n-cells 64 --n-steps 64

# Plancher de la zone concluante
python scripts/hashlife/k_trajectory.py --mode wolfram-ksf --all --n-cells 512 --n-steps 512

# Mesure canonique (JSON committe)
python scripts/hashlife/k_trajectory.py --mode wolfram-ksf --all --n-cells 1024 --n-steps 1024 \
    --json-out scripts/hashlife/wolfram_ksf_results.json

python -m pytest scripts/hashlife/tests/test_wolfram_ksf.py -v
```

## Limites

- **Horizon W = 32** : la fenetre max reste 2^5 etats. A n grand, W_last ne couvre qu'une fraction de la trajectoire ; la convergence de R110 vers son landmark (0.507 -> 0.376) n'est pas encore asymptotique.
- **Seed = 33 unique** : pas de multi-seed ; la robustesse du contenu R110 a la densite initiale reste a mesurer.
- **n_cells = 1024** : le cout de la mesure croit avec n x 2^W ; au-dela, un comptage de facteurs LZ76 remplacerait zlib sans changer la nature du resultat.
- **zlib comme approximateur de K** : borne superieure atteignable, sensible au build (~3 % mesure entre postes). La discrimination (1.000 vs 0.376) est tres au-dessus de ce bruit.

## Suite Origami

- **Pli 5/6** : bloques par env Lean/JVM absent (routeur po-2023/ai-01 WSL).
- **Pli 8** : Block decomposition (Zenil), instrumentee (#19836), meme question de discriminant.
- **Pli 9+ (propose)** : SAT-based minimal program, causal graph analysis.

## Conclusion forte

K_trajectory (LZ fenetre, pli 4) restait non discriminant a n = 64 ; la Kolmogorov structure function (pli 7), une fois corrigee de son erreur d'unite et mesuree hors de la zone de saturation zlib, **discrimine** Rule 30 (1.000 bit/cellule, entropie maximale) de Rule 110 (0.376, structure reguliere compressible), et **retrouve les quatre landmarks de la theorie**. Ce qui demeure hors de portee de cette famille d'instruments n'est pas la separation chaos/structure — elle est acquise — mais la mesure de la **Turing-completude** elle-meme, qui demande un instrument non-local.
