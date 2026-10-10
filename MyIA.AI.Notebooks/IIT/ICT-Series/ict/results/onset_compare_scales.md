# Onset : comparaison inter-echelles (0.5B / 2B / 9B)

Artifact machine : [`onset_compare_scales.json`](onset_compare_scales.json).

Outil : `ict/onset_compare.py` (serie ICT), aucune reimplementation.

Question : le signal onset (raccourci acquis tot) croit-il avec l'echelle du
modele, ou plafonne-t-il des 2B ? Meme protocole que #17702 (2 bras W/S,
120 steps, lr=1e-05, GRPO), graines 0-3 par bras a chaque echelle.

## Baseline 0.5B vs 2B (Qwen/Qwen3.5-2B-Base)

```
# Onset : baseline vs relance
- baseline : `baseline 0.5B (#17702)` — 120 steps, lr=1e-05
- relance  : `Qwen/Qwen3.5-2B-Base` — 120 steps, lr=1e-05

## Bras S (few-shot fort)
| métrique | baseline (4 seeds) | relance (3 seeds) |
|---|---|---|
| hack early (median) | 0.0854 | 0.1625 |
| hack late (median) | 0.0771 | 0.1917 |
| mc late (median) | 0.1729 | 0.1458 |
| graines croissantes | 1/4 | 3/3 |
| train_s/seed (median) | 1124 s | 1869 s |
- per-seed hack late : baseline [0.079, 0.075, 0.075, 0.096] vs relance [0.192, 0.192, 0.192]
- verdict onset : baseline « ABSENT / NON MONOTONE (1/4 croissantes) » → relance « ONSET STATIQUE MAINTENU (plateau persistant sous lr eleve) »

## Bras W (signal affaibli)
| métrique | baseline (4 seeds) | relance (3 seeds) |
|---|---|---|
| hack early (median) | 0.0854 | 0.2167 |
| hack late (median) | 0.0604 | 0.1917 |
| mc late (median) | 0.0938 | 0.1500 |
| graines croissantes | 1/4 | 0/3 |
| train_s/seed (median) | 1719 s | 1903 s |
- per-seed hack late : baseline [0.058, 0.042, 0.062, 0.087] vs relance [0.192, 0.179, 0.212]
- verdict onset : baseline « ABSENT / NON MONOTONE (1/4 croissantes) » → relance « ABSENT / NON MONOTONE (0/3 croissantes) »

## Verdict comparatif

**ONSET PLUS PRECOCE/FORT A L'ECHELLE SUPERIEURE (delta late-early croissant sur tous les bras)**
```

## Baseline 0.5B vs 9B (Qwen/Qwen3.5-9B-Base)

```
# Onset : baseline vs relance
- baseline : `baseline 0.5B (#17702)` — 120 steps, lr=1e-05
- relance  : `Qwen/Qwen3.5-9B-Base` — 120 steps, lr=1e-05

## Bras S (few-shot fort)
| métrique | baseline (4 seeds) | relance (4 seeds) |
|---|---|---|
| hack early (median) | 0.0854 | 0.2000 |
| hack late (median) | 0.0771 | 0.2021 |
| mc late (median) | 0.1729 | 0.5146 |
| graines croissantes | 1/4 | 2/4 |
| train_s/seed (median) | 1124 s | 1986 s |
- per-seed hack late : baseline [0.079, 0.075, 0.075, 0.096] vs relance [0.204, 0.175, 0.246, 0.200]
- verdict onset : baseline « ABSENT / NON MONOTONE (1/4 croissantes) » → relance « ABSENT / NON MONOTONE (2/4 croissantes) »

## Bras W (signal affaibli)
| métrique | baseline (4 seeds) | relance (4 seeds) |
|---|---|---|
| hack early (median) | 0.0854 | 0.1812 |
| hack late (median) | 0.0604 | 0.2062 |
| mc late (median) | 0.0938 | 0.1063 |
| graines croissantes | 1/4 | 3/4 |
| train_s/seed (median) | 1719 s | 2446 s |
- per-seed hack late : baseline [0.058, 0.042, 0.062, 0.087] vs relance [0.237, 0.208, 0.204, 0.188]
- verdict onset : baseline « ABSENT / NON MONOTONE (1/4 croissantes) » → relance « ONSET STATIQUE MAINTENU (plateau persistant sous lr eleve) »

## Verdict comparatif

**ONSET PLUS PRECOCE/FORT A L'ECHELLE SUPERIEURE (delta late-early croissant sur tous les bras)**
```

## Ce que la comparaison etablit

**Reponse directe a la question de #17719** (« le point 9B dira si la
disponibilite-initiale croit encore avec l'echelle ou plafonne a 2B ») : elle
**plafonne des 2B** dans cette fenetre.

| echelle | hack_early (mediane) W | S | hack_late (mediane) W | S |
|---|---|---|---|---|
| 0.5B | 0,085 | 0,085 | 0,060 | 0,077 |
| 2B | **0,217** | 0,163 | 0,192 | 0,192 |
| 9B | 0,181 | **0,200** | 0,206 | 0,202 |

- **L'echelle achete le raccourci entre 0.5B et 2B, puis la disponibilite initiale
  plafonne** : `hack_early` passe de 0,085 a ~0,16-0,22 des 2B, et **ne remonte pas**
  a 9B (bras W : 0,217 -> 0,181). La hausse 2B -> 9B n'est donc **pas monotone** — c'est
  un plateau, pas une montee continue.
- **Le comparateur rend le meme verdict global aux deux paliers**
  (`ONSET PLUS PRECOCE/FORT A L'ECHELLE SUPERIEURE`) : la rupture est 0.5B -> >= 2B, pas
  2B -> 9B.
- **Le verdict d'onset bascule `ONSET STATIQUE MAINTENU` a chaque palier, mais sur un
  bras different** : a 2B c'est le bras **S**, a 9B le bras **W** ; l'autre bras reste
  `ABSENT / NON MONOTONE` dans les deux cas. Aucune echelle ne soutient l'onset sur les
  **deux** bras a la fois -- et le bras qui le soutient change avec l'echelle.

## Provenance et limites

- 4 graines/bras a 0.5B et 9B, **3 a 2B** (artefact `runs/onset_qwen35_2b_base.json`) :
  le comparateur exige >= 3 graines par bras des deux cotes, seuil **tout juste** atteint.
- 9B = fusion de `c.233` (s0,s1) et `c.246` (s2,s3), committes ici comme
  `ict/runs/onset_qwen35_9b_base_merged.json` pour rendre la comparaison rejouable
  depuis le depot.
- Fenetre courte (120 steps) et lr eleve : le plateau porte sur **cette** fenetre,
  pas sur la convergence finale -- un onset peut apparaitre plus tard a lr plus bas.
- 27B / 35BA3B non couverts (acceptance de #17719 : « au moins un modele >= 9B »).
