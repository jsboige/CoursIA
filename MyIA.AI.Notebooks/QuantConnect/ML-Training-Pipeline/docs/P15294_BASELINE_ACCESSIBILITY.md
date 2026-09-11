# P15294 — Matrice baseline d'accessibilite (probe B)

Mesure du critere de calibration de #15294 : l'**accessibilite** d'un dataset
pour un backbone = `reward_mean` du modele de base (sans entraînement) sur le
split d'eval du harnais probe. Fenetre cible **20-60 %** — en dessous de ~20 %
un groupe GRPO de 4 generations est majoritairement uniforme (pas de signal de
gradient), au-dessus de ~80 % le dataset ne discrimine plus (trop facile).

Complète la note de veille [`P15294_SMALL_MODEL_RL_DATASETS.md`](P15294_SMALL_MODEL_RL_DATASETS.md)
(acceptance 1) en livrant l'acceptance 2 (runs probe) et les données de la
comparaison vs DAPO-Math-17k (acceptance 3, voir #15099 / #15249).

## Protocole (probe B, inchangé)

| Paramètre | Valeur |
|---|---|
| Modèles | MiniCPM5-2B, Qwen3.5-0.8B (4-bit NF4) |
| Datasets | GSM8K-train, Hermes-function-calling-v1 singleturn, DAPO-Math-17k |
| `EVAL_N_PROMPTS` | 40 |
| `EVAL_GENS` | 4 (échantillonnage — 160 générations par run) |
| `MAX_COMPLETION` | 384 |
| `SPLIT_SEED` | 0 (fixe — split déterministe) |
| Mode chat | nonthinking |
| Run | `probe_15099_dapo_grpo.py baseline --model <k> --dataset <k>` |

xlam-function-calling-60k est couvert par le substitut documenté Hermes
(`P15294_SMALL_MODEL_RL_DATASETS.md` — accès gated xlam).

## Résultats

| Dataset | Backbone | accessibilité (reward_mean) | n_gens | length_mean | wallclock_s |
|---|---|---|---|---|---|
| GSM8K-train | MiniCPM5-2B | **0,4313** | 160 | 406,1 | 1597 |
| GSM8K-train | Qwen3.5-0.8B | **0,1437** | 160 | 648,6 | 2222 |
| Hermes-function-calling-v1 (singleturn) | MiniCPM5-2B | **0,2313** | 160 | 324,6 | 1424 |
| Hermes-function-calling-v1 (singleturn) | Qwen3.5-0.8B | **0,2000** | 160 | 407,7 | 1789 |
| DAPO-Math-17k | MiniCPM5-2B | *en cours d'exécution* | | | |
| DAPO-Math-17k | Qwen3.5-0.8B | *en cours d'exécution* | | | |

JSON bruts : `scripts/results/p15294_accessibility/` (non committe —
`results/` est gitignore ; la table ci-dessus est la reference).

## Lecture de calibration

- **MiniCPM5-2B** : GSM8K 0,43 — dans la fenêtre ; Hermes 0,23 — dans la
  fenêtre. Les deux datasets sont exploitables pour un entraînement GRPO sur
  ce backbone.
- **Qwen3.5-0.8B** : Hermes 0,20 — à la limite basse exacte de la fenêtre ;
  GSM8K **0,14 — sous la fenêtre** : ~86 % des groupes de 4 générations sont
  probablement uniformes (tout-échec), le signal de gradient attendu d'un
  GRPO sur ce couple est faible. Le couple GSM8K × Qwen3.5-0.8B n'est pas un
  candidat d'entraînement sans relance du protocole (k générations plus
  grand, ou prompts plus faciles).
- La comparaison vs DAPO-Math-17k (le BEATS de #15099 était-il un artefact
  de casting ?) sera tranchée par les deux runs DAPO en cours et ajoutée ici.

## Reproduction

```bash
python scripts/probe_15099_dapo_grpo.py baseline --model minicpm5 --dataset gsm8k
```

GPU requis (4-bit NF4) ; prévoir ~25-40 min par run selon le backbone.
