# Mesures — premier étage du ping-pong GPU sur une carte 8 Go (`myia-po-2028`)

**Grain** : #21620 (fille de l'EPIC #1454). **Siège** : `myia-po-2028` (RTX 3070 Ti **Laptop, 8 192 Mio**).
**Réservé** au ledger GPU avant tout chargement (`obs-31d2562d3d64b70a`, `held`, puis `released`).
**Harnais** : `scripts/probe_15099_dapo_grpo.py`, protocole **inchangé** (GRPO/TRL + QLoRA, non-thinking, `max_completion` 384, seeds fixées).
**Poids** : snapshot `Qwen/Qwen3.5-0.8B` **`2fc06364715b967f1860aea9cf38778875588b17`** — **exactement** le hash du manifeste de référence `scripts/results/p15294_hermes_grpo/qwen35_seed0.json` : les poids sont bit-identiques au run de référence, **seule la carte change**.
**Dataset** : `hermes` (le substitut documenté du `xlam` *gated* — donc **aucun token HF** requis).

---

## 1. Critère d'accessibilité (mode `baseline`, 160 générations)

Artefact : `../p15294_accessibility/hermes_qwen35.json`.

| | Référence (carte 16 Go, `p15294_hermes_grpo/qwen35_seed0.json`) | **Ici (8 Go)** | Écart |
|---|---:|---:|---:|
| `reward_mean` (160 générations) | **0,20625** | **0,20625** | **0** |
| `length_mean` | 399,29375 | 397,725 | −0,39 % |
| Durée de l'évaluation | — | 977,9 s | — |

**Ce que cela dit** : le **critère d'accessibilité** du 0,8 B sur `hermes` **se rejoue à l'identique** sur une autre carte — le reward moyen tombe au même chiffre au 5ᵉ décimal (33/160 générations correctes dans les deux cas).

**Ce que cela ne dit pas** : les **générations ne sont pas bit-identiques** (longueur moyenne −0,39 %). Le reward, lui, retombe au même nombre : c'est le *critère* qui est stable, pas la génération.

## 2. Boucle GRPO/TRL + QLoRA de bout en bout (mode `smoke`, 3 steps)

Artefact : `qwen35_seed0_smoke.json` (mode smoke : 3 steps, évaluation réduite à 8 prompts × 4 générations = 32).

| | Valeur |
|---|---|
| `pre_eval.reward_mean` (32 générations) | 0,1875 |
| `post_eval.reward_mean` (32 générations) | **0,21875** (Δ **+0,03125**) |
| `pre_eval.length_mean` → `post_eval.length_mean` | 377,78 → 268,44 |
| Entraînement | **3 steps en 574,8 s** (191,6 s/step), `train_loss` −0,1961, `clipped_ratio` 0,0625 |
| Durée totale du run | 1 070,8 s (17,9 min) |
| Adapter QLoRA produit | oui (26,8 Mo, `adapter_model.safetensors`) |

**Ce que cela dit** : la boucle **tourne de bout en bout** sur 8 Go — l'étage *pionnier* sait exécuter le harnais complet, et le reward monte après 3 steps.

**Ce que cela ne dit pas** : **ce n'est pas une mesure de Δ**. 8 prompts, 1 seed, 3 steps : le Δ de +0,031 est dans le bruit. Le run de référence (100 steps, 40 prompts × 4 générations, 2 seeds) a donné +0,0625 (seed 0) et +0,4375 (seed 1) — l'**acceptance ML** de l'EPIC (4 seeds, `dm_p_median < 0,05` sur `mse`/`mae`, rapport de biais par modèle) **n'est pas remplie par ce grain, et ce grain ne prétend pas la remplir**.

## 3. Enveloppe VRAM — la mesure qui manquait à l'EPIC

769 échantillons à 5 s, `nvidia-smi` (utilisation, mémoire, température).

| | Valeur |
|---|---|
| **Pic VRAM** | **7 844 Mio / 8 192 Mio = 95,7 %** |
| Mémoire au repos (modèle déchargé) | 322 Mio |
| Mémoire moyenne sur le run | 4 552 Mio |
| Échantillons > 7 000 Mio (phase d'entraînement) | 286 (~24 min) |
| Utilisation GPU (pic) | 100 % |
| **Température (pic)** | **69 °C** (seuil d'abandon 85 °C non franchi) |

**Lecture d'ingénierie** : l'étage 8 Go exécute le harnais **mais avec 4 % de marge seulement** en phase d'entraînement (QLoRA 4 bits + états d'optimiseur). Toute augmentation de longueur de séquence, de nombre de générations ou de taille de batch fait tomber cet étage en OOM. C'est la donnée qui manquait pour **armer l'étage moyen** : un lead qui dépasse ~7,8 Go n'est pas reprenable par une 8 Go.

**Contrainte de débit, mesurée** : 191,6 s/step ici, contre un run de référence de 47 050 s pour 100 steps + 2 évaluations de 160 générations ; en retranchant deux évaluations de même nature que celle mesurée ici (978 s), l'ordre de grandeur du training de référence est ~450 s/step, soit **× 2,4 plus lent sur 8 Go**. Le modèle est par ailleurs une architecture hybride dont les noyaux optimisés (`flash-linear-attention`, `causal_conv1d`) ne sont pas installés sur ce siège : transformers y replie sur l'implémentation PyTorch de référence, correcte mais « much slower » (avertissement explicite dans les logs).

## 4. Ce qu'il a fallu corriger pour mesurer

`RUNS_ROOT` était codé en dur à `D:/Dev/probe15099_runs` : sur un siège **sans disque D:**, le `mkdir` échouait **avant** la moindre mesure — un échec d'infrastructure déguisé en échec de mesure. Le chemin est désormais surchargeable par `PROBE15099_RUNS_ROOT`, **défaut inchangé** pour les sièges qui l'utilisent.

## 5. Reproductibilité

```powershell
conda create -n coursia-ml-training --override-channels -c conda-forge python=3.12 -y
# torch 2.8.0+cu126 (cu126 = la version de la référence), trl, peft, transformers, datasets, accelerate, bitsandbytes, matplotlib
$env:PROBE15099_RUNS_ROOT = "<racine hors dépôt>"
python scripts/probe_15099_dapo_grpo.py selftest
python scripts/probe_15099_dapo_grpo.py baseline --model qwen35 --dataset hermes
python scripts/probe_15099_dapo_grpo.py smoke --model qwen35 --dataset hermes --seed 0
```

`selftest` : **17/17** (dapo 10/10, xlam 7/7).
