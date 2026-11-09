# Mesures — premier étage du ping-pong GPU sur une carte 8 Go (`myia-po-2028`)

**Grain** : #21620 (fille de l'EPIC #1454). **Siège** : `myia-po-2028` (RTX 3070 Ti **Laptop, 8 192 Mio**).
**Réservé** au ledger GPU avant tout chargement (`obs-31d2562d3d64b70a` pour la première exécution, `obs-541b109cb4c0be16` pour l'exécution instrumentée du §3, puis `released`).
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
**Série VRAM de la même exécution** : `vram_smoke_seed0.jsonl` (+ `vram_smoke_seed0.meta.json`, `vram_smoke_seed0.aggregats.json`) — voir §3.

| | Valeur |
|---|---|
| `pre_eval.reward_mean` (32 générations) | 0,1875 |
| `post_eval.reward_mean` (32 générations) | **0,25** (Δ **+0,0625**) |
| `pre_eval.length_mean` → `post_eval.length_mean` | 377,78 → 276,09 |
| Entraînement | **3 steps en 705,5 s** (235,2 s/step), `train_loss` −0,2080 |
| `clipped_ratio` par step | 0,0625 / 0,03125 / 0 (moyenne **0,03125**) |
| Durée totale du run | 1 355,8 s (22,6 min) |
| Adapter QLoRA produit | oui (26,8 Mo, `adapter_model.safetensors`) |

`log_history` : **4 entrées** (3 steps + l'agrégat final `train_runtime` 705,5 s / `train_loss` −0,2080).

**Ce que cela dit** : la boucle **tourne de bout en bout** sur 8 Go — l'étage *pionnier* sait exécuter le harnais complet, et le reward monte après 3 steps.

**Ce que cela ne dit pas** : **ce n'est pas une mesure de Δ**. 8 prompts, 1 seed, 3 steps : le Δ de +0,0625 est dans le bruit. Le run de référence (100 steps, 40 prompts × 4 générations, 2 seeds) a donné +0,0625 (seed 0) et +0,4375 (seed 1) — l'**acceptance ML** de l'EPIC (4 seeds, `dm_p_median < 0,05` sur `mse`/`mae`, rapport de biais par modèle) **n'est pas remplie par ce grain, et ce grain ne prétend pas la remplir**.

**Ce qui n'est pas reproductible au bit près** : le **pas 3** diverge d'une exécution à l'autre (noyaux non déterministes) — une exécution antérieure de la configuration identique a donné `post_eval.reward_mean` 0,21875 et `train_loss` −0,1961, alors que les pas 1 et 2 étaient identiques au bit près. Tous les chiffres de cette page sont ceux de l'exécution **instrumentée** ci-dessous, dont l'artefact et la série VRAM sont committés.

## 3. Enveloppe VRAM — la mesure qui manquait à l'EPIC

**Série brute committée** : `vram_smoke_seed0.jsonl` — une ligne par échantillon (`t`, `elapsed_s`, `mem_used_MiB`, `util_pct`, `temp_C`), prélevées par `scripts/probe_15099_vram_sampler.py`, **l'instrument est dans le harnais**. Le sidecar `vram_smoke_seed0.meta.json` porte la cadence **déclarée**, la carte et la raison d'arrêt ; `vram_smoke_seed0.aggregats.json` porte les agrégats **dérivés** de la série (rien n'est saisi à la main). La série couvre **l'exécution entière** — évaluation pré, entraînement, évaluation post : 1 364,1 s d'échantillonnage pour 1 355,8 s de run.

| | Valeur |
|---|---|
| **Pic VRAM** | **7 803 Mio / 8 192 Mio = 95,3 %** (19:32:52Z) |
| Mémoire au repos (début de série, avant chargement) | 374 Mio |
| Mémoire moyenne sur le run | 6 112,6 Mio (médiane 7 757) |
| **Fenêtre > 7 000 Mio** | **830 échantillons consécutifs, 829,1 s** (19:27:43 → 19:41:32Z) |
| Utilisation GPU (pic) | 100 % |
| **Température (pic)** | **69 °C** (seuil d'abandon 85 °C non franchi) |
| Cadence | **1,0 s déclarée** ; observée : min 0,968 s · **médiane 1,000 s** · max 1,062 s |

### La fenêtre haute est alignée sur la phase d'entraînement

| Phase | Fenêtre (UTC) | Mémoire |
|---|---|---|
| Évaluation pré | 19:18:50 → 19:25:58 (427 s) | 431 → 3 347 Mio (médiane 2 689) |
| Entraînement, montée | 19:25:58 → 19:27:43 (105 s) | 3 326 → 7 694 Mio (médiane 6 796) |
| Entraînement, régime | 19:27:43 → 19:37:44 (600 s) | 7 694 → **7 803 Mio** (médiane 7 763) |
| Évaluation post | 19:37:44 → 19:41:31 (228 s) | 7 743 → 7 771 Mio |

Les bornes de phase sont celles imprimées par le harnais (`pre-eval:`, `post-eval:`, fin de la barre `3/3`) : la fenêtre d'entraînement ainsi reconstruite dure **705,9 s**, contre les **705,5 s** de `train_runtime` déclarés par le harnais — enveloppe et durée d'entraînement se recoupent.

Les 830 échantillons au-dessus de 7 000 Mio ne sont donc **pas** « la phase d'entraînement » : ils couvrent les **600 dernières secondes de l'entraînement** — les 105 premières restent à ~6 800 Mio, pendant l'allocation des états de l'optimiseur — **plus les 228 s de l'évaluation finale**. C'est exactement la confusion que la version précédente de cette page portait (« 286 échantillons > 7 000 Mio (~24 min) ») : ces 286 échantillons ne pouvaient pas couvrir 24 min dans un run de 17,9 min.

**Lecture d'ingénierie** : l'étage 8 Go exécute le harnais **mais avec 4,7 % de marge seulement** en régime d'entraînement (QLoRA 4 bits + états d'optimiseur). Toute augmentation de longueur de séquence, de nombre de générations ou de taille de batch fait tomber cet étage en OOM. C'est la donnée qui manquait pour **armer l'étage moyen** : un lead qui dépasse ~7,8 Go n'est pas reprenable par une 8 Go.

**Contrainte de débit, mesurée** : 235,2 s/step ici, contre un run de référence de 47 050 s pour 100 steps + 2 évaluations de 160 générations ; en retranchant deux évaluations de même nature que celle mesurée ici (978 s), l'ordre de grandeur du training de référence est ~451 s/step, soit **× 1,9 plus lent sur 8 Go**. Le modèle est par ailleurs une architecture hybride dont les noyaux optimisés (`flash-linear-attention`, `causal_conv1d`) ne sont pas installés sur ce siège : transformers y replie sur l'implémentation PyTorch de référence, correcte mais « much slower » (avertissement explicite dans les logs).

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

La série VRAM du §3 se collecte en **concomitance** du run `smoke` : l'échantillonneur tourne dans un second processus, cadencé par `--interval`, et s'arrête sur un fichier sentinelle (`--stop-file`) créé par le wrapper du run — de sorte que la série couvre l'exécution entière, du chargement du modèle au déchargement :

```powershell
python scripts/probe_15099_vram_sampler.py --out "<racine>/vram_smoke_seed0.jsonl" --interval 1.0 --gpu 0 --stop-file "<racine>/STOP"
```

## 6. Le classement 2B > 0,8 B se rejoue-t-il à l'étage 8 Go ?

Le verdict de paire 2B > 0,8 B (`../../docs/P15294_SMALL_MODEL_RL_DATASETS.md`, acceptances 2-3 closes) a été établi avec le 0,8 B sur l'étage 16 Go et le 2 B **déjà sur une 3070 à 8 Go** : les manifestes 2 B existaient à l'étage pionnier, mais hors de ce dossier. Cette section les relie à l'étage.

**Le 2 B a tourné en run complet à l'étage 8 Go** — chaîne détachée sur le 3070, manifestes `../p15294_hermes_grpo/minicpm5_seed{0,1}.json`, mode `run` 100 steps, même recette (GRPO+QLoRA non-thinking, complétion ≤ 384, held-out 40 prompts × 4 générations) :

| seed | pre | post | Δ | wallclock |
|---|---:|---:|---:|---:|
| 0 | 0,2125 | 0,64375 | **+0,43125** | 10 656,5 s |
| 1 | 0,2500 | 0,68125 | **+0,43125** | 7 687,7 s |

Provenance de la carte : le doc de référence écrit « en chaîne détachée sur le 3070 » (§ verdict de paire) et l'observation `obs-a97fc8fc7aea275b` du ledger GPU la précise (« les seeds 0/1 viennent de la 3070 de po-2024 »). Les manifestes ne portent pas de champ carte — l'attestation est **croisée sur ces deux sources**, pas auto-portée par les artefacts.

**Énoncé d'étage** :

1. **Le classement ne se déplace pas par inaccessibilité** : les deux backbones de la paire s'exécutent à l'étage 8 Go — le 2 B en run complet (2 seeds, 100 steps, contrôle de dégénérescence du doc de référence : signature inverse du no-op `m19`), le 0,8 B en critère d'accessibilité + boucle smoke (§1-§2).
2. **Il se rejoue en tendance** : à 8 Go, le 2 B complet gagne **+0,43125 sur 2 seeds** (Δ identique au 5ᵉ décimal) pendant que le 0,8 B n'y montre qu'un smoke de 3 steps au Δ dans le bruit (+0,0625, §2) — sens cohérent avec le verdict de référence.
3. **Limite, dite plutôt que tuée** : la paire stricte même-carte (0,8 B **complet** à 8 Go, ≥ 2 seeds, `summarize`) n'a pas été produite. Le Δ 0,8 B de référence (+0,2500 ± 0,1875 sur étage 16 Go, 47 050 s / 23 666 s par seed) n'est pas transposé tel quel ; au débit relatif mesuré au §3 (× 1,9 plus lent sur 8 Go), son équivalent complet à 8 Go extrapolerait à ~12 à 25 h par seed. Cette page énonce donc « le classement se rejoue en tendance et rien ne le déplace », pas « le classement est confirmé à 8 Go » — la paire stricte reste à produire si la coordination la demande.
