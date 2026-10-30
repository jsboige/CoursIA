# Decision Index — palier `4b` : mesure locale sur une carte 24 Go

> **Statut** : grain **#23612**, Pli 1 de **#18204**. Mesure **faite** le **2026-10-30** sur le **device 2** de `myia-ai-01` (RTX 4090, 23,99 Gio), avec l'organe déjà livré par #21921 (`scripts/genai-stack/decision_local_check.py`), sur la **tranche reconstruite** de #21910.
> **Tranche identique à celle du palier `0.8b`** : les trois empreintes sha256 sont **byte-identiques** à celles de `scripts/results/decision_local_2026-10-22.json` → les deux paliers sont comparables **item à item**.
> **Page sœur** : [decision-models-local-verification.md](decision-models-local-verification.md) (palier `0.8b`, carte 8 Gio). **Page de relevé** : [decision-models.md](decision-models.md).
> **Agrégat** : `scripts/results/decision_local_2026-10-31_jiwo4b_gpu2.json` (437 468 octets).

## Verdict en une phrase

L'exigence « **GPU 24 Go** » est **réfutée pour le palier `4b`** : les deux checkpoints `eljiwo/jiwo-4b` (`v1`, `v2`) sont servis **sur GPU** avec un pic VRAM de **8,02 Gio** — une classe « **carte 16 Go** », pas « carte 24 Go » — et, sur la tranche reconstruite, ils atteignent **89,67 %** (`v2`) et **88,78 %** (`v1`) d'exactitude, contre **69,78 %** et **69,56 %** pour `0.8b` sur les **mêmes 900 items**.

## 1. Ce que cette page ferme

Deux réserves ouvertes, l'une par la page sœur, l'autre par la page de relevé :

| Réserve | Où | État après cette page |
|---|---|---|
| « Les modèles `4b` : **non mesurés** … L'affirmation "24 Go" reste donc **non réfutée pour `4b`** » | [decision-models-local-verification.md](decision-models-local-verification.md) §5 | **close** — les deux checkpoints sont mesurés, sur GPU, avec leur pic VRAM |
| « Le besoin 24 Go **reste non réfuté pour `4b`** (non mesuré) » | [decision-models.md](decision-models.md), ligne de statut | **close sur le fond** ; la **correction de la ligne** est due à une PR de suivi (voir §7) |

La réserve « le score de l'index n'est pas reproductible » **reste ouverte** : c'est un échec de données, pas de mesure (les charges utiles de `multimodalart/decision-index-suite-0.3` répondent **401**).

## 2. Méthode

### 2.1 L'organe déjà présent

Rien n'est réimplémenté : la mesure utilise `scripts/genai-stack/decision_local_check.py`, livré par **#21921** (lane `myia-po-2028:CoursIA-2`), et la tranche reconstruite de **#21910** — jeux `arc_easy`, `openbookqa`, `commonsense_qa`, **300 items** chacun, graine **42**.

| jeu | items | sha256 de la tranche |
|---|---|---|
| `arc_easy` | 300 | `fa4fb46267650ae1d8b0ae83b3ff3313e510d041171487e651db43ae29226359` |
| `openbookqa` | 300 | `61d3c51a6ef3cedfaf8fa5a1fb3bcef58b2c3a7cc52f0ad8c03ef68fdad28d74` |
| `commonsense_qa` | 300 | `be46577a92d4f3d8c06b921eda43d7240c57c84e584e3bc566672fb9d38f59c8` |

Ces trois empreintes sont **celles du palier `0.8b`** (`scripts/results/decision_local_2026-10-22.json`) : c'est ce qui autorise la comparaison inter-paliers du §3.2.

### 2.2 Le siège de mesure

| | |
|---|---|
| machine / device | `myia-ai-01`, **device 2** (`CUDA_DEVICE_ORDER=PCI_BUS_ID CUDA_VISIBLE_DEVICES=2`) |
| carte | NVIDIA GeForce RTX 4090 — **23,99 Gio** |
| python / torch | 3.12.9 / 2.14.1+cu126 |
| bibliothèque de service | `jiwo` 0.1.0 (native, MIT) — `DecisionModel.from_pretrained(..., device="cuda")` |
| dtype | **bfloat16** (défaut de la bibliothèque sur `cuda`), `attn_implementation="sdpa"` |
| longueur de contexte | `max_length` **8192** (défaut de l'organe) |
| checkpoints | `eljiwo/jiwo-4b@v1` (`2e31a9c0…`), `eljiwo/jiwo-4b@v2` (`9adc559f…`) — licence **apache-2.0**, base `Qwen/Qwen3.5-4B` |

### 2.3 La commande

```bash
CUDA_DEVICE_ORDER=PCI_BUS_ID CUDA_VISIBLE_DEVICES=2 \
python scripts/genai-stack/decision_local_check.py \
  --model "eljiwo/jiwo-4b@v2#cuda" --model "eljiwo/jiwo-4b@v1#cuda" \
  --json scripts/results/decision_local_2026-10-31_jiwo4b_gpu2.json
```

> **Piège de syntaxe, mesuré.** L'argument `--model` est analysé par `rpartition(":")` : la forme `"…#cuda:0"` est lue comme un **device** `cuda` et une **limite par jeu** `0` → l'organe évalue **0 item** et le dit comme un résultat valide (silencieux). Le device s'écrit `"…#cuda"` : avec `CUDA_VISIBLE_DEVICES=2`, `cuda` désigne déjà l'unique device visible.

## 3. Résultats mesurés

### 3.1 Exactitude et calibration — palier `4b`

| checkpoint | exactitude (900 items) | ECE | Brier | confiance moyenne | pic VRAM | chargement | évaluation |
|---|---|---|---|---|---|---|---|
| `eljiwo/jiwo-4b@v2` | **89,67 %** | 0,1042 | **0,1596** | 0,7926 | **8,02 Gio** | 15,3 s | 102,3 s (0,114 s/item) |
| `eljiwo/jiwo-4b@v1` | **88,78 %** | **0,0670** | 0,1757 | 0,8208 | **8,02 Gio** | 9,6 s | 104,6 s (0,116 s/item) |

Par jeu :

| jeu | `4b@v1` | `4b@v2` |
|---|---|---|
| `arc_easy` | 98,00 % | 97,67 % |
| `openbookqa` | 85,67 % | **88,33 %** |
| `commonsense_qa` | 82,67 % | 83,00 % |

### 3.2 Comparaison inter-paliers — **900 items identiques**

| | `0.8b@v1` | `0.8b@v2` | `4b@v1` | `4b@v2` |
|---|---|---|---|---|
| exactitude | 69,78 % | 69,56 % | 88,78 % | **89,67 %** |
| ECE | 0,0892 | 0,1314 | **0,0670** | 0,1042 |
| Brier | 0,4195 | 0,4223 | 0,1757 | **0,1596** |
| pic VRAM | 1,47 Gio | 1,47 Gio | 8,02 Gio | 8,02 Gio |

Ce que la comparaison **établit** :

- **Le palier `4b` est meilleur de ~19 à 20 points** sur les mêmes items : +19,00 points pour `v1`, **+20,11 points** pour `v2` — l'écart n'est pas un effet de tranche.
- **Il est mieux calibré** : Brier divisé par ~2,5 (0,42 → 0,16-0,18). Sur l'ECE, `4b@v1` (0,0670) est la **meilleure calibration de l'ensemble des quatre checkpoints**, devant `0.8b@v1` (0,0892) — l'avantage du palier supérieur ne porte donc pas que sur l'exactitude.
- **Le gain coûte 5,45× la mémoire** (8,02 contre 1,47 Gio).

Ce que la comparaison **ne dit pas** : les **temps** ne sont pas comparables entre paliers — le `0.8b` a été mesuré sur une **RTX 3070 Ti Laptop (8,0 Gio)**, le `4b` ici sur une **RTX 4090 (23,99 Gio)**. Le `4b` est plus rapide par item (0,114 s contre 0,234 s) malgré une charge 5,45× plus lourde, mais cela mesure **les deux cartes à la fois**, pas le modèle.

### 3.3 Ce que la mesure dit de « 24 Go »

Le pic est mesuré par `torch.cuda.max_memory_allocated()` (mémoire **allouée**, pas réservée), après `reset_peak_memory_stats()` : **8,02 Gio** pour les deux checkpoints.

- Un modèle de **4 Md de paramètres en bfloat16** représente **7,45 Gio** de poids seuls ; le solde (**~0,57 Gio**) couvre les activations de la passe et la tête de lecture.
- **8,02 Gio < 23,99 Gio** : le seuil « 24 Go » est **réfuté** pour ce palier. Le service tient sur une carte de **16 Go** sans tension.
- **8,02 Gio > 8,00 Gio** : il ne tient **pas** sur la carte 8 Gio qui sert de référence au palier `0.8b` (RTX 3070 Ti Laptop, 8,0 Gio). Sur cette carte, l'organe basculerait le modèle en **CPU float32** — repli documenté de l'organe, **ici non mesuré** : c'est une inférence d'encombrement, pas une observation.

> **Ce que cette mesure ne réfute pas.** Elle porte sur **l'empreinte de service de ces deux checkpoints**, servis par leur bibliothèque native, en bfloat16, avec une longueur de contexte de 8192. Elle ne dit rien d'un déploiement quantifié (int4/int8), ni d'un contexte plus long, ni des paliers supérieurs de l'index. L'affirmation « 24 Go » n'est réfutée **que** pour `4b` servi ainsi.

### 3.4 Profil d'aires (mesuré)

| aire (reconstruction) | items | `4b@v1` | `4b@v2` |
|---|---|---|---|
| knowledge (`arc_easy` + `openbookqa`) | 600 | 91,83 % | 93,00 % |
| language (`commonsense_qa`) | 300 | 82,67 % | 83,00 % |

### 3.5 Ordre mesuré contre ordre publié

| paire | rang mesuré | rang publié (index 0.3) | concordant |
|---|---|---|---|
| `4b@v2` (46,06) vs `4b@v1` (45,76) | v2 > v1 | v2 > v1 | **oui** |
| `0.8b@v2` (29,58) vs `0.8b@v1` (28,72) | v1 > v2 | v2 > v1 | **non** |

**Ce qu'il faut en dire exactement** : la concordance de la paire `4b` est un **signal faible** — l'écart mesuré entre `v2` et `v1` est de **0,89 point, soit 8 items sur 900**. La paire `0.8b`, où l'ordre mesuré **inverse** l'ordre publié, montre que cette tranche **ne résout pas** l'écart entre `v1` et `v2`. Conclusion honnête : **le classement de l'index entre deux révisions d'un même palier n'est pas vérifiable sur cette tranche** ; le classement **entre paliers** (`4b` devant `0.8b`, +19 à 20 points) l'est.

## 4. Ce que la mesure ne dit pas

- **Le score public de l'index n'est pas reproductible** : les charges utiles sont dans `multimodalart/decision-index-suite-0.3`, qui répond **401**. La mesure porte sur une **tranche reconstruite** depuis des jeux de QCM publics — la comparaison avec l'index porte sur l'**ordre**, pas sur les scores.
- **Les accuracies publiées par les cartes modèle** (« trois jeux de données », « sept jeux de données ») portent sur des jeux **non nommés** : ce sont des repères de plausibilité, pas des valeurs à reproduire.
- **La base non entraînée** (`Qwen3.5-0.8B`, 6,99 publié sur l'édition 0.2.1) reste **non mesurée** : elle suppose l'index.
- **Le palier CPU** et un éventuel **déploiement quantifié** ne sont pas mesurés.
- **Le profil d'aires publié** n'est pas comparable : les scores publiés sont des `skill × 100`, pas des exactitudes.

## 5. Reproduction

```bash
# env dédié (Python 3.12, torch cu126, jiwo)
pip install jiwo torch --index-url https://download.pytorch.org/whl/cu126

cd <checkout CoursIA>
CUDA_DEVICE_ORDER=PCI_BUS_ID CUDA_VISIBLE_DEVICES=2 \
python scripts/genai-stack/decision_local_check.py \
  --model "eljiwo/jiwo-4b@v2#cuda" --model "eljiwo/jiwo-4b@v1#cuda" \
  --json scripts/results/decision_local_2026-10-31_jiwo4b_gpu2.json
```

Durée mesurée : **~4 min** (chargement + 900 items par checkpoint). L'organe écrit l'agrégat et imprime le classement mesuré, le classement publié et la concordance des paires.

## 6. Voir aussi

- [decision-models-local-verification.md](decision-models-local-verification.md) — palier `0.8b` sur carte 8 Gio, obstacle de données et reproduction sur un second siège (#21910, #21921, #21930)
- [decision-models.md](decision-models.md) — relevé du shortlist et licences (#18204)
- [3d-enveloppe-vram-8go.md](3d-enveloppe-vram-8go.md) — autre mesure d'enveloppe VRAM du dépôt, sur l'étage pionnier 8 Gio
- `scripts/genai-stack/decision_local_check.py` — l'organe de mesure ; `scripts/results/decision_local_2026-10-31_jiwo4b_gpu2.json` — l'agrégat de cette page
