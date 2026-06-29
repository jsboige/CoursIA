# FineTuning - Adapter les LLMs à vos tâches

<!-- CATALOG-STATUS
series: GenAI-FineTuning
pedagogical_count: 5
breakdown: FineTuning=5
maturity: PRODUCTION=4, BETA=1
-->

[← GenAI](../README.md) | [↑ ..](../README.md) | [→ PostTraining](../PostTraining/README.md)

Série progressive sur le fine-tuning des modèles de langue : des bases LoRA à la fusion de modèles, en passant par la quantization, l'instruction-following et l'alignement par préférences humaines. GPU recommandé (T4/V100 suffisent pour la plupart des exercices).

## Objectifs d'apprentissage

À l'issue de cette série, vous serez capable de :

1. **Appliquer** LoRA et QLoRA pour fine-tuner des modèles 7B sur un GPU consumer
2. **Transformer** un base model en instruct model via SFT (format ChatML)
3. **Aligner** les modèles sur les préférences humaines avec DPO
4. **Fusionner** plusieurs adaptateurs fine-tunés en un seul modèle unifié (TIES, DARE, MoE)

## Structure

```text
FineTuning/
├── FT-01-Introduction-FineTuning.ipynb   # LoRA, full vs partial vs PEFT
├── FT-02-QLoRA-Quantization.ipynb        # Quantization 4-bit (NF4) + LoRA
├── FT-03-Supervised-FineTuning-SFT.ipynb # Instruction-following, format chat
├── FT-04-RLHF-DPO.ipynb                  # Alignement préférences, DPO
└── FT-05-ModelMerging-Routing.ipynb      # Fusion d'adaptateurs, routage MoE
```

## Progression pédagogique

| Notebook | Sujet | Prérequis | Durée | Niveau |
|----------|-------|-----------|-------|--------|
| [FT-01](FT-01-Introduction-FineTuning.ipynb) | Fine-tuning complet, partiel, LoRA | Bases LLMs | ~30 min | Débutant |
| [FT-02](FT-02-QLoRA-Quantization.ipynb) | Quantization NF4, QLoRA, bitsandbytes | FT-01 | ~30 min | Intermédiaire |
| [FT-03](FT-03-Supervised-FineTuning-SFT.ipynb) | Base model vs Instruct model, format ChatML | FT-01 | ~45 min | Intermédiaire |
| [FT-04](FT-04-RLHF-DPO.ipynb) | Reward Model, RLHF, DPO | FT-01, FT-02, FT-03 | ~30 min | Avancé |
| [FT-05](FT-05-ModelMerging-Routing.ipynb) | TIES, DARE, MergeKit, routage MoE | FT-01 à FT-04 | ~45 min | Avancé |

## Technologies couvertes

### Frameworks
- **transformers** (Hugging Face) - Modèles de base
- **peft** (Hugging Face) - LoRA, adaptateurs
- **bitsandbytes** - Quantization 4-bit / 8-bit
- **trl** (Hugging Face) - SFTTrainer, DPOTrainer
- **mergekit** - Fusion de modèles (TIES, DARE, SLERP)

### Modèles utilisés
- **Petits modèles** (FT-01) : DistilBERT, TinyLlama
- **Modèles 1-3B** (FT-02, FT-03) : Phi-3, Llama-3.2
- **Modèles 7B+** (FT-04, FT-05) : Mistral-7B, Llama-2-7B (avec QLoRA)

## Prérequis

```bash
pip install transformers peft accelerate bitsandbytes trl datasets
pip install mergekit  # Pour FT-05 uniquement
```

### Configuration GPU

| Notebook | VRAM minimale | VRAM recommandée |
|----------|---------------|------------------|
| FT-01 | 4 GB (CPU possible) | 8 GB |
| FT-02 | 6 GB (QLoRA) | 12 GB |
| FT-03 | 8 GB | 16 GB |
| FT-04 | 12 GB (DPO 2 modèles en mémoire) | 24 GB |
| FT-05 | 16 GB (merge) | 24 GB |

## Concepts clés

### LoRA (Low-Rank Adaptation)
Décompose les mises à jour de poids en matrices de bas rang (A, B avec rang r << dim). Réduit les paramètres entraînables de ~99%.

### QLoRA
Combine quantization 4-bit (NF4 + double quantization) avec LoRA. Permet de fine-tuner des modèles 7B sur un GPU consumer (RTX 3090/4090).

### SFT (Supervised Fine-Tuning)
Transforme un base model en instruct model via supervision sur des paires (instruction, réponse). Format ChatML recommandé.

### DPO (Direct Preference Optimization)
Alternative simplifiée à RLHF : optimise directement sur les paires (preferred, rejected) sans Reward Model explicite.

### Model Merging
Combine plusieurs adaptateurs LoRA fine-tunés sur des tâches différentes en un seul modèle unifié. Algorithmes : TIES, DARE, SLERP, weighted average.

## Parcours recommandé

### Découverte (1h)
1. **FT-01** - Comprendre LoRA et le compromis paramètres/qualité
2. **FT-03** - SFT pour instruction-following (sans QLoRA)

### Standard (2-3h)
1. FT-01 à FT-04 dans l'ordre

### Avancé (3-4h)
1. FT-01 à FT-05 dans l'ordre + expérimenter mergekit recipes

## FAQ

### OOM pendant FT-04 (DPO) ou FT-05 (Model Merging)

DPO (FT-04) charge **deux modèles** en mémoire (policy + reference), ce qui double la consommation VRAM. Stratégies :

- Utiliser QLoRA 4-bit (`load_in_4bit=True`) pour réduire chaque modèle à ~25% de sa taille FP16.
- Réduire `per_device_train_batch_size` à 1 et compenser avec `gradient_accumulation_steps`.
- Pour FT-05 (merge), les modèles sont chargés séquentiellement, pas en parallèle — 16 GB suffisent si vous mergez un modèle à la fois.

FT-01 à FT-03 sont accessibles sur GPU 8-12 GB (T4, RTX 3060). FT-04 et FT-05 préfèrent 24 GB (RTX 3090/4090).

### Quelle différence entre cette série et PostTraining ?

| Aspect | FineTuning (cette série) | PostTraining |
|--------|-------------------------|--------------|
| **Focus** | Boîte à outils pratique | Profondeur méthodologique |
| **Approche** | "Comment faire" | "Pourquoi ça marche" |
| **Modèles** | 0.5B à 7B, variés | Qwen2.5-0.5B/1.5B uniquement |
| **Techniques** | LoRA, QLoRA, SFT, DPO, merging | SFT, DPO, GRPO, RLVR |
| **GPU cible** | T4/V100 (4-8 GB min) | RTX 3070 (8 GB) |
| **Math du loss** | Non détaillée | Expliquée avant le code |

Recommandation : faire FineTuning d'abord pour la pratique, puis PostTraining pour comprendre les fondamentaux.

### LoRA rank : comment choisir r ?

Le rang `r` de LoRA contrôle le compromis paramètres/qualité :

- **r=4-8** : bon pour des tâches simples (classification, formatage). ~0.1% paramètres entraînables.
- **r=16** (défaut) : bon compromis pour instruction-following et DPO. ~0.5% paramètres.
- **r=32-64** : tâches complexes (raisonnement, code). Plus de paramètres mais plus de VRAM.
- **r=128+** : rarement nécessaire — à ce stade, un full fine-tuning partiel est souvent plus efficace.

Le notebook [FT-01](FT-01-Introduction-FineTuning.ipynb) compare r=4 vs r=16 vs r=64 sur DistilBERT pour rendre ce compromis visible.

### bitsandbytes ne s'installe pas sur Windows

`bitsandbytes` (requis pour QLoRA, FT-02 à FT-04) dépend de CUDA. Sur Windows :

```bash
# Vérifier CUDA
python -c "import torch; print(torch.version.cuda)"

# Installer bitsandbytes compatible Windows
pip install bitsandbytes>=0.45

# Si erreur DLL non trouvée
# Vérifier que CUDA_HOME est configuré
set CUDA_HOME=C:\Program Files\NVIDIA GPU Computing Toolkit\CUDA\v12.4
```

Alternative : utiliser Google Colab (GPU T4 gratuit) pour les notebooks FT-02 à FT-04 si votre machine n'a pas de GPU.

### Peut-on fine-tuner sans GPU ?

Partiellement. FT-01 fonctionne en mode CPU (DistilBERT, petit modèle). Pour les notebooks FT-02 à FT-05 :

- **Google Colab** (GPU T4 gratuit) : FT-01 à FT-03 exécutables.
- **Kaggle Kernels** (GPU P100 gratuit, 30h/semaine) : FT-01 à FT-04.
- **Unsloth** (optimisation mémoire) : réduit la VRAM requise de ~40%, permet QLoRA 7B sur T4.

Les notebooks sont conçus pour tourner avec `LOAD_MODEL_AND_TRAIN=False` en mode démo (outputs pré-calculés visibles sans GPU).

### MergeKit produit un modèle dégradé

Si le modèle merge (FT-05) perd en qualité par rapport aux adaptateurs individuels :

- Vérifier que les adaptateurs ont été fine-tunés sur des tâches **suffisamment différentes** (merger des adaptateurs trop similaires ne produit pas de gain).
- L'algorithme TIES est plus robuste que SLERP pour les merges multi-tâches.
- DARE (Drop And Rescale) élimine les poids redondants — essayer si TIES ne converge pas.
- Le routage MoE (Mixture of Experts) est une alternative au merge statique : chaque token est routé vers l'adaptateur le plus compétent. FT-05 couvre cette approche.

## Ponts avec les autres séries

| Série | Connection | Détails |
|-------|------------|---------|
| **[GenAI/PostTraining](../PostTraining/README.md)** | Profondeur méthodologique | Série sœur : la math du loss derrière SFT/DPO + GRPO/RLVR. FineTuning = recettes, PostTraining = pourquoi ça marche. |
| **[RL — rl_5 MDP/Q-Learning](../../RL/rl_5_mdp_dp_qlearning.ipynb)** | Fondations policy/value | Socle Bellman/Q réutilisé par tout post-training. |
| **[RL — rl_6c PPO from scratch](../../RL/rl_6c_ppo_from_scratch.ipynb)** | PPO from scratch | L'optimiseur derrière PPO-RLHF, implémenté pas à pas. |
| **[RL — rl_9 offline RL](../../RL/rl_9_offline_rl.ipynb)** | SFT = Behavior Cloning | DPO comme preference learning offline ; contrainte de support = KL. |
| **[RL — rl_10 reward shaping](../../RL/rl_10_reward_shaping.ipynb)** | Reward model = shaping appris | Reward shaping (Ng 1999) et reward hacking, préfiguration tabulaire du reward model RLHF. |

## Références

- **Hugging Face PEFT** : https://huggingface.co/docs/peft
- **QLoRA paper** : https://arxiv.org/abs/2305.14314
- **DPO paper** : https://arxiv.org/abs/2305.18290
- **MergeKit** : https://github.com/arcee-ai/mergekit
