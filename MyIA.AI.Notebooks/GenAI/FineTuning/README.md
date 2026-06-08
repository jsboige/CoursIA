# FineTuning - Adapter les LLMs a vos taches

[← Documentation GenAI](../README.md)

<!-- CATALOG-STATUS
series: GenAI-FineTuning
pedagogical_count: 5
breakdown: FineTuning=5
maturity: PRODUCTION=4, BETA=1
-->

Serie progressive sur le fine-tuning des modeles de langue : des bases LoRA a la fusion de modeles, en passant par la quantization, l'instruction-following et l'alignement par preferences humaines.

**5 notebooks** | **~2-3h** | **GPU recommande** (T4/V100 suffisent pour la plupart des exercices)

## Structure

```text
FineTuning/
├── FT-01-Introduction-FineTuning.ipynb   # LoRA, full vs partial vs PEFT
├── FT-02-QLoRA-Quantization.ipynb        # Quantization 4-bit (NF4) + LoRA
├── FT-03-Supervised-FineTuning-SFT.ipynb # Instruction-following, format chat
├── FT-04-RLHF-DPO.ipynb                  # Alignement preferences, DPO
└── FT-05-ModelMerging-Routing.ipynb      # Fusion d'adaptateurs, routage MoE
```

## Progression pedagogique

| Notebook | Sujet | Prerequis | Duree | Niveau |
|----------|-------|-----------|-------|--------|
| [FT-01](FT-01-Introduction-FineTuning.ipynb) | Fine-tuning complet, partiel, LoRA | Bases LLMs | ~30 min | Debutant |
| [FT-02](FT-02-QLoRA-Quantization.ipynb) | Quantization NF4, QLoRA, bitsandbytes | FT-01 | ~30 min | Intermediaire |
| [FT-03](FT-03-Supervised-FineTuning-SFT.ipynb) | Base model vs Instruct model, format ChatML | FT-01 | ~45 min | Intermediaire |
| [FT-04](FT-04-RLHF-DPO.ipynb) | Reward Model, RLHF, DPO | FT-01, FT-02, FT-03 | ~30 min | Avance |
| [FT-05](FT-05-ModelMerging-Routing.ipynb) | TIES, DARE, MergeKit, routage MoE | FT-01 a FT-04 | ~45 min | Avance |

## Technologies couvertes

### Frameworks
- **transformers** (Hugging Face) - Modeles de base
- **peft** (Hugging Face) - LoRA, adaptateurs
- **bitsandbytes** - Quantization 4-bit / 8-bit
- **trl** (Hugging Face) - SFTTrainer, DPOTrainer
- **mergekit** - Fusion de modeles (TIES, DARE, SLERP)

### Modeles utilises
- **Petits modeles** (FT-01) : DistilBERT, TinyLlama
- **Modeles 1-3B** (FT-02, FT-03) : Phi-3, Llama-3.2
- **Modeles 7B+** (FT-04, FT-05) : Mistral-7B, Llama-2-7B (avec QLoRA)

## Prerequis

```bash
pip install transformers peft accelerate bitsandbytes trl datasets
pip install mergekit  # Pour FT-05 uniquement
```

### Configuration GPU

| Notebook | VRAM minimale | VRAM recommandee |
|----------|---------------|------------------|
| FT-01 | 4 GB (CPU possible) | 8 GB |
| FT-02 | 6 GB (QLoRA) | 12 GB |
| FT-03 | 8 GB | 16 GB |
| FT-04 | 12 GB (DPO 2 modeles en memoire) | 24 GB |
| FT-05 | 16 GB (merge) | 24 GB |

## Concepts cles

### LoRA (Low-Rank Adaptation)
Decompose les mises a jour de poids en matrices de bas rang (A, B avec rang r << dim). Reduit les parametres entrainables de ~99%.

### QLoRA
Combine quantization 4-bit (NF4 + double quantization) avec LoRA. Permet de fine-tuner des modeles 7B sur un GPU consumer (RTX 3090/4090).

### SFT (Supervised Fine-Tuning)
Transforme un base model en instruct model via supervision sur des paires (instruction, reponse). Format ChatML recommande.

### DPO (Direct Preference Optimization)
Alternative simplifiee a RLHF : optimise directement sur les paires (preferred, rejected) sans Reward Model explicite.

### Model Merging
Combine plusieurs adaptateurs LoRA fine-tunes sur des taches differentes en un seul modele unifie. Algorithmes : TIES, DARE, SLERP, weighted average.

## Parcours recommande

### Decouverte (1h)
1. **FT-01** - Comprendre LoRA et le compromis parametres/qualite
2. **FT-03** - SFT pour instruction-following (sans QLoRA)

### Standard (2-3h)
1. FT-01 a FT-04 dans l'ordre

### Avance (3-4h)
1. FT-01 a FT-05 dans l'ordre + experimenter mergekit recipes

## Ressources externes

- **Hugging Face PEFT** : https://huggingface.co/docs/peft
- **QLoRA paper** : https://arxiv.org/abs/2305.14314
- **DPO paper** : https://arxiv.org/abs/2305.18290
- **MergeKit** : https://github.com/arcee-ai/mergekit

## FAQ

### OOM pendant FT-04 (DPO) ou FT-05 (Model Merging)

DPO (FT-04) charge **deux modeles** en memoire (policy + reference), ce qui double la consommation VRAM. Strategies :

- Utiliser QLoRA 4-bit (`load_in_4bit=True`) pour reduire chaque modele a ~25% de sa taille FP16.
- Reduire `per_device_train_batch_size` a 1 et compenser avec `gradient_accumulation_steps`.
- Pour FT-05 (merge), les modeles sont charges sequentiellement, pas en parallele — 16 GB suffisent si vous mergez un modele a la fois.

FT-01 a FT-03 sont accessibles sur GPU 8-12 GB (T4, RTX 3060). FT-04 et FT-05 preferent 24 GB (RTX 3090/4090).

### Quelle difference entre cette serie et PostTraining ?

| Aspect | FineTuning (cette serie) | PostTraining |
|--------|-------------------------|--------------|
| **Focus** | Boite a outils pratique | Profondeur methodologique |
| **Approche** | "Comment faire" | "Pourquoi ca marche" |
| **Modeles** | 0.5B a 7B, variés | Qwen2.5-0.5B/1.5B uniquement |
| **Techniques** | LoRA, QLoRA, SFT, DPO, merging | SFT, DPO, GRPO, RLVR |
| **GPU cible** | T4/V100 (4-8 GB min) | RTX 3070 (8 GB) |
| **Math du loss** | Non detaillee | Expliquee avant le code |

Recommandation : faire FineTuning d'abord pour la pratique, puis PostTraining pour comprendre les fondamentaux.

### LoRA rank : comment choisir r ?

Le rang `r` de LoRA controle le compromis parametres/qualite :

- **r=4-8** : bon pour des taches simples (classification, formatage). ~0.1% parametres entrainables.
- **r=16** (defaut) : bon compromis pour instruction-following et DPO. ~0.5% parametres.
- **r=32-64** : taches complexes (raisonnement, code). Plus de parametres mais plus de VRAM.
- **r=128+** : rarement necessaire — a ce stade, un full fine-tuning partiel est souvent plus efficace.

Le notebook [FT-01](FT-01-Introduction-FineTuning.ipynb) compare r=4 vs r=16 vs r=64 sur DistilBERT pour rendre ce compromis visible.

### bitsandbytes ne s'installe pas sur Windows

`bitsandbytes` (requis pour QLoRA, FT-02 a FT-04) depend de CUDA. Sur Windows :

```bash
# Verifier CUDA
python -c "import torch; print(torch.version.cuda)"

# Installer bitsandbytes compatible Windows
pip install bitsandbytes>=0.45

# Si erreur DLL non trouvee
# Verifier que CUDA_HOME est configure
set CUDA_HOME=C:\Program Files\NVIDIA GPU Computing Toolkit\CUDA\v12.4
```

Alternative : utiliser Google Colab (GPU T4 gratuit) pour les notebooks FT-02 a FT-04 si votre machine n'a pas de GPU.

### Peut-on fine-tuner sans GPU ?

Partiellement. FT-01 fonctionne en mode CPU (DistilBERT, petit modele). Pour les notebooks FT-02 a FT-05 :

- **Google Colab** (GPU T4 gratuit) : FT-01 a FT-03 executables.
- **Kaggle Kernels** (GPU P100 gratuit, 30h/semaine) : FT-01 a FT-04.
- **Unsloth** (optimisation memoire) : reduit la VRAM requise de ~40%, permet QLoRA 7B sur T4.

Les notebooks sont concus pour tourner avec `LOAD_MODEL_AND_TRAIN=False` en mode demo (outputs pre-calcules visibles sans GPU).

### MergeKit produit un modele degradé

Si le modele merge (FT-05) perd en qualite par rapport aux adaptateurs individuels :

- Verifier que les adaptateurs ont ete fine-tunes sur des taches **suffisamment differentes** (merger des adaptateurs trop similaires ne produit pas de gain).
- L'algorithme TIES est plus robuste que SLERP pour les merges multi-taches.
- DARE (Drop And Rescale) elimine les poids redondants — essayer si TIES ne converge pas.
- Le routage MoE (Mixture of Experts) est une alternative au merge statique : chaque token est route vers l'adaptateur le plus competent. FT-05 couvre cette approche.

## Liens

- [← GenAI README](../README.md) - Vue d'ensemble GenAI
- [SemanticKernel](../SemanticKernel/README.md) - Integration .NET pour LLMs fine-tunes
- [Texte](../Texte/README.md) - Notebooks LLMs generaux
