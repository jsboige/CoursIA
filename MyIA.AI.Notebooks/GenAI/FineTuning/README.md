# FineTuning - Adapter les LLMs a vos taches

[← Documentation GenAI](../README.md)

<!-- CATALOG-STATUS
series: GenAI-FineTuning
pedagogical_count: 5
breakdown: Introduction=1, QLoRA=1, SFT=1, RLHF-DPO=1, ModelMerging=1
maturity: BETA
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

## Liens

- [← GenAI README](../README.md) - Vue d'ensemble GenAI
- [SemanticKernel](../SemanticKernel/README.md) - Integration .NET pour LLMs fine-tunes
- [Texte](../Texte/README.md) - Notebooks LLMs generaux
