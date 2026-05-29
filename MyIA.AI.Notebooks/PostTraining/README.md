# PostTraining - Techniques de post-training des Language Models (SOTA 2024-2025)

Serie pedagogique dediee aux techniques de **post-training** des LMs ouverts : SFT, DPO, GRPO, RLVR. L'objectif est de comprendre pourquoi 2024-2025 marque une rupture pedagogique dans la facon dont les modeles de langue passent du pre-training brut a un assistant utile, et comment cette chaine s'est simplifiee depuis la cascade RLHF historique jusqu'aux methodes "direct" recentes.

## Pourquoi cette serie

Le post-training est le maillon qui transforme un modele pre-entraine — au mieux un excellent statisticien du langage — en assistant aligne sur des preferences humaines ou des objectifs verifiables. Pendant longtemps, la chaine canonique etait RLHF : Supervised Fine-Tuning, puis Reward Model, puis PPO. Trois etapes, trois bugs potentiels, beaucoup d'instabilite. Les techniques recentes (DPO en 2023, GRPO en 2024, RLVR en 2024-2025) ont reduit cette chaine en s'attaquant aux deux maillons faibles : la dependance au Reward Model appris (DPO le supprime) et la lourdeur memoire de PPO (GRPO la divise).

En janvier 2025, Deepseek-R1 a publiquement valide cette progression en montrant qu'un modele moyen entraine avec GRPO sur des taches a recompense verifiable (math, code) peut atteindre un niveau de raisonnement competitif avec des modeles bien plus gros entraines de facon classique. Cette serie didactise cette chaine de techniques avec des reproductions concretes sur **petits modeles** (Qwen2.5-0.5B/1.5B) deployables sur **GPU 8 Go** (RTX 3070), conformement a l'esprit "po-2024 pionnier parcimonieux" de l'Epic #1454.

L'angle pedagogique est d'expliquer la **math du loss** avant le code pour chaque technique. Trop de tutoriels existants montrent une cellule `trainer.train()` qui converge sans donner l'intuition de pourquoi DPO marche, pourquoi GRPO economise la memoire, ou pourquoi RLVR contourne le besoin d'un Reward Model. Cette serie inverse l'ordre : d'abord la formule, puis l'intuition, puis l'implementation TRL/HuggingFace, puis les outputs reels d'entrainement.

**A qui s'adresse cette serie** : ingenieurs ML curieux de comprendre la chaine post-training au-dela des annonces de presse, etudiants en NLP voulant reproduire les techniques Deepseek-R1 sans cluster H100, et formateurs ayant besoin de notebooks pedagogiques sur des modeles que leurs etudiants peuvent reellement faire tourner. Prerequis : Python intermediate, PyTorch elementaire, familiarite avec `transformers`, intuition de la backprop et de la cross-entropy. Le notebook PT-01 etablit le contexte theorique sans code execute ; PT-02 reprend les bases SFT ; les notebooks PT-03 a PT-06 ajoutent une technique par etape.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 1 scaffold (5 prevus) |
| Kernel | Python 3 |
| Duree estimee | ~6-10h total |
| GPU cible | RTX 3070 8 Go (po-2024) |
| Statut | DRAFT (scaffold initial) |

## Notebooks prevus

| # | Notebook | Sujet | Technique | Modele cible |
|---|----------|-------|-----------|--------------|
| PT-01 | `PT_01_intro_post_training.ipynb` | Vue d'ensemble historique : SFT → RLHF → DPO → GRPO → RLVR | Theorique (markdown + figures) | N/A |
| PT-02 | `PT_02_sft_baseline.ipynb` | Supervised Fine-Tuning baseline | `trl.SFTTrainer` | Qwen2.5-0.5B-Instruct |
| PT-03 | `PT_03_dpo_direct_preference.ipynb` | Direct Preference Optimization (Rafailov 2023) | `trl.DPOTrainer` | Qwen2.5-0.5B post-SFT |
| PT-04 | `PT_04_grpo_deepseek_r1.ipynb` | Group Relative Policy Optimization (livrable cle) | `trl.GRPOTrainer` | Qwen2.5-0.5B |
| PT-05 | `PT_05_rlvr_verifiable_rewards.ipynb` | RL with Verifiable Rewards (math/code) | `trl.GRPOTrainer` + verifier | Qwen2.5-Math-1.5B |
| PT-06 | `PT_06_evaluation_post_training.ipynb` | Eval comparative SFT vs DPO vs GRPO vs RLVR | `lm-evaluation-harness` | tous |

## Progression pedagogique

Les notebooks s'enchainent **dans l'ordre**. Sauter PT-02 (SFT) avant PT-03 (DPO) est techniquement possible mais perd l'intuition cle de DPO : pourquoi la formule contient un terme implicite de reward model est evident apres avoir vu un SFT classique converger. De meme, GRPO (PT-04) s'eclaire apres avoir compris la limite memoire de PPO. RLVR (PT-05) reutilise l'infrastructure GRPO mais remplace le reward appris par un verificateur exact (sympy pour les expressions, sandbox pour le code).

PT-01 (intro) peut etre lu **en parallele** des autres notebooks ; c'est un compagnon theorique.

## Architecture conceptuelle

```
                  ┌──────────────────────┐
                  │  Base LM (pretrained)│
                  │  Qwen2.5-0.5B-Base   │
                  └──────────┬───────────┘
                             │
                  ┌──────────▼───────────┐
                  │  SFT (PT-02)         │
                  │  trl.SFTTrainer      │
                  │  → Qwen-0.5B-SFT     │
                  └──────────┬───────────┘
                             │
              ┌──────────────┼──────────────┐
              │              │              │
       ┌──────▼──────┐ ┌─────▼──────┐ ┌────▼─────────┐
       │ DPO (PT-03) │ │GRPO (PT-04)│ │ RLVR (PT-05) │
       │ pair-based  │ │ group-based│ │ exact reward │
       │ no RM       │ │ no critic  │ │ no RM appris │
       └─────────────┘ └────────────┘ └──────────────┘
              │              │              │
              └──────────────┼──────────────┘
                             │
                  ┌──────────▼───────────┐
                  │  Eval (PT-06)        │
                  │  GSM8K, IFEval       │
                  │  comparaison metriques│
                  └──────────────────────┘
```

## Contraintes RTX 3070 8 Go (parsimonie po-2024)

- **Modeles ≤ 1.5B params**, prioritise Qwen2.5-0.5B/1.5B
- **Quantization 4-bit** (`bitsandbytes`) obligatoire pour modeles > 0.5B
- **LoRA** rank ≤ 16, alpha ≤ 32, adapters sur attention + MLP
- **Batch size** ≤ 4, gradient accumulation jusqu'a 16 pour batch effectif 64
- **Training time cible** : < 60 min par notebook
- **Datasets HF publics** : `HuggingFaceH4/ultrafeedback_binarized` subset, `openai/gsm8k`, `HuggingFaceH4/MATH-500`

## Quick Start

```bash
# 1. Activer l'environnement
conda activate coursia-ml-training

# 2. Installer dependances post-training (a faire une fois)
pip install --upgrade transformers trl peft accelerate datasets bitsandbytes

# 3. Verifier la VRAM
python -c "import torch; print(f'CUDA: {torch.cuda.is_available()}, {torch.cuda.get_device_name(0)}, {torch.cuda.get_device_properties(0).total_memory / 1e9:.1f} GB')"

# 4. Lancer le premier notebook
jupyter notebook PT_01_intro_post_training.ipynb
```

## Conformite regles CoursIA

| Regle | Application |
|-------|-------------|
| **C.1** (no NotImplementedError) | Stubs etudiants : `pass`, `print("Exercice a completer")`, `return None` |
| **C.2** (outputs committed) | Tous les notebooks executes avec outputs reels avant commit |
| **C.3** (scope strict re-exec) | Ne commit que les notebooks modifies, pas de re-exec massives |
| **E** (no emojis) | Naming professionnel |
| **F** (env reparer) | `coursia-ml-training` doit avoir TRL + bitsandbytes + datasets installes |
| **Multi-seed ≥ 4** | Pour toute claim "GRPO outperforms DPO" → 4 seeds + ecart ≥ 2σ |

## Ponts avec les autres series

| Serie | Connection | Details |
|-------|------------|---------|
| **[RL](../RL/)** | RL classique fondamentaux | Les notebooks RL (`rl_4_mdp_dp_qlearning`, `stable_baseline_*`) etablissent l'intuition policy/value que PPO/GRPO reutilisent. Recommande comme prerequis pour PT-04. |
| **[GenAI/Texte](../GenAI/Texte/)** | Usage des LMs aligned | Les notebooks GenAI consomment des modeles deja post-trained. Cette serie explique comment ces modeles arrivent dans cet etat. |
| **[ML](../ML/)** | Tutoriels ML.NET | Pont conceptuel : ML.NET = inference de modeles deja entraines ; PostTraining = production de ces modeles. |
| **[QuantConnect ML-Training-Pipeline](../QuantConnect/ML-Training-Pipeline/)** | Pipeline training trading | Pipeline soeur sur RL/transformers pour trading (DT, PatchTST). PostTraining cible LMs, ML-Training-Pipeline cible time series. |

## References academiques

| Reference | Couverture |
|-----------|------------|
| Christiano et al., "Deep RL from human preferences" (NeurIPS 2017) | Origine RLHF |
| Stiennon et al., "Learning to summarize with human feedback" (NeurIPS 2020) | RLHF appliquee aux LMs |
| Ouyang et al., "Training language models to follow instructions" (InstructGPT, NeurIPS 2022) | SFT + RM + PPO canonical |
| Rafailov et al., "Direct Preference Optimization" (NeurIPS 2023) | DPO origin |
| Shao et al., "DeepSeekMath: Pushing the Limits of Mathematical Reasoning" (2024) | GRPO origin |
| Deepseek-AI, "Deepseek-R1: Incentivizing Reasoning Capability via RL" (2025) | RLVR + GRPO at scale |
| Lambert et al., "Tulu 3" (2024) | Survey post-training methods |

## Ressources en ligne

- [HuggingFace TRL documentation](https://huggingface.co/docs/trl/index) — librairie principale (SFT, DPO, GRPO trainers)
- [HuggingFace PEFT documentation](https://huggingface.co/docs/peft/index) — LoRA et adapters
- [Unsloth](https://github.com/unslothai/unsloth) — optimisations memoire pour RTX 3070 (optionnel)

## Statut

DRAFT — scaffold initial (README + structure). Notebooks PT-01 a PT-06 a livrer dans les cycles suivants (priorite PT-01 → PT-02 → PT-04, autres optionnels).

Suivi : [Issue #1742](https://github.com/jsboige/CoursIA/issues/1742) (parent Epic #1454).

## Licence

Voir la licence du repository principal.
