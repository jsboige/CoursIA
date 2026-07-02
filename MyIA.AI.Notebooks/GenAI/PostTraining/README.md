# PostTraining - Techniques de post-training des Language Models (SOTA 2024-2025)

[← Documentation GenAI](../README.md) | [↑ ..](../README.md) | [→ SemanticKernel](../SemanticKernel/README.md)

<!-- CATALOG-STATUS
series: GenAI-PostTraining
pedagogical_count: 7
breakdown: PostTraining=7
maturity: PRODUCTION=4, BETA=3
-->

> **Place dans GenAI** : cette série est le pendant *théorique et SOTA 2024-2025* de la série [FineTuning](../FineTuning/README.md). FineTuning couvre la boîte à outils pratique (LoRA, QLoRA, SFT, DPO, model merging) sur 5 notebooks exécutés ; PostTraining remonte la chaîne conceptuelle complète SFT → RLHF → DPO → GRPO → RLVR et reproduit les techniques récentes (Deepseek-R1) sur petits modèles, complétée par un notebook d'évaluation comparative et un détecteur de reward hacking, soit **7 notebooks** au total. Les deux se complèment : commencer par FineTuning pour la pratique, PostTraining pour la profondeur méthodologique.

Série pédagogique dédiée aux techniques de **post-training** des LMs ouverts : SFT, DPO, GRPO, RLVR. L'objectif est de comprendre pourquoi 2024-2025 marque une rupture pédagogique dans la façon dont les modèles de langue passent du pre-training brut à un assistant utile, et comment cette chaîne s'est simplifiée depuis la cascade RLHF historique jusqu'aux méthodes "direct" récentes.

## Pourquoi cette série

Le post-training est le maillon qui transforme un modèle pré-entraîné — au mieux un excellent statisticien du langage — en assistant aligné sur des préférences humaines ou des objectifs vérifiables. Pendant longtemps, la chaîne canonique était RLHF : Supervised Fine-Tuning, puis Reward Model, puis PPO. Trois étapes, trois bugs potentiels, beaucoup d'instabilité. Les techniques récentes (DPO en 2023, GRPO en 2024, RLVR en 2024-2025) ont réduit cette chaîne en s'attaquant aux deux maillons faibles : la dépendance au Reward Model appris (DPO le supprime) et la lourdeur mémoire de PPO (GRPO la divise).

En janvier 2025, Deepseek-R1 a publiquement validé cette progression en montrant qu'un modèle moyen entraîné avec GRPO sur des tâches à récompense vérifiable (math, code) peut atteindre un niveau de raisonnement compétitif avec des modèles bien plus gros entraînés de façon classique. Cette série didactise cette chaîne de techniques avec des reproductions concrètes sur **petits modèles** (Qwen2.5-0.5B/1.5B) déployables sur **GPU 8 Go** (RTX 3070), conformément à l'esprit "po-2024 pionnier parcimonieux" de l'Epic #1454.

L'angle pédagogique est d'expliquer la **math du loss** avant le code pour chaque technique. Trop de tutoriels existants montrent une cellule `trainer.train()` qui converge sans donner l'intuition de pourquoi DPO marche, pourquoi GRPO économise la mémoire, ou pourquoi RLVR contourne le besoin d'un Reward Model. Cette série inverse l'ordre : d'abord la formule, puis l'intuition, puis l'implémentation TRL/HuggingFace, puis les outputs réels d'entraînement.

**À qui s'adresse cette série** : ingénieurs ML curieux de comprendre la chaîne post-training au-delà des annonces de presse, étudiants en NLP voulant reproduire les techniques Deepseek-R1 sans cluster H100, et formateurs ayant besoin de notebooks pédagogiques sur des modèles que leurs étudiants peuvent réellement faire tourner. Prérequis : Python intermediate, PyTorch élémentaire, familiarité avec `transformers`, intuition de la backprop et de la cross-entropy. Le notebook PT-01 établit le contexte théorique sans code exécuté ; PT-02 reprend les bases SFT ; les notebooks PT-03 à PT-06 ajoutent une technique par étape.

## Notebooks

| # | Notebook | Sujet | Technique | Modele cible | PR |
|---|----------|-------|-----------|--------------|----|
| PT-01 | `PT_01_intro_post_training.ipynb` | Vue d'ensemble historique : SFT → RLHF → DPO → GRPO → RLVR | Théorique (markdown + figures) | N/A | — |
| PT-02 | `PT_02_sft_baseline.ipynb` | Supervised Fine-Tuning baseline | `trl.SFTTrainer` | Qwen2.5-0.5B-Instruct | #1764 |
| PT-03 | `PT_03_dpo_direct_preference.ipynb` | Direct Preference Optimization (Rafailov 2023) | `trl.DPOTrainer` | Qwen2.5-0.5B post-SFT | #1766 |
| PT-04 | `PT_04_grpo_deepseek_r1.ipynb` | Group Relative Policy Optimization (livrable clé) | `trl.GRPOTrainer` | Qwen2.5-0.5B | #1768 |
| PT-05 | `PT_05_rlvr_verifiable_rewards.ipynb` | RL with Verifiable Rewards (math/code) | `trl.GRPOTrainer` + verifier SymPy | Qwen2.5-0.5B | #1771 |
| PT-06 | `PT_06_eval_comparative.ipynb` | Évaluation comparative SFT vs DPO vs GRPO vs RLVR | Tableaux, chart, framework décision | tous | #1772 |
| PT-07 | `PT_07_rewardspy_reward_hacking.ipynb` | Détecter le reward hacking (Goodhart) — observabilité reward | `rewardspy.watch`/`audit` (offline, sans GPU) | N/A (offline) | #4538 |

## Progression pédagogique

Les notebooks s'enchaînent **dans l'ordre**. Sauter PT-02 (SFT) avant PT-03 (DPO) est techniquement possible mais perd l'intuition clé de DPO : pourquoi la formule contient un terme implicite de reward model est évident après avoir vu un SFT classique converger. De même, GRPO (PT-04) s'éclaire après avoir compris la limite mémoire de PPO. RLVR (PT-05) réutilise l'infrastructure GRPO mais remplace le reward appris par un vérificateur exact (sympy pour les expressions, sandbox pour le code).

PT-01 (intro) peut être lu **en parallèle** des autres notebooks ; c'est un compagnon théorique.

## Comprendre les techniques en profondeur

Cette section développe le fond de chaque technique au-delà du simple nom dans le tableau. Les détails mathématiques précis vivent dans les notebooks ; ce qui suit est la **carte mentale** que la série cherche à installer chez l'apprenant.

### SFT — Supervised Fine-Tuning

La technique la plus simple du post-training : un dataset de paires (prompt, réponse_souhaitée), un loss de cross-entropy classique, un optimiseur Adam. Du point de vue formel, c'est un MLE sur une distribution conditionnelle. Toute la subtilité réside dans la qualité du dataset : un SFT sur des réponses moyennes produit un assistant moyen. Les datasets de référence (OpenAssistant, Dolly, Tulu, Open-Hermes) sont devenus des assets à part entière de la communauté. Le piège majeur pour l'apprenant est de penser que SFT "aligne" le modèle : il l'imite seulement. L'alignement vient des étapes suivantes ou de la composition du dataset (curation, refus, ton).

### DPO — Direct Preference Optimization (Rafailov 2023)

Le bond conceptuel clé de 2023. Plutôt que d'apprendre un Reward Model (RM) puis de l'utiliser dans PPO, DPO dérive une formule de loss qui consomme directement les paires de préférences (réponse_préférée, réponse_rejetée) et entraîne la policy directement. La dérivation passe par la solution analytique de l'optimum de PPO régularisé par KL : on montre que `r(x, y) = β log(π_θ(y|x) / π_ref(y|x)) + Z(x)`, ce qui permet d'éliminer `r` du loss au profit d'une expression ne dépendant que de `π_θ` et `π_ref`. Bénéfice : un seul modèle à entraîner au lieu de deux, pas de critic, training stable. Inconvénients : suppose un BTL (Bradley-Terry-Luce) sous-jacent valide, sensible à la qualité des préférences (bruit dans le dataset = perturbation directe du gradient).

### GRPO — Group Relative Policy Optimization (Deepseek 2024)

La rupture mémoire de 2024. PPO classique nécessite (1) la policy, (2) une copie référence de la policy pour le KL penalty, (3) un value head (critic) entraîné en parallèle. Sur un modèle 7B, c'est ~30 Go de VRAM pour les seuls poids. GRPO supprime le critic en estimant l'avantage par **comparaison intra-groupe** : pour chaque prompt, générer N completions (typiquement 8-16), évaluer chacune via la reward, calculer l'avantage relatif normalisé dans le groupe. Le baseline implicite du groupe remplace le critic. Bénéfice : ~40% de VRAM gagnée, même performance qu'PPO sur les benchmarks math/code. Inconvénients : sensibilité à N (trop petit = baseline bruitée, trop grand = coûteux), couplage fort à une reward de qualité.

### RLVR — RL with Verifiable Rewards (Deepseek-R1 2025)

L'innovation méthodologique de 2025. Au lieu d'apprendre un Reward Model sur des préférences (cycle long, biaisé par les annotateurs), on utilise des tâches dont la réponse est vérifiable **algorithmiquement** : équations math (`sympy.simplify(answer - target) == 0`), code (`exec(code); assert tests`), traduction (`bleu_score(translation, reference) > seuil`). Le RM devient un vérificateur exact, ce qui élimine toute la complexité RLHF en aval. C'est ce qui a rendu possible Deepseek-R1 : combiné avec GRPO, on entraîne sur des prompts math/code sans aucune annotation humaine, et le modèle développe spontanément des chains-of-thought longs. Limite : applicable uniquement aux tâches vérifiables (math, code, logique formelle), pas aux tâches subjectives (écriture créative, conseil).

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

## Contraintes RTX 3070 8 Go (parcimonie po-2024)

- **Modèles ≤ 1.5B params**, priorise Qwen2.5-0.5B/1.5B
- **Quantization 4-bit** (`bitsandbytes`) obligatoire pour modèles > 0.5B
- **LoRA** rank ≤ 16, alpha ≤ 32, adapters sur attention + MLP
- **Batch size** ≤ 4, gradient accumulation jusqu'à 16 pour batch effectif 64
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

## Pièges pédagogiques courants

Les notebooks anticipent et adressent explicitement plusieurs **erreurs d'interprétation** que les apprenants développent typiquement face à ces techniques :

- **"DPO est juste un SFT sur les préférences"** — faux. DPO contient un terme de divergence par rapport au modèle de référence (`π_ref`) qui empêche le drift catastrophique. Un SFT sur paires préférées seules effondrerait la diversité. PT-03 isole expérimentalement ce terme via un ablation (`β = 0` vs `β = 0.1`) pour rendre visible son effet.
- **"Plus de seeds GRPO = mieux"** — faux jusqu'à un seuil. Au-delà de N ≈ 16, le baseline intra-groupe devient stable mais le coût VRAM explose. PT-04 documente la courbe rendement/coût avec N ∈ {4, 8, 16, 32} sur Qwen2.5-0.5B.
- **"RLVR remplace toutes les autres méthodes"** — faux. RLVR est restreint aux tâches vérifiables. Pour écriture créative, conversation ouverte, assistance, DPO reste l'approche dominante. PT-05 expose cette limite via un contre-exemple : appliquer RLVR à une tâche subjective produit un modèle dégénéré qui exploite la fonction de reward exacte.
- **"LoRA = moins de qualité que full fine-tuning"** — vrai marginalement, faux pratiquement. Sur un budget GPU 8 Go, LoRA atteint 95-98% de la qualité d'un full FT à 5% du coût mémoire. PT-02 documente ce trade-off explicitement.
- **"Le post-training résout les hallucinations"** — faux. Les hallucinations viennent du pre-training (sous-représentation factuelle) ; le post-training les masque parfois en augmentant la confiance des refus, mais ne les supprime pas. PT-06 illustre via TruthfulQA : SFT/DPO/GRPO améliorent surface, pas substance.

Ces points sont signalés en encarts `> **Piège :**` au fil des notebooks, avec exercices de vérification.

## Méthodologie d'évaluation

Comparer SFT vs DPO vs GRPO vs RLVR de façon honnête requiert une discipline expérimentale stricte. La série applique les règles suivantes, alignées sur la règle CoursIA **Multi-seed ≥ 4** :

- **Seeds fixées** : `{0, 1, 7, 42}` (au minimum). Résultats single-seed = signal bruit, jamais une "victoire".
- **Held-out separation** : datasets HF splittés via `seed=42` réservé évaluation. Aucune training data ne fuit dans l'eval.
- **Benchmarks distincts** : aucune métrique unique ne suffit. La série évalue sur :
  - **GSM8K** (math reasoning, 1.3k test) — cible RLVR
  - **MMLU subset** (knowledge, 5k test) — non-cible, contrôle de régression
  - **IFEval** (instruction following, 541 test) — cible DPO/SFT
  - **HumanEval** (code, 164 test) — cible RLVR
- **Verdict honnête** : BEATS / NO BEATS / INCONCLUSIVE selon écart ≥ 2σ cross-seed. Pas de "promising", pas de "trending positive".
- **Budget compute fixe** : chaque technique reçoit le même budget GPU-hour pour la comparaison finale (typiquement 30 min RTX 3070).
- **Coût cache** : on rapporte VRAM peak, training time, et nombre de tokens vus pour rendre les trade-offs visibles. "DPO bat GRPO de 2%" est inutile si DPO consomme 3x plus de VRAM.

PT-06 documente le pipeline d'évaluation complet et produit un tableau comparatif final reproductible.

## Qualité pédagogique

| Aspect | Application |
|--------|-------------|
| Exercices | Stubs sans erreur (`pass`, `print(...)`, `return None`) : le notebook s'exécute de bout en bout même exercices non complétés |
| Outputs | Tous les notebooks committés avec outputs réels d'exécution |
| Environnement | `coursia-ml-training` requis (TRL + bitsandbytes + datasets) |
| Méthodologie | Toute claim comparative ("GRPO > DPO") vérifiée sur >= 4 seeds avec écart >= 2 sigma |

## Ponts avec les autres séries

| Série | Connection | Details |
|-------|------------|---------|
| **[RL](../../RL/)** | RL classique fondamentaux | Les notebooks RL ([rl_5 MDP/Q-Learning](../../RL/rl_5_mdp_dp_qlearning.ipynb) et [rl_6c PPO from scratch](../../RL/rl_6c_ppo_from_scratch.ipynb)) établissent l'intuition policy/value que PPO/GRPO réutilisent. Recommandés comme prérequis pour PT-04. |
| **[RL — rl_9 offline](../../RL/rl_9_offline_rl.ipynb)** | DPO = preference learning offline | Le Behavior Cloning y est l'analogue tabulaire du SFT, et la contrainte de support de BCQ celle de la pénalité KL de DPO (PT-03). Le meilleur prérequis conceptuel pour DPO. |
| **[RL — rl_10 reward shaping](../../RL/rl_10_reward_shaping.ipynb)** | Reward model = shaping appris | Le reward shaping (Ng 1999) et son biais (shaping naïf → reward hacking) préfigurent le reward model appris et le Goodhart traité en [PT-07](PT_07_rewardspy_reward_hacking.ipynb). |
| **[GenAI/FineTuning](../FineTuning/)** | Boîte à outils fine-tuning | Série sœur dans GenAI : LoRA/QLoRA/SFT/DPO en pratique sur 5 notebooks. PostTraining = profondeur méthodologique (7 notebooks), FineTuning = recettes exécutables. |

## Contexte industriel et historique 2017-2025

La chaîne SFT → RLHF → DPO → GRPO → RLVR n'est pas une succession linéaire d'améliorations techniques : c'est une succession d'**adaptations à des contraintes économiques et infrastructurelles** changeantes. Comprendre ces contraintes aide à anticiper la prochaine étape.

**2017-2020 : l'ère du Reward Model** — Christiano et al. (NeurIPS 2017) introduisent le concept de "deep RL from human preferences" sur des tâches Atari. Stiennon et al. (NeurIPS 2020) l'appliquent au résumé de texte. À cette époque, le calcul est abondant et le bottleneck est la qualité des annotations. L'industrie investit massivement dans des équipes d'annotateurs (OpenAI/Surge, Anthropic/Surge, Scale AI, Mechanical Turk rénové). PPO domine.

**2022 : InstructGPT canonise RLHF** — Ouyang et al. (NeurIPS 2022) publient la "recipe" complète (SFT + RM + PPO) qui devient le standard de facto chez OpenAI, Anthropic, Meta. Cette recipe est chère : ~6 mois d'annotation, 3 modèles à entraîner en parallèle, infrastructure RL maison.

**2023 : DPO redistribue les cartes** — Rafailov et al. (NeurIPS 2023) montrent que la moitié de la stack peut être supprimée. Stanford, Allen AI, et la communauté open source (Tulu 2) démontrent rapidement que DPO atteint des performances proches de PPO pour 10x moins de complexité. Résultat : les labos avec budget moyen peuvent enfin entraîner des assistants compétitifs (Mistral, Yi, Qwen).

**2024 : Deepseek change la perspective mémoire** — Shao et al. publient le papier GRPO. La motivation est explicitement industrielle : entraîner des modèles math/code sans louer des clusters H100 à $10/h. La méthode permet de faire tenir l'entraînement RL d'un 7B sur 8x A100, ou d'un 1.5B sur 1x A100. C'est le moment où le RL post-training redevient accessible aux laboratoires académiques.

**2025 : Deepseek-R1 et la disparition de l'annotateur** — Deepseek-AI (janvier 2025) publie R1 et R1-Zero. R1-Zero est entraîné **sans aucun SFT humain**, uniquement GRPO + RLVR sur des prompts math/code. Le modèle développe spontanément des chains-of-thought longs, des comportements de re-vérification, des phases de "wait, let me reconsider". C'est le moment où la communauté réalise que pour les domaines vérifiables, le post-training peut se passer d'annotation humaine. L'industrie commence à explorer le RLVR pour les agents (le succès étant vérifiable par exécution du plan), pour la traduction (BLEU/chrF comme reward), pour la génération SQL (test sur DB de validation).

**Vers 2026 et au-delà** — les directions actives à la date de cette série : (1) **synthetic preferences** (modèles juges au lieu d'annotateurs), (2) **on-policy distillation** (GRPO + distillation simultanée), (3) **process reward models** (PRM : récompenser les étapes intermédiaires, pas seulement le résultat final), (4) **multi-turn RL** (entraîner la cohérence sur plusieurs tours, pas tour par tour). La série ne couvre pas ces directions mais les notebooks de tête les référencent en "Pour aller plus loin".

## Compatibilité matérielle et choix d'implémentation

Le choix Qwen2.5-0.5B / 1.5B / Math-1.5B n'est pas anodin. Il résulte d'un arbitrage explicite entre :

- **Petite taille pour itération rapide** : un GRPO sur 0.5B converge en ~30 min sur RTX 3070, ce qui rend les exercices réalisables en TP. Un même exercice sur 7B prendrait 6-8h et nécessiterait du gradient checkpointing agressif.
- **Qualité suffisante pour observer les effets** : un modèle trop petit (< 0.5B) montre des effets de régularisation rendant l'observation des techniques bruitée. 0.5B-1.5B est la zone Goldilocks pour observer **clairement** les effets de SFT/DPO/GRPO.
- **Licence permissive Qwen** : Apache 2.0, utilisable en cours sans friction.
- **Famille cohérente** : même tokenizer, même architecture, ce qui permet de comparer techniques sans confondre effets de modèle et effets de méthode.
- **Variante Math-1.5B pour RLVR** : Qwen propose une variante pré-entraînée sur math, ce qui évite de devoir partir de zéro pour observer un comportement RLVR concret.

Alternatives écartées et raisons : Llama-3.2-1B (gated, friction d'inscription HF), Phi-3-mini (architecture custom mal supportée par TRL au moment de la série), Gemma-2-2B (licence restrictive sur usage commercial, compliqué pour les apprenants en formation pro).

Pour les apprenants disposant de plus de VRAM (RTX 4090 24Go, A100 40Go), la série indique en encart les hyperparamètres à modifier pour scaler à Qwen2.5-7B sans changer la structure pédagogique.

## References academiques

| Reference | Couverture |
|-----------|------------|
| Christiano et al., "Deep RL from human preferences" (NeurIPS 2017) | Origine RLHF |
| Stiennon et al., "Learning to summarize with human feedback" (NeurIPS 2020) | RLHF appliquée aux LMs |
| Ouyang et al., "Training language models to follow instructions" (InstructGPT, NeurIPS 2022) | SFT + RM + PPO canonique |
| Rafailov et al., "Direct Preference Optimization" (NeurIPS 2023) | DPO origin |
| Shao et al., "DeepSeekMath: Pushing the Limits of Mathematical Reasoning" (2024) | GRPO origin |
| Deepseek-AI, "Deepseek-R1: Incentivizing Reasoning Capability via RL" (2025) | RLVR + GRPO at scale |
| Lambert et al., "Tulu 3" (2024) | Survey post-training methods |

## Ressources en ligne

- [HuggingFace TRL documentation](https://huggingface.co/docs/trl/index) — librairie principale (SFT, DPO, GRPO trainers)
- [HuggingFace PEFT documentation](https://huggingface.co/docs/peft/index) — LoRA et adapters
- [Unsloth](https://github.com/unslothai/unsloth) — optimisations mémoire pour RTX 3070 (optionnel)

## Statut

Série complète : tous les notebooks sont exécutés avec outputs réels.

Suivi : [Issue #1742](https://github.com/jsboige/CoursIA/issues/1742).

## FAQ

### OOM CUDA pendant GRPO ou DPO

Les notebooks PT-03 à PT-05 sont conçus pour RTX 3070 (8 Go) avec Qwen2.5-0.5B, mais OOM reste possible si l'environnement n'est pas optimal. Stratégies :

- Vérifier que `bitsandbytes` est installé et que la quantization 4-bit est activée (`load_in_4bit=True`).
- Réduire `per_device_train_batch_size` à 1 et augmenter `gradient_accumulation_steps` pour garder un batch effectif correct.
- Le paramètre N (nombre de completions par prompt) dans GRPO est le principal consommateur VRAM : utiliser `N=4` ou `N=8` plutôt que `N=16` sur GPU limité.
- Fermer tous les autres processus GPU avant l'entraînement (`nvidia-smi` pour vérifier).

Si votre GPU à 4 Go ou moins, passer `LOAD_MODEL_AND_TRAIN=False` dans les notebooks pour exécuter en mode démo (chargement des outputs pré-calculés sans entraînement réel).

### Quelle série faire en premier : FineTuning ou PostTraining ?

Les deux séries sont complémentaires :

- **FineTuning d'abord** si vous voulez rapidement fine-tuner un modèle pour votre cas d'usage (LoRA, SFT pratique, DPO pratique). Approche "boîte à outils".
- **PostTraining d'abord** si vous voulez comprendre la théorie derrière les techniques avant de les appliquer. Approche "fondamentaux".

Le parcours optimal est FineTuning (pratique) puis PostTraining (profondeur), mais l'inverse fonctionne aussi pour les profils théoriciens.

### DPO vs GRPO : quand utiliser quoi ?

| Critère | DPO | GRPO |
|---------|-----|------|
| **Données requises** | Paires de préférences (choisi/rejeté) | Prompts + fonction de reward |
| **Reward Model** | Non (implicitement éliminé) | Non (baseline intra-groupe) |
| **Critic** | Non | Non |
| **VRAM** | Plus faible (1 modèle) | Plus élevée (N completions en mémoire) |
| **Tâches cibles** | Préférences subjectives, style, ton | Math, code, tâches vérifiables |
| **Stabilité** | Bonne (BTL assumption) | Variable (sensible à N et à la reward) |
| **Data annotation** | Nécessaire (préférences humaines) | Optionnelle (reward vérifiable) |

En pratique : DPO pour l'alignement conversationnel, GRPO+RLVR pour le raisonnement mathématique et code.

### Les métriques d'évaluation ne s'améliorent pas après training

Si SFT, DPO ou GRPO ne produisent pas d'amélioration mesurable sur GSM8K ou MMLU :

- Vérifier que le dataset d'évaluation est bien séparé du dataset d'entraînement (`seed=42` pour le split, pas de fuite).
- S'assurer que le nombre de steps d'entraînement est suffisant (minimum 100 steps pour observer un signal sur 0.5B).
- Un seul seed ne suffit pas : les résultats sont bruités. Utiliser au minimum 4 seeds (`{0, 1, 7, 42}`) et vérifier que l'écart est >= 2 sigma (cf règle multi-seed CoursIA).
- Le notebook PT-06 (`PT_06_eval_comparative.ipynb`) automatise cette comparaison avec verdict BEATS/NO BEATS/INCONCLUSIVE.

### ImportError avec trl, peft ou bitsandbytes

L'environnement `coursia-ml-training` doit contenir les dépendances post-training :

```bash
conda activate coursia-ml-training
pip install --upgrade transformers trl peft accelerate datasets bitsandbytes

# Verifier
python -c "import trl; print(f'TRL {trl.__version__}')"
python -c "import bitsandbytes; print('bitsandbytes OK')"
```

Sur Windows, `bitsandbytes` peut nécessiter CUDA 12.x. Si erreur DLL not found, vérifier que `CUDA_HOME` pointe vers le bon toolkit et que `bitsandbytes` est à jour (`>= 0.45`).

### Peut-on reproduire Deepseek-R1 avec cette serie ?

Non directement, mais les briques conceptuelles sont les mêmes. Deepseek-R1 utilise GRPO + RLVR sur des modèles 671B (architecture MoE) avec une infrastructure distribuée massive. Cette série reproduit les mêmes techniques sur Qwen2.5-0.5B/1.5B pour rendre les concepts accessibles sur GPU 8 Go. Les formules de loss, les mécanismes de reward, et les stratégies d'évaluation sont identiques — seule l'échelle change. PT-04 (GRPO) et PT-05 (RLVR) reproduisent fidèlement le pipeline Deepseek-R1 en miniature.

## Licence

Voir la licence du dépôt principal.
