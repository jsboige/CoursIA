# PostTraining - Techniques de post-training des Language Models (SOTA 2024-2025)

[← Documentation GenAI](../README.md) | [↑ ..](../README.md) | [→ SemanticKernel](../SemanticKernel/README.md)

<!-- CATALOG-STATUS
series: GenAI-PostTraining
pedagogical_count: 6
breakdown: PostTraining=6
maturity: BETA=3, PRODUCTION=3
-->

> **Place dans GenAI** : cette serie est le pendant *theorique et SOTA 2024-2025* de la serie [FineTuning](../FineTuning/README.md). FineTuning couvre la boite a outils pratique (LoRA, QLoRA, SFT, DPO, model merging) sur 5 notebooks executes ; PostTraining remonte la chaine conceptuelle complete SFT → RLHF → DPO → GRPO → RLVR et reproduit les techniques recentes (Deepseek-R1) sur petits modeles. Les deux se complementent : commencer par FineTuning pour la pratique, PostTraining pour la profondeur methodologique.

Serie pedagogique dediee aux techniques de **post-training** des LMs ouverts : SFT, DPO, GRPO, RLVR. L'objectif est de comprendre pourquoi 2024-2025 marque une rupture pedagogique dans la facon dont les modeles de langue passent du pre-training brut a un assistant utile, et comment cette chaine s'est simplifiee depuis la cascade RLHF historique jusqu'aux methodes "direct" recentes.

## Pourquoi cette serie

Le post-training est le maillon qui transforme un modele pre-entraine — au mieux un excellent statisticien du langage — en assistant aligne sur des preferences humaines ou des objectifs verifiables. Pendant longtemps, la chaine canonique etait RLHF : Supervised Fine-Tuning, puis Reward Model, puis PPO. Trois etapes, trois bugs potentiels, beaucoup d'instabilite. Les techniques recentes (DPO en 2023, GRPO en 2024, RLVR en 2024-2025) ont reduit cette chaine en s'attaquant aux deux maillons faibles : la dependance au Reward Model appris (DPO le supprime) et la lourdeur memoire de PPO (GRPO la divise).

En janvier 2025, Deepseek-R1 a publiquement valide cette progression en montrant qu'un modele moyen entraine avec GRPO sur des taches a recompense verifiable (math, code) peut atteindre un niveau de raisonnement competitif avec des modeles bien plus gros entraines de facon classique. Cette serie didactise cette chaine de techniques avec des reproductions concretes sur **petits modeles** (Qwen2.5-0.5B/1.5B) deployables sur **GPU 8 Go** (RTX 3070), conformement a l'esprit "po-2024 pionnier parcimonieux" de l'Epic #1454.

L'angle pedagogique est d'expliquer la **math du loss** avant le code pour chaque technique. Trop de tutoriels existants montrent une cellule `trainer.train()` qui converge sans donner l'intuition de pourquoi DPO marche, pourquoi GRPO economise la memoire, ou pourquoi RLVR contourne le besoin d'un Reward Model. Cette serie inverse l'ordre : d'abord la formule, puis l'intuition, puis l'implementation TRL/HuggingFace, puis les outputs reels d'entrainement.

**A qui s'adresse cette serie** : ingenieurs ML curieux de comprendre la chaine post-training au-dela des annonces de presse, etudiants en NLP voulant reproduire les techniques Deepseek-R1 sans cluster H100, et formateurs ayant besoin de notebooks pedagogiques sur des modeles que leurs etudiants peuvent reellement faire tourner. Prerequis : Python intermediate, PyTorch elementaire, familiarite avec `transformers`, intuition de la backprop et de la cross-entropy. Le notebook PT-01 etablit le contexte theorique sans code execute ; PT-02 reprend les bases SFT ; les notebooks PT-03 a PT-06 ajoutent une technique par etape.

## Notebooks

| # | Notebook | Sujet | Technique | Modele cible | PR |
|---|----------|-------|-----------|--------------|----|
| PT-01 | `PT_01_intro_post_training.ipynb` | Vue d'ensemble historique : SFT → RLHF → DPO → GRPO → RLVR | Theorique (markdown + figures) | N/A | — |
| PT-02 | `PT_02_sft_baseline.ipynb` | Supervised Fine-Tuning baseline | `trl.SFTTrainer` | Qwen2.5-0.5B-Instruct | #1764 |
| PT-03 | `PT_03_dpo_direct_preference.ipynb` | Direct Preference Optimization (Rafailov 2023) | `trl.DPOTrainer` | Qwen2.5-0.5B post-SFT | #1766 |
| PT-04 | `PT_04_grpo_deepseek_r1.ipynb` | Group Relative Policy Optimization (livrable cle) | `trl.GRPOTrainer` | Qwen2.5-0.5B | #1768 |
| PT-05 | `PT_05_rlvr_verifiable_rewards.ipynb` | RL with Verifiable Rewards (math/code) | `trl.GRPOTrainer` + verifier SymPy | Qwen2.5-0.5B | #1771 |
| PT-06 | `PT_06_eval_comparative.ipynb` | Evaluation comparative SFT vs DPO vs GRPO vs RLVR | Tableaux, chart, framework decision | tous | #1772 |

## Progression pedagogique

Les notebooks s'enchainent **dans l'ordre**. Sauter PT-02 (SFT) avant PT-03 (DPO) est techniquement possible mais perd l'intuition cle de DPO : pourquoi la formule contient un terme implicite de reward model est evident apres avoir vu un SFT classique converger. De meme, GRPO (PT-04) s'eclaire apres avoir compris la limite memoire de PPO. RLVR (PT-05) reutilise l'infrastructure GRPO mais remplace le reward appris par un verificateur exact (sympy pour les expressions, sandbox pour le code).

PT-01 (intro) peut etre lu **en parallele** des autres notebooks ; c'est un compagnon theorique.

## Comprendre les techniques en profondeur

Cette section developpe le fond de chaque technique au-dela du simple nom dans le tableau. Les details mathematiques precis vivent dans les notebooks ; ce qui suit est la **carte mentale** que la serie cherche a installer chez l'apprenant.

### SFT — Supervised Fine-Tuning

La technique la plus simple du post-training : un dataset de paires (prompt, reponse_souhaitee), un loss de cross-entropy classique, un optimiseur Adam. Du point de vue formel, c'est un MLE sur une distribution conditionnelle. Toute la subtilite reside dans la qualite du dataset : un SFT sur des reponses moyennes produit un assistant moyen. Les datasets de reference (OpenAssistant, Dolly, Tulu, Open-Hermes) sont devenus des assets a part entiere de la communaute. Le piege majeur pour l'apprenant est de penser que SFT "aligne" le modele : il l'imite seulement. L'alignement vient des etapes suivantes ou de la composition du dataset (curation, refus, ton).

### DPO — Direct Preference Optimization (Rafailov 2023)

Le bond conceptuel cle de 2023. Plutot que d'apprendre un Reward Model (RM) puis de l'utiliser dans PPO, DPO derive une formule de loss qui consomme directement les paires de preferences (reponse_preferee, reponse_rejetee) et entraine la policy directement. La derivation passe par la solution analytique de l'optimum de PPO regularise par KL : on montre que `r(x, y) = β log(π_θ(y|x) / π_ref(y|x)) + Z(x)`, ce qui permet d'eliminer `r` du loss au profit d'une expression ne dependant que de `π_θ` et `π_ref`. Beneficie : un seul modele a entrainer au lieu de deux, pas de critic, training stable. Inconvenients : suppose un BTL (Bradley-Terry-Luce) sous-jacent valide, sensible a la qualite des preferences (bruit dans le dataset = perturbation directe du gradient).

### GRPO — Group Relative Policy Optimization (Deepseek 2024)

La rupture memoire de 2024. PPO classique necessite (1) la policy, (2) une copie reference de la policy pour le KL penalty, (3) un value head (critic) entraine en parallele. Sur un modele 7B, c'est ~30 Go de VRAM pour les seuls poids. GRPO supprime le critic en estimant l'avantage par **comparaison intra-groupe** : pour chaque prompt, generer N completions (typiquement 8-16), evaluer chacune via la reward, calculer l'avantage relatif normalise dans le groupe. Le baseline implicite du groupe remplace le critic. Beneficie : ~40% de VRAM gagnee, meme performance qu'PPO sur les benchmarks math/code. Inconvenients : sensibilite a N (trop petit = baseline bruite, trop grand = couteux), couplage fort a une reward de qualite.

### RLVR — RL with Verifiable Rewards (Deepseek-R1 2025)

L'innovation methodologique de 2025. Au lieu d'apprendre un Reward Model sur des preferences (cycle long, biaise par les annotateurs), on utilise des taches dont la reponse est verifiable **algorithmiquement** : equations math (`sympy.simplify(answer - target) == 0`), code (`exec(code); assert tests`), traduction (`bleu_score(translation, reference) > seuil`). Le RM devient un verificateur exact, ce qui elimine toute la complexite RLHF en aval. C'est ce qui a rendu possible Deepseek-R1 : combine avec GRPO, on entraine sur des prompts math/code sans aucune annotation humaine, et le modele developpe spontanement des chains-of-thought longs. Limite : applicable uniquement aux taches verifiables (math, code, logique formelle), pas aux taches subjectives (ecriture creative, conseil).

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

## Pieges pedagogiques courants

Les notebooks anticipent et adressent explicitement plusieurs **erreurs d'interpretation** que les apprenants developpent typiquement face a ces techniques :

- **"DPO est juste un SFT sur les preferences"** — faux. DPO contient un terme de divergence par rapport au modele de reference (`π_ref`) qui empeche le drift catastrophique. Un SFT sur paires preferees seules effondrerait la diversite. PT-03 isole experimentalement ce terme via un ablation (`β = 0` vs `β = 0.1`) pour rendre visible son effet.
- **"Plus de seeds GRPO = mieux"** — faux jusqu'a un seuil. Au-dela de N ≈ 16, le baseline intra-groupe devient stable mais le cout VRAM explose. PT-04 documente la courbe rendement/cout avec N ∈ {4, 8, 16, 32} sur Qwen2.5-0.5B.
- **"RLVR remplace toutes les autres methodes"** — faux. RLVR est restreint aux taches verifiables. Pour ecriture creative, conversation ouverte, assistance, DPO reste l'approche dominante. PT-05 expose cette limite via un contre-exemple : appliquer RLVR a une tache subjective produit un modele degenere qui exploite la fonction de reward exacte.
- **"LoRA = moins de qualite que full fine-tuning"** — vrai marginalement, faux pratiquement. Sur un budget GPU 8 Go, LoRA atteint 95-98% de la qualite d'un full FT a 5% du cout memoire. PT-02 documente ce trade-off explicitement.
- **"Le post-training resout les hallucinations"** — faux. Les hallucinations viennent du pre-training (sous-representation factuelle) ; le post-training les masque parfois en augmentant la confiance des refus, mais ne les supprime pas. PT-06 illustre via TruthfulQA : SFT/DPO/GRPO ameliorent surface, pas substance.

Ces points sont signales en encarts `> **Piege :**` au fil des notebooks, avec exercices de verification.

## Methodologie d'evaluation

Comparer SFT vs DPO vs GRPO vs RLVR de facon honnete requiert une discipline experimentale stricte. La serie applique les regles suivantes, alignees sur la regle CoursIA **Multi-seed ≥ 4** :

- **Seeds fixees** : `{0, 1, 7, 42}` (au minimum). Resultats single-seed = signal bruit, jamais une "victoire".
- **Held-out separation** : datasets HF splittes via `seed=42` reserve evaluation. Aucune training data ne fuit dans l'eval.
- **Benchmarks distincts** : aucune metrique unique ne suffit. La serie evalue sur :
  - **GSM8K** (math reasoning, 1.3k test) — cible RLVR
  - **MMLU subset** (knowledge, 5k test) — non-cible, controle de regression
  - **IFEval** (instruction following, 541 test) — cible DPO/SFT
  - **HumanEval** (code, 164 test) — cible RLVR
- **Verdict honnete** : BEATS / NO BEATS / INCONCLUSIVE selon ecart ≥ 2σ cross-seed. Pas de "promising", pas de "trending positive".
- **Budget compute fixe** : chaque technique recoit le meme budget GPU-hour pour la comparaison finale (typiquement 30 min RTX 3070).
- **Cout cache** : on rapporte VRAM peak, training time, et nombre de tokens vus pour rendre les trade-offs visibles. "DPO bat GRPO de 2%" est inutile si DPO consomme 3x plus de VRAM.

PT-06 documente le pipeline d'evaluation complet et produit un tableau comparatif final reproductible.

## Qualite pedagogique

| Aspect | Application |
|--------|-------------|
| Exercices | Stubs sans erreur (`pass`, `print(...)`, `return None`) : le notebook s'execute de bout en bout meme exercices non completes |
| Outputs | Tous les notebooks committes avec outputs reels d'execution |
| Environnement | `coursia-ml-training` requis (TRL + bitsandbytes + datasets) |
| Methodologie | Toute claim comparative ("GRPO > DPO") verifiee sur >= 4 seeds avec ecart >= 2 sigma |

## Ponts avec les autres series

| Serie | Connection | Details |
|-------|------------|---------|
| **[RL](../../RL/)** | RL classique fondamentaux | Les notebooks RL ([rl_5 MDP/Q-Learning](../../RL/rl_5_mdp_dp_qlearning.ipynb) et [rl_6c PPO from scratch](../../RL/rl_6c_ppo_from_scratch.ipynb)) etablissent l'intuition policy/value que PPO/GRPO reutilisent. Recommandes comme prerequis pour PT-04. |
| **[GenAI/Texte](../Texte/)** | Usage des LMs aligned | Les notebooks GenAI consomment des modeles deja post-trained. Cette serie explique comment ces modeles arrivent dans cet etat. |
| **[GenAI/FineTuning](../FineTuning/)** | Boite a outils fine-tuning | Serie soeur dans GenAI : LoRA/QLoRA/SFT/DPO en pratique sur 5 notebooks. PostTraining = profondeur methodologique, FineTuning = recettes executables. |
| **[ML](../../ML/)** | Tutoriels ML.NET | Pont conceptuel : ML.NET = inference de modeles deja entraines ; PostTraining = production de ces modeles. |
| **[QuantConnect ML-Training-Pipeline](../../QuantConnect/ML-Training-Pipeline/)** | Pipeline training trading | Pipeline soeur sur RL/transformers pour trading (DT, PatchTST). PostTraining cible LMs, ML-Training-Pipeline cible time series. |

## Contexte industriel et historique 2017-2025

La chaine SFT → RLHF → DPO → GRPO → RLVR n'est pas une succession lineaire d'ameliorations techniques : c'est une succession d'**adaptations a des contraintes economiques et infrastructurelles** changeantes. Comprendre ces contraintes aide a anticiper la prochaine etape.

**2017-2020 : l'ere du Reward Model** — Christiano et al. (NeurIPS 2017) introduisent le concept de "deep RL from human preferences" sur des taches Atari. Stiennon et al. (NeurIPS 2020) l'appliquent au resume de texte. A cette epoque, le calcul est abondant et le bottleneck est la qualite des annotations. L'industrie investit massivement dans des equipes d'annotateurs (OpenAI/Surge, Anthropic/Surge, Scale AI, Mechanical Turk renove). PPO domine.

**2022 : InstructGPT canonise RLHF** — Ouyang et al. (NeurIPS 2022) publient la "recipe" complete (SFT + RM + PPO) qui devient le standard de facto chez OpenAI, Anthropic, Meta. Cette recipe est cher : ~6 mois d'annotation, 3 modeles a entrainer en parallele, infrastructure RL maison.

**2023 : DPO redistribue les cartes** — Rafailov et al. (NeurIPS 2023) montrent que la moitie de la stack peut etre supprimee. Stanford, Allen AI, et la communaute open source (Tulu 2) demontrent rapidement que DPO atteint des performances proches de PPO pour 10x moins de complexite. Resultat : les labos avec budget moyen peuvent enfin entrainer des assistants competitifs (Mistral, Yi, Qwen).

**2024 : Deepseek change la perspective memoire** — Shao et al. publient le papier GRPO. La motivation est explicitement industrielle : entrainer des modeles math/code sans louer des clusters H100 a $10/h. La methode permet de faire tenir l'entrainement RL d'un 7B sur 8x A100, ou d'un 1.5B sur 1x A100. C'est le moment ou le RL post-training redevient accessible aux laboratoires academiques.

**2025 : Deepseek-R1 et la disparition de l'annotateur** — Deepseek-AI (janvier 2025) publie R1 et R1-Zero. R1-Zero est entraine **sans aucun SFT humain**, uniquement GRPO + RLVR sur des prompts math/code. Le modele developpe spontanement des chains-of-thought longs, des comportements de re-verification, des phases de "wait, let me reconsider". C'est le moment ou la communaute realise que pour les domaines verifiables, le post-training peut se passer d'annotation humaine. L'industrie commence a explorer le RLVR pour les agents (le succes etant verifiable par execution du plan), pour la traduction (BLEU/chrF comme reward), pour la generation SQL (test sur DB de validation).

**Vers 2026 et au-dela** — les directions actives a la date de cette serie : (1) **synthetic preferences** (modeles juges au lieu d'annotateurs), (2) **on-policy distillation** (GRPO + distillation simultanee), (3) **process reward models** (PRM : recompenser les etapes intermediaires, pas seulement le resultat final), (4) **multi-turn RL** (entrainer la coherence sur plusieurs tours, pas tour par tour). La serie ne couvre pas ces directions mais les notebooks de tete les referencent en "Pour aller plus loin".

## Compatibilite materielle et choix d'implementation

Le choix Qwen2.5-0.5B / 1.5B / Math-1.5B n'est pas anodin. Il resulte d'un arbitrage explicite entre :

- **Petite taille pour iteration rapide** : un GRPO sur 0.5B converge en ~30 min sur RTX 3070, ce qui rend les exercices realisables en TP. Un meme exercice sur 7B prendrait 6-8h et necessiterait du gradient checkpointing agressif.
- **Qualite suffisante pour observer les effets** : un modele trop petit (< 0.5B) montre des effets de regularisation rendant l'observation des techniques bruitee. 0.5B-1.5B est la zone Goldilocks pour observer **clairement** les effets de SFT/DPO/GRPO.
- **Licence permissive Qwen** : Apache 2.0, utilisable en cours sans friction.
- **Famille coherente** : meme tokenizer, meme architecture, ce qui permet de comparer techniques sans confondre effets de modele et effets de methode.
- **Variante Math-1.5B pour RLVR** : Qwen propose une variante pre-entrainee sur math, ce qui evite de devoir partir de zero pour observer un comportement RLVR concret.

Alternatives ecartees et raisons : Llama-3.2-1B (gated, friction d'inscription HF), Phi-3-mini (architecture custom mal supportee par TRL au moment de la serie), Gemma-2-2B (license restrictive sur usage commercial, complique pour les apprenants en formation pro).

Pour les apprenants disposant de plus de VRAM (RTX 4090 24Go, A100 40Go), la serie indique en encart les hyperparametres a modifier pour scaler a Qwen2.5-7B sans changer la structure pedagogique.

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

Serie complete : 6 notebooks, tous executes avec outputs reels.

Suivi : [Issue #1742](https://github.com/jsboige/CoursIA/issues/1742).

## FAQ

### OOM CUDA pendant GRPO ou DPO

Les notebooks PT-03 a PT-05 sont concus pour RTX 3070 (8 Go) avec Qwen2.5-0.5B, mais OOM reste possible si l'environnement n'est pas optimal. Strategies :

- Verifier que `bitsandbytes` est installe et que la quantization 4-bit est active (`load_in_4bit=True`).
- Reduire `per_device_train_batch_size` a 1 et augmenter `gradient_accumulation_steps` pour garder un batch effectif correct.
- Le parametre N (nombre de completions par prompt) dans GRPO est le principal consommateur VRAM : utiliser `N=4` ou `N=8` plutot que `N=16` sur GPU limite.
- Fermer tous les autres processus GPU avant l'entrainement (`nvidia-smi` pour verifier).

Si votre GPU a 4 Go ou moins, passer `LOAD_MODEL_AND_TRAIN=False` dans les notebooks pour executer en mode demo (chargement des outputs pre-calcules sans entrainement reel).

### Quelle serie faire en premier : FineTuning ou PostTraining ?

Les deux series sont complementaires :

- **FineTuning d'abord** si vous voulez rapidement fine-tuner un modele pour votre cas d'usage (LoRA, SFT pratique, DPO pratique). Approche "boite a outils".
- **PostTraining d'abord** si vous voulez comprendre la theorie derriere les techniques avant de les appliquer. Approche "fondamentaux".

Le parcours optimal est FineTuning (pratique) puis PostTraining (profondeur), mais l'inverse fonctionne aussi pour les profils theoriens.

### DPO vs GRPO : quand utiliser quoi ?

| Critere | DPO | GRPO |
|---------|-----|------|
| **Donnees requises** | Paires de preferences (choisi/rejete) | Prompts + fonction de reward |
| **Reward Model** | Non (implicitement elimine) | Non (baseline intra-groupe) |
| **Critic** | Non | Non |
| **VRAM** | Plus faible (1 modele) | Plus eleve (N completions en memoire) |
| **Taches cibles** | Preferences subjectives, style, ton | Math, code, taches verifiables |
| **Stabilite** | Bonne (BTL assumption) | Variable (sensible a N et a la reward) |
| **Data annotation** | Necessaire (preferences humaines) | Optionnelle (reward verifiable) |

En pratique : DPO pour l'alignement conversationnel, GRPO+RLVR pour le raisonnement mathematique et code.

### Les metriques d'evaluation ne s'amelorent pas apres training

Si SFT, DPO ou GRPO ne produisent pas d'amelioration mesurable sur GSM8K ou MMLU :

- Verifier que le dataset d'evaluation est bien separé du dataset d'entrainement (`seed=42` pour le split, pas de fuite).
- S'assurer que le nombre de steps d'entrainement est suffisant (minimum 100 steps pour observer un signal sur 0.5B).
- Un seul seed ne suffit pas : les resultats sont bruites. Utiliser au minimum 4 seeds (`{0, 1, 7, 42}`) et verifier que l'ecart est >= 2 sigma (cf regle multi-seed CoursIA).
- Le notebook PT-06 (`PT_06_eval_comparative.ipynb`) automatise cette comparaison avec verdict BEATS/NO BEATS/INCONCLUSIVE.

### ImportError avec trl, peft ou bitsandbytes

L'environnement `coursia-ml-training` doit contenir les dependances post-training :

```bash
conda activate coursia-ml-training
pip install --upgrade transformers trl peft accelerate datasets bitsandbytes

# Verifier
python -c "import trl; print(f'TRL {trl.__version__}')"
python -c "import bitsandbytes; print('bitsandbytes OK')"
```

Sur Windows, `bitsandbytes` peut necessiter CUDA 12.x. Si erreur DLL not found, verifier que `CUDA_HOME` pointe vers le bon toolkit et que `bitsandbytes` est a jour (`>= 0.45`).

### Peut-on reproduire Deepseek-R1 avec cette serie ?

Non directement, mais les briques conceptuelles sont les memes. Deepseek-R1 utilise GRPO + RLVR sur des modeles 671B (architecture MoE) avec une infrastructure de distribuee massive. Cette serie reproduit les memes techniques sur Qwen2.5-0.5B/1.5B pour rendre les concepts accessibles sur GPU 8 Go. Les formules de loss, les mecanismes de reward, et les strategies d'evaluation sont identiques — seul l'echelle change. PT-04 (GRPO) et PT-05 (RLVR) reproduisent fidelement le pipeline Deepseek-R1 en miniature.

## Licence

Voir la licence du repository principal.
