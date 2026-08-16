# Périmètre PRODUCTION — dérivation mécanique v1

> **Epic [#11259](https://github.com/jsboige/CoursIA/issues/11259) — tâches T1 + T1b.**
> Candidats à la signature `PRODUCTION`, dérivés du calendrier d'enseignement
> ([teaching-context.md](../reference/teaching-context.md), cycle 2026→2027).
> **La décision se prend par série**, dans le tableau « La passe par série » ci-dessous —
> une réponse par ligne, rien d'autre à faire. Le détail par notebook (strate A)
> reste en dessous comme référence consultable ; la strate B n'est pas soumise à
> décision (non tranché = BETA, verdict correct), la strate C reste exclue sauf
> demande explicite.

## Critères mécaniques appliqués

| Règle | Portée |
|-------|--------|
| Séries in-scope | 4 écoles : EPF GenAI (4 modalités), ECE/partner (QuantConnect Python), EPITA-PrCon (Search Part1+Part2), EPITA-IS (6 séries SymbolicAI) |
| Exclus — jumeaux | un seul notebook par concept : version principale (sans suffixe plateforme, sinon Python) ; `-Csharp` duplicata exclu |
| Exclus — variantes | numéros lettres (`12b`, `23b`, `11b-Deep-PartN`), suffixes `_agent` |
| Exclus — technique | `*_en.ipynb` (traduction), `*_output*`, `_archive/`, `_research/`, `temp/`, `_probes/`, `RDF.Net-Legacy/` |
| Exclus — setup | notebooks d'environnement/`Setup` (réintégrables : ils s'exécutent, ne s'enseignent pas) |
| Strate A (proposé) | GenAI **Foundation** des 4 modalités + Texte 1-8 · QC-Py **02-21** + série Cloud · Search **Part1+Part2** · SymbolicAI **têtes** (numéros ≤3 + fondateurs) |
| Strate B (hors proposition v1) | GenAI Advanced/Applications + Texte 9-21 · QC-Py 22-41 (ML avancé) + `research_*` · le reste des séries SymbolicAI — BETA par défaut, intégration sur demande explicite |

## Ordre de passage (d'après l'Epic)

1. **Prochains cours au calendrier** — rentrée septembre 2026 : QC League (ex-ECE) et nouvelle promo EPF → séries QC-Py cœur et GenAI Foundation en tête.
2. **Référencés par les sujets de projet** — EPITA-IS (TP = 1 série au choix) → têtes SymbolicAI.
3. **Têtes de série** — le notebook qu'un étudiant ouvre en premier dans chaque série.
4. Le reste du périmètre (strate B arbitrée).

## La passe par série — la seule surface de décision

Une ligne par série, dans l'ordre de passage. La question, une seule fois par ligne :
**cette série entière entre-t-elle dans le périmètre signé ?**
Répondre « oui », « non », ou « oui sauf … » (citer le notebook). La colonne *Tête de série*
nomme le notebook qu'un étudiant ouvre en premier dans la série — le point d'appui du jugement.
Le détail par notebook suit en strate A ci-dessous : consultation, plus décision.

| Série | Cours | Tête de série | N proposés | Verdict |
|-------|-------|---------------|------------|---------|
| QuantConnect Python | ECE IA Finance Ing4 + Partner Algo Trading | `QC-Py-02-Platform-Fundamentals.ipynb` | 35 | |
| GenAI Image — Foundation | EPF GenAI Bachelor 3A | `01-1-OpenAI-DALL-E-3.ipynb` | 5 | |
| GenAI Audio — Foundation | EPF GenAI Bachelor 3A | `01-1-OpenAI-TTS-Intro.ipynb` | 5 | |
| GenAI Video — Foundation | EPF GenAI Bachelor 3A | `01-1-Video-Operations-Basics.ipynb` | 5 | |
| GenAI Texte (1-8) | EPF GenAI Bachelor 3A | `1_OpenAI_Intro.ipynb` | 8 | |
| Search — Part 1 Foundations | EPITA Programmation par Contraintes | `Search-1-StateSpace.ipynb` | 13 | |
| Search — Part 2 CSP | EPITA Programmation par Contraintes | `CSP-1-Fundamentals.ipynb` | 9 | |
| Argument Analysis | EPITA IA Symbolique | `Argument_Analysis_Toulmin_Model.ipynb` | 4 | |
| Tweety | EPITA IA Symbolique | `Tweety-2-Basic-Logics.ipynb` | 6 | |
| Lean | EPITA IA Symbolique | `Lean-2-Dependent-Types.ipynb` | 2 | |
| Semantic Web | EPITA IA Symbolique | `SW-2-CSharp-RDFBasics.ipynb` | 2 | |
| Planners (01-02) | EPITA IA Symbolique | `Planners-1-Introduction.ipynb` | 3 | |
| SmartContracts (00-01) | EPITA IA Symbolique | `SC-0-Cypherpunk-Origins.ipynb` | 2 | |

## Strate A — proposés pour signature (99)

*Référence consultable — la décision se prend par série dans le tableau ci-dessus. Un dossier de revue sera préparé pour chaque entrée dans l'ordre de passage.*

### EPF — GenAI Bachelor 3A (MSBNS3IN03) (23)

<!-- MyIA.AI.Notebooks/GenAI/Image/01-Foundation -->
- [ ] `MyIA.AI.Notebooks/GenAI/Image/01-Foundation/01-1-OpenAI-DALL-E-3.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Image/01-Foundation/01-2-GPT-5-Image-Generation.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Image/01-Foundation/01-3-Basic-Image-Operations.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Image/01-Foundation/01-4-Forge-SD-XL-Turbo.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Image/01-Foundation/01-5-Qwen-Image-Edit.ipynb`
<!-- MyIA.AI.Notebooks/GenAI/Audio/01-Foundation -->
- [ ] `MyIA.AI.Notebooks/GenAI/Audio/01-Foundation/01-1-OpenAI-TTS-Intro.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Audio/01-Foundation/01-2-OpenAI-Whisper-STT.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Audio/01-Foundation/01-3-Basic-Audio-Operations.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Audio/01-Foundation/01-4-Whisper-Local.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Audio/01-Foundation/01-5-Kokoro-TTS-Local.ipynb`
<!-- MyIA.AI.Notebooks/GenAI/Video/01-Foundation -->
- [ ] `MyIA.AI.Notebooks/GenAI/Video/01-Foundation/01-1-Video-Operations-Basics.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Video/01-Foundation/01-2-GPT-5-Video-Understanding.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Video/01-Foundation/01-3-Qwen-VL-Video-Analysis.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Video/01-Foundation/01-4-Video-Enhancement-ESRGAN.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Video/01-Foundation/01-5-AnimateDiff-Introduction.ipynb`
<!-- MyIA.AI.Notebooks/GenAI/Texte -->
- [ ] `MyIA.AI.Notebooks/GenAI/Texte/1_OpenAI_Intro.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Texte/2_PromptEngineering.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Texte/3_Structured_Outputs.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Texte/4_Function_Calling.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Texte/5_RAG_Modern.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Texte/6_PDF_Web_Search.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Texte/7_Code_Interpreter.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Texte/8_Reasoning_Models.ipynb`

### ECE IA Finance Ing4 + Partner Algo Trading QuantConnect (35)

<!-- MyIA.AI.Notebooks/QuantConnect/Python -->
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-01-FinBERT-Sentiment.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-01-RiskParity-Composite.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-02-Platform-Fundamentals.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-02-ML-Classification.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-02-SectorRotation-Momentum.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-03-Data-Management.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-03-DualMomentum.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-03-Risk-Parity.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-04-Research-Workflow.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-04-MeanReversion.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-04-RL-DQN-Trading.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-05-Universe-Selection.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-05-MLP-Forecasting.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-05-RegimeSwitching.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-06-Options-Trading.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-06-PCA-StatArb.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-06-VolTargeting.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-07-Futures-Forex.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-07-TemporalCNN.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-08-Multi-Asset-Strategies.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-08-ValueFactor-ZScore.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-09-Order-Types.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-09-OptionWheel.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-10-Risk-Portfolio-Management.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-11-Technical-Indicators.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-12-Backtesting-Analysis.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-13-Alpha-Models.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-14-Portfolio-Construction-Execution.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-15-Parameter-Optimization.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-16-Alternative-Data.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-17-Sentiment-Analysis.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-18-ML-Features-Engineering.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-19-ML-Supervised-Classification.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-20-ML-Regression-Prediction.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-21-Portfolio-Optimization-ML.ipynb`

### EPITA — Programmation par Contraintes (22)

<!-- MyIA.AI.Notebooks/Search/Part1-Foundations -->
- [ ] `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-1-StateSpace.ipynb`
- [ ] `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-2-Uninformed.ipynb`
- [ ] `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-3-Informed.ipynb`
- [ ] `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-4-LocalSearch.ipynb`
- [ ] `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-5-GeneticAlgorithms.ipynb`
- [ ] `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-6-AdversarialSearch.ipynb`
- [ ] `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-7-MCTS-And-Beyond.ipynb`
- [ ] `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-8-DancingLinks.ipynb`
- [ ] `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-9-LinearProgramming.ipynb`
- [ ] `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-10-SymbolicAutomata.ipynb`
- [ ] `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-11-Metaheuristics.ipynb`
- [ ] `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-15-NetworkX.ipynb`
- [ ] `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-16-QuikGraph.ipynb`
<!-- MyIA.AI.Notebooks/Search/Part2-CSP -->
- [ ] `MyIA.AI.Notebooks/Search/Part2-CSP/CSP-1-Fundamentals.ipynb`
- [ ] `MyIA.AI.Notebooks/Search/Part2-CSP/CSP-2-Consistency.ipynb`
- [ ] `MyIA.AI.Notebooks/Search/Part2-CSP/CSP-3-Advanced.ipynb`
- [ ] `MyIA.AI.Notebooks/Search/Part2-CSP/CSP-4-Scheduling.ipynb`
- [ ] `MyIA.AI.Notebooks/Search/Part2-CSP/CSP-5-Optimization.ipynb`
- [ ] `MyIA.AI.Notebooks/Search/Part2-CSP/CSP-6-Hybridization.ipynb`
- [ ] `MyIA.AI.Notebooks/Search/Part2-CSP/CSP-7-Soft.ipynb`
- [ ] `MyIA.AI.Notebooks/Search/Part2-CSP/CSP-8-Temporal.ipynb`
- [ ] `MyIA.AI.Notebooks/Search/Part2-CSP/CSP-9-Distributed.ipynb`

### EPITA — IA Symbolique (19)

<!-- MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis -->
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Agentic-0-init.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Agentic-1-informal.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Agentic-2-formal.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Toulmin_Model.ipynb`
<!-- MyIA.AI.Notebooks/SymbolicAI/Tweety -->
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-2-Basic-Logics.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-3-Advanced-Logics.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-3-Conditional-Logics-Csharp.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-3-Dung-Csharp.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-3-ModalLogic-Csharp.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-3-QBF-Csharp.ipynb`
<!-- MyIA.AI.Notebooks/SymbolicAI/Lean -->
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-2-Dependent-Types.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-3-Propositions-Proofs.ipynb`
<!-- MyIA.AI.Notebooks/SymbolicAI/SemanticWeb -->
- [ ] `MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/SW-2-CSharp-RDFBasics.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/SW-3-CSharp-GraphOperations.ipynb`
<!-- MyIA.AI.Notebooks/SymbolicAI/Planners -->
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Planners/01-Foundation/Planners-1-Introduction.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Planners/01-Foundation/Planners-2-PDDL-Basics.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Planners/01-Foundation/Planners-3-State-Space.ipynb`
<!-- MyIA.AI.Notebooks/SymbolicAI/SmartContracts -->
- [ ] `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/00-Foundations/SC-0-Cypherpunk-Origins.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/01-Solidity-Foundation/SC-3-Solidity-Basics.ipynb`

## Strate B — hors proposition v1 (112)

*Non soumise à la passe de validation. Statut BETA par défaut — verdict correct, pas une dette.
Une entrée n'entre dans le périmètre PRODUCTION que sur demande explicite (mention sur
l'Epic) ; un dossier de revue est alors préparé (T2).*

### EPF — GenAI Bachelor 3A (MSBNS3IN03) (34)

<!-- MyIA.AI.Notebooks/GenAI/Image/02-Advanced -->
- [ ] `MyIA.AI.Notebooks/GenAI/Image/02-Advanced/02-1-Qwen-Image-Edit-2509.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Image/02-Advanced/02-2-FLUX-1-Advanced-Generation.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Image/02-Advanced/02-3-Stable-Diffusion-3-5.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Image/02-Advanced/02-4-Z-Image-Lumina2.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Image/02-Advanced/02-5-Bonsai-Image-Ternary.ipynb`
<!-- MyIA.AI.Notebooks/GenAI/Audio/02-Advanced -->
- [ ] `MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-1-Chatterbox-TTS.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-2-XTTS-Voice-Cloning.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-3-MusicGen-Generation.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-4-Demucs-Source-Separation.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-5-Multi-Model-TTS-Gateway.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-6-MIDI-Generation.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-7-Song-Generation.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-8-Expressive-TTS.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-9-AceStep-Music-Generation.ipynb`
<!-- MyIA.AI.Notebooks/GenAI/Video/02-Advanced -->
- [ ] `MyIA.AI.Notebooks/GenAI/Video/02-Advanced/02-1-HunyuanVideo-Generation.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Video/02-Advanced/02-2-LTX-Video-Lightweight.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Video/02-Advanced/02-3-Wan-Video-Generation.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Video/02-Advanced/02-4-SVD-Image-to-Video.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Video/02-Advanced/02-5-LTX2-Audiovisual.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Video/02-Advanced/02-6-MiniMax-H3-Architecture-Licensing.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Video/02-Advanced/02-7-CogVideoX-Text-to-Video.ipynb`
<!-- MyIA.AI.Notebooks/GenAI/Texte -->
- [ ] `MyIA.AI.Notebooks/GenAI/Texte/9_Production_Patterns.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Texte/10_LocalLlama.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Texte/11_Quantization.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Texte/12_Test_Time_Scaling.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Texte/13_Agentic_Orchestration.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Texte/14_Persistent_Memory.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Texte/15_Tree_of_Thoughts_Search.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Texte/16_Scaling_Test_Time_Compute.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Texte/17_Native_Reasoning_vs_Scaling.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Texte/18_Semantic_Kernel_Plugins.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Texte/19_OWUI_Orchestration.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Texte/20_OWUI_Native_API.ipynb`
- [ ] `MyIA.AI.Notebooks/GenAI/Texte/21_LoRA_FineTuning.ipynb`

### ECE IA Finance Ing4 + Partner Algo Trading QuantConnect (18)

<!-- MyIA.AI.Notebooks/QuantConnect/Python -->
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-22-Deep-Learning-LSTM.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-23-Attention-Transformers.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-24-Autoencoders-Anomaly.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-25-Reinforcement-Learning.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-26-LLM-Trading-Signals.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-27-Production-Deployment.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-28-Market-Regime-Detection.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-30-LSTM-Training.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-31-Transformer-Training.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-32-RL-DQN-Trading.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-33-RL-PPO-Trading.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-34-RL-SAC-A2C-Trading.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-35-RL-Portfolio-Construction.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-40-PaperTrading-Binance.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-41-PaperTrading-IBKR.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Dataset-Workflow.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/research/research_classification.ipynb`
- [ ] `MyIA.AI.Notebooks/QuantConnect/Python/research/research_lstm.ipynb`

### EPITA — IA Symbolique (60)

<!-- MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis -->
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Agentic-3-orchestration.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Agentic-4-capstone.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Agentic-5-jtms.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_ArgumentProfile.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Argumentum_Cards.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Dung_AF_Semantics.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Executor.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Formal_Richness_Matrix.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Multi_Backend_Routing.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Ontology_AIF.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Ontology_CrossLinks.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Ontology_Virtues.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Ranking_Semantics.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Restitution_3_Actes.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_UI_configuration.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Value_Based_AF.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/groupe-I2-contre-arguments-aspic/I2_Contre_arguments_ASPIC.ipynb`
<!-- MyIA.AI.Notebooks/SymbolicAI/Tweety -->
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-4-Aspic-Csharp.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-4-Belief-Revision.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-5-Abstract-Argumentation.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-6-Structured-Argumentation.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-8-Agent-Dialogues.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-9-Preferences.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-10-MLN.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-11-Causal.ipynb`
<!-- MyIA.AI.Notebooks/SymbolicAI/Lean -->
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-4-Quantifiers.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-5-Tactics.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-6-Mathlib-Essentials.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-7-LLM-Integration.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-8-Agentic-Proving.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-9-SK-Multi-Agents.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-10-LeanDojo.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-11-TorchLean.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-12-Sensitivity-Theorem.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-13-Kochen-Specker.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-14-Finiteness-Derivatives.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-15-Grothendieck-Tribute.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-17-Knots-a-Conway-and-Proofs.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-17-Knots-b-Invariants-Companion.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-18-Search-AStar-Optimality.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-19-Sendov-Complex-Analysis.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-20-Analysis-I-Tao-Workflow.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-21-PFR-Entropy-Method.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-22-MIMO-Detection-Flips.ipynb`
<!-- MyIA.AI.Notebooks/SymbolicAI/SemanticWeb -->
- [ ] `MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/SW-4-CSharp-SPARQL.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/SW-5-CSharp-LinkedData.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/SW-6-CSharp-RDFS.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/SW-7-CSharp-OWL.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/SW-8-Python-SHACL.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/SW-9-Python-JSONLD.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/SW-10-Python-RDFStar.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/SW-11-Python-KnowledgeGraphs.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/SW-12-Python-GraphRAG.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/SW-13-Python-Reasoners.ipynb`
<!-- MyIA.AI.Notebooks/SymbolicAI/Planners -->
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Planners/02-Classical/Planners-4-Fast-Downward.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Planners/02-Classical/Planners-5-Heuristics.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/Planners/02-Classical/Planners-6-Domains.ipynb`
<!-- MyIA.AI.Notebooks/SymbolicAI/SmartContracts -->
- [ ] `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/01-Solidity-Foundation/SC-4-Functions-State.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/01-Solidity-Foundation/SC-5-Inheritance.ipynb`
- [ ] `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/01-Solidity-Foundation/SC-6-Errors-Events.ipynb`

## Séries hors périmètre — justification en une ligne

Chaque série non recensée ci-dessus, et pourquoi (contestable sur l'Epic sans rouvrir le dossier) :

| Série | Pourquoi hors périmètre v1 |
|-------|----------------------------|
| `ML/` (ML.NET) | cursus .NET non rattaché aux 4 écoles in-scope ; le ML enseigné passe par QC-Py (ECE) et GenAI (EPF) |
| `Search/Part3-Advanced/`, `Search/Part4-Metaheuristics/` | au-delà du programme PrCon — Part1+Part2 couvrent le cours référencé |
| `Search/Applications/`, `Search/MetaGeneticSharp/` | applications dérivées non citées par le calendrier des cours |
| `Sudoku/` | série .NET autonome, non rattachée à un cours du calendrier |
| `Probas/` (Infer.NET) | idem — non rattachée à une des 4 écoles |
| `GameTheory/` | les preuves Lean associées sont du code (i18n #4980), non des notebooks à signer ; les `.ipynb` ne sont pas cités nommément par le calendrier |
| `IIT/` (PyPhi) | non rattaché à un cours du calendrier |
| `RL/`, `CaseStudies/`, `FallacyDetection/`, `cross-series/` | hors des 4 écoles in-scope |
| `QuantConnect/` hors `Python/` (C#, partner-course, ML-Training-Pipeline, projects, kelly_lean) | le cours ECE/partner suit la série Python ; le reste est outillage/projets, non enseigné en cours |
| `SymbolicAI/Planners/03-Advanced/`, `04-NeuroSymbolic/` | au-delà des 2 sous-séries scoping EPITA-IS (TP = tête de série) |
| `SymbolicAI/SmartContracts/02-*/` à `06-*/` | idem — scoping EPITA-IS limité à `00-Foundations` + `01-Solidity-Foundation` |
| `SymbolicAI/Z3.Linq/` | fork externe non tracké (submodule) |

## Strate C — exclus mécaniques (81)

Non candidats par règle (aucune action attendue ; réintégration = demande explicite
sur l'Epic). Comptes par catégorie :

- `EXCL-JUMEAU` : 42
- `EXCL-VARIANTE` : 33
- `SETUP` : 6

---

*Dérivé mécaniquement depuis le disque (worktree frais `origin/main`) le 2026-08-16.
Source du calendrier : [docs/reference/teaching-context.md](../reference/teaching-context.md) — à jour 2026-08-08.
La validation en une passe fige la strate A ; les ajustements ultérieurs passent par l'Epic.*
