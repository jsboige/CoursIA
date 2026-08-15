# Détection de sophismes — état de l'art et cadrage de l'EPIC #10355

> Document de recherche — Phase 1 / livrable 1 de l'EPIC [#10355](https://github.com/jsboige/CoursIA/issues/10355) (détection de sophismes via Qwen3.5/3.6 FT + PT, gated by SAE analysis). Voir la sous-tâche opérationnelle [#10356](https://github.com/jsboige/CoursIA/issues/10356).
>
> Scope de ce document : **survey SOTA** (détection computationnelle de sophismes + argument mining) + cadrage de l'approche SAE-gated FT+PT. Les livrables 2 (paysage datasets), 3 (extraction Jessynoo) et 4 (inventaire SAE Qwen) font l'objet de PRs ultérieures. Toute affirmation chiffrée citée d'un papier est vérifiée soit par lecture firsthand (WebFetch sur la source primaire), soit par snippet de recherche avec URL primaire stable (ACL Anthology, Springer, ACM, arXiv).

## 1. Contexte et ambition

L'EPIC #10355 vise à détecter et classifier les sophismes (fallacies) dans des textes argumentatifs réels, en s'appuyant sur :

- **la taxonomie Argumentum** (`MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/data/argumentum_fallacies_taxonomy.csv`) comme grilles d'étiquettes ;
- **des modèles Qwen 3.5/3.6** équipés de **sparse autoencoders (SAE)**, afin que la décision de classification soit *interprétable* (les features SAE activées explicitent *pourquoi* un passage est jugé fallacieux) ;
- une distinction fine entre **fine-tuning (FT)** — mémoriser le motif « général → particulier » des traces de raisonnement — et **post-training (PT)** — apprendre à *utiliser* ce workflow plutôt qu'à le réciter.

La source de données principale est le corpus de la fractique pédagogique `r/fallacy` (contributeur pivot `u/Jessynoo`, dont le dump est exploité sous PII-anonymisation), croisé avec la base Argumentum (deck-2 « mises en situation » × 50+ sophismes).

### 1.1 La taxonomie Argumentum : une richesse hors-norme

Un constat firsthand ouvre le cadrage : la taxonomie Argumentum compte **1408 entrées de sophismes réparties en 8 familles** :

| Famille | Entrées |
|---|---|
| Influence | 420 |
| Tricherie | 394 |
| Insuffisance | 174 |
| Obstruction | 126 |
| Erreur mathématique | 102 |
| Erreur de raisonnement | 102 |
| Abus de langage | 89 |
| (Argument fallacieux, racine) | 1 |

Ce volume écrase les taxonomies académiques usuelles (13 à 23 catégories, §3). C'est à la fois la force du projet (granularité pédagogique fine, alignée à un jeu de cartes pédagogique réel) et son défi principal : les datasets étiquetés existants ne couvrent qu'une fraction de ces familles, et le mapping d'étiquettes (Argumentum ↔ académique) est un sous-produit de recherche à part entière (Phase 2, dataset builder).

## 2. Méthodologie du survey

Recensement par recherche sémantique (SearXNG) sur « computational logical fallacy detection », « argument mining dataset », complété par lecture primaire (WebFetch) des papiers fondateurs pour vérifier auteurs/année/venue/taille de taxonomie. Les papiers retenus le sont sur trois critères : (a) tâche de détection/classification de sophismes OU extraction d'arguments, (b) dataset public ou reproductible, (c) pertinence pour l'approche LM-based + interprétabilité.

## 3. État de l'art — détection computationnelle de sophismes

### 3.1 Papier fondateur — Jin et al. (2021), « Logical Fallacy Detection »

Jin, Lalwani, Vaidhya, Shen, Ding, Lyu, Sachan, Mihalcea, Schölkopf. *Logical Fallacy Detection.* Findings of EMNLP 2021. [arXiv:2202.13758](https://arxiv.org/abs/2202.13758) · [ACL Anthology](https://aclanthology.org/2022.findings-emnlp.532/).

- **Première** formulation de la classification de sophismes par deep learning.
- Introduit le dataset **Logic** (13 types de sophismes) et le challenge set **LogicClimate** (sophismes dans des affirmations sur le changement climatique).
- Établit le protocole canonique : classification multi-classes + challenge domaine-spécifique. LogicClimate reste le benchmark de référence pour la robustesse cross-domaine.

### 3.2 Benchmark de référence — MAFALDA (Helwe et al. 2023)

Helwe, Calamai, Paris, Clavel, Suchanek. *MAFALDA: A Benchmark and Comprehensive Study of Fallacy Detection and Classification.* 2023. [arXiv:2311.09761](https://ar5iv.labs.arxiv.org/html/2311.09761).

Vérifié firsthand. Taxonomie hiérarchique **à 3 niveaux** :

- **Niveau 0** — binaire (fallacieux / non-fallacieux) ;
- **Niveau 1** — 3 catégories aristotéliciennes : *Pathos* (appel à l'émotion), *Logos* (sophismes de logique), *Ethos* (crédibilité) ;
- **Niveau 2** — **23 sophismes fins** (Ad Hominem, Ad Populum, Appel à l'autorité, Pente glissante, Homme de paille, Fausse causalité, Faux dilemme, Généralisation hâtive, etc.).

Évaluation **zero-shot** d'une batterie de LLMs : GPT-3.5, Falcon (7B), LLaMA-2 / LLaMA-2 Chat (7B, 13B), Vicuna (7B, 13B), Mistral / Mistral Instruct (7B), WizardLM (7B, 13B), Zephyr (7B). MAFALDA fournit à la fois le dataset annoté et le cadre d'évaluation zero-shot que l'EPIC #10355 reprend (avec passage au *fine-tuné* + interprétabilité SAE).

### 3.3 LLMs et prompt-engineering (2024-2025)

- *Large Language Models Are Better Logical Fallacy Reasoners (with Prompt Formulation).* Findings of NAACL 2025. [ACL Anthology](https://aclanthology.org/2025.findings-naacl.384/). — Approche de formulation de prompt applicable en *supervisé (fine-tuné)* ET *non-supervisé (zero-shot)* : directement pertinent pour la distinction FT vs PT de l'EPIC.
- *Large Language Models for Logical Fallacy Detection.* Springer 2025. [link](https://link.springer.com/chapter/10.1007/978-981-96-8197-6_29). — Étude comparative des performances LLM par classe de sophisme.
- *Logical Fallacy Detection in Text: Leveraging LLMs (fine-tuned).* Springer 2024. [link](https://link.springer.com/chapter/10.1007/978-3-031-90341-0_4). — Classifieur à base de LLM *fine-tuné* sur LOGIC combiné à SNLI : démontre que le FT sur données synthétiques + d'inférence naturelle améliore la détection.
- *Evaluation of an LLM in Identifying Logical Fallacies.* ACM 2024. [DOI](https://dl.acm.org/doi/10.1145/3678884.3681867). — GPT-4 atteint 0,79 de justesse (0,90 en usage restreint excluant instances non-identifiées) sur un dataset étiqueté : référence pour le plafond « out-of-the-box » à battre.

## 4. État de l'art — argument mining (sources de données et tâches connexes)

La détection de sophismes se nourrit de l'argument mining (extraction de la structure argumentative), dont les datasets fournissent cadres et corpus.

- **IBM Project Debater** — Slonim et al., *Nature* (2021). Dataset des discours d'ouverture annotés : [`ibm-research/debate_speeches`](https://huggingface.co/datasets/ibm-research/debate_speeches). C'est la référence industrielle de l'argument mining à grande échelle.
- **IBM-Rank-30k** (Gretz et al. 2019). *A Large-scale Dataset for Argument Quality Ranking.* [arXiv:1911.11408](https://arxiv.org/pdf/1911.11408) — 30 497 arguments étiquetés en qualité *point-wise* (la plus grande ressource de qualité argumentative à sa sortie). Référence pour le scorng de qualité, distinct de mais complémentaire à la détection de sophisme.
- **AraucariaDB** (Reed et al., ARG-tech). [araucaria.arg.tech](http://araucaria.arg.tech/) — premier corpus mondial d'argumentation analysée, construit via l'outil Araucaria. Grille de diagrammes argumentatifs (Toulmin, premises/conclusion) réutilisable pour la Phase 2 (dataset builder).
- **ArgumenText** (IBM) — service d'extraction d'arguments, dont dérivent les datasets Arg-Search / Arg-GPT2 (`ibm-research/debate_speeches`).
- **Argument Mining relationnel par LLM** (2024). *Can Large Language Models perform Relation-based Argument Mining?* [arXiv:2402.11243](https://arxiv.org/pdf/2402.11243). — Démontre la viabilité des LLMs pour l'extraction de *relations* entre arguments : pertinent pour reconstruire le tissu argumentatif dans lequel un sophisme s'insère.
- **Catalogue de corpora** — [`shiwei-liu522/argumentation-mining-corpora`](https://github.com/shiwei-liu522/argumentation-mining-corpora) : inventaire maintenu (forums, éditoriaux, réseaux sociaux, essais étudiants) à consulter pour le livrable 2 (paysage datasets).

## 5. Discussion — implications pour l'EPIC #10355

### 5.1 La fausse équivalence « dataset académique → taxonomie Argumentum »

Les datasets ci-dessus couvrent **13 (Logic) à 23 (MAFALDA L2) types**. La taxonomie Argumentum en compte **1408 / 8 familles**. Aucun dataset existant n'est étiqueté dans la grille Argumentum. Conséquence :

- **Phase 2 (dataset builder)** devra soit (a) projeter les étiquettes Argumentum sur du texte non-annoté via un LLM oracle (coûteux, bruité), soit (b) s'appuyer sur le deck-2 Argumentum (mises en situation × 50+ sophismes) comme données faiblement supervisées, soit (c) restreindre le périmètre initial à un sous-ensemble de familles Argumentum bien couvertes par les datasets académiques (Influence/Tricherie ↔ Pathos/Ethos MAFALDA).
- Le mapping **Argumentum ↔ académique** est un livrable de recherche à part entière, à produire en Phase 1 (complément de ce survey) ou Phase 2.

### 5.2 Mémorisation vs généralisation — la distinction FT/PT

L'EPIC postule que **le fine-tuning mémorise** le motif « général → particulier » des traces de raisonnement (le modèle *reconnaît* le schéma), tandis que **le post-training apprend à l'utiliser** (le modèle *déroule* le schéma sur un cas nouveau). Cette distinction rejoint un fil de recherche actif : la détection de texte généré/fine-tuné et la robustesse fine-tuning vs zero-shot. MAFALDA (§3.2) montre que les LLMs *zero-shot* ont déjà une capacité non-négligeable ; le NAACL 2025 (§3.3) montre qu'une *formulation de prompt fine-tunée* surpasse le zero-shot. La question ouverte pour l'EPIC : un **SAE** entraîné sur le modèle fine-tuné révèle-t-il des features « motif général→particulier » activées *différemment* après PT ? C'est l'hypothèse testable au cœur de la Phase 5 (SAE analysis, strate 6 ICT).

### 5.3 Le SAE comme gate d'interprétabilité — cadrage (inventaire Qwen = livrable 4)

Le paysage SAE (sparse autoencoders pour interprétabilité des LM) s'est structuré autour de : le principe de décomposition *monosémantique* (features interprétables individuelles), l'écosystème open-source (SAELens et apparentés pour Gemma/Llama), et les travaux de l'école anthropique (Bricken et al. 2023, *Towards Monosemanticity*) ainsi que Cunningham et al. (*Sparse Autoencoders Find Highly Interpretable Features*). L'enjeu pour l'EPIC : **disposer d'un SAE pour Qwen 3.5/3.6 sur au moins 3 tailles** de modèle — faute de quoi le pivot SAE (gate de succès déclarée) n'est pas tenu. L'inventaire Qwen-spécifique est le **livrable 4** de la Phase 1 (PR séparé) ; si < 3 tailles disposent d'un SAE, escalade owner (cf. body #10356).

## 6. Conclusion et chaîne de phases

| Phase | Livrable | Statut après ce survey |
|---|---|---|
| 1 — Survey SOTA | ce document (≥ 8 papiers, 10 cités) | **livré (cette PR)** |
| 1 — Paysage datasets | ≥ 5 datasets testés en accès réel | à livrer |
| 1 — Extraction Jessynoo | notebook 03, PII-anonymisé | dump dispo, à livrer |
| 1 — Inventaire SAE Qwen | ≥ 3 tailles | gate de faisabilité, à livrer |
| 2 — Dataset builder | projection Argumentum sur corpus | Phase 2 |
| 3 — Fine-tuning (série FT) | mémorisation du motif général→particulier | Phase 3 |
| 4 — Post-training (série PT) | utilisation du workflow | Phase 4 |
| 5 — SAE analysis (ICT strate 6) | features « motif » FT vs PT | gate de succès, Phase 5 |

### Sources primaires

- Jin et al. 2021, *Logical Fallacy Detection*, Findings EMNLP — [arXiv:2202.13758](https://arxiv.org/abs/2202.13758)
- Helwe et al. 2023, *MAFALDA* — [arXiv:2311.09761](https://ar5iv.labs.arxiv.org/html/2311.09761)
- *LLMs Are Better Logical Fallacy Reasoners*, Findings NAACL 2025 — [ACL Anthology](https://aclanthology.org/2025.findings-naacl.384/)
- *Large Language Models for Logical Fallacy Detection*, Springer 2025 — [link](https://link.springer.com/chapter/10.1007/978-981-96-8197-6_29)
- *Logical Fallacy Detection in Text (fine-tuned LLM)*, Springer 2024 — [link](https://link.springer.com/chapter/10.1007/978-3-031-90341-0_4)
- *Evaluation of an LLM in Identifying Logical Fallacies*, ACM 2024 — [DOI](https://dl.acm.org/doi/10.1145/3678884.3681867)
- IBM Project Debater — [`ibm-research/debate_speeches`](https://huggingface.co/datasets/ibm-research/debate_speeches)
- Gretz et al. 2019, *IBM-Rank-30k* — [arXiv:1911.11408](https://arxiv.org/pdf/1911.11408)
- AraucariaDB — [araucaria.arg.tech](http://araucaria.arg.tech/)
- *Relation-based Argument Mining with LLMs*, 2024 — [arXiv:2402.11243](https://arxiv.org/pdf/2402.11243)
- Catalogue corpora — [`shiwei-liu522/argumentation-mining-corpora`](https://github.com/shiwei-liu522/argumentation-mining-corpora)
