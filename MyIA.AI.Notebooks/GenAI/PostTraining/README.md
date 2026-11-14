# PostTraining — apprendre des démonstrations, des préférences et des récompenses

[↑ GenAI](../README.md) · [FineTuning](../FineTuning/README.md)

<!-- CATALOG-STATUS
series: GenAI-PostTraining
pedagogical_count: 23
breakdown: PostTraining=23
maturity: BETA=17, ALPHA=5, DRAFT=1
-->

Comment adapter un modèle de langage préentraîné à une tâche, et comment savoir si cette adaptation l'améliore ? Ce parcours relie supervision, optimisation de préférences, apprentissage par récompense et vérification. Les expériences à petite échelle rendent les mécanismes inspectables ; les carnets sur modèles de langage montrent leurs conditions d'exécution et les difficultés d'évaluation.

Le point d'entrée suppose Python, les bases de PyTorch, la rétropropagation et l’entropie croisée. Le [parcours FineTuning](../FineTuning/) apporte une entrée pratique complémentaire. Ici, l'accent porte sur le signal d'apprentissage, les avantages utilisés pour mettre à jour une politique et les preuves nécessaires avant d'annoncer un gain.

## Comment lire ce README — découverte

Le principe [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) distingue les paliers principaux de leurs variantes.

- **Vous découvrez** : suivez les numéros nus, en choisissant les étapes CPU ou GPU selon votre environnement.
- **Vous creusez un palier** : les variantes 11a–11d et 15b–15c sont regroupées sous « Approfondissements ». Elles se lisent après les paliers dont elles reprennent les mécanismes.
- **Vous cherchez des prolongements** : consultez les limites des résultats, les liens avec RL et ICT, puis les références.

L'ajustement supervisé (**SFT**) apprend à reproduire des réponses choisies ; l'optimisation directe des préférences (**DPO**) exploite des paires de réponses préférées et rejetées. L'optimisation relative à un groupe (**GRPO**) construit un avantage par comparaison entre les réponses produites, tandis que l'apprentissage par renforcement à récompense vérifiable (**RLVR**) utilise un vérificateur pour calculer la récompense. Ces choix répondent à des données et des objectifs différents : disposer d'une récompense calculable ne garantit ni qu'elle mesure correctement la tâche, ni qu'elle fournisse un signal d'apprentissage suffisant.

## Parcours principal — lecture guidée et prérequis

Les variantes du palier 11 sont présentées sous [Approfondissements](#autour-de-11--modèles-de-langage-et-répétition-des-expériences) : il n'existe pas de fichier PT-11 sans lettre, d'où le passage de 10 à 12 dans la table. Les prérequis indiquent la profondeur de lecture ; les expériences sur modèles de langage et les interventions causales demandent un bagage avancé.

| # | Notebook | Ce qu'on y apprend | Public et prérequis | Pour approfondir |
|---|---|---|---|---|
| 01 | [Introduction au post-training](PT_01_intro_post_training.ipynb) | Choisir un signal de supervision et lire une estimation de coût ou de mémoire. | Entrée du parcours ; CPU. | Arbre de décision et hypothèses des estimations. |
| 02 | [Référence SFT](PT_02_sft_baseline.ipynb) | Préparer données et template, construire la loss supervisée et entraîner un adaptateur LoRA. | PyTorch et Transformers ; entraînement GPU optionnel. | Qualité des données, rang LoRA, contrôle du run. |
| 03 | [Optimisation directe de préférences](PT_03_dpo_direct_preference.ipynb) | Relier Bradley–Terry, modèle de référence et loss DPO ; évaluer des paires choisies/rejetées. | Après 02 ; GPU pour le run. | Sensibilité à beta et séparation des données. |
| 04 | [GRPO et raisonnement](PT_04_grpo_deepseek_r1.ipynb) | Construire avantages de groupe, clipping et pénalité KL, puis un dispositif d'évaluation. | Après 02–03 ; tests CPU, entraînement conditionnel GPU. | Palier 08, [variantes 11](#autour-de-11--modèles-de-langage-et-répétition-des-expériences) et palier 13. |
| 05 | [Récompenses vérifiables](PT_05_rlvr_verifiable_rewards.ipynb) | Extraire une réponse, la confronter à la cible et distinguer exactitude et crédit partiel. | Après 04 ; SymPy, entraînement conditionnel GPU. | Limites du parseur et qualité du vérificateur. |
| 06 | [Comparaison des méthodes](PT_06_eval_comparative.ipynb) | Organiser un choix de méthode et un protocole comparatif à partir de scénarios de coût. | Après 02–05 ; CPU. | Les valeurs GSM8K de cette synthèse sont estimatives. |
| 07 | [Détecter le détournement de récompense](PT_07_rewardspy_reward_hacking.ipynb) | Instrumenter une récompense, lire un journal et repérer des comportements de Goodhart. | Notion de récompense ; `rewardspy`. | Trajectoire synthétique et analyse hors ligne. |
| 08 | [GRPO écrit à la main](PT_08_grpo_from_scratch_toy_env.ipynb) | Comparer REINFORCE, PPO et GRPO sur une tâche vérifiée par Z3. | PyTorch et probabilités ; CPU. | Taille du groupe et définition de la récompense. |
| 09 | [Baseline leave-one-out](PT_09_rloo_from_scratch_toy_env.ipynb) | Comparer RLOO, REINFORCE et GRPO, puis discuter biais et variance. | Après 08 ; CPU. | Sensibilité au groupe et aux graines. |
| 10 | [Modèle de valeur et GAE](PT_10_gae_from_scratch_toy_env.ipynb) | Construire un modèle de valeur (*critic*) qui estime le retour attendu, puis un avantage ; comprendre le rôle de lambda. | Après 08–09 ; CPU. | Le palier 12 traite le crédit réellement différé. |
| 12 | [Crédit différé multi-étapes](PT_12_multistep_delayed_credit.ipynb) | Construire une récompense terminale causale et mesurer l'effet de GAE sur un horizon étendu. | Après 10 ; CPU. | Ablation du façonnage de récompense et variation de l'horizon. |
| 13 | [Corrections DAPO et Dr.GRPO](PT_13_dapo_drgrpo_corrections.ipynb) | Isoler biais de longueur, normalisation par l'écart-type et clipping asymétrique. | Après 08 ; gradients PyTorch, CPU. | Distinguer effet sur le gradient et gain comportemental. |
| 14 | [Thermodynamique de l'entraînement](PT_14_neural_thermodynamic_laws.ipynb) | Examiner des relations entre taux d'apprentissage, fluctuations et relaxation sur des modèles contrôlés. | Optimisation et statistiques ; CPU. | Résolution de la mesure et limites du mini-GPT. |
| 15 | [Contrôle et interprétabilité](PT_15_controle_interpretabilite.ipynb) | Extraire une direction du refus, intervenir sur les activations et comparer retrait d'une composante et ajout dirigé (*steering*) aux activations. | Transformers et interception des activations (*hooks*) ; GPU pour les expériences. | [15b — SAE](PT_15b_geometrie_features_sae.ipynb), [15c — crosscoder](PT_15c_crosscoder_distillation.ipynb). |
| 16 | [Vérification formelle du code généré](PT_16_vericoding_formal_verification.ipynb) | Boucler spécification, génération, vérification et réparation ; éprouver la spécification elle-même. | Ollama, Dafny et Lean. | Gardes anti-contournement et spécifications incomplètes. |
| 17 | [Récompenses propres et calibration](PT_17_laya_proper_rewards_toy.ipynb) | Comparer règles de score, calibration et optimisation directe ou par perturbation. | Probabilités et gradients ; CPU. | Comparer calibration et exactitude prédictive. |
| 18 | [Ablation de distillation](PT_18_laya_ablation_distillation.ipynb) | Analyser des agrégats de distillation et éprouver un gain avec des comparaisons statistiques. | Après 17 ; analyse CPU de mesures enregistrées. | La grille d'entraînement vit dans les scripts associés. |

### Du signal d'apprentissage à la preuve d'un gain

Les premières étapes comparent des façons de dire au modèle ce qu'on attend de lui. Une démonstration fournit une réponse cible ; une préférence ordonne des réponses ; un vérificateur donne un score selon une règle. Les bancs 08–10 rendent ensuite visibles les calculs qui transforment ces signaux en mise à jour des paramètres. RLOO (*REINFORCE Leave-One-Out*) soustrait aux récompenses une référence calculée sur les autres réponses du groupe ; GAE (*Generalized Advantage Estimation*, estimation généralisée de l'avantage) combine des estimations pour répartir le crédit dans le temps.

Le passage de 10 à 12 illustre pourquoi le problème d'essai compte : sur un horizon immédiat, le paramètre lambda de GAE ne peut montrer son rôle dans le crédit différé. Le carnet 12 construit précisément un environnement où les actions précédentes affectent une récompense ultérieure. De même, une modification du gradient en 13 peut être réelle sans produire une différence de réussite sur un banc trop facile.

Les derniers paliers changent l'objet du contrôle : comportement récompensé, représentations internes, correction d'un programme ou calibration d'une distribution. Ils apprennent à choisir une observation adaptée à la conclusion recherchée. Une baisse de perte, une sortie acceptée par un vérificateur et une amélioration hors échantillon sont des résultats distincts.

### Comprendre les choix de méthode — Licence

En SFT, la perte d'entropie croisée augmente la vraisemblance des réponses de démonstration conditionnellement aux prompts. Le choix des données détermine donc ce que le modèle apprend à imiter : format, contenu, refus ou ton. L'objectif d'entraînement ne suffit pas à établir la qualité de ces comportements sur d'autres entrées.

DPO utilise des paires de préférences et un modèle de référence. Sa dérivation relie une récompense implicite au logarithme du rapport entre politique entraînée et politique de référence, avec un coefficient `beta`. Sous le modèle de préférences de Bradley–Terry, on obtient ainsi une perte sur les paires sans entraîner séparément un modèle de récompense. La qualité des préférences et le choix de la référence restent déterminants ; DPO n'est pas un SFT sur les seules réponses préférées.

GRPO remplace l'estimation d'avantage par un modèle de valeur par une comparaison au sein du groupe de réponses. Agrandir ce groupe peut changer la qualité du signal, mais augmente aussi le coût des générations. Si toutes les réponses reçoivent la même récompense, le groupe ne permet pas de les départager. RLVR désigne, lui, la provenance du score : un calcul ou un vérificateur. Il peut donc être combiné à GRPO. La fiabilité du score dépend de l'extraction de réponse, des tests ou de la spécification effectivement vérifiée.

GAE utilise les erreurs de différence temporelle
$\delta_t = r_t + \gamma V(s_{t+1}) - V(s_t)$
et les combine en
$A_t = \sum_{l=0}^{T-t-1}(\gamma\lambda)^l\delta_{t+l}$.
Le modèle de valeur $V$ estime le retour attendu ; $\gamma$ actualise les récompenses et $\lambda$ règle la profondeur de la combinaison. Faire davantage appel à $V$ peut réduire la variance, mais transmet aussi son erreur d'estimation. Les carnets 10 et 12 donnent des contextes différents pour examiner ce compromis.

### Choisir entre DPO et GRPO

| Critère | DPO | GRPO |
|---|---|---|
| Signal | Paires de réponses choisies et rejetées | Prompts, réponses groupées et fonction de récompense |
| Modèles auxiliaires | Référence pour la perte ; pas de modèle de récompense séparé | Comparaison au sein du groupe ; pas de modèle de valeur séparé |
| Usages | Préférences de style ou de conversation | Raisonnement avec récompense calculable, par exemple mathématiques ou code |
| Coût et limites | Dépend de la qualité des préférences et de la référence | Générations multiples coûteuses ; signal sensible à la taille du groupe et à la récompense |

Ces méthodes peuvent se compléter : choisir selon les données disponibles et la fiabilité du signal, puis évaluer sur des données distinctes.

### Idées reçues à éprouver

- **« Plus de réponses par groupe améliore toujours GRPO »** : un groupe plus grand coûte davantage et ne garantit pas un meilleur signal ; si toutes les récompenses sont identiques, il ne départage pas les réponses.
- **« LoRA implique toujours une qualité inférieure »** : sa restriction des paramètres entraînés économise de la mémoire ; le compromis de qualité dépend du modèle, de la tâche et du budget, et doit être mesuré.
- **« RLVR remplace toutes les autres méthodes »** : il faut un vérificateur fiable ; les préférences subjectives peuvent appeler un autre signal.
- **« Le post-entraînement supprime les hallucinations »** : une amélioration des réponses ou des refus ne garantit pas la factualité ; il faut l'évaluer sur des exemples distincts.

## Approfondissements — Recherche et prérequis

### Autour de 11 — modèles de langage et répétition des expériences

| Variante | Apport | Prérequis et limite à lire |
|---|---|---|
| [11a — Qwen et Z3](PT_11a_grpo_qwen35_rlvr.ipynb) | Relier QLoRA, GRPO, vérificateur de contraintes et instrumentation de récompense pendant un entraînement. | Paliers 04–08 ; GPU. Le fonctionnement du mécanisme n'établit pas à lui seul une amélioration comparative. |
| [11b — Variantes de vérificateur](PT_11b_grpo_qwen_rlvr_on_verifiers.ipynb) | Comparer arithmétique SymPy et contraintes Z3 ; mesurer les groupes dont les réponses reçoivent des récompenses différentes. | Après 11a ; GPU. L'évaluation enregistrée est post-entraînement seulement. |
| [11c — Changement d'échelle](PT_11c_grpo_qwen17_rlvr.ipynb) | Lire des journaux de modèles de tailles différentes et comparer les variations entre graines. | Après 11a ; l'analyse sauvegardée est accessible sur CPU. Le verdict de reproductibilité du mécanisme n'est pas un gain d'apprentissage. |
| [11d — Répétition du protocole](PT_11d_multiseed_qwen35_4x100.ipynb) | Distinguer journal d'un run, jeu uniforme de mesures et décision statistique au sein d'une graine. | Après 11a–11c. Le nom du fichier ne décrit pas à lui seul la boucle effectivement exécutée. |

### Autour de 15 — représentation et distillation

| Variante | Apport | Prérequis et limite à lire |
|---|---|---|
| [15b — Géométrie des features SAE](PT_15b_geometrie_features_sae.ipynb) | Comparer structures spectrales, axes denses et contrôles de dictionnaires d'autoencodeurs parcimonieux. | Algèbre linéaire ; modules et traces ICT accessibles. Certaines analyses restent partielles ou non concluantes. |
| [15c — Crosscoder de distillation](PT_15c_crosscoder_distillation.ipynb) | Construire un dictionnaire partagé entre modèle de base et modèle distillé, puis tester une ablation causale. | Après 15 ; GPU et chargement de modèles. Une ressemblance statistique n'établit pas une interprétation sémantique stable. |

## Installation et exécution — pratique, tous niveaux

Partir d'un environnement isolé et des cellules de configuration du carnet choisi. Le fichier [requirements.txt](requirements.txt) décrit la pile commune ; les versions effectivement utilisées et les conditions CUDA doivent être confrontées au carnet. Une mise à jour globale de TRL, Transformers et PEFT peut modifier leurs interfaces.

- **Parcours CPU** : cartographie et scénarios 01/06, audit synthétique 07, bancs 08–10/12–14/17 et analyse des agrégats en 18. Certaines analyses de 11c/11d relisent également des mesures sauvegardées.
- **Entraînement et interventions sur modèles** : prévoir CUDA et les dépendances de quantification indiquées dans les carnets concernés. Les pics mémoire enregistrés caractérisent leurs configurations ; ils ne garantissent pas la faisabilité de toute la série sur une carte donnée.
- **Commutateurs** : `LOAD_MODEL_AND_TRAIN` existe dans 02–05. Vérifier chaque carnet avant de l'utiliser : il n'y a pas de commutateur CPU universel pour le dossier.
- **Dépendances particulières** : `rewardspy` est utilisé par certains carnets et son installation depuis GitHub est précisée dans le fichier de dépendances ; sa ligne non publiée sur PyPI peut empêcher un simple `pip install -r requirements.txt` d'aboutir. Le carnet 15b utilise les modules et traces ICT ; 16 demande Ollama et les outils Dafny/Lean. La reproduction de la grille de 18 requiert les ressources de ses scripts, au-delà de la lecture des agrégats committés.

En cas de mémoire CUDA insuffisante, examiner quantification, taille des lots, accumulation de gradients, longueur des séquences et nombre de réponses par groupe. Ces réglages modifient aussi le protocole : consigner leur effet avant de comparer les résultats. La [sonde mémoire](_measurements/vram_wall_probe.py) et ses [résultats archivés](_measurements/) donnent un autre point d’entrée pour examiner les configurations par modèle et par carte ; ils ne dispensent pas de vérifier l’environnement courant. Les cartes et checkpoints [Qwen](https://huggingface.co/Qwen/Qwen3.5-0.8B), la documentation [TRL](https://huggingface.co/docs/trl/index), [PEFT](https://huggingface.co/docs/peft/index) et les optimisations [Unsloth](https://github.com/unslothai/unsloth) complètent les instructions des carnets.

### Dépannage des imports

Si `trl`, `peft` ou `bitsandbytes` ne s'importe pas, vérifier que le noyau Jupyter utilise l'environnement où les dépendances de [requirements.txt](requirements.txt) ont été installées. Tester `python -c "import trl, peft, bitsandbytes"` dans cet environnement, puis consulter les versions et contraintes CUDA du carnet et du manifeste avant de réinstaller. Pour une erreur de bibliothèque CUDA ou de DLL, vérifier la compatibilité entre pilote, PyTorch et bitsandbytes ; consulter la documentation du paquet pour la plateforme utilisée.

## Pour aller plus loin — recherche

### Lire les résultats et leurs limites

Les sorties committées permettent de distinguer ce qui a été exécuté, ce qui est estimé et ce qui reste à tester :

- Les entraînements et évaluations GPU de **04 et 05 sont sautés dans les sorties enregistrées** ; leurs tests CPU ne prouvent pas un gain sur modèle de langage. Les valeurs comparatives GSM8K de 06 sont des estimations pédagogiques.
- Le run SFT de 02 est court. DPO en 03 évalue des paires disjointes, mais répéter l'analyse d'un même sous-ensemble fixe ne démontre pas une généralisation à d'autres données.
- Les succès des bancs 08–12 décrivent leurs environnements synthétiques. En 10, un horizon immédiat neutralise le rôle de lambda ; 12 construit un problème où le crédit différé permet de l'étudier.
- Les analyses 11c/11d attestent un mécanisme reproductible sans établir l'amélioration intra-graine recherchée. L'absence d'alerte de `rewardspy` ne remplace pas une comparaison avant/après.
- En 13, des différences de gradients coexistent avec un banc comportemental qui ne départage pas les variantes. En 14, certains effets thermiques du mini-GPT restent sous la résolution de mesure.
- Les interventions de 15 portent sur les activations : les expériences de désapprentissage des poids et de fine-tuning évoquées ne sont pas toutes exécutées. Le steering trop fort peut dégrader la génération.
- En 16, un programme peut satisfaire une spécification incomplète. Les résultats publiés par un article et ceux du banc local restent distincts ; la vérification de l'outil ne valide pas automatiquement l'intention de la tâche.
- En 17, la comparaison ordinale utilise un substitut logarithmique partagé. En 18, les agrégats ne concluent pas à un avantage établi de la combinaison RL et cross-entropie.

Pour une nouvelle expérience, séparer les données d'apprentissage et d'évaluation, conserver une méthode de référence, comparer plusieurs graines et vérifier le signal de récompense. Choisir la métrique avant d'interpréter un gain : perte, calibration, exactitude et succès d'un vérificateur répondent à des questions différentes.

### Vérificateurs et spécifications

Les vérificateurs de récompense ont des contrats différents : SymPy compare des expressions en 05 ; Z3 contrôle les contraintes des tâches de 11a/11b ; le [vérificateur Lean](verifiers/lean_rlvr_verifier.py) vérifie une preuve et examine ses dépendances axiomatiques. Une preuve qui compile avec `sorry` ne remplit pas ce dernier contrat. Le module réutilise le contrôle des axiomes de l'outillage Lean et applique sa liste d'axiomes autorisés.

Pour utiliser ce vérificateur, installer la toolchain requise et examiner son choix de version : `ELAN_TOOLCHAIN` si défini, sinon le fichier `lean-toolchain` du projet, puis la version par défaut résolue par elan. Définir la variable ne télécharge pas à lui seul le moteur. En 16, la boucle de génération et de réparation ajoute une question distincte : même une preuve acceptée peut porter sur une spécification qui ne décrit pas correctement la tâche souhaitée.

### Parcours voisins

- **Préparer les modèles** : [FT-02 — QLoRA](../FineTuning/FT-02-QLoRA-Quantization-Python.ipynb) étudie quantification et budget mémoire avant PT-02/11. [FT-03 — SFT](../FineTuning/FT-03-Supervised-FineTuning-SFT-Python.ipynb) et [FT-04 — Préférences](../FineTuning/FT-04-RLHF-DPO-Python.ipynb) apportent les recettes pratiques auxquelles PT-02/03 ajoutent l'étude du signal d'apprentissage.
- **Revenir aux politiques et valeurs** : [RL-05 — Décision séquentielle](../../RL/RL-05-MDP-Programmation-Dynamique-Q-Learning-Python.ipynb) puis [RL-06c — PPO](../../RL/RL-06c-PPO-Depuis-Zero-Python.ipynb) préparent les estimateurs des paliers 08–10.
- **Passer du banc synthétique à un modèle de langage** : [RLPT-02 — GRPO minimal](../../RL/PostTraining/RLPT-02-GRPO-Minimal-Python.ipynb) construit une boucle manuelle sur un petit modèle Qwen ; PT-11a/11b utilisent la pile d'entraînement outillée. [RLPT-04 — DPO contre GRPO](../../RL/PostTraining/RLPT-04-DPO-Offline-contre-GRPO-Online-Python.ipynb) offre un protocole comparatif complémentaire aux scénarios estimatifs de PT-06.
- **Comparer apprentissage hors ligne et objectifs de substitution** : [RL-09 — Apprentissage hors ligne](../../RL/RL-09-RL-Offline-Behavior-Cloning-Python.ipynb) prépare la réflexion sur les données et la politique de référence de PT-03. [RL-10 — Façonnage de récompense](../../RL/RL-10-Reward-Shaping-Curriculum-Python.ipynb) prépare l'analyse de l'objectif récompensé en PT-05/07.
- **Examiner une récompense détournée** : après l'instrumentation de PT-07, [RLPT-03 — Reward hacking](../../RL/PostTraining/RLPT-03-Reward-Hacking-Python.ipynb) étudie le comportement induit par un objectif de substitution imparfait.
- **Retrouver les données de représentation** : PT-15b utilise les modules et traces d'[ICT-21 — Trajectoires SAE](../../IIT/ICT-Series/ICT-20-FeatureCatastrophes/ICT-21-SAETrajectoires-Python.ipynb) et d'[ICT-24 — Workspace](../../IIT/ICT-Series/ICT-24-WorkspaceIgnition-Python.ipynb). PT-15c compare, lui, deux modèles avec un dictionnaire partagé ; il ne dépend pas des traces ICT consommées par 15b.

## Ressources — tous niveaux

Les références suivantes sont celles mobilisées par les carnets et leur contexte bibliographique. Les résultats des publications ne sont pas des mesures locales de cette série.

| Référence | Lien | Couverture |
|-----------|------|------------|
| Christiano et al., "Deep reinforcement learning from human preferences" (NeurIPS 2017) | [arXiv:1706.03741](https://arxiv.org/abs/1706.03741) | Origine RLHF |
| Stiennon et al., "Learning to summarize with human feedback" (NeurIPS 2020) | [arXiv:2009.01325](https://arxiv.org/abs/2009.01325) | RLHF appliquée aux LMs |
| Ouyang et al., "Training language models to follow instructions" (InstructGPT, NeurIPS 2022) | [arXiv:2203.02155](https://arxiv.org/abs/2203.02155) | SFT + RM + PPO canonique |
| Rafailov et al., "Direct Preference Optimization" (NeurIPS 2023) | [arXiv:2305.18290](https://arxiv.org/abs/2305.18290) | Origine de DPO |
| Shao et al., "DeepSeekMath: Pushing the Limits of Mathematical Reasoning" (2024) | [arXiv:2402.03300](https://arxiv.org/abs/2402.03300) | Origine de GRPO |
| Deepseek-AI, "Deepseek-R1: Incentivizing Reasoning Capability via RL" (2025) | [rapport technique](https://github.com/deepseek-ai/DeepSeek-R1) | RLVR et GRPO à grande échelle |
| Lambert et al., "Tulu 3" (2024) | [arXiv:2411.15124](https://arxiv.org/abs/2411.15124) | Panorama des méthodes de post-training |
| Hoffmann et al., "Chinchilla" (NeurIPS 2022) | [arXiv:2203.15556](https://arxiv.org/abs/2203.15556) | Lois d’échelle et allocation du calcul |
| Penedo et al., "FineWeb-Edu" (2024) | [arXiv:2406.17557](https://arxiv.org/abs/2406.17557) | Corpus de préentraînement éducatif et coût des données |
| Liu / Su et al., "Moonlight / Muon" (2025) | [arXiv:2502.16982](https://arxiv.org/abs/2502.16982) | Optimiseur Muon ; contexte des architectures étudiées |
| Liu et al., "Neural Thermodynamic Laws for Large Language Model Training" (2025) | [arXiv:2505.10559](https://arxiv.org/abs/2505.10559) | Thermodynamique de l'entraînement : T ∼ η, équipartition, 1/t, force entropique (source de PT-14) |
| Zhai, "XSA: X-only Sparse Attention" (2026) | [arXiv:2603.09078](https://arxiv.org/abs/2603.09078) | Architecture XSA ; lecture complémentaire |
| Ye et al., "Differential Attention" (Microsoft, 2024) | [arXiv:2410.05258](https://arxiv.org/abs/2410.05258) | Attention différentielle (citée par la série Substack) |
| Ainslie et al., "GQA: Training Generalized Multi-Query Transformer Models from Multi-Head Checkpoints" (Google, 2023) | [arXiv:2305.13245](https://arxiv.org/abs/2305.13245) | Attention à requêtes groupées, citée par la série Substack |


### Interprétabilité, vérification et calibration

Les sources des paliers avancés complètent les références du début du parcours :

- Pour 15, [Arditi et al. — Refusal in Language Models Is Mediated by a Single Direction](https://arxiv.org/abs/2406.11717), [Sharkey et al. — Open Problems in Mechanistic Interpretability](https://arxiv.org/abs/2501.16496) et [Casper et al. — The 2026 Singapore Consensus on Global AI Safety Research Priorities](https://arxiv.org/abs/2608.14611) situent interventions causales et questions d'interprétabilité.
- Pour 15b, les travaux de [Li et ses coauteurs](https://arxiv.org/abs/2410.19750) et de [Sun et ses coauteurs](https://arxiv.org/abs/2506.15679) fondent les analyses des représentations ; la bibliographie du carnet précise leur rôle.
- Pour 15c, [Baek et Tegmark — Towards Understanding Distilled Reasoning Models: A Representational Approach](https://arxiv.org/abs/2503.03730) développe la comparaison des représentations de modèles distillés.
- Pour 16, [Bursuc et al. — A Benchmark for Vericoding: Formally Verified Program Synthesis](https://arxiv.org/abs/2509.22908) présente le problème de synthèse vérifiée et son banc d'évaluation.
- Pour 17–18, le [projet laya](https://github.com/NandhaKishorM/laya) fournit la recette étudiée ; les carnets séparent l'effet de ses composantes et discutent les règles de score propres.

### Lectures complémentaires

La série modern-llm de JohnEnev offre un retour d’expérience externe : [préentraînement](https://johne.substack.com/p/modern-llm-part-1-building-a-350m-transformer-from), [architecture](https://johne.substack.com/p/modern-llm-part-2-modernizing-the-architecture), [SFT et GRPO](https://johne.substack.com/p/modern-llm-part-3-post-training-sft-and-grpo), [inférence et service](https://johne.substack.com/p/modern-llm-part-4-v3-inference-and-serving-models). Lire ses coûts et performances dans leur protocole propre.

[Retour à GenAI](../README.md) · [Catalogue du dépôt](../../../COURSE_CATALOG.generated.md) · [Licence](../../../LICENSE)

### Compagnon C# de PT-08

[PT-08 C#](PT_08_grpo_from_scratch_toy_env-CSharp.ipynb) reprend [PT-08 Python](PT_08_grpo_from_scratch_toy_env.ipynb) avec TorchSharp-cpu 0.107.0/libtorch CPU 2.10.0 pour les réseaux et Microsoft.Z3 4.12.2 pour les vérifications. La fast-path tensorielle d'entraînement est contrôlée contre 2400 vrais checks SMT ; elle ne lance pas Z3 à chaque action. Les générateurs et trajectoires diffèrent entre langages. Le jouet a 96 prompts sans jeu séparé et n'inclut ni séquence ni pénalité KL.

Sous Linux, préparer le binaire Z3 4.12.2 dans un environnement Python isolé, puis exporter son chemin **avant de démarrer le noyau .NET** :

```bash
python3 -m venv .venv-pt08
.venv-pt08/bin/pip install z3-solver==4.12.2.0
export Z3_NATIVE_LIBRARY="$(.venv-pt08/bin/python -c 'import pathlib,z3; print(pathlib.Path(z3.__file__).parent / "lib" / "libz3.so")')"
export OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1
# Lancer ici Jupyter avec le noyau .NET Interactive.
```

Le paquet Python fournit ici uniquement la bibliothèque native du solveur, appelée depuis C# ; il n'exécute pas la leçon. Les paquets NuGet sont restaurés à l'exécution. Le Python jumeau requiert PyTorch CPU, NumPy, Matplotlib et z3-solver ; aucune clé ni GPU n'est nécessaire.
