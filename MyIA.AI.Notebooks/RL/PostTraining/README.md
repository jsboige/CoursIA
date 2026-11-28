# RL Post-Training — aligner un modèle de langue : préférences, reward models, PPO/DPO/GRPO

Sous-série de la série [RL](../README.md) : le post-training d'un modèle de langue par préférences humaines, du reward model écrit à la main jusqu'au départage DPO offline contre GRPO online. Elle conserve ses identifiants RLPT propres et son parcours de post-training, indépendant de la numérotation du socle RL.

L'arc part du déplacement du RLHF (Christiano et al. 2017) : personne ne sait **noter** une réponse, tout le monde sait **comparer** deux réponses au même prompt. Bradley-Terry transforme ces paires en reward utilisable (RLPT-00) ; des biais injectés à paramètres connus mesurent ensuite ce qu'un dataset de préférences fait subir au juge (RLPT-00b), et comment un reward biaisé détourne PPO (RLPT-00c) ; le même monde passe alors sous le harnais `trl` pour être comparé à budget égal au code maison (RLPT-00d à 00f) ; un troisième bras, PPO avec GAE, vient compléter la comparaison en ligne sur le même monde symbolique, et son carnet mesure le retrait de la surface `trl.experimental.ppo` (RLPT-00g) ; les algorithmes s'exécutent sur de vrais petits modèles (RLPT-01 à 03) ; la sortie départage offline contre online avec test statistique (RLPT-04).

## Objectifs d'apprentissage — découverte

À la fin du parcours, le lecteur sait :

- entraîner un reward model **from scratch** depuis des paires de préférences (Bradley-Terry, sans `trl`), l'évaluer contre le plafond de Bayes et lire sa calibration (RLPT-00) ;
- injecter des biais de longueur, de position et d'annotateur **à paramètres connus**, mesurer leur dégât contre un juge oracle, et confronter les mitigations usuelles au seuil des deux écarts-types — verdict mesuré : aucune prise isolément ne le franchit ; leur combinaison oui (+2,0σ) (RLPT-00b) ;
- diagnostiquer un reward hacking **qui prend**, par bras de contrôle et normalisation par canal, plutôt que par chirurgie du proxy (RLPT-00c), et un hack **qui ne prend pas**, par la construction du piège et la détection de sa signature (RLPT-03) ;
- rejouer le même monde, le même juge et les mêmes graines sous `trl.RewardTrainer`, `trl.DPOTrainer` et `trl.GRPOTrainer`, et lire ce que le verdict mesuré dit de chaque pile — y compris son coût fixe (RLPT-00d à 00f) ;
- aligner un petit modèle de langue par PPO avec pénalité KL contre la politique SFT de référence (RLPT-01), puis par GRPO avec récompense arithmétique vérifiable sur un modèle local (RLPT-02) ;
- départager DPO offline et GRPO online **sur la même tâche à budget égal**, multi-graines, avec test de Diebold-Mariano et dispersion inter-graines documentée (RLPT-04).

## Prérequis et entrée — découverte

RLPT-00 est l'entrée autonome : Bradley-Terry y est dérivé depuis le contrat de préférences, sans `trl`. Les carnets d'algorithme (RLPT-01 à 04) gagnent à connaître le PPO du socle RL (chapitres RL-06), sans en dépendre — chaque verdict est mesuré dans le carnet lui-même. Les carnets qui entraînent de vrais modèles de langage (RLPT-02 à 04) sont marqués `coursia-ml-training` et demandent le kernel d'entraînement de la flotte (GPU).

**Escalier** : l'entrée est RLPT-00 ; la sous-série se referme sur RLPT-04 ; le parcours du socle RL reprend au [README de la série](../README.md).

## Comment lire ce README — découverte

Le principe [« Choisir sa vitesse de lecture »](../../../README.md#choisir-sa-vitesse-de-lecture) distingue trois vitesses de lecture, qui suivent le même fil : le parcours principal, les approfondissements et la recherche.

- **Vous découvrez** : lisez les numéros nus du parcours principal, dans l'ordre, sans ouvrir une seule lettre. Ils forment à eux seuls le fil de la sous-série, du reward model écrit à la main jusqu'au départage entre DPO offline et GRPO online.
- **Vous creusez le palier 00** : la section « Autour de 00 » présente ce que le carnet du palier montre et mesure, puis ce que chaque carnet lettré y ajoute et les prérequis qu'il suppose en plus.
- **Vous cherchez la recherche ou l'outillage** : « Pour aller plus loin » donne la frontière avec GenAI/PostTraining, le carnet de synthèse et le statut des surfaces branchées ; « Installation » donne les noyaux.

Chaque section annonce son public dans son titre : découverte, Licence, recherche ou tous niveaux. Les jumeaux Python et C# d'un même carnet partagent leur numéro : choisissez l'implémentation, pas le contenu.

## Parcours principal — Licence

Les numéros nus forment le fil de la sous-série : le reward model, puis les algorithmes d'alignement, jusqu'au départage final. Les carnets lettrés du palier 00 ne sont pas des étapes : ils approfondissent ce palier et se lisent sous « Approfondissements », qui donne aussi, pour chaque carnet, son noyau et sa durée annoncée.

| # | Notebook | Ce qu'on y apprend | Public et prérequis | Pour approfondir |
|---|---|---|---|---|
| 00 | [RLPT-00 — Reward model Bradley-Terry (Python)](RLPT-00-Reward-Model-Bradley-Terry-Python.ipynb) · [C# / TorchSharp](RLPT-00-Reward-Model-Bradley-Terry-CSharp.ipynb) | Reward model from scratch depuis des paires, plafond de Bayes, calibration (ECE), identification affine | Licence. Entrée autonome de la sous-série : Bradley-Terry y est dérivé depuis le contrat de préférences, sans `trl`. Le jumeau C# tourne sous `.net-csharp`. | [Autour de 00](#autour-de-00) : [00b](#autour-de-00) · [00c](#autour-de-00) · [00d](#autour-de-00) · [00e](#autour-de-00) · [00f](#autour-de-00) · [00g](#autour-de-00). |
| 01 | [RLPT-01 — PPO RLHF petit modèle](RLPT-01-PPO-RLHF-Petit-Modele-Python.ipynb) | PPO from scratch, char-level, pénalité KL contre la politique SFT, multi-graines | Licence. Noyau `python3`. Connaître le PPO du socle RL (chapitres RL-06) y gagne, sans en dépendre. | [Autour de 01](#autour-de-01) : le noyau et la durée annoncée. |
| 02 | [RLPT-02 — GRPO minimal](RLPT-02-GRPO-Minimal-Python.ipynb) | GRPO sur Qwen3.5-0.8B local, récompense arithmétique vérifiable, générations groupées sans critic | Licence. Noyau `coursia-ml-training`. Il suit le RLPT-01 : on passe du monde jouet à un vrai modèle de langage chargé localement. | [Autour de 02](#autour-de-02) : le noyau et la durée annoncée. |
| 03 | [RLPT-03 — Reward hacking](RLPT-03-Reward-Hacking-Python.ipynb) | Trois voies pour déclencher le hack sur récompense vérifiable faillible, détection, inoculation | Licence. Noyau `coursia-ml-training`. Il est monté sur la stack du RLPT-02. | [Autour de 03](#autour-de-03) : le noyau et la durée annoncée. |
| 04 | [RLPT-04 — DPO offline contre GRPO online](RLPT-04-DPO-Offline-contre-GRPO-Online-Python.ipynb) | Même tâche conversationnelle, même budget, préférences auto-fabriquées, Diebold-Mariano | Licence. Noyau `coursia-ml-training`. Sa tâche reprend celle du RLPT-02. | [Autour de 04](#autour-de-04) : le noyau et la durée annoncée. |

## Approfondissements — Licence et lectures avancées

Chaque palier a sa sous-section : ce que le carnet du palier montre et mesure, son noyau et sa durée annoncée, puis ce que chaque carnet lettré y ajoute.

### Autour de 00

Le point de départ de la sous-série : un monde synthétique à oracle graduée, un juge qui compare au lieu de noter, et le reward model appris à partir de ses préférences.

**00** — [RLPT-00 — Reward model Bradley-Terry (Python)](RLPT-00-Reward-Model-Bradley-Terry-Python.ipynb) · [C# / TorchSharp](RLPT-00-Reward-Model-Bradley-Terry-CSharp.ipynb)

- *Ce qu'on y apprend* : Reward model from scratch depuis des paires, plafond de Bayes, calibration (ECE), identification affine.
- *Noyau* : python3 / .net-csharp. *Durée annoncée* : 35-40 min.

Les carnets suivants approfondissent ce palier.

- **00b** — [RLPT-00b — Biais de dataset](RLPT-00b-Biais-Dataset-Preferences-Python.ipynb)
  - *Ce qu'on y apprend* : Trois biais injectés à paramètres connus, dégât mesuré contre oracle, mitigations confrontées au seuil 2σ.
  - *Noyau* : python3. *Durée annoncée* : 40-45 min.
  - *Prérequis en plus* : le monde de RLPT-00, qu'il reprend à longueurs variables (sa section 1).
- **00c** — [RLPT-00c — Anatomie d'un reward hacking](RLPT-00c-Anatomie-Reward-Hacking-Python.ipynb)
  - *Ce qu'on y apprend* : Un hack **qui prend** : PPO from scratch sur proxy biaisé, bras de contrôle qui isolent la cause.
  - *Noyau* : coursia-ml-training. *Durée annoncée* : 35-40 min.
  - *Prérequis en plus* : le monde de RLPT-00 ; la boucle PPO est écrite dans le carnet lui-même (sa section 5).
- **00d** — [RLPT-00d — RewardTrainer TRL](RLPT-00d-Reward-Trainer-TRL-Python.ipynb)
  - *Ce qu'on y apprend* : Le monde de RLPT-00 sous `trl.RewardTrainer` : une seule variable, le harnais.
  - *Noyau* : python3. *Durée annoncée* : 35-40 min.
  - *Prérequis en plus* : le monde de RLPT-00, repris verbatim (sa section 1), et son reward model écrit à la main, dont le harnais impose un autre contrat de modèle (sa section 3).
- **00e** — [RLPT-00e — DPO TRL](RLPT-00e-DPO-TRL-Python.ipynb)
  - *Ce qu'on y apprend* : `trl.DPOTrainer` contre DPO maison et reward explicite, à budget égal, départagé au plafond de Bayes.
  - *Noyau* : python3. *Durée annoncée* : 25-35 min.
  - *Prérequis en plus* : le monde synthétique de RLPT-00, repris tel quel, et la recette de son reward model (son bras A).
- **00f** — [RLPT-00f — GRPO TRL contre PPO maison](RLPT-00f-GRPO-TRL-contre-PPO-Maison-Python.ipynb)
  - *Ce qu'on y apprend* : Budget apparié entre la boucle PPO maison et `trl.GRPOTrainer` : les deux bras apprennent, de la même quantité, et le verdict imprimé est INCONCLUSIVE ; ce qui change est la baseline de l'avantage — value net appris contre moyenne du groupe — et les seuls écarts francs sont le coût et l'interface.
  - *Noyau* : python3. *Durée annoncée* : 30-45 min.
  - *Prérequis en plus* : ceux que sa bannière énumère — RLPT-00 (le monde synthétique et le reward model Bradley-Terry, repris verbatim), RLPT-01 (PPO from scratch) et RLPT-00e (le geste SOTA côté offline, même monde).
- **00g** — [RLPT-00g — PPO avec GAE, troisième bras](RLPT-00g-PPO-TRL-Experimental-Python.ipynb)
  - *Ce qu'on y apprend* : Le troisième bras de la comparaison en ligne : PPO avec GAE, sur le même monde symbolique que le RLPT-00f. Le carnet mesure que la surface `trl.experimental.ppo` a été retirée du paquet en `trl` 1.13.0, et présente sa boucle PPO comme une copie pédagogique déclarée de l'algorithme de Schulman 2017. Sa conclusion lit un résultat négatif et stable, et en situe la cause dans la value net.
  - *Noyau* : python3. *Durée annoncée* : 30-40 min.
  - *Prérequis en plus* : ceux que sa bannière énumère — RLPT-00 (monde synthétique) et RLPT-00f (comparatif maison vs GRPO, même monde).

### Autour de 01

L'algorithme écrit de bout en bout, sur un modèle de langage jouet.

**01** — [RLPT-01 — PPO RLHF petit modèle](RLPT-01-PPO-RLHF-Petit-Modele-Python.ipynb)

- *Ce qu'on y apprend* : PPO from scratch, char-level, pénalité KL contre la politique SFT, multi-graines.
- *Noyau* : python3. *Durée annoncée* : 40-45 min.

### Autour de 02

Le passage du monde jouet au vrai modèle de langage, avec une récompense vérifiable par programme.

**02** — [RLPT-02 — GRPO minimal](RLPT-02-GRPO-Minimal-Python.ipynb)

- *Ce qu'on y apprend* : GRPO sur Qwen3.5-0.8B local, récompense arithmétique vérifiable, générations groupées sans critic.
- *Noyau* : coursia-ml-training. *Durée annoncée* : 45-55 min.
- *Renvoi* : le carnet ouvre par une section « Frontière avec GenAI/PostTraining » (voir « Pour aller plus loin »).

### Autour de 03

Le contrepoint du 00c : un hack que l'on construit, et trois voies pour essayer de le déclencher.

**03** — [RLPT-03 — Reward hacking](RLPT-03-Reward-Hacking-Python.ipynb)

- *Ce qu'on y apprend* : Trois voies pour déclencher le hack sur récompense vérifiable faillible, détection, inoculation.
- *Noyau* : coursia-ml-training. *Durée annoncée* : 35-40 min.
- *Renvoi* : le carnet ouvre par une section « Frontière avec GenAI/PostTraining » (voir « Pour aller plus loin »).

### Autour de 04

La sortie du parcours : la même tâche et le même budget pour deux stratégies d'alignement, l'une offline et l'autre online, départagées par un test statistique.

**04** — [RLPT-04 — DPO offline contre GRPO online](RLPT-04-DPO-Offline-contre-GRPO-Online-Python.ipynb)

- *Ce qu'on y apprend* : Même tâche conversationnelle, même budget, préférences auto-fabriquées, Diebold-Mariano.
- *Noyau* : coursia-ml-training. *Durée annoncée* : 50-55 min.

## Installation — pratique, tous niveaux

Trois noyaux suffisent pour la sous-série. `python3` porte les carnets 00, 00b, 00d, 00e, 00f, 00g et 01 ; `coursia-ml-training` porte les carnets 00c, 02, 03 et 04 ; le jumeau C# du 00 tourne sous `.net-csharp`, avec TorchSharp.

- **GPU** : les carnets 02, 03 et 04 entraînent un modèle de langage quantifié en 4 bits sur GPU CUDA ; les carnets 03 et 04 l'exigent par une assertion explicite (`Ce notebook exige un GPU (QLoRA 4-bit).`), et le carnet 02 charge Qwen3.5-0.8B en QLoRA 4 bits pour tenir dans 8 Go de VRAM. Aucune cellule des autres carnets n'appelle CUDA.
- **Versions** : les carnets 00d, 00e, 00f et 00g impriment chacun la pile qu'ils exécutent (`torch`, `transformers`, `trl`, `datasets`), et ces empreintes diffèrent d'un carnet à l'autre : la sortie du carnet fait autorité. Le carnet 00d le dit lui-même, cette empreinte de versions n'est pas une constante de la série.

## Pour aller plus loin — recherche

### Frontière avec GenAI/PostTraining

La sous-série pose ses gestes à la main, sur des mondes synthétiques et de petits modèles ; son pendant outillé vit dans [GenAI/PostTraining](../../GenAI/PostTraining/README.md). Les carnets 02 et 03 ouvrent chacun par une section « Frontière avec GenAI/PostTraining » : le 02 renvoie à [PT-11a](../../GenAI/PostTraining/PT_11a_grpo_qwen35_rlvr.ipynb) et [PT-11b](../../GenAI/PostTraining/PT_11b_grpo_qwen_rlvr_on_verifiers.ipynb), qui montrent le déploiement outillé de GRPO ; le 03 à [PT-07](../../GenAI/PostTraining/PT_07_rewardspy_reward_hacking.ipynb), où vit l'outil de détection `rewardspy`. La frontière complète — quel carnet ouvrir pour quelle question — est posée dans le [README de la série RL](../README.md), section « Frontière avec GenAI/PostTraining — où ouvrir `RLPT-*`, où ouvrir `PT_*` ».

### Carnet de synthèse

Le parcours se referme sur un carnet de synthèse qui appartient au socle, à la racine de la série : [RL-20-Capstone-PostTraining-Python](../RL-20-Capstone-PostTraining-Python.ipynb) · [C#](../RL-20-Capstone-PostTraining-CSharp.ipynb). Il ne réentraîne rien : il lit les sorties committées des carnets de la sous-série et calcule ce qu'elles autorisent à affirmer. Il s'exécute sur CPU, sans GPU ni checkpoint.

### Statut des surfaces branchées

Une surface SOTA est un fait daté par la version de la bibliothèque, et les carnets de la famille `trl` le mesurent : le 00f et le 00g constatent que `trl.experimental.ppo` a été livrée de `trl` 1.10.0 à 1.12.0, puis retirée du paquet en 1.13.0. Sous la version installée, le 00f conserve ce bras en lecture seulement, et le 00g documente un verdict `INTRINSIC` avant d'exécuter une copie pédagogique déclarée.

## Ressources — tous niveaux

Les sources sont portées par les carnets, auprès des expériences qui s'y appuient. Le 00 les nomme dans sa section « Pour aller plus loin » ; le 00e, le 00f et le 01 ouvrent une section « Références », le 00g une section « References ». Le [README de la série RL](../README.md#références) tient la table des travaux cités par les carnets — l'attribution et la discussion vivent dans le carnet.
