# RL Post-Training — aligner un modèle de langue : préférences, reward models, PPO/DPO/GRPO

Sous-série de la série [RL](../README.md) : le post-training d'un modèle de langue par préférences humaines, du reward model écrit à la main jusqu'au départage DPO offline contre GRPO online. Elle conserve ses identifiants RLPT propres et son parcours de post-training, indépendant de la numérotation du socle RL.

L'arc part du déplacement du RLHF (Christiano et al. 2017) : personne ne sait **noter** une réponse, tout le monde sait **comparer** deux réponses au même prompt. Bradley-Terry transforme ces paires en reward utilisable (RLPT-00) ; des biais injectés à paramètres connus mesurent ensuite ce qu'un dataset de préférences fait subir au juge (RLPT-00b), et comment un reward biaisé détourne PPO (RLPT-00c) ; le même monde passe alors sous le harnais `trl` pour être comparé à budget égal au code maison (RLPT-00d à 00g) ; les algorithmes s'exécutent sur de vrais petits modèles (RLPT-01 à 03) ; la sortie départage offline contre online avec test statistique (RLPT-04).

## Objectifs d'apprentissage

À la fin du parcours, le lecteur sait :

- entraîner un reward model **from scratch** depuis des paires de préférences (Bradley-Terry, sans `trl`), l'évaluer contre le plafond de Bayes et lire sa calibration (RLPT-00) ;
- injecter des biais de longueur, de position et d'annotateur **à paramètres connus**, mesurer leur dégât contre un juge oracle, et confronter les mitigations usuelles au seuil des deux écarts-types — verdict mesuré : aucune prise isolément ne le franchit ; leur combinaison oui (+2,0σ) (RLPT-00b) ;
- diagnostiquer un reward hacking **qui prend**, par bras de contrôle et normalisation par canal, plutôt que par chirurgie du proxy (RLPT-00c, RLPT-03) ;
- rejouer le même monde, le même juge et les mêmes graines sous `trl.RewardTrainer`, `trl.DPOTrainer` et `trl.GRPOTrainer`, et lire ce que le verdict mesuré dit de chaque pile — y compris son coût fixe (RLPT-00d à 00g) ;
- aligner un petit modèle de langue par PPO avec pénalité KL contre la politique SFT de référence (RLPT-01), puis par GRPO avec récompense arithmétique vérifiable sur un modèle local (RLPT-02) ;
- départager DPO offline et GRPO online **sur la même tâche à budget égal**, multi-graines, avec test de Diebold-Mariano et dispersion inter-graines documentée (RLPT-04).

## Parcours

| # | Carnet | Le geste | Kernel | Durée |
|---|---|---|---|---|
| pt-00 | [RLPT-00 — Reward model Bradley-Terry](RLPT-00-Reward-Model-Bradley-Terry-Python.ipynb) | Reward model from scratch depuis des paires, plafond de Bayes, calibration (ECE), identification affine | python3 | 35-40 min |
| pt-00b | [RLPT-00b — Biais de dataset](RLPT-00b-Biais-Dataset-Preferences-Python.ipynb) | Trois biais injectés à paramètres connus, dégât mesuré contre oracle, mitigations confrontées au seuil 2σ | python3 | 40-45 min |
| pt-00c | [RLPT-00c — Anatomie d'un reward hacking](RLPT-00c-Anatomie-Reward-Hacking-Python.ipynb) | Un hack **qui prend** : PPO from scratch sur proxy biaisé, bras de contrôle qui isolent la cause | coursia-ml-training | 35-40 min |
| pt-00d | [RLPT-00d — RewardTrainer TRL](RLPT-00d-Reward-Trainer-TRL-Python.ipynb) | Le monde de RLPT-00 sous `trl.RewardTrainer` : une seule variable, le harnais | python3 | 35-40 min |
| pt-00e | [RLPT-00e — DPO TRL](RLPT-00e-DPO-TRL-Python.ipynb) | `trl.DPOTrainer` contre DPO maison et reward explicite, à budget égal, départagé au plafond de Bayes | python3 | 25-35 min |
| pt-00f | [RLPT-00f — GRPO TRL contre PPO maison](RLPT-00f-GRPO-TRL-contre-PPO-Maison-Python.ipynb) | Budget apparié : la différence robuste est le critic (réseau de valeur appris contre moyenne de groupe) | python3 | 30-45 min |
| pt-00g | [RLPT-00g — PPO TRL expérimental](RLPT-00g-PPO-TRL-Experimental-Python.ipynb) | `trl.experimental.ppo.PPOTrainer` introspecté comme surface réelle, boucle PPO conforme | python3 | 30-40 min |
| pt-01 | [RLPT-01 — PPO RLHF petit modèle](RLPT-01-PPO-RLHF-Petit-Modele-Python.ipynb) | PPO from scratch, char-level, pénalité KL contre la politique SFT, multi-graines | python3 | 40-45 min |
| pt-02 | [RLPT-02 — GRPO minimal](RLPT-02-GRPO-Minimal-Python.ipynb) | GRPO sur Qwen3.5-0.8B local, récompense arithmétique vérifiable, générations groupées sans critic | coursia-ml-training | 45-55 min |
| pt-03 | [RLPT-03 — Reward hacking](RLPT-03-Reward-Hacking-Python.ipynb) | Trois voies pour déclencher le hack sur récompense vérifiable faillible, détection, inoculation | coursia-ml-training | 35-40 min |
| pt-04 | [RLPT-04 — DPO offline contre GRPO online](RLPT-04-DPO-Offline-contre-GRPO-Online-Python.ipynb) | Même tâche conversationnelle, même budget, préférences auto-fabriquées, Diebold-Mariano | coursia-ml-training | 50-55 min |

## Prérequis et entrée

RLPT-00 est l'entrée autonome : Bradley-Terry y est dérivé depuis le contrat de préférences, sans `trl`. Les carnets d'algorithme (RLPT-01 à 04) gagnent à connaître le PPO du socle RL (chapitres RL-06), sans en dépendre — chaque verdict est mesuré dans le carnet lui-même. Les carnets marqués `coursia-ml-training` entraînent de vrais modèles et demandent le kernel d'entraînement de la flotte (GPU).

**Escalier** : l'entrée est RLPT-00 ; la sous-série se referme sur RLPT-04 ; le parcours du socle RL reprend au [README de la série](../README.md).
