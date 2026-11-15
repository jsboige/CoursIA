# ICT-20 — Feature Catastrophes (catastrophes en espace de caractéristiques)

Sous-série **strate 4 → strate 5** de la série ICT : la **porte de sortie du GPU-free**. Elle calibre la méthode de détection des ruptures en *feature-space* (changepoints, signaux d'alerte précoce, hystérésis), puis franchit le pas des substrats LLM — SAE sur activations de Qwen, transformer comme substrat mesuré, moteur d'interventions causales transversal.

> [↑ Index ICT-Series](../README.md) · [Cadrage ICT-0](../ICT-0-Framing.md) · [Matrice des dissociations](../../../../docs/ict/dissociations-matrix.md) · Epic [#4588](https://github.com/jsboige/CoursIA/issues/4588)

## Ce que chaque carnet démontre

| Carnet | Ce qu'il démontre |
|---|---|
| [ICT-20 — Catastrophes en feature-space : calibration de méthode](ICT-20-FeatureCatastrophes-Python.ipynb) | **Calibrer** la détection de ruptures en *feature-space* : changepoints, *early-warning signals*, hystérésis — sur un système dont la ground truth est connue. La calibration clôt la strate 4 : la série sait mesurer une rupture avant de chercher à la provoquer. |
| [ICT-21 — Trajectoires SAE : états discrets dans le LLM](ICT-21-SAETrajectoires-Python.ipynb) | **Entrée de la strate 5** : un auto-encodeur creux (SAE) sur les activations d'un LLM révèle une trajectoire d'états discrets — le substrat LLM devient observable au même titre que Gray-Scott ou le Game of Life. |
| [ICT-21b — Calibration SAE : que reconstruit chaque SAE ?](ICT-21b-SAECalibration-Python.ipynb) | L'étape 0 de l'épic [#8236](https://github.com/jsboige/CoursIA/issues/8236) : avant d'interpréter un SAE, mesurer **ce qu'il reconstruit** — fidélité, sparsité, features mortes. Un SAE mal calibré fabrique des états discrets fantômes. |
| [ICT-21c — Catastrophes SAE](ICT-21c-SAECatastrophes-Python.ipynb) | Livrable 2 de l'épic [#8236](https://github.com/jsboige/CoursIA/issues/8236) : perturber le **dictionnaire** du SAE et distinguer ce qui tient à la *forme* des features de ce qui tient à la *dynamique* de la trajectoire. |
| [ICT-22 — LLM comme substrat du banc cross-substrat](ICT-22-LLMSubstrat-Python.ipynb) | Le LLM devient le **quatrième substrat** du banc cross-substrat de la série, avec son contrôle shuffle — la grammaire des catastrophes, validée sur Gray-Scott, Game of Life et réseaux de Hopfield, s'étend au substrat LLM. |
| [ICT-22b — CausalInterventionEngine : le moteur transversal](ICT-22b-CausalInterventionEngine-Python.ipynb) | Le moteur d'**interventions causales** ([#15479](https://github.com/jsboige/CoursIA/issues/15479)) : cinq opérations (ablate, clamp, patch, steer, interchange) uniformisées, réutilisables sur tous les substrats de la série — l'instrument transversal que la strate 5 actionne. |

## Place dans l'escalier

Charinière de la série : ICT-20 referme la strate 4 (ICT-14 → ICT-20) en dotant la série d'une méthode de détection calibrée, et l'accrétion 21 → 22b ouvre la **strate 5** (ICT-21 → ICT-25) — le passage des substrats GPU-free au substrat LLM, sans changer d'instruments. En amont, la batterie d'enjeu d'[ICT-19](../ICT-19-EnjeuBattery/README.md) fournit le gabarit des bancs ; en aval, le moteur d'interventions d'ICT-22b armera les carnets de la strate 5.

## Instruments

Organes : `catastrophe` et `feature_dynamics` (calibration des ruptures), `sae_calibration` / `sae_dictionary` / `sae_traces` (strate 5), `causal_engine` (moteur d'interventions) — voir la table des organes de l'[index de série](../README.md) et le paquet [`ict/`](../ict/). L'état scientifique de chaque claim se lit dans la [matrice des dissociations](../../../../docs/ict/dissociations-matrix.md).
