# Enveloppe GPU de la famille NeRF sur l'étage pionnier 8 Go

**Question.** L'EPIC Origami #18605 répartit le travail GPU en trois étages. Le premier — *pionnier*, petite carte 8 Go — est le rôle où l'on **défriche** : c'est là qu'on vérifie qu'un pipeline tient, avant de le passer à l'étage moyen. Pour la famille **0,8 B en GRPO+QLoRA**, l'enveloppe est mesurée : **pic 7 844 Mio sur 8 192 (95,7 %)** — 4 % de marge, donc rien de plus lourd n'y passe (mesure #21620, PR #21624).

Ce document mesure **l'autre moitié** de l'EPIC : la famille **NeRF** (`3D-01-NeRF-From-Scratch`), dont le Pli 2 est livré et dont la mesure d'enveloppe n'existait pas.

**Mesure.** Poste `myia-po-2028`, **NVIDIA GeForce RTX 3070 Ti Laptop GPU, 8 192 Mio**, `torch 2.8.0+cu126`, Python 3.13.16, kernel `python3`. Exécution par `scripts/notebook_tools/notebook_tools.py execute` (Papermill). Sortie `nvidia-smi` échantillonnée **toutes les 5 s** (42 échantillons sur le run). Le notebook a été exécuté **sur une copie hors dépôt** : `3D-01` et `3D-02` sont dans le scope de claims d'autres lanes (PR #21413, #20544) et n'ont pas été touchés.

| Mesure | Valeur |
|---|---|
| **Pic VRAM** | **4 318 Mio / 8 192 Mio = 52,7 %** |
| Mémoire au repos (modèle déchargé) | 331 Mio |
| Température max | 73 °C (seuil d'abandon 85 °C non franchi) |
| Utilisation GPU max | 97 % |
| Durée du run complet | **207,6 s** (3,5 min) |
| Débit — scène Lego (2 000 itérations) | 15,8 it/s |
| Débit — scène jouet (1 000 itérations) | 17,2 it/s |
| Fidélité finale (Lego, PSNR) | **21,92 dB** |

**La fidélité se rejoue encore.** Le run précédent sur ce même poste (20/10, PR #21607) avait donné **21,92 dB** ; la référence sur carte 16 Go donne **21,85 dB**. Trois exécutions, deux cartes, un écart de 0,07 dB sur le chiffre final.

## Lecture : où passe la frontière de l'étage 8 Go

| Pipeline | Pic VRAM sur 8 Go | Marge restante | Verdict |
|---|---:|---:|---|
| **NeRF** (`3D-01`, 2 000 it. + éval, réseau dense 5D) | 4 318 Mio (52,7 %) | 47 % | **tient largement** — l'étage pionnier peut defriche le socle A1 |
| **0,8 B GRPO + QLoRA** (0,8 B, GRPO, budget 384 tok) | 7 844 Mio (95,7 %) | 4 % | **au bord** — rien de plus lourd ne passe |

La conséquence opérationnelle est nette : **le premier étage n'est pas un « petit GPU » générique, il est un étage à deux vitesses.** La famille NeRF y a de la place ; un entraînement RL, même sur 0,8 B, n'y a que 4 %. Un lead RL ne peut donc pas être défriche sur l'étage pionnier : il part **directement** à l'étage moyen, et le pionnier garde sa vocation (défriche NeRF, Fourier, petits apprentissages).

**Ce que cette mesure ne couvre pas** : le volet **évaluatif** `3D-02-NeRF-Critic` (non rejoué ici) et le pipeline **3DGS/gsplat** du Pli 3, qui exige le moteur CUDA `gsplat` — absent de ce poste (cf. #21614 : `nvcc` non installé, chaîne CUDA à construire). L'enveloppe du 3DGS reste donc à mesurer sur l'eGPU 24 Go désigné par l'EPIC.

## Artefacts

- Manifeste de mesure : `MyIA.AI.Notebooks/GenAI/3D/_measurements/3d01_enveloppe_8go.json` (pic VRAM, température, débit, courbe PSNR complète, comparaison avec la mesure #21620).
- Mesure jumelle de l'étage pionnier : `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/scripts/results/p15294_8go_pionnier/` (issue #21620, PR #21624).

**Reproductibilité.** Issue #21626 (fille de l'EPIC #18605). GPU réservé au ledger `CoursIA-gpu-reservation-ledger` **avant** tout chargement (`obs-55b043a6b21cc586`, `held`, puis `released`), un seul job à la fois, sortie `nvidia-smi` échantillonnée à 5 s.
