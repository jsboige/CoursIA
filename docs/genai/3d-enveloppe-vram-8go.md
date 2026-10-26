# Enveloppe GPU de la famille NeRF sur l'étage pionnier 8 Go

**Question.** L'EPIC Origami #18605 répartit le travail GPU en trois étages. Le premier — *pionnier*, petite carte 8 Go — est le rôle où l'on **défriche** : c'est là qu'on vérifie qu'un pipeline tient, avant de le passer à l'étage moyen. Pour la famille **0,8 B en GRPO+QLoRA**, l'enveloppe est mesurée : **pic 7 844 Mio sur 8 192 (95,7 %)** — 4 % de marge, donc rien de plus lourd n'y passe (mesure #21620, PR #21624).

Ce document mesure **l'autre moitié** de l'EPIC : la famille **NeRF**, dont le Pli 2 est livré et dont la mesure d'enveloppe n'existait pas. Les **deux volets** de la famille y sont mesurés : l'entraînement (`3D-01-NeRF-From-Scratch`) et l'évaluation (`3D-02-NeRF-Critic`). Le **Pli 1** (`3.4d-Fourier-Features`) y est mesuré aussi, pour la comparaison que l'issue demande entre les deux plis.

**Mesure.** Poste `myia-po-2028`, **NVIDIA GeForce RTX 3070 Ti Laptop GPU, 8 192 Mio**, `torch 2.8.0+cu126`, Python 3.13.16, kernel `python3`. Exécution par `scripts/notebook_tools/notebook_tools.py execute` (Papermill). Sortie `nvidia-smi` échantillonnée **toutes les 5 s** (42 échantillons sur le run). Le notebook a été exécuté **sur une copie hors dépôt** : `3D-01` et `3D-02` sont dans le scope de claims d'autres lanes (PR #21413, #20544) et n'ont pas été touchés. Le volet évaluatif (`3D-02`) a été rejoué sur la même carte avec `torch 2.14.1+cu126`, 242 échantillons à 5 s. Le Pli 1 (`3.4d`) a été rejoué sur le même siège, en NumPy pur, avec un échantillonnage à 2 s de la carte **et** de la RAM hôte.

| Mesure | Valeur |
|---|---|
| **Pic VRAM** | **4 318 Mio / 8 192 Mio = 52,7 %** |
| Mémoire au repos (modèle déchargé) | 322 Mio |
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
| **NeRF** (`3D-01`, 2 000 it. + éval, réseau dense 5D) | 4 318 Mio (52,7 %) | 47 % | **tient largement** — l'étage pionnier peut défricher le socle A1 |
| **NeRF — volet évaluatif** (`3D-02-NeRF-Critic` : critic, bruit de pose, focales, comptage de points) | **7 740 Mio (94,5 %)** | 5,5 % | **au bord** — et le pic n'est pas dans l'entraînement |
| **Fourier features** (`3.4d`, Pli 1, NumPy pur) | 0 Mio attribuable (carte au repos) | — | **hors GPU** — harnais CPU, 288 Mio de RAM hôte, 64 s |
| **0,8 B GRPO + QLoRA** (0,8 B, GRPO, budget 384 tok) | 7 844 Mio (95,7 %) | 4 % | **au bord** — rien de plus lourd ne passe |

La conséquence opérationnelle est nette : **le premier étage n'est pas un « petit GPU » générique, il est un étage à deux vitesses.** La famille NeRF y a de la place ; un entraînement RL, même sur 0,8 B, n'y a que 4 %. Un lead RL ne peut donc pas être défriché sur l'étage pionnier : il part **directement** à l'étage moyen, et le pionnier garde sa vocation (défricher NeRF, Fourier, petits apprentissages) — pour le Pli 1, cette vocation ne consomme même pas de carte.

**Ce que cette mesure ne couvre pas** : le pipeline **3DGS/gsplat** du Pli 3 (`3D-04`, `3D-05`), qui exige le moteur CUDA `gsplat` — absent de ce poste (cf. #21614 : `nvcc` non installé, chaîne CUDA à construire). L'enveloppe du 3DGS reste donc à mesurer sur l'eGPU 24 Go désigné par l'EPIC.

## Le volet évaluatif (`3D-02-NeRF-Critic`) : l'enveloppe change de nature

Le second volet de la famille NeRF — celui qui **évalue** (pénalité critic, sensibilité au bruit de pose, transfert entre focales, comptage de points) — a été rejoué en entier sur la même carte, le 20/10 de 23:17Z à 23:38Z.

| Mesure | Valeur |
|---|---|
| **Pic VRAM** | **7 740 Mio / 8 192 Mio = 94,5 %** |
| Mémoire au repos (avant le run) | 428 Mio |
| Température max | 72 °C (seuil d'abandon 85 °C non franchi) |
| Utilisation GPU max | 100 % |
| Durée du run complet | **1 222,3 s** (20,4 min) |
| Plateau de l'entraînement (scène jouet, puis Lego 100×100) | 3 001 Mio, puis 4 217 Mio (51 % de la carte) |
| Fidelity — scène jouet, 1 600 it. | **21,76 dB** (96 s) |
| Fidélité — Lego, 3 000 it. | 20,15 dB (L=0), **22,45 dB** (L=4), 22,26 dB (L=10) |
| Fidélité — bruit de pose, 800 it. | 19,84 dB (σ=0°) → 18,01 dB (σ=2°) |
| Fidélité — transfert de focale (diag. de la matrice) | 19,76 dB (native→native), 18,92 dB (télé→télé), 6,66 dB (grand angle→native) |
| Coût du comptage de points | 9,4 ms (N=8) → **15 084 ms** (N=256, 1 048 576 points) |

**Traçabilité de ce tableau.** Chaque valeur est un champ du manifeste `3d02_enveloppe_8go.json`, et le chemin est donné parce qu'une relecture doit pouvoir remonter jusqu'au chiffre sans refaire le run : `vram.peak_mib` et `vram.peak_pct` pour le pic, `vram.idle_mib` pour le repos, `vram.temp_max_c`, `vram.util_max_pct`, `execution.wallclock_s`, `fidelite.scene_jeu_psnr_final_db` et `fidelite.grille_critic_*` pour les fidelités, `fidelite.bruit_pose_psnr_db_800it`, `fidelite.matrice_focale_psnr_db`, `fidelite.comptage_points` pour les temps de comptage ; les deux plateaux de la ligne « plateau de l'entraînement » sont `vram.profil_par_phase_mib[0].plateau_mib` (3 001) et `[1].plateau_mib` (4 217). Le temps de 144 ms pour `N=128` est `fidelite.comptage_points[4].temps_ms`. **Un seul chiffre de cette section n'a pas de champ** : la mémoire au repos *après* le run, qui n'était pas relevée par la sonde — la ligne ne cite donc plus que la valeur d'avant, celle que le manifeste porte. La correspondance chiffre → champ → **ligne de la trace brute** est au §« Traçabilité ».

Le point important n'est pas le total : c'est **où** le pic arrive. Le profil échantillonné à 5 s montre un plateau stable à 4 200 Mio pendant les vingt minutes d'entraînement et d'évaluation, puis une **montée de 3 523 Mio dans les vingt dernières secondes** — la cellule de comptage de points `N=256`, qui mobilise 1 048 576 points et met 15 secondes à elle seule. Entraîner un NeRF sur 8 Go n'est pas le problème ; **évaluer un NeRF de façon dense l'est**.

C'est la même arithmétique que le run 0,8 B GRPO+QLoRA (95,7 %) : le pionnier reste un étage pour l'entraînement et l'**évaluation dense doit monter d'un étage**. La réserve « le pionnier garde sa vocation » ne se justifie plus telle quelle : elle se restreint au *socle* NeRF.

**Ce que le volet évaluatif ajoute comme lecture pédagogique** (les valeurs sont dans le manifeste) : sur la scène jouet, la pénalité critic dégrade la PSNR (20,88 → 19,92 → 19,13 dB pour L = 0, 4, 10) alors que sur Lego elle l'améliore (20,15 → 22,45 dB) — la pénalité n'a pas le même sens selon la scène ; le bruit de pose dégrade la qualité de façon monotone (19,84 → 18,01 dB pour σ de 0° à 2°) ; la matrice de transfert entre focales est maximale sur sa diagonale, ce qui veut dire qu'un modèle appris à une focale ne se transpose pas ; le coût du comptage de points explose entre N=128 (144 ms) et N=256 (15 s), soit un facteur 105 pour un doublement du nombre de points.

## Le Pli 1 (Fourier) : la comparaison demandée tranche autrement

L'issue demandait de comparer le profil des deux plis sur la même carte 8 Go — « est-ce compatible avec un **même run conjoint**, ou faut-il enchaîner les deux ? ». La mesure répond, mais pas par un chiffre de VRAM : le harnais du Pli 1 (`3.4d-Fourier-Features-Biais-Spectral-Python.ipynb`) est **CPU-borné en NumPy pur** — Adam et le gradient sont écrits à la main dans le carnet, et son propre verdict indique « sur CPU, en NumPy pur, en ~30 secondes ». Il n'importe ni `torch` ni aucun moteur CUDA.

| Mesure | Valeur |
|---|---|
| Durée du run complet | **64,2 s** (5 entraînements : 1 baseline + 3 σ + 1 témoin négatif) |
| VRAM de la carte | **427 Mio au repos → 444 Mio au pic observé** (delta ≤ 17 Mio, bruit ambiant) |
| VRAM attribuable au harnais | **0 Mio** — aucun contexte CUDA créé |
| RAM hôte — pic de l'arbre de processus | **288 Mio** |
| Fidélité rejouée | baseline 3,226e-01 · σ=1,0 → 1,404e-02 · σ=5,0 → 1,012e-02 · σ=50 → 4,115e-01 |

Les figures rejouées sont celles du carnet committé : le run **reproduit** la référence (baseline 3,23e-01, écart de gradient 2,08e-07), il ne la modifie pas.

La conclusion est donc une **non-concurrence de ressources** : Fourier occupe 288 Mio de RAM hôte pendant 64 s et **zéro octet de VRAM**, la famille NeRF occupe 52,7 % puis 94,5 % de la carte. Un run conjoint est possible du point de vue de la mémoire vidéo ; ce qui ne se partage pas, c'est la carte elle-même entre deux jobs CUDA. Autrement dit, la question « run conjoint ou enchaînement ? » ne se pose pas en VRAM : elle se pose en **temps GPU**, et le Pli 1 n'en consomme pas.

C'est aussi ce qui recadre la lecture d'ensemble : ce qui ne tient pas sur l'étage pionnier n'est pas le Pli 1 ni l'entraînement NeRF, c'est **l'évaluation dense** du Pli 2.

## Traçabilité : de chaque chiffre à une ligne de la trace

Les séries `nvidia-smi` des deux runs NeRF sont **committées** avec ce document
(`scripts/results/3d_enveloppe_8go/traces/`), parce qu'elles tiennent sous 512 Ko
et que la valeur d'un manifeste est de se **re-dériver** sans refaire le run. Le
détail du format, la provenance run par run et les tableaux de phase sont dans
`scripts/results/3d_enveloppe_8go/traces/README.md` ; ce qui suit est la carte
des chiffres cités plus haut.

| Fichier | Octets | sha256 |
|---|---:|---|
| `traces/vram-3d01.csv` | 2 060 | `bf2c924b8e825de51486837174e993d78b6809a82612f2703e92b028ed5dae1e` |
| `traces/3d01-enveloppe.log` | 1 324 | `62c6817842a5cd3d30e1939ee5b3b300ae38e2acfd4c6b32d75df606585312e0` |
| `traces/vram-3d02.csv` | 11 656 | `81407a7191be24fcae8371c68f63edd500c4021d21cc2c296e443a4a1302e30e` |
| `traces/3d02-enveloppe.log` | 660 | `3e62a2013be2416b0f2aa52b89efd5fa9926a900309676eb4b7e760816eb8ccd` |

Les deux CSV portent l'en-tête `horodatage,utilisation_gpu,memoire_mib,temp_gpu_c`,
un échantillon toutes les 5 s (cadence observée : 5,07 s et 5,09 s de médiane).
La **commande de sonde exacte n'a pas été archivée** — elle n'existe ni dans le
dépôt ni dans le dossier GDrive d'où les traces ont été récupérées ; le format
des fichiers (en-tête français, horodatages .NET à sept décimales et décalage
`+02:00`) établit qu'il s'agissait d'une boucle reformatant `nvidia-smi`, pas
d'un `--format=csv` direct, et l'instrument du dépôt
`probe_15099_vram_sampler.py` n'en est pas le producteur (il écrit du JSONL à
champs anglais).

### Chiffre du document → champ du manifeste → ligne de la trace

| Chiffre cité | Champ | Ligne de la trace |
|---|---|---|
| Pic **4 318 Mio** (52,7 %), 3D-01 | `vram.peak_mib` | `vram-3d01.csv` indices **24** (t = 121,7 s) et **29** (t = 147,0 s) |
| Repos **322 Mio**, 3D-01 | `vram.idle_mib` | indice **2** (t = 10 s), minimum de la série ; le repos d'avant run vaut 331 Mio (indices 0-1, et lignes `GPU avant` / `GPU apres` du journal) |
| 73 °C, 97 % | `vram.temp_max_c`, `vram.util_max_pct` | maximum des colonnes `temp_gpu_c` et `utilisation_gpu` sur 42 échantillons |
| Run **207,6 s** | `execution.wallclock_s` | journal : `Total time: 207.6s` ; la trace couvre 207,8 s (42 échantillons à 5,07 s) |
| Pic **7 740 Mio** (94,5 %), 3D-02 | `vram.peak_mib` | `vram-3d02.csv` indice **240** (t = 1 220,8 s) |
| Repos **428 Mio**, 3D-02 | `vram.idle_mib` | indice **2** (t = 10 s) et ligne `GPU avant` du journal ; la série descend ensuite à 425 (indice 4) |
| Plateau **3 001 Mio** | `vram.profil_par_phase_mib[0].plateau_mib` | échantillon réel (indices 26, 29, 49) de la fenêtre `0-300` ; statistique de la fenêtre : médiane 2 992, mode 2 989, min 425 (les indices 0-6 sont le repos et la rampe) |
| Plateau **4 217 Mio** | `vram.profil_par_phase_mib[1].plateau_mib` | échantillon réel, deux fois : indices **184** (t = 936 s) et **231** (t = 1 175 s) |
| « montée de **3 523 Mio** » | prose de `pic_atteint_par` | `7 740 − 4 217` ; depuis le maximum du palier `7 740 − 4 228 = 3 512` ; entre échantillons consécutifs `7 736 − 4 219 = 3 517` (indices 237→238) |
| 15 084 ms pour N=256 | `fidelite.comptage_points[5].temps_ms` | **aucune** : c'est un temps de cellule, pas un échantillon VRAM — la sortie du carnet en est la trace |

La dernière ligne marque la frontière : la trace brute prouve l'**enveloppe**
(mémoire, température, occupation, durée), pas les chiffres de **fidélité**, qui
viennent de l'exécution du carnet et n'ont de trace que dans ses sorties.

### L'écart 4228 / 4217 est tranché par la trace

Les deux valeurs sont **des lignes réelles**, prises à deux instants différents —
ce n'est donc pas un désaccord de mesure, et il n'y a pas à choisir laquelle
serait « la bonne » :

| Valeur | Où elle vit dans `vram-3d02.csv` |
|---|---|
| **4 217** | indices **184** (t = 936 s) et **231** (t = 1 175 s) — deux échantillons, aucun rôle de borne |
| **4 228** | indice **235** (t = 1 195 s) — le **maximum** de la phase 2, 15 s avant le saut vers le pic |
| **4 202** | médiane et mode de la phase 2 (177 échantillons de la fenêtre `300-1200`, 4 195-4 228) |

Le champ `plateau_mib` et la prose « de 4228 à 7740 » désignent donc **deux
échantillons du même palier**, et ni l'un ni l'autre n'en est la statistique. La
trace départage en montrant la queue montante qui les sépare : 4 203 à
t = 1 109 s, 4 209 à 1 149 s, 4 218 à 1 165 s, 4 228 à 1 195 s, puis 7 736 à
1 211 s. Les valeurs des manifestes sont **conservées telles quelles** (#22110
demande la traçabilité, pas la réécriture) ; c'est la lecture du champ qui se
précise : il nomme un échantillon de palier, pas le palier.

La trace tranche aussi le second écart nommé en revue, **322 contre 331 Mio** :
331 Mio est la lecture d'avant-run (indices 0 et 1, et le journal), 322 Mio le
creux d'un unique échantillon à t = 10 s — le minimum de la série, celui que le
manifeste 3D-01 porte sous `idle_mib`.

### Ce qui reste non re-dérivable : la trace du Pli 1

La série du run Fourier n'a pas été conservée (ni sur le siège d'origine, ni sur
GDrive, ni dans le dépôt) : les agrégats de `3d4d_fourier_8go.json` — 427 → 444
Mio, pic RSS hôte 288 Mio, `contexte_cuda_cree: false` — sont donc **non
re-dérivables**, et le manifeste l'écrit désormais dans son bloc `provenance`
plutôt que de laisser croire à une trace consultable. C'est une perte mesurée,
pas une absence : le run a été échantillonné, ses fichiers ont disparu avant
rapatriement. La conclusion « zéro octet de VRAM attribuable » ne dépend pas de
cette série : elle repose sur l'absence d'import CUDA et sur la carte restée au
niveau du repos, que le manifeste atteste.

**Vérification.** `python scripts/audit/check_vram_envelope_rederivable.py`
refait ces calculs depuis les CSV et contrôle ce qui se re-dérive exactement :
les deux empreintes (`trace_sha256`, `journal_sha256`), `samples`,
`sample_period_s`, `trace_bytes`, `trace_samples`, `trace_span_s`, `peak_mib`,
`peak_pct`, `temp_max_c`, `util_max_pct`, et `idle_mib` **à l'échantillon que
le `field_map` désigne** (indice 2) : l'indice est **lu dans le manifeste**
(`provenance.field_map.idle_mib`), puis recoupé avec l'ancre attendue par
l'organe — une divergence, ou une ancre que le manifeste ne nomme plus en
clair, fait rougir le contrôle. Pour `profil_par_phase_mib[i].plateau_mib`
il vérifie la **présence** de la valeur citée dans la fenêtre de sa phase et
imprime à côté la statistique du palier (n, min, max, médiane, mode) : il
n'arbitre pas lequel des échantillons mérite le nom de palier, et deux valeurs
voisines y sont donc également acceptées. Un champ re-dérivable qui dérive
rougit ; un choix éditorial ne se détecte pas mécaniquement. Il n'est pas câblé
en CI : il se lance à la main après toute modification d'un manifeste ou d'une
trace.

## Artefacts

- Manifeste de mesure (entraînement) : `scripts/results/3d_enveloppe_8go/3d01_enveloppe_8go.json` (pic VRAM, température, débit, courbe PSNR complète, comparaison avec la mesure #21620).
- Manifeste de mesure (volet évaluatif) : `scripts/results/3d_enveloppe_8go/3d02_enveloppe_8go.json` (pic VRAM et son profil par phase, température, débit, grilles critic / pose / focale / comptage de points).
- Manifeste de mesure (Pli 1, Fourier) : `scripts/results/3d_enveloppe_8go/3d4d_fourier_8go.json` (enveloppe VRAM et RAM hôte, hyper-paramètres du harnais, figures de fidélité rejouées, comparatif des quatre pipelines ; `provenance.trace: "perdue"` — sa série brute n'a pas été conservée).
- Traces brutes et leur provenance : `scripts/results/3d_enveloppe_8go/traces/` — `vram-3d01.csv`, `vram-3d02.csv` et les deux journaux de run, avec empreintes sha256 et tableaux de phase dans `traces/README.md`.
- Organe de re-dérivation : `scripts/audit/check_vram_envelope_rederivable.py` (recalcule pic, repos et plateaux depuis les CSV, contrôle les empreintes ; se lance à la main).
- Mesure jumelle de l'étage pionnier : `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/scripts/results/p15294_8go_pionnier/` (issue #21620, PR #21624).

**Reproductibilité.** Issue #21626 (fille de l'EPIC #18605). GPU réservé au ledger `CoursIA-gpu-reservation-ledger` **avant** tout chargement (`obs-55b043a6b21cc586` pour `3D-01`, `obs-12e553f00d6132f3` pour `3D-02` ; `held` puis `released`), un seul job à la fois, sortie `nvidia-smi` échantillonnée à 5 s. Les deux notebooks ont été exécutés **sur une copie hors dépôt** : `3D-01` et `3D-02` sont dans le scope de claims d'autres lanes (PR #21413, #20544) et n'ont pas été touchés. Les deux mesures portent le même siège et la même carte mais deux versions de torch (2.8.0+cu126 pour `3D-01`, 2.14.1+cu126 pour `3D-02`) : l'effet de la version n'est pas isolé comme facteur du pic.

Le run du **Pli 1** (`3.4d`) est le seul des trois à ne **pas** avoir réservé la carte : il ne charge aucun moteur CUDA, donc rien ne s'exécute sur le GPU — la réservation du ledger aurait immobilisé une ressource inutilement demandée. La carte a été néanmoins échantillonnée à 2 s pendant le run (c'est cette trace qui établit qu'elle reste au repos) et la RAM hôte a été suivie par lecture de la RSS de l'arbre de processus au même pas de 2 s.
