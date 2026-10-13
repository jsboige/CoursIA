# Issue #15159 — axe Vidéo Wan 2.1/2.2 sur TensorSharp .NET — ledger d'investigation

**Issue** : [#15159](https://github.com/jsboige/CoursIA/issues/15159)
**Issue parente** : [#14549](https://github.com/jsboige/CoursIA/issues/14549) (axe multimodal TensorSharp)
**Lane** : `myia-po-2023:CoursIA` — machine routée par le body de l'issue (« seule machine portant l'eGPU 3090 + les services GenAI Video Docker »)
**Claim** : [commentaire #5963436956](https://github.com/jsboige/CoursIA/issues/15159#issuecomment-5963436956)
**Ledger parent** : `docs/ledgers/14549-tensorsharp-multimodal.md` (section `c.419` : axe Vidéo `NON MESURÉ`, VAE incompatible)

## Résumé

| Élément | État mesuré |
|---|---|
| CLI TensorSharp v3.3.0.0 `win-x64-cuda` | chargé firsthand sur po-2023, backend `GgmlCuda` |
| Cause racine héritée de c.419 (VAE au schéma Diffusers) | **confirmée par mesure des clés safetensors** |
| Fix prescrit par c.419 (swap vers la VAE au schéma legacy) | **appliqué — le blocage est levé** |
| Denoise 30 steps UniPC | exécuté de bout en bout |
| Artefacts MP4 | **3090** : `wan21_t2v_probe_3090.mp4`, 775 132 o, sha256 `e25e70f8…` — **3080 Ti** : `wan21_t2v_probe.mp4`, 531 651 o, sha256 `e58f42aa…` (tous deux h264 832×480 × 33 f @ 16 fps, 2,0625 s) |
| Identité GPU (acceptance 1) | **RTX 3090 visée par `CUDA_VISIBLE_DEVICES=0`** — `nvidia-smi` 5063 MiB / 100 %, CLI nommant `Device 0: RTX 3090` (24575 MiB) |
| Débit mesuré | 3090 : **124,4 s** (1,8 s/passe) · 3080 Ti : **194,2 s** (2,8 s/passe) — 1,56× |
| Verdict axe Vidéo | **`RECOVERABLE-LOCAL`, résolu** |

## 1. Le blocage hérité — ce que c.419 avait établi

Le cycle c.419 avait runtime-validé la CLI Wan (options `--video-dit|--video-vae|--video-text-encoder`,
`--video-frames`, `--fps`, `--flow-shift`, `--sampler`, `--video-mode` parsées ; DiT Wan2.1-T2V-1.3B
chargé, UMT5-XXL encodé, 30 steps de denoise complétés) puis **crashait au chargement de la VAE** :

```text
KeyNotFoundException: safetensors tensor not found: conv2.weight
   at TensorSharp.Vae.Wan.WanVaeWeights..ctor(...)
   at TensorSharp.Vae.Wan.WanVae.Load(...)
```

Son diagnostic : la source `ai-toolkit/wan2.1-vae` expose le **schéma Diffusers** (préfixes
`decoder.`/`encoder.`, nesting `down_blocks`/`up_blocks`/`mid_block`) alors que
`TensorSharp.Vae.Wan.WanVaeWeights` attend le **naming legacy** (`conv1`, `conv2`,
`decoder.middle.N`, `decoder.upsamples.N`, `decoder.head.0.gamma`). Verdict rendu : `NON MESURÉ`,
`RECOVERABLE-LOCAL` avec pour chemin de fix le swap vers une VAE au schéma legacy.

## 2. Mesure des clés — la cause racine est confirmée firsthand

Trois VAE sont présentes sur le disque de po-2023 (`C:/Users/jsboi/tensorsharp-investigation/models-wan/`).
Leur en-tête safetensors a été lu directement (8 octets de longueur + JSON), et chaque clé classée
par motif :

| Fichier | Taille | Clés | Clés schéma legacy | Clés schéma Diffusers |
|---|---|---|---|---|
| `wan_2.1_vae.safetensors` (celle qui crashait) | 253,8 MB | 194 | 96 | **167** |
| **`Wan2_1_VAE_bf16.safetensors`** | 253,8 MB | 194 | **174** | **0** |
| `Wan2.2_VAE.safetensors` | 2 818,8 MB | 196 | 176 | 0 |

Motifs comptés — legacy : `conv1`, `conv2`, `decoder.middle`, `decoder.upsamples`,
`encoder.downsamples`, `decoder.head` ; Diffusers : `decoder.conv_in`, `decoder.mid_block`,
`encoder.down_blocks`, `up_blocks`, `post_quant_conv`.

Les huit premières clés de `Wan2_1_VAE_bf16.safetensors` sont verbatim :

```text
conv1.bias, conv1.weight, conv2.bias, conv2.weight,
decoder.conv1.bias, decoder.conv1.weight, decoder.head.0.gamma, decoder.head.2.bias
```

`conv2.weight` — **exactement le tenseur dont l'absence faisait crasher c.419** — est présent.
La cause racine diagnostiquée par c.419 est donc confirmée, et le fichier qui la lève était
**déjà sur disque** : aucun téléchargement n'était nécessaire.

## 3. Le fix appliqué

Le probe c.419 est rejoué à l'identique, à une substitution près — `--video-vae` reçoit
`Wan2_1_VAE_bf16.safetensors` au lieu de `wan_2.1_vae.safetensors` :

```bash
CVD=0   # 0 -> RTX 3090 ; 1 -> RTX 3080 Ti (voir finding 3)
OUT=C:/Users/jsboi/tensorsharp-investigation/out/wan21_t2v_probe_3090.mp4

CUDA_VISIBLE_DEVICES=$CVD ./TensorSharp.Cli.exe --backend ggml_cuda --gpu-layers 99 \
  --model  C:/Users/jsboi/tensorsharp-investigation/models-wan/Wan2.1-T2V-1.3B-Q4_K_M.gguf \
  --video-vae C:/Users/jsboi/tensorsharp-investigation/models-wan/Wan2_1_VAE_bf16.safetensors \
  --video-text-encoder C:/Users/jsboi/tensorsharp-investigation/models-wan/umt5-xxl-encoder-Q4_K_M.gguf \
  --video-frames 33 --fps 16 --flow-shift 8.0 --sampler unipc --video-mode t2v \
  --seed 42 \
  --input C:/Users/jsboi/tensorsharp-investigation/out/prompt.txt \
  --output $OUT
```

La même commande a été passée deux fois, une par carte (`CVD=0` puis `CVD=1`), ce qui donne à
la fois l'artefact de l'acceptance 2 et le contrôle d'identité GPU de l'acceptance 1.

**Le crash VAE ne se reproduit pas** : la CLI annonce `Video companion override --video-vae -> …`,
charge le DiT (`architecture=wan`), encode le prompt, puis entre en denoise :

```text
Wan 2.1 T2V: 832x480x33f (9x30x52 = 14040 tokens), 30 steps, unipc, cfg 6, shift 8
[wan-timing] text-encode: 5620ms
[wan-timing] init: 91ms
Wan DiT: 30 blocks, dim=1536, heads=12, ffn=8960, in=16
```

## 4. Findings

1. **Le blocage de c.419 est un problème de source de VAE, pas de capacité.** Le fix ne demande
   aucun patch de TensorSharp ni de téléchargement : le schéma legacy est disponible dans
   `Wan2_1_VAE_bf16.safetensors`, déjà présente à côté du DiT.
2. **La documentation du CLI induit en erreur sur ce point précis.** L'aide de `--video-vae`
   nomme `wan_2.1_vae.safetensors` comme valeur attendue — c'est précisément le fichier au
   schéma Diffusers qui fait crasher le loader. Le nom de fichier est un piège : deux dépôts HF
   distincts portent ce basename avec deux schémas incompatibles.
3. **L'indexation CUDA est l'inverse de celle de `nvidia-smi`** — mesuré en A/B dans ce cycle, et
   c'est ce qui tranche l'acceptance 1. Avec `CUDA_VISIBLE_DEVICES=1` le CLI annonce
   `Device 0: NVIDIA GeForce RTX 3080 Ti Laptop GPU, VRAM: 16383 MiB` ; avec
   `CUDA_VISIBLE_DEVICES=0` il annonce `Device 0: NVIDIA GeForce RTX 3090, VRAM: 24575 MiB`.
   La 3090 s'obtient donc par `CVD=0`, **pas** par `CVD=1`. C'est cohérent avec le commit de
   l'axe Image (`feature/14707-tensorsharp-image-probe` : « CVD respecte dans l'ordre CUDA »),
   que c.257 laissait explicitement non testé pour la vidéo. `nvidia-smi` pris pendant le run
   `CVD=0` attribue la charge sans ambiguïté : index 1 (RTX 3090) à **5063 MiB / 100 %**, index 0
   (3080 Ti) à 0 MiB / 0 %.
4. **`--seed` est ignoré en mode vidéo.** La commande passait `--seed 42` ; le CLI annonce et
   journalise `seed 856751663` (et l'écrit jusque dans son message final). Le paramètre n'a pas
   d'effet sur ce chemin — l'axe Vidéo n'est donc pas reproductible bit-à-bit en l'état, et un
   second run ne se compare que statistiquement — c'est aussi pourquoi les deux artefacts ont des
   tailles différentes (531 651 o contre 775 132 o) pour des paramètres pourtant identiques. Les
   deux runs passaient bien `--seed 42` : le CLI a journalisé `seed 856751663` puis
   `seed 707057979`, deux valeurs distinctes tirées par lui.
5. **Le coût, et l'écart mesuré entre les deux cartes.** Le CLI avertit lui-même sur la taille de la requête : 60 passes DiT sur
   14 040 tokens, l'auto-attention en O(tokens²) dominant. Mesure : ~5,6 s par step
   (2,8 s cond + 2,8 s uncond) soit **194,2 s** au total, décodage VAE (20,0 s) inclus, pour
   33 frames en 832×480. La RTX 3090 fait le même travail en **124,4 s** (1,8 s/passe), soit
   **1,56×**, avec 5063 MiB occupés sur 24 576 : le plafond n'est pas la mémoire mais le débit
   de calcul — ce qui laisse le grain ouvert à un DiT 14B sans conclure sur sa VRAM.
6. **Le premier `.mp4` du dépôt ne s'introduit pas dans une PR d'investigation.** Le dépôt
   traque 1946 `.png` et **zéro `.mp4`** (`git ls-files "*.mp4"` → 0). L'artefact est donc laissé
   hors dépôt et cité par chemin, taille, sha256 et `ffprobe` — ce qui reste falsifiable sans
   créer un précédent binaire.

## 5. Bloc de reproduction

**Run 1 — `CUDA_VISIBLE_DEVICES=1` (RTX 3080 Ti Laptop GPU, 16 GB)** — le run initial

```text
ggml_cuda_init: found 1 CUDA devices
  Device 0: NVIDIA GeForce RTX 3080 Ti Laptop GPU, VRAM: 16383 MiB
```

Fin de run verbatim :

```text
[wan-timing] denoise-last-step: 0ms
[wan] denoise: 60 DiT passes, 2,8s mean
[wan] …vae-decode (33 frames at 832x480, band 1/1) 5s in this pass, 180s total
[wan-timing] vae-decode: 20023ms
[wan-timing] total: 194,2s
Saved 832x480 x 33 frames (h264, 16 fps, seed 856751663) to
  C:/Users/jsboi/tensorsharp-investigation/out/wan21_t2v_probe.mp4 in 194,2s
02:12:43 info: TensorSharp.Cli[1701] tensorsharp-cli completed
EXIT=0
```

Artefact `wan21_t2v_probe.mp4` — 531 651 octets,
sha256 `e58f42aac191e636be79b63cb17eccdb463f71970726ffb8a8cf3aa1d121c2e7`.
`ffprobe` : `codec_name=h264`, `width=832`, `height=480`, `pix_fmt=yuv420p`,
`r_frame_rate=16/1`, `nb_frames=33`, `duration=2.062500`.

**Run 2 — `CUDA_VISIBLE_DEVICES=0` (RTX 3090, 24 GB)** — même commande, seul l'index change

Ligne d'identité GPU (`ggml_cuda_init`) :

```text
ggml_cuda_init: found 1 CUDA devices (Total VRAM: 24575 MiB):
  Device 0: NVIDIA GeForce RTX 3090, compute capability 8.6, VMM: yes, VRAM: 24575 MiB
```

Fin de run verbatim :

```text
[wan-timing] text-encode: 2574ms
[wan-timing] init: 87ms
[wan] denoise: 60 DiT passes, 1,8s mean
[wan-timing] vae-decode: 12915ms
[wan-timing] total: 124,4s
Saved 832x480 x 33 frames (h264, 16 fps, seed 707057979) to
  C:/Users/jsboi/tensorsharp-investigation/out/wan21_t2v_probe_3090.mp4 in 124,4s
EXIT=0
```

Artefact `wan21_t2v_probe_3090.mp4` — 775 132 octets,
sha256 `e25e70f8325de1929bc782690c8260388bc38d00d72ed5fb335b889b1ac65387`.
`ffprobe` : mêmes champs que le run 1 (`h264`, 832×480, `yuv420p`, `16/1`, 33 frames,
2,0625 s) — seule la taille diffère, cohérent avec deux seeds distincts.

`nvidia-smi` échantillonné pendant ce run (t+40 s et t+75 s) :

```text
0, NVIDIA GeForce RTX 3080 Ti Laptop GPU, 0 MiB, 0 %
1, NVIDIA GeForce RTX 3090, 5063 MiB, 100 %
```

C'est la mesure qui satisfait l'acceptance 1 : la 3090 est l'index **1** côté `nvidia-smi`
mais s'obtient par `CUDA_VISIBLE_DEVICES=0` — l'ordre CUDA n'est pas l'ordre `nvidia-smi`,
et chaque run nomme l'autre carte quand l'index change, ce qui clôt le contrôle A/B.

## 6. Verdict

**Axe Vidéo Wan 2.1 — `RECOVERABLE-LOCAL`, et le recouvrement est fait.**

Le blocage hérité de c.419 n'était pas une limite de capacité mais un choix de fichier : la VAE
au schéma Diffusers. Avec `Wan2_1_VAE_bf16.safetensors` (schéma legacy, 0 clé Diffusers), la
chaîne s'exécute **de bout en bout et sort en code 0** — DiT chargé, prompt encodé, 30 steps
UniPC, 33 frames décodées, conteneur h264 écrit. Le chemin de fix que c.419 avait prescrit est
donc validé, et il ne coûtait aucun téléchargement : le bon fichier était déjà à côté du mauvais.

Ce que ce cycle **établit** est structurel : le pipeline va au bout, l'artefact est un h264
832×480 de 33 frames à 16 fps, conforme à la requête passée, et la 3090 est bien la carte visée.

Ce que ce cycle **n'établit pas**, et qu'il ne faut pas lire dans ces lignes :

- **L'inspection visuelle du clip.** L'acceptance 2 de l'issue la route explicitement vers « une
  lane MiniMax ou ai-01 ». La lane po-2023 est animée par un modèle sans vision : elle ne juge
  pas le rendu, elle établit que le fichier existe, qu'il est bien formé et qu'il correspond aux
  paramètres demandés. Le contenu (fidélité au prompt, cohérence temporelle) reste à regarder.
- **La comparaison de parité avec le stack Python/Docker (acceptance 4).** Aucune mesure de
  parité ComfyUI-Wan n'a été prise dans ce cycle, contrairement à l'axe Image où #14549 l'avait
  faite. Ce qui est mesuré ici est un coût et une chaîne, pas un écart de qualité entre moteurs.
- **La reproductibilité.** `--seed` étant ignoré, deux runs ne se comparent pas à graine fixée.

Le grain reste donc partiellement ouvert sur ces trois points (QA visuel routé, parité non
mesurée), mais le blocage technique qui fondait le `NON MESURÉ` de c.419 est levé, et le verdict
passe de « non mesuré » à **mesuré, artefact produit**.

## 7. Parité ComfyUI-Wan même-machine/même-prompt (critère 4) — mesure livrée

**Date** : 2026-10-09 (lane `myia-po-2023:CoursIA`, claim c.5963436956 amendé c.6085772244).
Équivalent vidéo de la parité Image c.272-c.273 du ledger parent. Jambe restante nommée par le
preflight ai-01 du 2026-10-09T12:44Z (critère 4 « axe Video NON COUVERT »).

### Setup — la prémisse « ComfyUI Wan non installé » était périmée

Le ledger parent (:965) disait « ComfyUI Wan non installé sur cette machine — hors fenêtre
worker, ~14 GB dl + redéploiement ». Mesure : le conteneur `comfyui-qwen` (ComfyUI **0.37.2**,
Wan natif dans le core, pytorch 2.14.0+cu126) portait **déjà** les trois composants dans son
volume `docker-configurations/shared/models/` — aucun des ~14 GB annoncés n'était à télécharger :

| Composant | Fichier (volume ComfyUI) | sha256 | Côté TensorSharp (probe §5) |
|---|---|---|---|
| DiT | `diffusion_models/wan2.1_t2v_1.3B_fp16.safetensors` (2,84 GB) | `be531024…` | `Wan2.1-T2V-1.3B-Q4_K_M.gguf` (982 MB, `1e22a681…`) |
| VAE | `vae/wan_2.1_vae.safetensors` (254 MB, schéma Diffusers) | `2fc39d31…` | `Wan2_1_VAE_bf16.safetensors` (schéma legacy) |
| TE | `text_encoders/umt5_xxl_fp8_e4m3fn_scaled.safetensors` (6,7 GB) | `c3355d30…` | `umt5-xxl-encoder-Q4_K_M.gguf` (`17cf97a5…`) |

**Le split de format EST le finding** : les deux stacks exigent des formats incompatibles du
même modèle — TensorSharp veut GGUF (DiT/TE) + VAE legacy, ComfyUI veut safetensors + VAE
Diffusers. La parité stricte n'est atteignable que sur le DiT/TE GGUF (copiés dans le volume,
sha256 vérifiés identiques de part et d'autre — leçon c.273 : le hash fait foi, pas le nom) ;
la VAE ne peut jamais être le même fichier des deux côtés.

### Workflow (API-format, patron c.272)

`UnetLoaderGGUF(Wan2.1-T2V-1.3B-Q4_K_M.gguf)` → `ModelSamplingSD3(shift=8.0)` ← `--flow-shift 8.0`
· `CLIPLoaderGGUF(umt5-xxl-encoder-Q4_K_M.gguf, type=wan)` · `VAELoader(wan_2.1_vae.safetensors)`
· `EmptyHunyuanLatentVideo(832×480, 33 f)` · `KSampler(seed=42, steps=30, cfg=6.0, uni_pc, simple,
denoise=1.0)` · `VAEDecode` → `CreateVideo(fps=16)` → `SaveVideo`. Paramètres alignés au bloc §5 :
« 832x480x33f, 30 steps, unipc, cfg 6, shift 8 » — prompt positif **verbatim**, négatif vide.
Serveur : `cuda:0 = RTX 3090` (24 GB, logs de démarrage du conteneur), même carte que le probe
TensorSharp. Timings serveur extraits de `/history` (`status.messages` :
`execution_start → execution_success` en ms d'horloge serveur), conciliés au wall client ; VRAM
échantillonnée côté hôte (`nvidia-smi`, 2,5 s) pendant le run.

**Leçon API SaveVideo (v0.37)** : l'entrée `format` est un combo dynamique V3 — la valeur doit
être une **clé d'option exacte en minuscules** (`mp4`) et le codec imbriqué se sérialise
`format.codec` (`auto`). Une valeur hors options (`"Auto"`) est **silencieusement dropée** par la
validation et le nœud échoue à l'exécution en `TypeError: missing 1 required positional
argument: 'format'` — aucun message d'erreur ne nomme la vraie cause.

### Résultats

| Voie | DiT | TE | VAE | cfg | Run | Wall client | Server exec | Pic VRAM 3090 | Sortie |
|---|---|---|---|---|---|---|---|---|---|
| TensorSharp.Cli §5 | Q4_K_M | Q4_K_M | legacy bf16 | 6 | froid (proc. neuf) | 124,4 s | n/a (CLI, 60 passes DiT 1,8 s mean) | 5063 MiB steady | MP4 775 Ko, std frame 75,0-75,3 |
| ComfyUI 0.37.2 run A′ | **Q4_K_M (même sha256)** | Q4_K_M (même sha256) | Diffusers | 6 | froid (post-restart, 0 nœud caché) | 224,3 s | 220,7 s | 20 776 MiB | MP4 681 Ko `eca6ea62…`, std 95,2-96,0 |
| ComfyUI 0.37.2 run B′ | fp16 natif | fp8 scaled | Diffusers | 6 | chaud (2 nœuds cachés, suit A′) | 163,7 s | 161,2 s | 22 094 MiB | MP4 612 Ko `06e0047b…`, std 91,4-92,0 |
| ComfyUI 0.37.2 (datapt) | Q4_K_M (même sha256) | Q4_K_M (même sha256) | Diffusers | 1 | froid (post-restart, 0 nœud caché) | 169,1 s | 164,4 s | 23 282 MiB | MP4 1 488 Ko `f1e7276e…`, std 69,8-71,9 |
| ComfyUI 0.37.2 (datapt) | fp16 natif | fp8 scaled | Diffusers | 1 | froid (2 nœuds cachés : VAE + latent) | 128,4 s | 123,4 s | 23 230 MiB | MP4 1 275 Ko `69ef7e9d…`, std 72,0-73,1 |

### Déterminisme — le contrepoint au §6

Deux exécutions complètes indépendantes du workflow q4 cfg 1 (processus serveur **redémarré**
entre les deux, seconde à `execution_cached: []`) produisent des MP4 **byte-identiques**
(sha256 `f1e7276e99b2d0063f75b5a9256e6cf545d0fd4d4090e5ff05d44ae69c983f18`, 1 488 189 o
chacun). Le `--seed` **ignoré** côté TensorSharp (§6, seed dérivée 856751663) ne l'est **pas**
côté ComfyUI : la reproductibilité, troisième point ouvert du §6, est tenue par ce stack —
vérifiée à cfg 1 ; les runs cfg 6 héritent du même mécanisme de seed mais n'ont pas été
re-doublés (coût GPU, apport informationnel nul après la preuve à cfg 1).

### Analyse et verdict

- **À paramètres alignés** (DiT/TE Q4 sha256-identiques, cfg 6, 30 steps, shift 8, 832×480×33 f,
  même RTX 3090, froid des deux côtés) : TensorSharp 124,4 s / 5 063 MiB — ComfyUI 224,3 s /
  20 776 MiB. **TensorSharp est 1,80× plus rapide et 4,1× plus économe en VRAM** sur ce bloc.
- L'écart est structurel, pas accidentel : TensorSharp exécute le DiT **quantifié** (ggml_cuda,
  Q4 natif) et offloade le TE sur CPU (5,1 GiB steady) ; ComfyUI **déquantise** le GGUF en fp16
  en VRAM et garde TE+VAE résidents (bande 20,8-23,3 GiB selon les runs). La parité de fichiers
  de poids ne vaut pas parité de chemin d'exécution — c'est le second finding de la mesure.
- **Contrôle de cohérence interne** : le delta cfg 6 − cfg 1 sur q4 froid (224,3 − 169,1 =
  55,2 s ≈ 30 passes uncond × 1,84 s) recoupe le 1,8 s/passe mesuré côté TensorSharp — les deux
  stacks paient la passe uncond au même tarif ; l'écart global vient du chargement et du chemin
  de poids, pas du sampler.
- **fp16 vs q4** : à cfg 6 (B′ chaud 161,2 s vs A′ froid 220,7 s — conditions de charge
  différentes, comparaison indicative seulement) et à cfg 1 (froids tous deux : fp16 123,4 s vs
  q4 164,4 s) — le chemin fp16 natif est plus rapide que la déquant GGUF dans ComfyUI.
- **Verdict critère 4** : **mesuré** — comparaison honnête même-machine/même-prompt livrée, avec
  split de format VAE documenté et écart débit/VRAM chiffré. Pas de gagnant absolu : TensorSharp
  = débit + efficacité VRAM + exécution quantifiée fidèle au fichier ; ComfyUI = déterminisme
  byte-level + écosystème de nœuds. La QA visuelle (critère 2) reste routée vers une lane vision.

### QA visuel (critère 2) — routage préparé

Les 2 clips TensorSharp §5 + les 4 clips ComfyUI ci-dessus passent le contrôle objectif de
non-dégénérescence (std luma par frame : 75,03-75,28 clip 3090 · 68,59-72,26 clip 3080 Ti ·
69,81-71,90 q4 cfg 1 · 72,04-73,07 fp16 cfg 1 · 95,20-96,00 q4 cfg 6 · 91,41-92,01 fp16 cfg 6 —
un rendu NaN/uniforme serait à 0). Les 6 MP4 + frames PNG + stats sont stageés pour une lane
vision : `G:\Mon Drive\MyIA\IA\wan-video-qa-15159\`. La lane exécutante (GLM, sans vision) ne
juge pas le rendu — fidélité au prompt et cohérence temporelle restent à regarder.
