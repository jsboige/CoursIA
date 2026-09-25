# Workflows Qwen-Image 2.1 (référence nomadoor) — issue #17334, Epic #17234

Les 12 workflows de référence publiés par
[ComfyUI nomadoor](https://comfyui.nomadoor.net/en/basic-workflows/qwen-image-2-1/)
pour Qwen-Image 2.1, versionnés tels quels (format UI ComfyUI, non modifiés).
Ils consomment **exactement** le palier INT8 hébergé par #17266 :
`qwen_image_2.1_int8_convrot.safetensors` (diffusion),
`qwen3vl_8b_int8_convrot.safetensors` (text encoder),
`qwen_image_2.1_vae_bf16.safetensors` (VAE) — voir `QWEN_IMAGE_21_MODELS`
dans [`scripts/genai-stack/commands/models.py`](../../commands/models.py).

Consommation : l'instance hébergée `comfyui-qwen`
(`https://qwen-image-edit.myia.io`, auth `COMFYUI_AUTH_TOKEN`).

## Couverture des nœuds par workflow

Analyse mécanique (`cnr_id` + type par nœud) — `core` = nœud natif ComfyUI :

| Workflow | Nœuds non-core ou nouveaux | Exécutable sur l'instance ? |
|---|---|---|
| `text2image` | — (100 % core) | bloqué : le VAE 2.1 est routé en classe WanVAE (erreur mesurée, voir « État mesuré ») |
| `text2image_rgba` | — (100 % core, VAE alpha) | bloqué (idem) |
| `ref2image` | `TextEncodeQwenImage21`, `LoadImage` | bloqué : `TextEncodeQwenImage21` absent de `/object_info` (mesuré) |
| `image_edit` | `TextEncodeQwenImage21`, `GetImageSize`, `ResizeImageMaskNode` | bloqué (idem) |
| `image_edit_local` | idem `image_edit` | bloqué (idem) |
| `image_edit_local_mask` | idem + `MaskToImage`, `PreviewImage` | bloqué (idem) |
| `image_edit_openpose` | idem + `OpenposePreprocessor` (pack controlnet_aux) | non sans custom node |
| `image_edit_upscale` | idem `image_edit` | bloqué (idem) |
| `outpainting` | `TextEncodeQwenImage21`, `LoadImage` | bloqué (idem) |
| `panorama` | idem + `PanoramaPreview` | bloqué (idem) |
| `subject_extraction` | idem `image_edit` | bloqué (idem) |
| `layer_decomposition` | `ComfyMath*`, `Switch`, boucles, `TextGenerate`, subgraph | non sans custom nodes (ComfyMath, Logic Utils) |

### État mesuré (2026-09-25, instance `comfyui-qwen`)

Le support natif de Qwen-Image 2.1 (nœud `TextEncodeQwenImage21`, détection
du VAE via `modelspec.architecture: qwen_image_2.1_vae`) a été ajouté à
l'éditeur dans la version 0.37.0. L'instance hébergeant le palier INT8 tourne
en 0.36.0 : mesure firsthand —

- `POST /prompt` du workflow `text2image` : validation acceptée, puis erreur
  d'exécution au `VAELoader` (`size mismatch for WanVAE`, conv 4D du
  checkpoint contre conv 5D vidéo attendue) — le routeur de classe VAE de
  0.36.0 ne connaît pas `qwen_image_2.1_vae` ;
- `GET /object_info` : `TextEncodeQwenImage21` absent.

Débloquer la série entière = mettre à jour le service vers 0.37.0 ou plus
récent, puis redémarrer. Les workflows 100 % core redeviennent alors
exécutables sur le même ensemble de nœuds que les notebooks Qwen-Image-Edit
existants (`01-5`, `01-5b`).

## Réglages de référence (extraits des JSON)

- `KSampler` : 25 steps, `cfg = 1.0`, `euler` / `simple` — modèle-distillé :
  le négatif passe par `ConditioningZeroOut`, pas de prompt négatif factice
  (même discipline que le 03-4 Krea 2) ;
- la page nomadoor note que **le seed change beaucoup le résultat** et que la
  résolution aussi — point repris en démonstration dans le notebook `01-5c` ;
- `ResolutionSelector` (core) pilote `EmptyLatentImage` en mégapixels
  (référence mesurée nomadoor : 121 s à 4 MP sur RTX 4070 Ti 12 Go).

## Provenance

Téléchargés le 2026-09-25 depuis
`https://comfyui.nomadoor.net/workflows/basic-workflows/qwen-image-2-1/<nom>.json`
— checksums dans l'historique Git. Toute adaptation locale
(substitution de nœuds custom → core) se fait **en copie déclarée**, jamais
en réécriture des originaux — ils sont la référence de l'éditeur.
