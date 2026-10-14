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
(`https://qwen-image-edit.myia.io`). L'API est protégée par **ComfyUI-Login** :
`Authorization: Bearer <jeton>`, le jeton étant la **première ligne du fichier
de mot de passe** du service — le hash bcrypt, pas le mot de passe en clair.
C'est exactement ce que produit `GenAIAuthManager.get_auth_header()` côté
dépôt (`scripts/genai-stack/core/auth_manager.py`), qui est donc la bonne voie
pour un client de ce dépôt.

## Exécutabilité réelle (mesuré le 2026-09-25, instance `comfyui-qwen`)

L'instance tourne en **ComfyUI 0.37.2** : le support natif de Qwen-Image 2.1
(nœud `TextEncodeQwenImage21`, détection `qwen_image_2.1_vae`) y est présent —
`/object_info` publie 981 nœuds. La mesure précédente, prise en 0.36.0, est
**périmée** : le blocage qu'elle décrivait (VAE routé en classe WanVAE,
`TextEncodeQwenImage21` absent) est levé par la montée de version.

Ces JSON sont au format **UI**. Les soumettre à `POST /prompt` exige une
conversion UI → API, portée par
[`WorkflowManager.convert_ui_to_api`](../../core/comfyui_client.py) : elle
prend `object_info` en argument et **refuse** tout appariement qu'elle ne peut
pas établir, plutôt que de produire un graphe faux en silence.

| Workflow | Conversion UI→API | Exécutable sur l'instance ? |
|---|---|---|
| `text2image` | oui (10 nœuds) | **oui — prouvé par une génération**, voir ci-dessous |
| `text2image_rgba` | oui (10 nœuds) | oui — 10 nœuds, tous présents |
| `ref2image` | oui (12 nœuds) | oui — `LoadImage` et `TextEncodeQwenImage21` présents |
| `outpainting` | oui (10 nœuds) | oui — mêmes nœuds que `ref2image` |
| `image_edit`, `image_edit_local`, `image_edit_local_mask`, `image_edit_upscale`, `subject_extraction` | **non** | nœuds présents, mais `ResizeImageMaskNode` porte un **combo dynamique** (`resize_type`) dont les sous-widgets ne sont pas déclarés par `/object_info` |
| `image_edit_openpose` | non | idem, plus `OpenposePreprocessor` absent (pack controlnet_aux) |
| `panorama` | non | `PanoramaPreview` absent de l'instance |
| `layer_decomposition` | non | `Reroute` + subgraph, `ComfyMath*`, `Switch` |

### Preuve de génération

`qwen_image_2_1_text2image.json` **tel que versionné**, converti contre
l'`object_info` vivant puis soumis :

- `prompt_id` `0d28b37a-6d7f-4e94-9b72-fd0af38496d5`, statut `success` en **330 s** ;
- sortie `ComfyUI_00013_.png`, **1664 × 2496** (4,2 MP), 5 109 070 octets ;
- pile réellement chargée (relevée dans `/history`) :
  `UNETLoader` → `qwen_image_2.1_int8_convrot.safetensors`,
  `CLIPLoader` → `qwen3vl_8b_int8_convrot.safetensors` (`type: qwen_image`),
  `VAELoader` → `qwen_image_2.1_vae_bf16.safetensors` ; `KSampler` 25 steps,
  `cfg 1.0`, `euler` / `simple` — les réglages de référence, inchangés.

La conversion traite le widget d'upload de `LoadImage` (valeur en fin de liste,
sans équivalent API). Restent non supportés les sous-widgets du combo dynamique
de `ResizeImageMaskNode`, qui s'intercalent **au milieu** des autres widgets :
rien ne permet de les apparier sans les deviner, donc les sept workflows qui
l'utilisent sont refusés nommément.


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
