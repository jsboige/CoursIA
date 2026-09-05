# Plan d'exécution acceptance #2 — TensorSharp multimodal

Une fois le téléchargement du text encoder Qwen2.5-VL-7B-Instruct-Q4_K_M.gguf terminé (cible 4.68 GB), exécuter dans l'ordre :

## Étape 1 — Vérifier intégrité GGUF (avant inférence)

```bash
cd $HOME/tensorsharp-investigation
ls -la models/Qwen2.5-VL-7B-Instruct-Q4_K_M.gguf
sha256sum models/Qwen2.5-VL-7B-Instruct-Q4_K_M.gguf  # > 5 minutes sur 5 GB
```

Attendu : taille 4919908992 bytes, sha256 imprimable mais on ne le confrontera pas à une référence (HF ne sert pas de sha256 sur le listing). On note la taille + l'archive.

## Étape 2 — Test minimal : inférence texte-only (sanity check GPU)

But : valider que le pipeline CUDA charge un GGUF sur la 3090 et fait une inférence triviale.

```bash
cd $HOME/tensorsharp-investigation
CUDA_VISIBLE_DEVICES=1 ./TensorSharp.Cli.exe \
    --backend ggml_cuda \
    --model ./models/Qwen2.5-VL-7B-Instruct-Q4_K_M.gguf \
    --prompt "What is 1+1? Reply with a single number, nothing else." \
    --max-tokens 16 \
    --gpu-layers 99 \
    --output /tmp/ts_test_output.txt 2>&1 | tee /tmp/ts_test_run.log
nvidia-smi --query-gpu=index,name,memory.used --format=csv,noheader
```

Attendu : réponse "2", VRAM occupée ~5-6 GB (modèle Q4_K_M 4.7 GB + overhead CUDA).

## Étape 3 — Mesure VRAM après chargement GPU

Comparer VRAM occupée avant/après inférence. La persistance du modèle en VRAM dépend du backend — ggml_cuda garde les poids chargés tant que le process vit.

## Étape 4 — (si temps le permet) Télécharger DiT Q4_K_M + mmproj

```bash
curl -L -o models/qwen-image-edit-2511-Q4_K_M.gguf "https://huggingface.co/unsloth/Qwen-Image-Edit-2511-GGUF/resolve/main/qwen-image-edit-2511-Q4_K_M.gguf?download=true"
curl -L -o models/mmproj-BF16.gguf "https://huggingface.co/unsloth/Qwen2.5-VL-7B-Instruct-GGUF/resolve/main/mmproj-BF16.gguf?download=true"
```

Cible : ~14 GB de plus. Réaliste seulement si fenêtre large.

## Étape 5 — Édit d'image réel

```bash
# Image source : créer une image de test simple (fond uni + texte) ou utiliser une du dossier
python -c "from PIL import Image, ImageDraw; im=Image.new('RGB',(512,512),(80,120,200)); d=ImageDraw.Draw(im); d.text((20,20),'hello world',fill=(255,255,255)); im.save('/tmp/ts_test_image.png')"

CUDA_VISIBLE_DEVICES=1 ./TensorSharp.Cli.exe \
    --backend ggml_cuda \
    --model ./models/qwen-image-edit-2511-Q4_K_M.gguf \
    --mmproj ./models/mmproj-BF16.gguf \
    --image /tmp/ts_test_image.png \
    --prompt "Add a small red heart in the upper-right corner" \
    --output /tmp/ts_edited.png \
    --gpu-layers 99 2>&1 | tee /tmp/ts_edit_run.log
```

Attendu : fichier PNG modifié, ~12 GB VRAM (DiT Q4_K_M + text encoder + mmproj).

## Étape 6 — Inspection visuelle

Sauver l'image éditée dans le worktree, puis ouvrir avec une lane MiniMax/ai-01 (vision-only QA) pour validation du rendu réel.

## Critères d'arrêt

- Si étape 2 échoue (CUDA ne charge pas le GGUF) → verdict `RECOVERABLE-MACHINE` documenté, sortie investigation.
- Si étape 2 OK mais étape 5 échoue → verdict `SOTA-OK` axe Texte, `INTRINSIC` axe Image documenté avec checklist 6 axes.
- Si toutes étapes OK → verdict `RECOVERABLE-MACHINE` (chemin .NET viable, comparaison perf vs Python/Docker pour trancher).
