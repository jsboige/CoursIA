# TensorSharp Multimodal — investigation #14549

Investigation de la voie TensorSharp pour les axes **Image** (Qwen-Image-Edit) et **Vidéo** (Wan 2.1/2.2) sur l'eGPU RTX 3090 24 GB de `myia-po-2023`. Issue de référence : [#14549](https://github.com/jsboige/CoursIA/issues/14549).

## Contexte

`#14549` est ouvert comme **successeur de #12353** pour ne pas fermer l'axe multimodal sur un `N/A — gated hardware` que le matériel de la flotte contredit. Le verdict correct selon `.claude/rules/sota-not-workaround.md` est `RECOVERABLE-MACHINE` : « a marché / marche sur une machine SPECIFIQUE avec le bon env → router vers cette machine + re-exec ».

Cette investigation vise à vérifier les **4 critères d'acceptance** de #14549 :

1. **Binaire chargé firsthand** sur po-2023 avec l'eGPU 3090 : release `win-x64-cuda` de TensorSharp, `nvidia-smi` citant la 3090, VRAM occupée relevée.
2. **Au moins un des deux axes exécuté de bout en bout** : une génération Qwen-Image-Edit **ou** un clip Wan 2.1/2.2, artefact produit et inspecté à l'œil (QA visuel — lane MiniMax ou ai-01).
3. **Verdict écrit par axe**, un des cinq de `sota-not-workaround.md` : `SOTA-OK` / `RECOVERABLE-LOCAL` / `RECOVERABLE-MACHINE` / `RECOVERABLE-USER-HAND` / `INTRINSIC`.
4. **Comparaison honnête à l'existant** : ce que le stack Python/Docker fait déjà pour le même axe, et ce que la voie .NET apporte ou coûte.

## Acceptance #1 — binaire chargé firsthand (2026-09-05 03:38Z)

Mesure `nvidia-smi --query-gpu=index,name,memory.used,memory.total --format=csv,noheader` après lancement de `TensorSharp.Cli.exe --backend ggml_cuda --gpu-layers 99 --help` :

```
0, NVIDIA GeForce RTX 3080 Ti Laptop GPU, 0 MiB, 16384 MiB
1, NVIDIA GeForce RTX 3090,                625 MiB, 24576 MiB
```

- **GPU ciblé** : index 1 = RTX 3090 24 GB (eGPU confirmée, le GPU 0 = RTX 3080 Ti Laptop GPU = iGPU)
- **Sélection** : `CUDA_VISIBLE_DEVICES=1` force le runtime CUDA à ne voir que le GPU 1
- **VRAM occupée au repos** : **625 MiB** = runtime .NET + bindings CUDA natifs (`TensorSharp.Backends.Cuda.dll` + `GgmlOps.dll`)
- **Aucune erreur CUDA** : le chargement du CLI ne lève ni `DllNotFoundException` ni `CUDA_ERROR_NO_DEVICE`

## Artefacts mesurés

- `mesure_vram_initial.json` : sortie verbatim de `nvidia-smi` après chargement CLI
- `cli_help.txt` : sortie verbatim de `TensorSharp.Cli.exe --help`
- (à venir) `cli_run_<modele>.log` : log d'exécution avec timings et prompt effectif

## Références

- Issue : https://github.com/jsboige/CoursIA/issues/14549
- TensorSharp upstream : https://github.com/zhongkaifu/TensorSharp
- TensorSharp getting started : https://tensorsharp.ai/getting-started.html
- TensorSharp models image : https://tensorsharp.ai/models-image.html
- HuggingFace DiT : https://huggingface.co/unsloth/Qwen-Image-Edit-2511-GGUF
- HuggingFace text encoder : https://huggingface.co/unsloth/Qwen2.5-VL-7B-Instruct-GGUF
- HuggingFace VAE : https://huggingface.co/QuantStack/Qwen-Image-Edit-GGUF (VAE/Qwen_Image-VAE.safetensors)
- HuggingFace Lightning LoRA : https://huggingface.co/lightx2v/Qwen-Image-Edit-2511-Lightning

## Lane

`myia-po-2023:CoursIA-2` (routage verbatim body #14549). Aucune autre lane ne bloque (`stale_claims: []` à l'instant `T0`).
