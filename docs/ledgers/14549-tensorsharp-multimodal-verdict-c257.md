# Issue #14549 — verdict c.257 — TensorSharp multimodal axe Image/Vidéo

**Issue** : #14549 (investigation(genai-dotnet): axe multimodal de #12353 — TensorSharp Qwen-Image-Edit / Wan video sur eGPU RTX 3090)
**Statut investigation c.257** : partiellement terminée — acceptance #1 OK + acceptance #2 texte OK ; image/vidéo non tentées (taille download hors fenêtre cron 30 min)
**Lane** : myia-po-2023 (verbatim body #14549 « seule machine de la flotte portant à la fois la VRAM requise »)
**Claim** : commentaire #5548472386 + amend #5548505745

## Récit

#14549 demandait un verdict par axe sur TensorSharp pour Image et Vidéo. #12353 avait tranché l'axe Texte sur LLamaSharp (rejet implicite TensorSharp Texte). Axe multimodal restait non tranché — qualifié `N/A — gated hardware` à tort (qualifié sur GPU 16 GB alors que la flotte a une RTX 3090 24 GB éligible).

c.257 a procédé à la première investigation firsthand :

1. **Acceptance #1** : binaire chargé sur 3090 (vérifié `nvidia-smi` + VRAM 625 MiB idle). Sortie verbatim dans `mesure_vram_initial.json`.
2. **Acceptance #2 — axe Texte** : inférence CUDA sur `Qwen2.5-VL-7B-Instruct-Q4_K_M.gguf` (4.683 GB) avec réponse correcte (`1 + 1 equals 2.`), decode 37.5-40.5 tok/s comparable à LLamaSharp (36.57 tok/s c.12353). Mesure verbatim dans `mesure_inference_text.json` + log `inf_test_run.log`.
3. **Acceptance #2 — axe Image** : non tenté (DiT Q4_K_M + mmproj BF16 + VAE + Lightning LoRA = ~14 GB supplémentaires hors fenêtre cron).
4. **Acceptance #2 — axe Vidéo** : non tenté (Wan 2.1/2.2 tout neuf v3.3.0.0, doc sparse, pas d'exécution firsthand).

## Verdict par axe

### Axe Texte : `RECOVERABLE-MACHINE` (mais perdant vs LLamaSharp)

- **Mesure** : 37.5-40.5 tok/s decode (c.257 TensorSharp) vs 36.57 tok/s GPU (c.12353 LLamaSharp) → parité .NET.
- **Verdict SOTA-OK** pour le binaire : CUDA + GGUF chargent et tournent sur 3090.
- **Verdict REJET** pour le choix de TensorSharp : LLamaSharp reste préféré (NuGet officiel 3786★, bus factor sain, NuGet mature vs single-maintainer zhongkaifu).
- **Conclusion** : axe Texte **hors-scope** de ce PR, déjà tranché par #12353.

### Axe Image (Qwen-Image-Edit) : `INTRINSIC` pressenti (à confirmer c.258+)

- **Mesure constructeur** : 40.44s sur image 544×1184 (Q2_K DiT + 4-step Lightning LoRA).
- **Mesure Python/Docker ComfyUI (référence)** : ~25-30s sur la même 3090 (à reconfirmer).
- **Verdict INTRINSIC pressenti** : si la mesure TensorSharp confirme la latence constructeur, la voie .NET n'apporte rien que Python/Docker ne fasse déjà, et le coût (bus factor, doc sparse, latence moindre) l'emporte sur le gain (interop .NET).
- **À reconfirmer** : exécution firsthand DiT Q4_K_M + mmproj BF16 + VAE + Lightning LoRA, mesure latence sur la même image que la mesure ComfyUI.

### Axe Vidéo (Wan 2.1/2.2) : `INTRINSIC` ou `RECOVERABLE-MACHINE` (à trancher)

- **Hésitation** : Wan 2.1/2.2 = capacité ajoutée à v3.3.0.0 (30 août 2026), doc sparse, bus factor single-maintainer. Sans exécution firsthand bout en bout, le verdict reste `INTRINSIC` pressenti par défaut.
- **À reconfirmer** : exécution firsthand Wan 2.1/2.2 sur la 3090, mesure qualité + latence.

## Comparaison honnête — stack Python/Docker GenAI Image vs TensorSharp .NET

| Métrique | Python/Docker ComfyUI (po-2023) | TensorSharp .NET |
|---|---|---|
| Latence 544×1184 (Lightning 4-step) | ~25-30s (à reconfirmer) | 40.44s (constructeur, Q2_K) |
| Bus factor | communauté ComfyUI massive | single-maintainer + 3 contributeurs |
| Documentation | abondante (workflows, custom nodes, etc.) | sparse (1 page getting started, 1 page modèles) |
| Modèles supportés | ComfyUI natif + custom nodes HF | Qwen-Image-Edit GGUF, Wan 2.1/2.2 GGUF |
| Interop avec reste du dépôt | Docker standalone | Natif C#/.NET |

**Lecture** : si la mesure TensorSharp confirme la latence constructeur, la voie .NET n'apporte rien que Python/Docker ne fasse déjà. Verdict `INTRINSIC` sur axe Image/Vidéo dans son ensemble.

## Limitations trouvées (livrables de l'investigation)

1. **`CUDA_VISIBLE_DEVICES=1` n'est PAS respecté** par `TensorSharp.ggml_cuda`. Le binaire cible GPU 0 (RTX 3080 Ti Laptop GPU) par défaut. Le flag `--gpu-device 1` est **nécessaire** pour cibler le GPU 1 (eGPU RTX 3090 24 GB). C'est un **silent footgun** pour les workflows multi-GPU.
2. **`--prompt` semble ignoré** par le CLI quand `--input` n'est pas fourni — le prompt par défaut `What is 1+1?` est toujours utilisé. Pas de moyen simple de passer un prompt custom en mode one-shot.
3. **Warmup long** : ~17 s de compilation des kernels CUDA au premier run. Ré-utilisable pour runs successifs.

## Checklist 6 axes (en cas de verdict `INTRINSIC` final)

Si l'investigation c.258+ confirme `INTRINSIC` axe Image/Vidéo :

1. **Binding .NET / NuGet** : `tensorsharp-cli-3.3.0.0-win-x64-cuda.zip` disponible (671 MB), mais packaging = .zip, pas NuGet natif.
2. **`P/Invoke`** : GGUF inference via `GgmlOps.dll` (531 MB) + bindings CUDA via `TensorSharp.Backends.Cuda.dll`. **P/Invoke actif**.
3. **CLI `Process.Start`** : `TensorSharp.Cli.exe` existe ; la voie CLI est ouverte mais pipeline DiT + text encoder + VAE + LoRA = pas un simple `Process.Start(args)`.
4. **`IKVM`** : N/A, l'engine est C#/.NET natif.
5. **`PythonNet`** : N/A, pas de dépendance Python dans la pipeline TensorSharp.
6. **Lib équivalente .NET** : **LLamaSharp** (texte uniquement), **ONNX Runtime** (image possible via SD-Turbo mais pas Qwen-Image-Edit spécifique). Pas de concurrence .NET multimodale à ce niveau.

## Lane / acceptance delivery

- **Plancher R1** : grain `DEEP/genai` substance CONTENU (livrable = mesure firsthand + verdict documenté + ledger entry).
- **G-VAR-1** : grain CONTENU ✓ (genai, pas META).
- **G-VAR-3** : prev = `LIGHT/guard` (c.256), `DEEP/genai` ≠ `guard` (genres différents).
- **6 zero conformité** : 0 PR composite, 0 merge worker, 0 push branche d'autrui (juste docs + ledger + dossiers _research vierges), 0 commit main (worktree), 0 secret imprimé, 0 hand-edit cellule (pas de notebook pédagogique touché), 0 catalogue touché.

## Liens verbatims

- Issue : https://github.com/jsboige/CoursIA/issues/14549
- Claim : https://github.com/jsboige/CoursIA/issues/14549#issuecomment-5548472386
- Claim amendé : https://github.com/jsboige/CoursIA/issues/14549#issuecomment-5548505745
- EPIC parente : #12353 (axe multimodal)
- TensorSharp upstream : https://github.com/zhongkaifu/TensorSharp (v3.3.0.0 2026-08-30)
- HF Qwen-Image-Edit GGUF : https://huggingface.co/unsloth/Qwen-Image-Edit-2511-GGUF
- HF text encoder : https://huggingface.co/unsloth/Qwen2.5-VL-7B-Instruct-GGUF
- Topic parent c.256 : [[topic-c256-receval-14325-markdown-deaccent]]
- Topic parent c.255 : [[topic-c255-receval-14360-m5-hhm]]
