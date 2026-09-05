# Issue #14549 — TensorSharp multimodal (Qwen-Image-Edit / Wan 2.1/2.2) sur RTX 3090 24GB

**Issue** : [#14549](https://github.com/jsboige/CoursIA/issues/14549) — investigation(genai-dotnet): axe multimodal de #12353 — TensorSharp Qwen-Image-Edit / Wan video sur eGPU RTX 3090 (po-2023)

**Statut investigation** : en cours (c.257, lane `myia-po-2023:CoursIA-2`)
**Lane routée** : `myia-po-2023` (verbatim body : « seule machine de la flotte portant à la fois la VRAM requise et les services GenAI Image/Video »)
**Claim** : [commentaire #5548472386](https://github.com/jsboige/CoursIA/issues/14549#issuecomment-5548472386)

## 1. Contexte fleet

| Machine | GPU | VRAM | Rôle |
|---|---|---:|---|
| `myia-po-2023` | RTX 3080 + **eGPU RTX 3090** | **40 GB (16 + 24)** | hôte des 8 services Docker GenAI Image/Audio/Video |
| Autres machines | ... | < 24 GB | **gated hardware** sur l'axe multimodal |

`#12353` axe Texte = tranché `LLamaSharp` (NuGet officiel, 3786★, mesuré 36,57 tok/s GPU vs 11,95 tok/s CPU, ×3,06). Axes Image / Vidéo / Multimodal étaient restés `N/A — gated hardware` (qualifié sur GPU 16 GB), mesure contestée par #14549 qui rappelle que la flotte a une **RTX 3090 24 GB** éligible.

## 2. TensorSharp — release candidate

| Champ | Valeur |
|---|---|
| Upstream | https://github.com/zhongkaifu/TensorSharp |
| Latest release | **v3.3.0.0** (2026-08-30) |
| Assets Windows x64 CUDA | `tensorsharp-cli-3.3.0.0-win-x64-cuda.zip` (671 MB) + `tensorsharp-server-3.3.0.0-win-x64-cuda.zip` (686 MB) |
| Texte | GGUF inference via backends GGML/CUDA, modèles autoregressive LLMs + DiffusionGemma text diffusion |
| Image | **Qwen-Image-Edit** (DiT 20B + Lightning LoRA 4/8-step) |
| Vidéo | **Wan 2.1 / 2.2** (ajouté v3.3.0.0) + MiniMax-H3 (32 kHz stereo) |
| Alternative .NET Texte | **LLamaSharp** (rejeté par #12353 — TensorSharp ne se justifie que si multimodal tient) |

## 3. Acceptance #1 — binaire chargé firsthand (✓ 2026-09-05 03:38Z)

Mesure verbatim `nvidia-smi` après chargement CLI (`TensorSharp.Cli.exe --backend ggml_cuda --gpu-layers 99 --help`, `CUDA_VISIBLE_DEVICES=1`) :

```
0, NVIDIA GeForce RTX 3080 Ti Laptop GPU, 0 MiB, 16384 MiB
1, NVIDIA GeForce RTX 3090,                625 MiB, 24576 MiB
```

- GPU ciblé = RTX 3090 24 GB ✓
- VRAM occupée en idle = 625 MiB (runtime .NET + bindings CUDA natifs)
- Pas de `CUDA_ERROR_NO_DEVICE`, pas de `DllNotFoundException`

## 4. Acceptance #2 — axe exécuté (en cours)

Premier test cible : inférence texte-only avec Qwen2.5-VL-7B-Instruct Q4_K_M (text encoder du pipeline Qwen-Image-Edit), à valider que le pipeline CUDA charge un GGUF sur la 3090, mesure VRAM réelle d'inférence, et timng de chargement GPU.

Modèles à télécharger pour Image/Edit complet :
- `Qwen2.5-VL-7B-Instruct-Q4_K_M.gguf` (4.683 GB, **text encoder**)
- `qwen-image-edit-2511-Q4_K_M.gguf` (~12 GB, **DiT**)
- `mmproj-BF16.gguf` (~1.5 GB, **vision tower**)
- `Qwen_Image-VAE.safetensors` (~0.5 GB, **VAE**)
- `Qwen-Image-Edit-2511-Lightning-4steps-V1.0-bf16.safetensors` (~0.5 GB, **fast LoRA**)

Total ~19 GB. Premier test télécharge text encoder seulement (~5 GB) pour valider la chaîne CUDA + charge GPU.

## 5. Verdict SOTA attendu (à finaliser après exécutions)

| Axe | Verdict pressenti | Justification |
|---|---|---|
| Texte | `SOTA-OK` binaire mais **RECONNU perdant** vs LLamaSharp | #12353 tranché LLamaSharp ; TensorSharp Texte ne change rien |
| Image | `RECOVERABLE-MACHINE` probable | tient sur 3090 mais à parité de perf avec stack Python/Docker ComfyUI existant |
| Vidéo | **`INTRINSIC` ou `RECOVERABLE-MACHINE` à vérifier** | Wan 2.1/2.2 tout neuf (v3.3.0.0), doc sparse |

## 6. Comparaison honnête à l'existant (à finaliser)

**Stack Python/Docker GenAI Image existant (po-2023, services Docker)** :
- ComfyUI + Qwen-Image-Edit-2511 workflow custom
- Latence de référence mesurée ~25-30s sur image 544×1184, Lightning LoRA 4-step (à reconfirmer)
- Bus factor : communauté ComfyUI massive, plugins extensibles, modèles sur HuggingFace

**TensorSharp multimodal** :
- Latence de référence constructeur : 40.44s sur 544×1184 (Q2_K DiT + 4-step Lightning LoRA) — **plus lent** que la mesure ComfyUI
- Bus factor : single-maintainer (zhongkaifu) + 3 contributeurs occasionnels ; v3.3.0.0 publié il y a 5 jours
- API : CLI seul + bindings .NET ; pas d'équivalent ComfyUI nodes

**À creuser** : si TensorSharp est plus lent sur le même hardware ET même modèle, **l'argument « parité .NET face à LLamaSharp » ne tient pas** — l'axe multimodal serait **`INTRINSIC`** au sens où **la voie .NET n'apporte rien que Python/Docker ne fasse déjà**, et le coût de migration (bus factor, doc sparse, latence moindre) l'emporte sur le gain (interop .NET ↔ C# du reste du dépôt).

## 7. Checklist 6 axes (en cas de verdict `INTRINSIC`)

À remplir si l'exécution firsthand conclut à un blocage :

1. **Binding .NET / NuGet** : `tensorsharp-server-3.3.0.0-win-x64-cuda.zip` disponible, mais packaging = .zip, pas NuGet natif. À vérifier si une PR upstream a été ouverte.
2. **`P/Invoke`** : GGUF inference via `GgmlOps.dll` (531 MB) + bindings CUDA via `TensorSharp.Backends.Cuda.dll` ; **P/Invoke actif**.
3. **CLI `Process.Start`** : **TensorSharp.Cli.exe** existe ; la voie CLI est ouverte. Mais le rendu multimodal nécessite un pipeline CLI complexe (DiT + text encoder + VAE + LoRA) — pas un simple `Process.Start(args)`.
4. **`IKVM`** : N/A, l'engine est C#/.NET natif.
5. **`PythonNet`** : N/A, pas de dépendance Python dans la pipeline TensorSharp.
6. **Lib équivalente .NET** : **LLamaSharp** (texte uniquement), **ONNX Runtime** (image possible via SD-Turbo, mais pas Qwen-Image-Edit spécifique). Pas de concurrence .NET multimodale à ce niveau.

## 8. Lane / acceptance delivery

- **Plancher R1** : grain `DEEP/genai` substance CONTENU (livrable = mesure firsthand + verdict documenté + ledger entry).
- **G-VAR-1** : grain CONTENU ✓ (genai, pas META).
- **G-VAR-3** : prev = `LIGHT/guard` (c.256), `DEEP/genai` ≠ `guard` (genres différents).
- **6 zero conformité** : 0 PR composite, 0 merge worker, 0 push branche d'autrui (pas d'édition code du repo, juste docs + ledger), 0 commit main (worktree), 0 secret imprimé, 0 hand-edit cellule, 0 catalogue touché.

## 9. Liens verbatims

- Issue : https://github.com/jsboige/CoursIA/issues/14549
- Claim : https://github.com/jsboige/CoursIA/issues/14549#issuecomment-5548472386
- EPIC parente : #12353 (axe multimodal)
- TensorSharp upstream : https://github.com/zhongkaifu/TensorSharp
- HuggingFace Qwen-Image-Edit GGUF : https://huggingface.co/unsloth/Qwen-Image-Edit-2511-GGUF
- Topic parent c.256 : [[topic-c256-receval-14325-markdown-deaccent]]
