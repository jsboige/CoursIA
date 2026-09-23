# ComfyUI-Qwen rollback state (before nunchaku fix + ComfyUI upgrade, 2026-06-20)

Recorded BEFORE applying fixes per ai-01 greenlight.

## Pre-fix state (DEGRADED: gen hangs, CPU offload)

### ComfyUI core
- Repository: https://github.com/comfyanonymous/ComfyUI.git
- HEAD: `f8b981ae` (2025-11-30, 1187 commits behind master as of 2026-06-20)
- Path (bind-mounted): `docker-configurations/services/comfyui-qwen/workspace`

### pip packages
- torch: 2.6.0+cu124
- nunchaku: `1.0.1+torch2.6` (GitHub wheel, not PyPI)
- transformers: (4.50.3+ per requirements)

### Custom node ComfyUI-nunchaku
- Repository: https://github.com/nunchaku-ai/ComfyUI-nunchaku.git
- SHA: `930bc2266a4f3277e16be75e67c11875d20a01c6` (tag v1.1.0)

### Known bugs (root causes — CORRECTED diagnosis 2026-06-20)
1. **getpwuid blocker** (RESOLVED by USER=bonsai/LOGNAME=bonsai env compose):
   `torch._inductor` → `getpass.getuser()` → `pwd.getpwuid(1000)` KeyError (UID 1000
   not in python:3.11 /etc/passwd). Aborts transformers→hqq→inductor chain → 0 Nunchaku loaders.
2. **VRAM integer-overflow** (UNRESOLVED — the reason for ComfyUI upgrade attempt):
   `comfy/model_patcher.py:797` logs `lowvram_model_memory = 9.5e19 MB usable` →
   `full_load: True` but KSampler offloads to CPU (GPU 0%, CPU 176%). Bug is in
   ComfyUI core memory accumulator, NOT in mem_get_info (returns correct free=23GB).
   NOT fixed by --disable-cuda-malloc or --normalvram (tested). Hypothesis: fixed
   upstream in the 1187 commits between f8b981ae and master.

### Container
- Image: `python:3.11`
- user: "1000:1000"

## Fixes applied on branch fix/comfyui-qwen-nunchaku
- docker-compose.yml: USER=bonsai + LOGNAME=bonsai (env), memory 12G→28G, shm_size 16g

## Rollback procedure
1. Revert docker-compose.yml: `git checkout origin/main -- docker-configurations/services/comfyui-qwen/docker-compose.yml`
2. Revert ComfyUI core (if upgraded): `docker exec -u 0 comfyui-qwen bash -c "cd /workspace/ComfyUI && git config --global --add safe.directory '*' && git checkout f8b981ae"`
3. `docker compose -f docker-configurations/services/comfyui-qwen/docker-compose.yml --env-file .env up -d --force-recreate comfyui-qwen`
4. Re-ping ai-01 on dashboard.
