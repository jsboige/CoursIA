# GenAI Image/Video Execution Plan - Issue #60

**Date**: 14 mars 2026
**Author**: myia-po-2023
**GPU Available**: RTX 3090 (24GB) + RTX 3080 Ti (16GB) = 40GB VRAM total
**Services**: 10 services actifs (5 Image + 1 Video + 4 Audio)

---

## Executive Summary

**Total notebooks**: 35 (19 Image + 16 Video)
- **Cloud API (no VRAM)**: 6 notebooks (OpenAI)
- **Local lightweight (< 4GB)**: 5 notebooks (Python libs, FFmpeg)
- **Local models (4-18GB)**: 24 notebooks

**Critical constraint**: Qwen Image Edit monopolizes GPU 0 (~29GB, oversubscribed on 16GB card)

---

## Image Notebooks (19)

### Phase 1: Cloud API (No VRAM)

| Notebook | Service | API Key | Priority |
|----------|---------|---------|----------|
| 01-1-OpenAI-DALL-E-3.ipynb | OpenAI DALL-E 3 | OPENAI_API_KEY | P0 |
| 01-2-GPT-5-Image-Generation.ipynb | OpenAI GPT-5 | OPENAI_API_KEY | P0 |

**Execution**: Anytime, parallel, no GPU constraint
**Timeline**: 5 min each

### Phase 2: Local Libraries (No VRAM)

| Notebook | Service | Dependencies | Priority |
|----------|---------|--------------|----------|
| 01-3-Basic-Image-Operations.ipynb | PIL, OpenCV | Python only | P0 |

**Execution**: Anytime, no GPU
**Timeline**: 2 min

### Phase 3: SD Forge (GPU 1)

| Notebook | Service | VRAM | GPU | Priority |
|----------|---------|------|-----|----------|
| 01-4-Forge-SD-XL-Turbo.ipynb | SD Forge Turbo | ~8GB | GPU 1 | P1 |
| 02-3-Stable-Diffusion-3-5.ipynb | SD Forge main | ~12GB | GPU 1 | P1 |

**Execution**: Sequential on GPU 1
**Timeline**: 10 min each

### Phase 4: Qwen Image Edit (GPU 0 - BLOCKING)

| Notebook | Service | VRAM | GPU | Priority |
|----------|---------|------|-----|----------|
| 01-5-Qwen-Image-Edit.ipynb | Qwen Edit (8188) | ~29GB | GPU 0 | P1 |
| 02-1-Qwen-Image-Edit-2509.ipynb | Qwen Edit (8188) | ~29GB | GPU 0 | P1 |

**Critical**: Service already running, GPU 0 oversubscribed (29GB on 16GB card)
**Execution**: Sequential, potential OOM risk
**Timeline**: 15 min each

### Phase 5: Z-Image/Lumina (GPU 1)

| Notebook | Service | VRAM | GPU | Priority |
|----------|---------|------|-----|----------|
| 02-4-Z-Image-Lumina2.ipynb | Z-Image (8001) | ~10GB | GPU 1 | P1 |

**Execution**: After SD Forge, GPU 1
**Timeline**: 10 min

### Phase 6: Advanced/Applications (Multi-service)

| Notebook | Services | VRAM | Priority |
|----------|----------|------|----------|
| 02-2-FLUX-1-Advanced-Generation.ipynb | FLUX via ComfyUI | ~12GB | P2 |
| 03-1-Multi-Model-Comparison.ipynb | All services | Variable | P2 |
| 03-2-Workflow-Orchestration.ipynb | All services | Variable | P2 |
| 03-3-Performance-Optimization.ipynb | All services | Variable | P2 |
| 04-1-Educational-Content-Generation.ipynb | Multiple | Variable | P2 |
| 04-2-Creative-Workflows.ipynb | Multiple | Variable | P2 |
| 04-3-Production-Integration.ipynb | Multiple | Variable | P2 |
| 04-4-Cross-Stitch-Pattern-Maker-Legacy.ipynb | Multiple | Variable | P3 |
| examples/* (3 notebooks) | Multiple | Variable | P3 |

**Execution**: After core services tested, GPU 1 preferred
**Timeline**: 10-20 min each

---

## Video Notebooks (16)

### Phase 1: Local Libraries (No VRAM)

| Notebook | Service | Dependencies | Priority |
|----------|---------|--------------|----------|
| 01-1-Video-Operations-Basics.ipynb | moviepy, FFmpeg | Python + FFmpeg | P0 |

**Execution**: Anytime, no GPU
**Timeline**: 3 min

### Phase 2: Cloud API (No VRAM)

| Notebook | Service | API Key | Priority |
|----------|---------|---------|----------|
| 01-2-GPT-5-Video-Understanding.ipynb | OpenAI GPT-5 | OPENAI_API_KEY | P0 |
| 04-3-Sora-API-Cloud-Video.ipynb | OpenAI Sora 2 | OPENAI_API_KEY | P1 |

**Execution**: Anytime, parallel
**Timeline**: 5-10 min each

### Phase 3: Qwen2.5-VL (GPU 0 - CONFLICT)

| Notebook | Service | VRAM | GPU | Priority |
|----------|---------|------|-----|----------|
| 01-3-Qwen-VL-Video-Analysis.ipynb | Qwen2.5-VL | ~18GB | GPU 0 | P1 |

**Conflict**: Competes with Qwen Image Edit on GPU 0
**Execution**: When Qwen Edit not running, or swap
**Timeline**: 15 min

### Phase 4: Video Enhancement (GPU 1)

| Notebook | Service | VRAM | GPU | Priority |
|----------|---------|------|-----|----------|
| 01-4-Video-Enhancement-ESRGAN.ipynb | Real-ESRGAN/RIFE | ~4GB | GPU 1 | P1 |

**Execution**: GPU 1, lightweight
**Timeline**: 8 min

### Phase 5: AnimateDiff (GPU 1)

| Notebook | Service | VRAM | GPU | Priority |
|----------|---------|------|-----|----------|
| 01-5-AnimateDiff-Introduction.ipynb | AnimateDiff | ~12GB | GPU 1 | P1 |

**Execution**: GPU 1, after enhancement
**Timeline**: 15 min

### Phase 6: Advanced Video Generation (GPU 1)

| Notebook | Service | VRAM | GPU | Priority |
|----------|---------|------|-----|----------|
| 02-1-HunyuanVideo-Generation.ipynb | HunyuanVideo | ~18GB | GPU 1 | P1 |
| 02-2-LTX-Video-Lightweight.ipynb | LTX-Video | ~8GB | GPU 1 | P1 |
| 02-3-Wan-Video-Generation.ipynb | Wan 2.1/2.2 | ~10GB | GPU 1 | P1 |
| 02-4-SVD-Image-to-Video.ipynb | SVD | ~10GB | GPU 1 | P1 |

**Execution**: Sequential on GPU 1 (due to VRAM)
**Timeline**: 15-25 min each

### Phase 7: Orchestration/Applications (Multi-service)

| Notebook | Services | VRAM | Priority |
|----------|----------|------|----------|
| 03-1-Multi-Model-Video-Comparison.ipynb | All services | Variable | P2 |
| 03-2-Video-Workflow-Orchestration.ipynb | All services | Variable | P2 |
| 03-3-ComfyUI-Video-Workflows.ipynb | ComfyUI Video | ~12GB | P2 |
| 04-1-Educational-Video-Generation.ipynb | Multiple | Variable | P2 |
| 04-2-Creative-Video-Workflows.ipynb | Multiple | Variable | P2 |
| 04-4-Production-Video-Pipeline.ipynb | Multiple | Variable | P2 |

**Execution**: After core services tested
**Timeline**: 15-30 min each

---

## Execution Timeline

### Batch 1: Cloud + Local (0 VRAM) - 30 min
```
Phase 1 (parallel):
  - 01-1-OpenAI-DALL-E-3 (Image)
  - 01-2-GPT-5-Image-Generation (Image)
  - 01-2-GPT-5-Video-Understanding (Video)
  - 04-3-Sora-API-Cloud-Video (Video)
  - 01-3-Basic-Image-Operations (Image)
  - 01-1-Video-Operations-Basics (Video)
```

### Batch 2: GPU 1 Lightweight - 1 hour
```
Phase 2 (sequential):
  - 01-4-Forge-SD-XL-Turbo (10 min)
  - 01-4-Video-Enhancement-ESRGAN (8 min)
  - 02-4-Z-Image-Lumina2 (10 min)
  - 01-5-AnimateDiff (15 min)
  - 02-3-Stable-Diffusion-3-5 (10 min)
```

### Batch 3: GPU 0 Qwen (RISK) - 45 min
```
Phase 3 (sequential, OOM risk):
  - 01-5-Qwen-Image-Edit (15 min)
  - 02-1-Qwen-Image-Edit-2509 (15 min)
  - 01-3-Qwen-VL-Video-Analysis (15 min)
```

### Batch 4: GPU 1 Heavy Models - 3 hours
```
Phase 4 (sequential):
  - 02-1-HunyuanVideo (25 min)
  - 02-2-LTX-Video (15 min)
  - 02-3-Wan-Video (20 min)
  - 02-4-SVD (20 min)
  - 02-2-FLUX-1-Advanced (20 min)
  - 03-3-ComfyUI-Video-Workflows (20 min)
  - + Others (45 min)
```

### Batch 5: Multi-Service Apps - 4 hours
```
Phase 5 (sequential):
  - All 03-Orchestration notebooks
  - All 04-Applications notebooks
  - examples notebooks
```

**Total estimated time: 9-10 hours**

---

## Critical Issues & Recommendations

### Issue #1: GPU 0 Oversubscription (CRITICAL)
**Problem**: Qwen Image Edit uses ~29GB on 16GB GPU 0
**Impact**: High OOM risk, performance degradation
**Recommendation**: Move Qwen Edit to GPU 1 (3090, 24GB), or reduce batch size

### Issue #2: Service Conflicts (HIGH)
**Problem**: Qwen2.5-VL (Video) conflicts with Qwen Image Edit
**Recommendation**: Schedule Qwen VL when Qwen Edit not running, or implement hot-swap

### Issue #3: No Service Management (MEDIUM)
**Problem**: Services must be manually started/stopped to free VRAM
**Recommendation**: Implement automated service lifecycle with sleep/timeout

---

## Proposed Execution Order

### Week 1: Core Validation (Priority 0-1)
1. Cloud API notebooks (6)
2. Local library notebooks (2)
3. SD Forge (2)
4. Z-Image/Lumina (1)
5. Video enhancement (1)
6. AnimateDiff (1)

### Week 2: Advanced Models (Priority 1-2)
1. Qwen Image Edit (2) - **with GPU monitoring**
2. Qwen2.5-VL Video (1) - **swap with Qwen Edit**
3. HunyuanVideo (1)
4. LTX-Video (1)
5. Wan Video (1)
6. SVD (1)
7. FLUX-1 (1)

### Week 3: Applications (Priority 2-3)
1. Multi-model comparison (2)
2. Workflow orchestration (2)
3. ComfyUI workflows (2)
4. Educational/creative apps (8)
5. Examples (3)

---

## Prerequisites Checklist

### Environment
- [ ] Python 3.10+ with virtual environment
- [ ] FFmpeg installed and in PATH
- [ ] Docker services accessible (check with `genai.py docker status`)

### API Keys
- [ ] OPENAI_API_KEY set in `.env`
- [ ] COMFYUI_AUTH_TOKEN set (for Qwen services)

### Services Status
- [ ] Qwen Image Edit (8188) running
- [ ] Z-Image/Lumina (8001) running
- [ ] SD Forge services running
- [ ] ComfyUI Video (8189) running

### Monitoring
- [ ] `nvidia-smi` available for VRAM monitoring
- [ ] Log aggregation for service failures
- [ ] Sleep/timeout mechanism for model unload

---

## Next Steps

1. **Review and approve this plan** (comment on issue #60)
2. **Implement GPU 0 fix** (move Qwen Edit to GPU 1 or optimize)
3. **Start Week 1 execution** (Cloud + Local + SD Forge)
4. **Track results** and update plan based on actual VRAM usage

---

**Tags**: #genai #issue-60 #execution-plan #gpu-allocation
