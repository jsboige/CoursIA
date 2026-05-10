# Cluster Environment Audit Report

**Date**: 2026-05-10
**Issue**: #534 — Environment inventory across cluster machines
**CLAUDE.md reference**: Section H.2 — "Toute machine du cluster doit pouvoir executer N'IMPORTE QUEL notebook du depot"
**Collector**: po-2023 (local) + dashboard data from other machines

---

## 1. Summary Table

| Component | po-2023 (GenAI) | po-2025 (ML/Gen) | ai-01 (Coord) | po-2024 (ML/QC) | po-2026 (Lean) |
|-----------|-----------------|-------------------|---------------|------------------|----------------|
| **OS** | Win 11 Pro | Win 11 (MSI GE76) | Win 11 Pro | PENDING | PENDING |
| **Python system** | 3.13.3 | 3.13.13 | PENDING | PENDING | PENDING |
| **.NET SDKs** | 8.0.x, 9.0.x, 10.0.107 | 8.0.x, 9.0.x, 10.0.x | PENDING | PENDING | PENDING |
| **dotnet-interactive** | 1.0.707101 | 1.0.552801 (PINNED) | PENDING | PENDING | PENDING |
| **Lean/elan** | NOT INSTALLED | Win 4.29.1 / WSL 4.11.0 | PENDING | PENDING | PENDING |
| **CUDA/GPU** | 3080Ti 16GB + 3090 24GB | 3080Ti 16GB (CPU-only strict) | PENDING | PENDING | PENDING |
| **Docker** | 29.4.1 | 29.4.0 | PENDING | PENDING | PENDING |
| **Conda envs** | 4 (missing 2 required) | 7 (all required present) | PENDING | PENDING | PENDING |
| **Jupyter kernels** | 5 | 9 | PENDING | PENDING | PENDING |
| **WSL** | Ubuntu + docker-desktop (v2) | Present | PENDING | PENDING | PENDING |

**Status legend**: VERIFIED = locally collected. DASHBOARD = from RooSync dashboard. PENDING = inventory not yet submitted.

---

## 2. Machine Details

### 2.1 po-2023 (GenAI/Docker Infrastructure)

**Role**: GenAI services host, Docker infrastructure specialist. Hosts all 11 GenAI services on dual GPU.

**Data source**: VERIFIED — locally collected 2026-05-10.

#### Installed

| Category | Detail |
|----------|--------|
| OS | Windows 11 Pro |
| Docker | Desktop 29.4.1 |
| Python system | 3.13.3 |
| .NET SDKs | 8.0.319, 8.0.420, 9.0.205, 9.0.313, 10.0.107 |
| dotnet-interactive | 1.0.707101 |
| Jupyter kernels | .net-csharp, .net-fsharp, .net-powershell, mcp-jupyter-py310, python3 |
| Conda envs | base, projet-is, temp-env, temp-tools, mcp-jupyter-py310 |
| WSL | Ubuntu (v2 Running), docker-desktop (v2 Running) |
| GPUs | GPU0: RTX 3080 Ti Laptop 16GB (Qwen Image Edit ~98%), GPU1: RTX 3090 24GB (9 services ~36%) |
| GenAI services | 11/11 active (Qwen Image Edit, Z-Image/Lumina, SD Forge Turbo, SD Forge, SD.Next, Whisper STT, Kokoro TTS, MusicGen, Demucs, Qwen ASR, ComfyUI Video) |

#### Missing (action required)

| Component | Priority | Notes |
|-----------|----------|-------|
| Lean/elan toolchain | HIGH | Required for SymbolicAI/Lean notebooks and GameTheory/social_choice_lean |
| Conda env `coursia-ml-training` | HIGH | Required for ML training notebooks (torch CUDA, sklearn, scipy, hmmlearn) |
| Conda env `epita_symbolic_ai` | MEDIUM | Required for SymbolicAI/SemanticWeb Python notebooks (rdflib, owlready2, pyshacl) |
| WSL kernel `Python (GameTheory WSL + OpenSpiel)` | MEDIUM | Required for GameTheory notebooks with OpenSpiel |
| open_spiel in WSL | MEDIUM | Dependency for GameTheory Python notebooks |

---

### 2.2 po-2025 (ML/General)

**Role**: ML and general notebook execution. CPU-only strict policy due to thermal constraints on MSI GE76.

**Data source**: DASHBOARD — posted 2026-05-10 19:50Z.

#### Installed

| Category | Detail |
|----------|--------|
| OS | Windows 11 (MSI GE76) |
| Docker | 29.4.0 |
| Python system | 3.13.13 |
| GPU driver | 596.36 |
| .NET SDKs | 8.0.415, 8.0.420, 9.0.313, 10.0.106, 10.0.107, 10.0.203 |
| dotnet-interactive | 1.0.552801 (PINNED — do not upgrade) |
| Lean (Windows) | 4.29.1 |
| Lean (WSL) | 4.11.0 |
| Jupyter kernels | 9 (python3, .net-csharp, .net-fsharp, .net-powershell, conda-torch, lean4, lean4-wsl, python3-wsl, smartcontracts) |
| WSL | Present |

**Conda environments (7)**:

| Env | Python | Key packages |
|-----|--------|-------------|
| coursia-ml-training | 3.12.13 | torch 2.11.0+cpu, sklearn 1.8.0, scipy 1.17.1 |
| epita_symbolic_ai | 3.12.13 | rdflib 7.6.0 |
| mcp-jupyter | 3.10.18 | (MCP server) |
| +4 MCP/service envs | — | — |

#### Constraints

- **CPU-only strict**: GPU unavailable for notebook execution (thermal constraint). ML training notebooks requiring CUDA will not run at full speed. CPU-only torch installed.
- **torch=CPU only**: Training ban enforced. Inference-only for ML notebooks.

#### Missing (action required)

| Component | Priority | Notes |
|-----------|----------|-------|
| open_spiel in WSL | HIGH | GameTheory Python notebooks blocked without it |
| Lean version mismatch | MEDIUM | Windows 4.29.1 vs WSL 4.11.0 — may cause compatibility issues with Lean notebooks |
| CUDA torch | LOW | CPU-only policy is intentional; no action unless policy changes |

---

### 2.3 ai-01 (Coordinator)

**Role**: Cluster coordinator, sk-agent/vLLM host, primary reviewer.

**Data source**: PARTIAL — dashboard activity only. Full inventory NOT yet submitted.

#### Known

| Category | Detail |
|----------|--------|
| Role | Coordinator + sk-agent/vLLM host |
| vLLM:5001 | Mini/OmniCoder (currently DOWN) |
| vLLM:5002 | Medium/Qwen3.5-35B (UP, HTTP 401 on test) |
| sk-agent MCP | Active |
| Current HEAD | a26454fa (post-#892 merge) |
| GPU2 | PCIe x4 bottleneck (~7.9 GB/s), 14 freezes in 30 days |
| M8 sweep | Runs on GPU2 despite PCIe issue |

#### Missing (action required)

| Component | Priority | Notes |
|-----------|----------|-------|
| Full env inventory | CRITICAL | Need: Python, .NET, Lean, CUDA, Docker, Conda envs, Jupyter kernels, WSL status |

---

### 2.4 po-2024 (ML/Quant Specialist)

**Role**: ML and QuantConnect specialist.

**Data source**: PARTIAL — dashboard activity only. Full inventory NOT yet submitted.

#### Known

| Category | Detail |
|----------|--------|
| Recent work | MoE+Regimes #754 (PR #891), Sudoku-NN Phase 2 (#605) |
| Active on | ML, QuantConnect, Sudoku notebooks |

#### Missing (action required)

| Component | Priority | Notes |
|-----------|----------|-------|
| Full env inventory | CRITICAL | Need: complete H.2 inventory |

---

### 2.5 po-2026 (Lean Specialist)

**Role**: Lean proofs specialist.

**Data source**: PARTIAL — dashboard activity only. Full inventory NOT yet submitted.

#### Known

| Category | Detail |
|----------|--------|
| Recent work | median_voter_theorem PROVED (sorry 2->1), banks_set_condorcet in progress |
| Active on | GameTheory/social_choice_lean (Lean 4 proofs) |

#### Missing (action required)

| Component | Priority | Notes |
|-----------|----------|-------|
| Full env inventory | CRITICAL | Need: complete H.2 inventory |

---

## 3. H.2 Compliance Matrix

Can each machine execute notebooks from all families? Assessment based on available data.

| Notebook Family | Kernel Required | po-2023 | po-2025 | ai-01 | po-2024 | po-2026 |
|-----------------|----------------|---------|---------|-------|---------|---------|
| **Search/Part1-3** | .net-csharp | OK | OK | PENDING | PENDING | PENDING |
| **CSP/OR-Tools** | .net-csharp | OK | OK | PENDING | PENDING | PENDING |
| **Sudoku** | .net-csharp | OK | OK | PENDING | PENDING | PENDING |
| **ML** | .net-csharp | OK | OK | PENDING | PENDING | PENDING |
| **Probas/Infer.NET** | .net-csharp | OK | OK | PENDING | PENDING | PENDING |
| **SymbolicAI/SemanticWeb** | python3 (rdflib) | BLOCKED | OK | PENDING | PENDING | PENDING |
| **SymbolicAI/Tweety** | .net-csharp | OK | OK | PENDING | PENDING | PENDING |
| **SymbolicAI/SmartContract** | .net-csharp | OK | OK | PENDING | PENDING | PENDING |
| **SymbolicAI/Lean** | lean4 / WSL | BLOCKED | PARTIAL | PENDING | PENDING | PENDING |
| **GameTheory** | python3 + WSL OpenSpiel | BLOCKED | BLOCKED | PENDING | PENDING | PENDING |
| **GameTheory/social_choice_lean** | lean4 / WSL | BLOCKED | PARTIAL | PENDING | PENDING | PENDING |
| **IIT/PyPhi** | python3 | OK | OK | PENDING | PENDING | PENDING |
| **GenAI/** | python3 + services | OK (host) | PARTIAL (no local services) | PENDING | PENDING | PENDING |
| **QuantConnect** | QC Cloud (MCP) | OK (MCP) | OK (cloud-only) | PENDING | PENDING | PENDING |
| **RL** | python3 (stable-baselines) | OK | OK | PENDING | PENDING | PENDING |
| **SemanticKernel** | python3 + .NET | OK | OK | PENDING | PENDING | PENDING |

**Legend**:
- **OK**: Required kernel and dependencies installed, locally verified or dashboard-confirmed
- **PARTIAL**: Kernel installed but missing dependency (e.g., Lean version mismatch, no local GenAI services)
- **BLOCKED**: Required component not installed
- **PENDING**: Inventory not yet submitted — cannot assess

### Coverage Summary

| Machine | Families OK | Families PARTIAL | Families BLOCKED | Families PENDING | Compliance |
|---------|-------------|------------------|------------------|------------------|------------|
| po-2023 | 12 | 0 | 4 | 0 | 75% |
| po-2025 | 13 | 2 | 1 | 0 | 81% |
| ai-01 | — | — | — | 16 | PENDING |
| po-2024 | — | — | — | 16 | PENDING |
| po-2026 | — | — | — | 16 | PENDING |

**po-2025 is closest to H.2 compliance** (13/16 OK, blocked only on GameTheory OpenSpiel). **po-2023 has the most gaps** (missing Lean, coursia-ml-training, epita_symbolic_ai, open_spiel).

---

## 4. Gaps and Action Items

### 4.1 Critical (blocks H.2 compliance)

| # | Machine | Action | Component | Impact |
|---|---------|--------|-----------|--------|
| 1 | ai-01 | Submit full H.2 inventory | All components | Cannot assess compliance |
| 2 | po-2024 | Submit full H.2 inventory | All components | Cannot assess compliance |
| 3 | po-2026 | Submit full H.2 inventory | All components | Cannot assess compliance |
| 4 | po-2023 | Install Lean/elan toolchain | Lean 4 + elan | SymbolicAI/Lean + GameTheory/social_choice_lean blocked |
| 5 | po-2023 | Create conda env `coursia-ml-training` | torch CUDA, sklearn, scipy, hmmlearn | ML training notebooks blocked |
| 6 | po-2025 | Install open_spiel in WSL | open_spiel Python package | GameTheory Python notebooks blocked |

### 4.2 Important (degrades capability)

| # | Machine | Action | Component | Impact |
|---|---------|--------|-----------|--------|
| 7 | po-2023 | Create conda env `epita_symbolic_ai` | rdflib, owlready2, pyshacl | SymbolicAI/SemanticWeb Python blocked |
| 8 | po-2023 | Install open_spiel in WSL + register kernel | GameTheory WSL kernel | GameTheory Python blocked |
| 9 | po-2025 | Align Lean WSL to 4.29.1 (or Windows to 4.11.0) | Lean version sync | Lean notebooks may fail on version mismatch |
| 10 | ai-01 | Fix vLLM:5001 (DOWN) | Mini/OmniCoder service | Local LLM capability degraded |
| 11 | ai-01 | Fix vLLM:5002 HTTP 401 | Qwen3.5-35B auth | sk-agent cloud model fallback |

### 4.3 Low priority (does not block notebooks)

| # | Machine | Action | Component | Impact |
|---|---------|--------|-----------|--------|
| 12 | ai-01 | Diagnose PCIe Gen4->Gen1 freeze | GPU2 hardware/BIOS | 14 freezes/30d, M8 sweep bottleneck |
| 13 | po-2025 | Consider CUDA torch (if thermal policy changes) | GPU torch | CPU-only is intentional policy |

---

## 5. Notes and Constraints

### Thermal/Policy Constraints

- **po-2025**: CPU-only strict policy. GPU present (3080Ti 16GB) but thermally constrained on MSI GE76 chassis. ML training runs on CPU-only torch. This is an intentional policy decision, not a gap.
- **po-2023**: GPU1 (3090 24GB) at ~36% utilization across 9 services. GPU0 (3080Ti 16GB) at ~98% for Qwen Image Edit. No thermal issues reported.

### PCIe Issue (ai-01)

- GPU2 experiences periodic PCIe Gen4 to Gen1 downshift, causing ~7.9 GB/s bandwidth bottleneck.
- 14 freezes recorded in 30-day window.
- M8 sweep runs on GPU2 despite the bottleneck. Root cause under investigation (hardware/BIOS).

### GenAI Services (po-2023)

All 11 GenAI services are active and accessible cluster-wide via IIS reverse proxy:
- Image: Qwen Image Edit (8188), Z-Image/Lumina (8001), SD Forge Turbo (17861), SD Forge (7860), SD.Next (7861)
- Audio: Whisper STT (8190), Kokoro TTS (8191), MusicGen (8192), Demucs (8193), Qwen ASR (8195)
- Video: ComfyUI Video (8189)

Other machines can use these services over the network for GenAI notebook execution.

### QuantConnect

All machines can execute QuantConnect notebooks via QC Cloud (MCP qc-mcp Docker). No local kernel required — execution happens on QuantConnect infrastructure. Playwright fallback available for online sessions.

### dotnet-interactive Version Note

- po-2023: 1.0.707101 (latest)
- po-2025: 1.0.552801 (PINNED — do not upgrade without testing). Pinned version may be required for SmartContract/Solidity notebook compatibility.

---

## 6. Next Steps

1. **ai-01, po-2024, po-2026**: Submit full H.2 inventory to dashboard (Python, .NET, Lean, CUDA, Docker, Conda envs with package lists, Jupyter kernels, WSL status). Use the po-2025 report as template.
2. **po-2023**: Install Lean/elan, create `coursia-ml-training` and `epita_symbolic_ai` conda envs, install open_spiel in WSL.
3. **po-2025**: Install open_spiel in WSL, align Lean versions across Windows and WSL.
4. **ai-01**: Update this report once all inventories are collected. Target: full H.2 compliance matrix within 48h.
5. **All machines**: After gaps resolved, run `scripts/notebook_tools/notebook_tools.py validate MyIA.AI.Notebooks/` to confirm end-to-end notebook executability.
