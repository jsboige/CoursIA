#!/bin/bash
# Phase 11: Résolution Mapping GPU PyTorch vs nvidia-smi
# Date: 2025-10-13

set -e

echo "================================================================"
echo "PHASE CRITIQUE: RÉSOLUTION MAPPING GPU"
echo "================================================================"
echo ""

# Naviguer vers ComfyUI
cd /home/jesse/SD/workspace/comfyui-qwen/ComfyUI
source venv/bin/activate

echo "=== État nvidia-smi complet ==="
nvidia-smi --query-gpu=index,name,memory.total --format=csv
echo ""

echo "=== Test 1: CUDA_VISIBLE_DEVICES=0 (Test PyTorch GPU 0) ==="
CUDA_VISIBLE_DEVICES=0 python3 -c "
import torch
print(f'PyTorch version: {torch.__version__}')
print(f'CUDA available: {torch.cuda.is_available()}')
print(f'Device count: {torch.cuda.device_count()}')
if torch.cuda.is_available():
    for i in range(torch.cuda.device_count()):
        props = torch.cuda.get_device_properties(i)
        print(f'GPU {i}: {torch.cuda.get_device_name(i)}')
        print(f'  Memory: {props.total_memory / 1e9:.1f} GB')
        print(f'  Compute Capability: {props.major}.{props.minor}')
"
echo ""

echo "=== Test 2: CUDA_VISIBLE_DEVICES=1 (Test PyTorch GPU 1) ==="
CUDA_VISIBLE_DEVICES=1 python3 -c "
import torch
print(f'PyTorch version: {torch.__version__}')
print(f'CUDA available: {torch.cuda.is_available()}')
print(f'Device count: {torch.cuda.device_count()}')
if torch.cuda.is_available():
    for i in range(torch.cuda.device_count()):
        props = torch.cuda.get_device_properties(i)
        print(f'GPU {i}: {torch.cuda.get_device_name(i)}')
        print(f'  Memory: {props.total_memory / 1e9:.1f} GB')
        print(f'  Compute Capability: {props.major}.{props.minor}')
"
echo ""

echo "=== Test 3: Sans restriction (Tous GPUs visibles) ==="
python3 -c "
import torch
print(f'PyTorch version: {torch.__version__}')
print(f'CUDA available: {torch.cuda.is_available()}')
print(f'Device count: {torch.cuda.device_count()}')
if torch.cuda.is_available():
    for i in range(torch.cuda.device_count()):
        props = torch.cuda.get_device_properties(i)
        print(f'GPU {i}: {torch.cuda.get_device_name(i)}')
        print(f'  Memory: {props.total_memory / 1e9:.1f} GB')
        print(f'  Compute Capability: {props.major}.{props.minor}')
"
echo ""

echo "=== ANALYSE RÉSULTATS ==="
echo "nvidia-smi:"
nvidia-smi --query-gpu=index,name --format=csv,noheader

echo ""
echo "PyTorch (tous GPUs):"
python3 -c "
import torch
if torch.cuda.is_available():
    for i in range(torch.cuda.device_count()):
        print(f'{i},{torch.cuda.get_device_name(i)}')
"
echo ""

echo "=== DÉTERMINATION MAPPING CORRECT ==="
echo "Objectif: Utiliser RTX 3090 (24GB) pour ComfyUI"
echo ""
echo "Si PyTorch GPU 0 = RTX 3090 → CUDA_VISIBLE_DEVICES=0"
echo "Si PyTorch GPU 1 = RTX 3090 → CUDA_VISIBLE_DEVICES=1"
echo ""

# Test de charge minimale sur GPU 3090
echo "=== Test charge GPU (détection automatique RTX 3090) ==="
python3 -c "
import torch
import time

# Trouver la RTX 3090
gpu_idx = None
for i in range(torch.cuda.device_count()):
    name = torch.cuda.get_device_name(i)
    if 'RTX 3090' in name or '3090' in name:
        gpu_idx = i
        print(f'RTX 3090 détectée: PyTorch GPU {i}')
        break

if gpu_idx is not None:
    print(f'RÉSULTAT: Utiliser CUDA_VISIBLE_DEVICES={gpu_idx}')
    
    # Test allocation mémoire
    torch.cuda.set_device(gpu_idx)
    print(f'Test allocation 1GB sur GPU {gpu_idx}...')
    x = torch.randn(1024, 1024, 256, device=f'cuda:{gpu_idx}')
    print(f'Allocation réussie: {x.element_size() * x.nelement() / 1e9:.2f} GB')
    print(f'VRAM utilisée: {torch.cuda.memory_allocated(gpu_idx) / 1e9:.2f} GB')
    print(f'VRAM réservée: {torch.cuda.memory_reserved(gpu_idx) / 1e9:.2f} GB')
    del x
    torch.cuda.empty_cache()
    print('Test OK: GPU 3090 accessible')
else:
    print('ERREUR: RTX 3090 non trouvée!')
    exit(1)
"

echo ""
echo "================================================================"
echo "RÉSOLUTION MAPPING GPU TERMINÉE"
echo "================================================================"