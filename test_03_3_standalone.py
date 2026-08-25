"""Direct execution of 03-3 BenchmarkSuite cell via Python (not nbconvert).
Simulates the kernel environment + executes the real diffusers pipeline.
"""
import sys, os, json
from pathlib import Path

# Pre-amble: ensure user-site-packages is on sys.path for diffusers
from pathlib import Path as _P
_user_site = _P(os.environ.get('APPDATA', r'C:\Users\jsboi\AppData\Roaming')) / 'Python' / 'Python313' / 'site-packages'
_user_site_str = str(_user_site)
if _user_site_str not in sys.path:
    sys.path.insert(0, _user_site_str)

print(f"Python: {sys.executable}")
print(f"Version: {sys.version}")
print(f"diffusers path: {_user_site_str}")

import torch
CUDA_AVAILABLE = torch.cuda.is_available()
GPU_MEMORY_TOTAL = torch.cuda.get_device_properties(0).total_memory / (1024**3) if CUDA_AVAILABLE else 0
print(f"\nCUDA_AVAILABLE: {CUDA_AVAILABLE}")
print(f"GPU_MEMORY_TOTAL: {GPU_MEMORY_TOTAL:.1f} GB")
print(f"Device: {torch.cuda.get_device_name(0) if CUDA_AVAILABLE else 'CPU'}")

# Now execute BenchmarkSuite logic
import diffusers
print(f"\ndiffusers version: {diffusers.__version__}")
print(f"diffusers location: {diffusers.__file__}")

if not CUDA_AVAILABLE or GPU_MEMORY_TOTAL < 6.0:
    print("RECOVERABLE-MACHINE: no GPU/insufficient VRAM")
    sys.exit(0)

print("\n=== EXECUTING REAL BENCHMARK ===")
from diffusers import StableDiffusionPipeline

MODEL_ID = "runwayml/stable-diffusion-v1-5"
PROMPT = "a red apple on a wooden table, photorealistic, 8k"
INFERENCE_STEPS = 10
GUIDANCE_SCALE = 7.5
HEIGHT = 512
WIDTH = 512
SEED = 42
generator = torch.Generator(device="cuda").manual_seed(SEED)

print(f"\nLoading {MODEL_ID} in FP32 (this may take 1-2 min for download)...")
pipe_fp32 = StableDiffusionPipeline.from_pretrained(
    MODEL_ID, torch_dtype=torch.float32, safety_checker=None, requires_safety_checker=False
).to("cuda")

print(f"\nLoading {MODEL_ID} in FP16...")
pipe_fp16 = StableDiffusionPipeline.from_pretrained(
    MODEL_ID, torch_dtype=torch.float16, safety_checker=None, requires_safety_checker=False
).to("cuda")

print(f"\nLoading {MODEL_ID} in FP16 + attention_slicing...")
pipe_fp16_attn = StableDiffusionPipeline.from_pretrained(
    MODEL_ID, torch_dtype=torch.float16, safety_checker=None, requires_safety_checker=False
).to("cuda")
pipe_fp16_attn.enable_attention_slicing()

print("All pipelines loaded.")

def benchmark_one(name, pipe, warmup=True):
    if warmup:
        with torch.inference_mode():
            _ = pipe(PROMPT, num_inference_steps=2, generator=generator,
                     height=HEIGHT, width=WIDTH, guidance_scale=GUIDANCE_SCALE).images[0]
        torch.cuda.empty_cache()
        torch.cuda.synchronize()

    times, vram_peaks = [], []
    for _ in range(3):
        torch.cuda.reset_peak_memory_stats()
        start = torch.cuda.Event(enable_timing=True)
        end = torch.cuda.Event(enable_timing=True)
        with torch.inference_mode():
            start.record()
            image = pipe(PROMPT, num_inference_steps=INFERENCE_STEPS,
                         generator=generator,
                         height=HEIGHT, width=WIDTH,
                         guidance_scale=GUIDANCE_SCALE).images[0]
            end.record()
            torch.cuda.synchronize()
        times.append(start.elapsed_time(end))
        vram_peaks.append(torch.cuda.max_memory_allocated() / (1024**2))
        torch.cuda.empty_cache()

    return {
        "name": name,
        "avg_time_ms": sum(times) / len(times),
        "min_time_ms": min(times),
        "max_time_ms": max(times),
        "avg_vram_mb": sum(vram_peaks) / len(vram_peaks),
        "peak_vram_mb": max(vram_peaks),
        "iterations": len(times),
    }

print("\n🏃 Exécution des benchmarks RÉELS (3 configs × 3 itérations × 10 steps × 512×512)...")
REAL_BENCHMARK_RESULTS = [
    benchmark_one("Baseline (FP32)", pipe_fp32),
    benchmark_one("FP16", pipe_fp16),
    benchmark_one("FP16 + attention_slicing", pipe_fp16_attn),
]

baseline = REAL_BENCHMARK_RESULTS[0]["avg_time_ms"]
for r in REAL_BENCHMARK_RESULTS:
    r["speedup_vs_fp32"] = baseline / r["avg_time_ms"]

print("\n" + "=" * 80)
print("RÉSULTATS BENCHMARK RÉEL (Stable Diffusion v1.5, 10 steps, 512×512)")
print("=" * 80)
print(f"{'Configuration':<30} {'Temps moy (ms)':<16} {'VRAM pic (MB)':<16} {'Speedup':<10}")
print("-" * 80)
for r in REAL_BENCHMARK_RESULTS:
    print(f"{r['name']:<30} {r['avg_time_ms']:<16.1f} {r['peak_vram_mb']:<16.1f} {r['speedup_vs_fp32']:<10.2f}x")
print("=" * 80)

# Save results for notebook
results_path = Path('benchmark_03_3_results.json')
results_path.write_text(json.dumps(REAL_BENCHMARK_RESULTS, indent=2, ensure_ascii=False), encoding='utf-8')
print(f"\nResults saved to {results_path}")

# Cleanup
del pipe_fp32, pipe_fp16, pipe_fp16_attn
torch.cuda.empty_cache()
print("\nBenchmark SUCCEEDED")
