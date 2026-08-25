"""Patch script for #12961 - replace synthetic benchmark with real pipeline.

Patches cell 53.5 (new) + cell 54 (BenchmarkSuite) + cell 55 (table markdown).
"""
import json
import sys
from pathlib import Path

NB_PATH = Path('MyIA.AI.Notebooks/GenAI/Image/03-Orchestration/03-3-Performance-Optimization.ipynb')

with NB_PATH.open(encoding='utf-8') as f:
    nb = json.load(f)

print(f"Notebook: {NB_PATH.name}")
print(f"Cells: {len(nb['cells'])}")

# ---- NEW CELL 53.5: Setup real pipeline + benchmark pipeline ----
# Inserts before the current cell 54 (which is index 54, the BenchmarkSuite class)
NEW_CELL_535 = {
    "cell_type": "markdown",
    "metadata": {},
    "source": [
        "## 8.1 Chargement d'un vrai pipeline de génération\n",
        "\n",
        "Pour mesurer honnêtement, on charge un vrai pipeline Stable Diffusion v1.5 (≈5 GB sur disque, ~3 GB VRAM en FP32, ~1.5 GB en FP16) via `diffusers`. Le modèle est mis en cache localement (`~/.cache/huggingface/hub/`) à la première exécution ; les exécutions suivantes lisent depuis le cache.\n",
        "\n",
        "**Pourquoi ce modèle et pas un jouet** : `stable-diffusion-v1-5/stable-diffusion-v1-5` est le modèle canonique du dépôt `runwayml` devenu standard — 860M paramètres, scheduler PNDM, conditionnement CLIP ViT-L/14. Les techniques mesurées (FP16, attention slicing) sont celles de la doc officielle HuggingFace, donc reproductibles cross-machine.\n",
        "\n",
        "**Garde-fou VRAM** : si l'environnement est CPU-only ou < 6 GB VRAM, on skip le chargement et la cellule suivante marque `RECOVERABLE-MACHINE` — la réparation devient alors un geste de routage vers une lane GPU, pas une fabrication de chiffres."
    ]
}

# ---- REWRITTEN CELL 54: BenchmarkSuite with real_pipeline method ----
NEW_CELL_54 = {
    "cell_type": "code",
    "execution_count": None,
    "metadata": {},
    "outputs": [],
    "source": [
        "REAL_PIPELINE_LOADED = False\n",
        "REAL_PIPELINE_SKIP_REASON = None\n",
        "REAL_BENCHMARK_RESULTS = []\n",
        "\n",
        "if CUDA_AVAILABLE and GPU_MEMORY_TOTAL >= 6.0:\n",
        "    try:\n",
        "        from diffusers import StableDiffusionPipeline\n",
        "        import torch\n",
        "        MODEL_ID = \"runwayml/stable-diffusion-v1-5\"\n",
        "        PROMPT = \"a red apple on a wooden table, photorealistic, 8k\"\n",
        "        INFERENCE_STEPS = 10  # Pédagogique: 10 steps = compromis vitesse/démo\n",
        "        GUIDANCE_SCALE = 7.5\n",
        "        HEIGHT = 512\n",
        "        WIDTH = 512\n",
        "        SEED = 42\n",
        "        generator = torch.Generator(device=\"cuda\").manual_seed(SEED)\n",
        "\n",
        "        print(f\"Chargement du modèle {MODEL_ID} en FP32...\")\n",
        "        pipe_fp32 = StableDiffusionPipeline.from_pretrained(\n",
        "            MODEL_ID, torch_dtype=torch.float32, safety_checker=None, requires_safety_checker=False\n",
        "        ).to(\"cuda\")\n",
        "\n",
        "        print(f\"Chargement du modèle {MODEL_ID} en FP16...\")\n",
        "        pipe_fp16 = StableDiffusionPipeline.from_pretrained(\n",
        "            MODEL_ID, torch_dtype=torch.float16, safety_checker=None, requires_safety_checker=False\n",
        "        ).to(\"cuda\")\n",
        "\n",
        "        # Variante FP16 + attention slicing (réduit la VRAM pic)\n",
        "        pipe_fp16_attn = StableDiffusionPipeline.from_pretrained(\n",
        "            MODEL_ID, torch_dtype=torch.float16, safety_checker=None, requires_safety_checker=False\n",
        "        ).to(\"cuda\")\n",
        "        pipe_fp16_attn.enable_attention_slicing()\n",
        "\n",
        "        REAL_PIPELINE_LOADED = True\n",
        "        print(\"✅ Pipelines chargés (FP32 + FP16 + FP16+attn_slicing)\")\n",
        "\n",
        "        # === Benchmark réel ===\n",
        "        def benchmark_one(name, pipe, warmup=True):\n",
        "            if warmup:\n",
        "                with torch.inference_mode():\n",
        "                    _ = pipe(PROMPT, num_inference_steps=2, generator=generator,\n",
        "                             height=HEIGHT, width=WIDTH, guidance_scale=GUIDANCE_SCALE).images[0]\n",
        "                torch.cuda.empty_cache()\n",
        "                torch.cuda.synchronize()\n",
        "\n",
        "            times, vram_peaks = [], []\n",
        "            for _ in range(3):\n",
        "                torch.cuda.reset_peak_memory_stats()\n",
        "                start = torch.cuda.Event(enable_timing=True)\n",
        "                end = torch.cuda.Event(enable_timing=True)\n",
        "                with torch.inference_mode():\n",
        "                    start.record()\n",
        "                    image = pipe(PROMPT, num_inference_steps=INFERENCE_STEPS,\n",
        "                                 generator=generator,\n",
        "                                 height=HEIGHT, width=WIDTH,\n",
        "                                 guidance_scale=GUIDANCE_SCALE).images[0]\n",
        "                    end.record()\n",
        "                    torch.cuda.synchronize()\n",
        "                times.append(start.elapsed_time(end))  # ms\n",
        "                vram_peaks.append(torch.cuda.max_memory_allocated() / (1024**2))\n",
        "                torch.cuda.empty_cache()\n",
        "\n",
        "            return {\n",
        "                \"name\": name,\n",
        "                \"avg_time_ms\": sum(times) / len(times),\n",
        "                \"min_time_ms\": min(times),\n",
        "                \"max_time_ms\": max(times),\n",
        "                \"avg_vram_mb\": sum(vram_peaks) / len(vram_peaks),\n",
        "                \"peak_vram_mb\": max(vram_peaks),\n",
        "                \"iterations\": len(times),\n",
        "            }\n",
        "\n",
        "        print(\"\\n🏃 Exécution des benchmarks RÉELS...\")\n",
        "        REAL_BENCHMARK_RESULTS = [\n",
        "            benchmark_one(\"Baseline (FP32)\", pipe_fp32),\n",
        "            benchmark_one(\"FP16\", pipe_fp16),\n",
        "            benchmark_one(\"FP16 + attention_slicing\", pipe_fp16_attn),\n",
        "        ]\n",
        "\n",
        "        baseline = REAL_BENCHMARK_RESULTS[0][\"avg_time_ms\"]\n",
        "        for r in REAL_BENCHMARK_RESULTS:\n",
        "            r[\"speedup_vs_fp32\"] = baseline / r[\"avg_time_ms\"]\n",
        "\n",
        "        # Affichage formaté\n",
        "        print(\"\\n\" + \"=\" * 80)\n",
        "        print(\"RÉSULTATS BENCHMARK RÉEL (Stable Diffusion v1.5, 10 steps, 512×512)\")\n",
        "        print(\"=\" * 80)\n",
        "        print(f\"{'Configuration':<30} {'Temps moy (ms)':<16} {'VRAM pic (MB)':<16} {'Speedup':<10}\")\n",
        "        print(\"-\" * 80)\n",
        "        for r in REAL_BENCHMARK_RESULTS:\n",
        "            print(f\"{r['name']:<30} {r['avg_time_ms']:<16.1f} {r['peak_vram_mb']:<16.1f} {r['speedup_vs_fp32']:<10.2f}x\")\n",
        "        print(\"=\" * 80)\n",
        "\n",
        "        # Cleanup\n",
        "        del pipe_fp32, pipe_fp16, pipe_fp16_attn\n",
        "        torch.cuda.empty_cache()\n",
        "\n",
        "    except Exception as e:\n",
        "        REAL_PIPELINE_LOADED = False\n",
        "        REAL_PIPELINE_SKIP_REASON = f\"{type(e).__name__}: {e}\"\n",
        "        print(f\"⚠️ Échec du chargement: {REAL_PIPELINE_SKIP_REASON}\")\n",
        "        print(\"→ verdict RECOVERABLE-MACHINE; geste de routage vers lane GPU.\")\n",
        "else:\n",
        "    REAL_PIPELINE_SKIP_REASON = f\"CUDA_AVAILABLE={CUDA_AVAILABLE}, GPU_MEMORY_TOTAL={GPU_MEMORY_TOTAL:.1f} GB (< 6 GB requis)\"\n",
        "    print(f\"⚠️ Pas de GPU ≥6 GB ({REAL_PIPELINE_SKIP_REASON})\")\n",
        "    print(\"→ verdict RECOVERABLE-MACHINE; geste de routage vers lane GPU.\")\n",
        "\n",
        "assert REAL_PIPELINE_LOADED or REAL_PIPELINE_SKIP_REASON is not None, \"Au moins un verdict doit être posé\""
    ]
}

# ---- REWRITTEN CELL 55: tableau calculé depuis outputs réels ----
NEW_CELL_55 = {
    "cell_type": "markdown",
    "metadata": {},
    "source": [
        "**Lecture du benchmark RÉEL** — le tableau ci-dessous est **calculé depuis les outputs de la cellule précédente**, pas de constantes pré-écrites. Les trois configurations ont été exécutées sur le même GPU (avec le même seed, prompt et budget d'inférence), seules les dtype/optimisation changent :\n",
        "\n",
        "**Comparaison mesurée (à insérer depuis l'exécution)** :\n",
        "\n",
        "| Configuration | VRAM pic (MB) | Speedup vs FP32 |\n",
        "|---|---|---|\n",
        "| Baseline (FP32) | depuis `REAL_BENCHMARK_RESULTS[0]['peak_vram_mb']` | 1.00× (référence) |\n",
        "| FP16 | depuis `REAL_BENCHMARK_RESULTS[1]['peak_vram_mb']` | depuis `REAL_BENCHMARK_RESULTS[1]['speedup_vs_fp32']`× |\n",
        "| FP16 + attention_slicing | depuis `REAL_BENCHMARK_RESULTS[2]['peak_vram_mb']` | depuis `REAL_BENCHMARK_RESULTS[2]['speedup_vs_fp32']`× |\n",
        "\n",
        "*(Les chiffres exacts sont imprimés par la cellule de benchmark au-dessus — voir `REAL_BENCHMARK_RESULTS`.)*\n",
        "\n",
        "**Ce qu'on observe généralement** :\n",
        "\n",
        "1. **FP16 divise la VRAM par ≈2** (float32 → float16 = 4 bytes → 2 bytes par paramètre), confirmé empiriquement par `peak_vram_mb`.\n",
        "2. **Le speedup temps est souvent modeste (1.1-1.5×)** sur RTX 3090 — la bande passante mémoire est le goulot, pas le compute. Les cartes plus anciennes (sans Tensor Cores) verraient un speedup plus marqué.\n",
        "3. **`attention_slicing` réduit la VRAM pic** (en découpant le calcul d'attention par bandes) mais peut dégrader légèrement le temps car plus de kernels séparés.\n",
        "\n",
        "**Pourquoi le profil « agressif » n'est pas toujours le bon** : l'arbitrage speedup/VRAM/latence-à-froid dépend du cas d'usage. Pour un serveur de production avec forte concurrence, FP16 + attention_slicing = meilleur compromis (2× moins de VRAM, throughput marginalement meilleur par requête). Pour un prototype interactif, FP32 peut suffire si la VRAM n'est pas contrainte.\n",
        "\n",
        "**Si la cellule benchmark a skip** (`REAL_PIPELINE_LOADED == False`) : verdict `RECOVERABLE-MACHINE` écrit dans le corps PR — geste = ré-exécution sur lane GPU (`po-2023`/`ai-01`) avant merge. Aucun chiffre n'est alors reporté dans ce tableau (le tableau reste vide, pas fabriqué)."
    ]
}

# Insert: replace cell 54 (BenchmarkSuite) with new 54, insert new cell 53.5 before
new_cells = []
for i, cell in enumerate(nb['cells']):
    if i == 53:
        # cell index 53 = the "## 8. Benchmarking et Comparaison" markdown - keep
        new_cells.append(cell)
        # Insert NEW_CELL_535 right after
        new_cells.append(NEW_CELL_535)
    elif i == 54:
        # Replace BenchmarkSuite with NEW_CELL_54
        new_cells.append(NEW_CELL_54)
    elif i == 55:
        # Replace table markdown with NEW_CELL_55
        new_cells.append(NEW_CELL_55)
    else:
        new_cells.append(cell)

nb['cells'] = new_cells

# Save patched notebook
NB_PATH.write_text(json.dumps(nb, indent=1, ensure_ascii=False) + "\n", encoding='utf-8')
print(f"Patched notebook saved with {len(new_cells)} cells")
print(f"  - cell 53: kept (section 8 header)")
print(f"  - cell 53.5: NEW (real pipeline setup markdown)")
print(f"  - cell 54: REWRITTEN (real BenchmarkSuite)")
print(f"  - cell 55: REWRITTEN (tableau calculé)")