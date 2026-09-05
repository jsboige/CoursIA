"""Fit local J-lens par taille (sous-grain (c) #8236).

Reproduit la construction du lens publie 9B (neuronpedia/jacobian-lens,
Salesforce-wikitext n=458, min_chars 600) sur Qwen3-1.7B-Base et
Qwen3.5-2B-Base, aux profondeurs de calibration SAE (frac 0.25/0.5) :

  1.7B (28 couches) : source_layers [7, 14]
  2B   (24 couches) : source_layers [6, 12]

target = logits finaux (defaut). Le checkpoint de fit est resumable
(checkpoint_path + resume=True) ; le lens final est sauvegarde via
JacobianLens.save (fp16) HORS du depot (convention #8236 : les lens fits
ne sont jamais commites, seules les traces .npz le sont).

Usage :
  python fit_jlens_local.py --model Qwen/Qwen3-1.7B-Base --tag qwen3-1-7b
  python fit_jlens_local.py --model Qwen/Qwen3-1.7B-Base --tag test --n-prompts 3 --fresh
"""

import argparse
import hashlib
import json
import time
from pathlib import Path

import torch

MODELS = {
    "Qwen/Qwen3-1.7B-Base": [7, 14],  # 28 couches : frac 0.25 / 0.5
    "Qwen/Qwen3.5-2B-Base": [6, 12],  # 24 couches : frac 0.25 / 0.5
}
FITS_DIR = Path("C:/dev/jlens_fits")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--model", required=True, choices=sorted(MODELS))
    ap.add_argument("--tag", required=True, help="suffixe du fichier de sortie")
    ap.add_argument("--n-prompts", type=int, default=458)
    ap.add_argument("--min-chars", type=int, default=600)
    ap.add_argument("--dim-batch", type=int, default=8)
    ap.add_argument("--max-seq-len", type=int, default=128)
    ap.add_argument(
        "--fresh", action="store_true", help="ignorer un checkpoint existant"
    )
    args = ap.parse_args()

    import jlens
    from jlens.examples import load_wikitext_prompts

    t0 = time.time()
    device = torch.device("cuda")
    print(f"[device] {torch.cuda.get_device_name(0)}", flush=True)

    from transformers import AutoModelForCausalLM, AutoTokenizer

    tok = AutoTokenizer.from_pretrained(args.model)
    hf_model = AutoModelForCausalLM.from_pretrained(
        args.model, dtype=torch.bfloat16, device_map=device
    )
    print(
        f"[load] {args.model} bf16 {time.time() - t0:.1f}s "
        f"({torch.cuda.memory_allocated() / 2**30:.2f} GiB)",
        flush=True,
    )

    model = jlens.from_hf(hf_model, tok)
    source_layers = MODELS[args.model]
    print(f"[wrap] jlens.from_hf OK, source_layers={source_layers}", flush=True)

    prompts = load_wikitext_prompts(args.n_prompts, min_chars=args.min_chars)
    print(
        f"[prompts] {len(prompts)} WikiText-103 >= {args.min_chars} chars", flush=True
    )

    FITS_DIR.mkdir(parents=True, exist_ok=True)
    ckpt = FITS_DIR / f"{args.tag}_fit_ckpt.pt"
    out = FITS_DIR / f"{args.tag}_jacobian_lens.pt"

    t1 = time.time()
    lens = jlens.fit(
        model,
        prompts,
        source_layers=source_layers,
        dim_batch=args.dim_batch,
        max_seq_len=args.max_seq_len,
        checkpoint_path=str(ckpt),
        resume=not args.fresh,
    )
    lens.save(str(out))
    digest = hashlib.sha256(out.read_bytes()).hexdigest()
    from jlens.fitting import SKIP_FIRST_N_POSITIONS

    stats = {
        "model": args.model,
        "source_layers": source_layers,
        "n_prompts": len(prompts),
        "min_chars": args.min_chars,
        "dim_batch": args.dim_batch,
        "max_seq_len": args.max_seq_len,
        "skip_first": SKIP_FIRST_N_POSITIONS,
        "d_model": lens.d_model,
        "lens_sha256": digest,
        "fit_seconds": round(time.time() - t1, 1),
        "vram_peak_gib": round(torch.cuda.max_memory_allocated() / 2**30, 2),
        "vram_total_gib": round(
            torch.cuda.get_device_properties(0).total_memory / 2**30, 2
        ),
        "lens_path": str(out),
    }
    (FITS_DIR / f"{args.tag}_fit_stats.json").write_text(json.dumps(stats, indent=2))
    print(
        f"[fit] {stats['fit_seconds']}s, pic VRAM "
        f"{stats['vram_peak_gib']}/{stats['vram_total_gib']} GiB",
        flush=True,
    )
    print(f"[lens] {out} ({out.stat().st_size / 2**20:.1f} MiB)", flush=True)
    print(f"[lens] {lens!r}", flush=True)
    print("FIT_OK", flush=True)


if __name__ == "__main__":
    main()
