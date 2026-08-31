"""Fidelite J-lens par taille (sous-grain (c) #8236).

Applique un lens fitte localement (``fit_jlens_local.py``, C:/dev/jlens_fits,
JAMAIS commite) aux PROMPT_SETS de calibration SAE et mesure l'accord
lens-vs-modele aux profondeurs de calibration (frac 0.25/0.5) :

  - ``overlap@10`` : |top10(lens) ∩ top10(modele)| / 10, moyen positions+prompts
  - ``rel_l2``     : ||lens - modele||_2 / ||modele||_2 (lignes positions)
  - ``kl``         : KL(modele || lens) en nats (log_softmax des deux)

Sortie : ``traces/calib_jlens_<tag>.npz`` — une cle par ``<set>__<layer>``
(vecteur [overlap, rel_l2, kl] + n_prompts), plus les metadonnees du fit.
Comparable a ``calib_fidelity_*.npz`` (axe SAE) du meme notebook.

Usage :
  python extract_jlens_fidelity.py --lens qwen3-1-7b --model Qwen/Qwen3-1.7B-Base
"""
import argparse
import json
import sys
from pathlib import Path

import numpy as np
import torch

sys.path.insert(0, str(Path(__file__).parent))
from extract_sae_traces import PROMPT_SETS  # noqa: E402

import jlens  # noqa: E402

FITS_DIR = Path("C:/dev/jlens_fits")
TRACES_DIR = Path(__file__).resolve().parent.parent / "traces"


def prompt_metrics(lens_logits: torch.Tensor, model_logits: torch.Tensor,
                   k: int = 10) -> dict[str, float]:
    """Metrics moyennes sur les positions, une paire [T, vocab]."""
    top_lens = torch.topk(lens_logits, k, dim=-1).indices
    top_true = torch.topk(model_logits, k, dim=-1).indices
    overlap = np.mean([
        len(set(a.tolist()) & set(b.tolist())) / k
        for a, b in zip(top_lens, top_true)
    ])
    rel_l2 = (torch.norm(lens_logits - model_logits, dim=-1)
              / torch.norm(model_logits, dim=-1)).mean().item()
    log_p = torch.log_softmax(model_logits.float(), dim=-1)
    log_q = torch.log_softmax(lens_logits.float(), dim=-1)
    kl = (log_p.exp() * (log_p - log_q)).sum(-1).mean().item()
    return {"overlap10": float(overlap), "rel_l2": float(rel_l2), "kl": float(kl)}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--lens", required=True, help="tag du fit (ex qwen3-1-7b)")
    ap.add_argument("--model", required=True)
    ap.add_argument("--max-prompts", type=int, default=None,
                    help="limite par set (debug)")
    args = ap.parse_args()

    lens_path = FITS_DIR / f"{args.lens}_jacobian_lens.pt"
    stats_path = FITS_DIR / f"{args.lens}_fit_stats.json"
    lens = jlens.JacobianLens.load(str(lens_path))
    print(f"[lens] {lens!r} <- {lens_path.name}", flush=True)

    device = torch.device("cuda")
    from transformers import AutoModelForCausalLM, AutoTokenizer

    tok = AutoTokenizer.from_pretrained(args.model)
    hf_model = AutoModelForCausalLM.from_pretrained(
        args.model, torch_dtype=torch.bfloat16, device_map=device
    )
    model = jlens.from_hf(hf_model, tok)
    print(f"[model] {args.model} charge", flush=True)

    arrays: dict[str, np.ndarray] = {}
    for set_name, prompts in PROMPT_SETS.items():
        if args.max_prompts:
            prompts = prompts[: args.max_prompts]
        per_layer: dict[int, list[dict[str, float]]] = {
            layer: [] for layer in lens.source_layers
        }
        for prompt in prompts:
            ids = tok(prompt, return_tensors="pt")
            positions = list(range(ids["input_ids"].shape[1]))
            lens_logits, model_logits, _ = lens.apply(model, prompt, positions=positions)
            for layer in lens.source_layers:
                per_layer[layer].append(prompt_metrics(
                    torch.as_tensor(lens_logits[layer]).float().cuda(),
                    torch.as_tensor(model_logits).float().cuda(),
                ))
        for layer, rows in per_layer.items():
            mean = {m: float(np.mean([r[m] for r in rows])) for m in rows[0]}
            arrays[f"{set_name}__{layer}"] = np.array(
                [mean["overlap10"], mean["rel_l2"], mean["kl"]], dtype=np.float64
            )
            print(f"[{set_name}] layer {layer}: overlap@10={mean['overlap10']:.4f} "
                  f"rel_l2={mean['rel_l2']:.4f} kl={mean['kl']:.4f}", flush=True)

    fit_stats = json.loads(stats_path.read_text()) if stats_path.exists() else {}
    arrays["meta_model"] = np.array([ord(c) for c in args.model], dtype=np.int16)
    arrays["meta_layers"] = np.array(lens.source_layers, dtype=np.int64)
    arrays["meta_n_fit"] = np.array([fit_stats.get("n_prompts", lens.n_prompts)],
                                    dtype=np.int64)

    TRACES_DIR.mkdir(parents=True, exist_ok=True)
    out = TRACES_DIR / f"calib_jlens_{args.lens}.npz"
    np.savez_compressed(out, **arrays)
    print(f"[out] {out} ({out.stat().st_size/1024:.1f} KiB)", flush=True)
    print("EXTRACT_OK", flush=True)


if __name__ == "__main__":
    main()
