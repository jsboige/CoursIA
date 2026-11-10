"""Capture dense des residus layer-16 du banc 20 prompts 9B (#17740).

Meme modele, meme couche, meme jeu de prompts, meme tokenisation que les
traces SAE (ICT-21) et J-Lens (ICT-24) : le fichier produit est le substrat
commun des mesures F-Lens (geometrie factorisee, ict/flens_traces.py) et
S-Lens (probe de self-location positionnelle, ict/slens_traces.py), aligne
par contrat sur les traces existantes — ``--check-align`` verifie
l'egalite exacte des tokens contre ICT-21 avant d'ecrire quoi que ce soit.

Le jeu de prompts est importe d'``extract_sae_traces`` (source unique du
bench — jamais copie, une copie deriverait).

Usage (GPU 2 d'ai-01 STRICT — vLLM tient GPU 0-1) :

    CUDA_VISIBLE_DEVICES=2 python scripts/extract_dense_traces.py --stage full \
        --check-align traces/ict21_sae_layer16_trained.npz

Defaut : Qwen/Qwen3.5-9B-Base, layer 16, variant trained, seed 42 — les
valeurs des traces ICT-21/ICT-24. Sortie ~20 Mo (2699 tokens x 4096 en
float16 compresse).
"""

from __future__ import annotations

import argparse
import datetime as _dt
import json
import sys
from pathlib import Path

import numpy as np
import torch

sys.path.insert(0, str(Path(__file__).resolve().parent))

from extract_sae_traces import (  # noqa: E402
    PROMPT_SETS,
    CaptureHook,
    find_decoder_layers,
    guard_single_gpu,
)


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--model", default="Qwen/Qwen3.5-9B-Base")
    p.add_argument("--layer", type=int, default=16,
                   help="couche de capture (défaut 16 = ICT-21/ICT-24)")
    p.add_argument("--variant", default="trained",
                   choices=["trained", "control"],
                   help="trained = run réel ; control = permutation seedée des "
                        "lignes d'input embeddings (ICT-21).")
    p.add_argument("--seed", type=int, default=42)
    p.add_argument("--stage", default="smoke", choices=["smoke", "full"],
                   help="smoke = 2 prompts, écrit <out>_smoke.npz ; "
                        "full = 20 prompts, écrit --out.")
    p.add_argument("--out", type=Path, default=None,
                   help="défaut : traces/ict25_dense_layer<L>_<variant>.npz")
    p.add_argument("--check-align", type=Path, default=None,
                   help="trace SAE/J-Lens de référence : l'égalité exacte des "
                        "__tokens par prompt est exigée avant l'écriture.")
    return p.parse_args()


def make_control_permutation(embedding: torch.Tensor,
                             seed: int) -> torch.Tensor:
    """Contrôle ICT-21 : permutation seedée des lignes d'input embeddings."""
    generator = torch.Generator().manual_seed(seed)
    return torch.randperm(embedding.shape[0], generator=generator,
                          device=embedding.device)


def main() -> None:
    args = parse_args()
    t0 = _dt.datetime.now(_dt.timezone.utc)
    torch.manual_seed(args.seed)
    device = guard_single_gpu()

    from transformers import AutoConfig, AutoModelForCausalLM, AutoTokenizer

    cfg = AutoConfig.from_pretrained(args.model)
    text_cfg = getattr(cfg, "text_config", cfg)
    n_layers = getattr(text_cfg, "num_hidden_layers", None)
    d_model = getattr(text_cfg, "hidden_size", None)
    if n_layers is None or d_model is None:
        sys.exit(f"ERREUR: config {args.model} sans num_hidden_layers/hidden_size.")
    if not 0 <= args.layer < n_layers:
        sys.exit(f"ERREUR: --layer {args.layer} hors [{0}, {n_layers - 1}].")
    print(f"[model] {args.model} n_layers={n_layers} d_model={d_model} "
          f"layer={args.layer} ({args.layer / max(n_layers - 1, 1):.3f} frac)")

    tokenizer = AutoTokenizer.from_pretrained(args.model)
    model = AutoModelForCausalLM.from_pretrained(
        args.model, dtype=torch.bfloat16).to(device)
    model.eval()

    if args.variant == "control":
        # Convention ICT-21 : permutation seedée des lignes de la table
        # d'embeddings — le run contrôle garde les mêmes tokens, pas les
        # mêmes representations.
        table = model.get_input_embeddings().weight
        perm = make_control_permutation(table, args.seed)
        with torch.no_grad():
            new_table = table[perm].clone()
            model.get_input_embeddings().weight.data.copy_(new_table)
        print(f"[control] permutation seed={args.seed} des "
              f"{table.shape[0]} lignes d'embeddings appliquée.")

    layers = find_decoder_layers(model, n_layers)
    capture = CaptureHook()
    handle = layers[args.layer].register_forward_hook(capture)

    sets: dict[str, list[str]] = dict(PROMPT_SETS)
    if args.stage == "smoke":
        sets = {"code_python": PROMPT_SETS["code_python"][:1],
                "prose_fr": PROMPT_SETS["prose_fr"][:1]}

    arrays: dict[str, np.ndarray] = {}
    tok_total = 0
    for set_name, prompts in sets.items():
        for i, text in enumerate(prompts):
            enc = tokenizer(text, return_tensors="pt").to(device)
            with torch.no_grad():
                model(**enc)
            hidden = capture.hidden                      # [T, d_model] fp32 CPU
            if hidden is None:
                sys.exit(f"ERREUR: {set_name}__{i} : hook muet — capture ratée.")
            finite = torch.isfinite(hidden).all(dim=-1)
            n_bad = int((~finite).sum())
            if n_bad > 0.05 * hidden.shape[0]:
                sys.exit(f"ERREUR: {set_name}__{i} : {n_bad}/{hidden.shape[0]} "
                         f"positions non finies (> 5%) — chargement de poids "
                         "probablement cassé, pas un token isolé.")
            if n_bad:
                print(f"[warn] {set_name}__{i} : {n_bad} position(s) non "
                      f"finie(s) EXCLUE(S) de la trace dense.")
                hidden = hidden[finite]
            toks = tokenizer.convert_ids_to_tokens(enc["input_ids"][0].tolist())
            if n_bad:
                toks = [t for t, f in zip(toks, finite.tolist()) if f]
            key = f"{set_name}__{i}"
            arrays[f"{key}__tokens"] = np.array(toks, dtype=str)
            arrays[f"{key}__resid"] = hidden.to(torch.float16).numpy()
            tok_total += hidden.shape[0]
            print(f"[trace] {key}: T={hidden.shape[0]} "
                  f"norme moy={hidden.norm(dim=-1).mean():.1f}")

    handle.remove()
    print(f"[sanity] {tok_total} tokens, "
          f"vram pic={torch.cuda.max_memory_allocated() / 2**30:.1f} GiB")

    # Contrat d'alignement AVANT toute écriture : tokens strictement égaux
    # à la trace de référence, prompt par prompt.
    if args.check_align is not None:
        ref = np.load(args.check_align, allow_pickle=False)
        for key in sorted(arrays):
            if not key.endswith("__tokens"):
                continue
            if key not in ref.files:
                sys.exit(f"ERREUR d'alignement : {key} absent de "
                         f"{args.check_align.name}.")
            if not np.array_equal(arrays[key], ref[key]):
                sys.exit(f"ERREUR d'alignement : tokens de {key} différents "
                         f"de {args.check_align.name} — la capture dense ne "
                         "serait PAS le même run. Rien n'est écrit.")
        print(f"[align] tokens égaux à {args.check_align.name} sur "
              f"{len([k for k in arrays if k.endswith('__tokens')])} prompts.")

    traces_dir = Path(__file__).resolve().parent.parent / "traces"
    default_name = f"ict25_dense_layer{args.layer}_{args.variant}.npz"
    out = args.out if args.out is not None else traces_dir / default_name
    if args.stage == "smoke" and args.out is None:
        out = out.with_name(out.stem + "_smoke.npz")
    meta = {
        "model": args.model, "layer": int(args.layer),
        "n_layers": int(n_layers),
        "layer_frac": round(args.layer / max(n_layers - 1, 1), 4),
        "d_model": int(d_model),
        "variant": args.variant, "seed": int(args.seed),
        "capture_convention": ("resid_post hook lecture seule ; modèle bf16, "
                               "capture fp32, stockage float16"),
        "control_convention": ("permutation seedée des lignes d'input "
                               "embeddings (variant control)"),
        "prompt_sets": {k: len(v) for k, v in sets.items()},
        "n_tokens_total": tok_total,
        "aligns_with": ["ict21_sae_layer16_trained.npz",
                        "ict24_jlens_layer16_trained.npz"],
        "date": _dt.datetime.now(_dt.timezone.utc).isoformat(timespec="seconds"),
    }
    arrays["__meta__"] = np.array(json.dumps(meta, ensure_ascii=False))
    np.savez_compressed(out, **arrays)
    print(f"[out] {out} ({out.stat().st_size / 2**20:.1f} Mo, "
          f"{(_dt.datetime.now(_dt.timezone.utc) - t0).total_seconds():.0f} s)")


if __name__ == "__main__":
    main()
