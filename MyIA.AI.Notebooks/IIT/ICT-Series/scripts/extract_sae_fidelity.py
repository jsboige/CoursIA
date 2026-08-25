"""Capture de fidelite de reconstruction SAE par taille (Livrable 1 Phase 0, #8236).

Etablit la verite-terrain demandee par le corps de #8236 : pour chaque taille
modelee localement, mesure ce que le SAE officiel Qwen-Scope reconstruit du
residual stream a sa profondeur appariee, sur la MEME batterie de prompts que
les traces ICT-21 (``PROMPT_SETS`` de :mod:`scripts.extract_sae_traces` --
batterie appariee, Phase 2 de l'issue).

Pour chaque jeu de prompts et pour le corpus aggrege :

* capture du ``resid_post`` a ``--layer-frac`` (profondeur relative appariee,
  convention cross-echelle de la serie) ;
* encodage top-k officiel (demo Qwen-Scope) puis decodage ``acts @ W_dec``
  (le checkpoint stocke ``W_dec`` en [d_model, d_sae] : mathematiquement
  ``acts @ W_dec.T``, prises en colonnes) :
  la reconstruction est produite par le pipeline pour que la metrique mesure
  ce que l'aval consomme reellement ;
* metriques : MSE par element, FVU corpus, L0 mesure, compte d'activations
  par feature -> features mortes. Toutes calculees par
  :mod:`ict.sae_calibration` (numpy-only, teste unitairement) -- aucun calcul
  duplique dans ce script.

Sortie ``traces/calib_fidelity_<slug>_layer{L}of{N}.npz`` (sans pickle) :

* ``counts_total`` [d_sae] int64 et ``counts_<set>`` -- activites par feature ;
* ``l0_vals_<set>`` [T, k] float16 -- valeurs top-k (distribution L0) ;
* ``report`` -- JSON : ``fidelity_report`` corpus + un sous-dict par jeu ;
* ``meta`` -- modele / depot SAE / couche / k / d_model.

GPU UNIQUEMENT (regle d'architecture : ``ict/`` reste numpy-only, ce script
confine torch/transformers, cf :mod:`scripts.extract_sae_traces`). Dimensionne
pour les cartes 8 Go de la serie : bf16, un seul modele en memoire, un prompt
a la fois.

Usage (carte locale, venv GPU) :
    python extract_sae_fidelity.py --model Qwen/Qwen3-1.7B-Base \
        --sae-repo Qwen/SAE-Res-Qwen3-1.7B-Base-W32K-L0_50 --layer-frac 0.5
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import time
from pathlib import Path

import numpy as np
import torch

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from ict.sae_calibration import (  # noqa: E402
    dead_features,
    fidelity_report,
    fraction_variance_unexplained,
    l0_measured,
    reconstruction_mse,
)
from ict.sae_traces import (  # noqa: E402
    assert_bf16_readout,
    assert_sae_topk_compatible,
    check_sae_model_match,
    resolve_capture_layer,
)
from scripts.extract_sae_traces import PROMPT_SETS, load_sae, sae_encode_topk  # noqa: E402

DEFAULT_MODEL = "Qwen/Qwen3-1.7B-Base"
DEFAULT_SAE_REPO = "Qwen/SAE-Res-Qwen3-1.7B-Base-W32K-L0_50"


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    depth = p.add_mutually_exclusive_group()
    depth.add_argument("--layer", type=int, default=None,
                       help="couche resid_post absolue")
    depth.add_argument("--layer-frac", type=float, default=0.5,
                       help="profondeur relative appariee (defaut 0.5, convention #8236)")
    p.add_argument("--model", default=DEFAULT_MODEL)
    p.add_argument("--sae-repo", default=DEFAULT_SAE_REPO)
    p.add_argument("--out-dir", default=str(Path(__file__).resolve().parent.parent / "traces"))
    p.add_argument("--k", type=int, default=None,
                   help="top-k d'encodage (defaut : lu du config.json du depot SAE)")
    return p.parse_args()


def model_slug(model: str) -> str:
    return re.sub(r"[^a-z0-9]+", "-", model.split("/")[-1].lower()).strip("-")


def main() -> None:
    args = parse_args()
    t0 = time.time()
    torch.manual_seed(42)
    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    print(f"[device] {device}" + (f" ({torch.cuda.get_device_name(0)})" if device.type == "cuda" else ""))

    from transformers import AutoConfig, AutoModelForCausalLM, AutoTokenizer

    print(f"[load] config {args.model} ...")
    cfg = AutoConfig.from_pretrained(args.model)
    text_cfg = getattr(cfg, "text_config", cfg)
    n_layers = getattr(text_cfg, "num_hidden_layers", None)
    d_model = getattr(text_cfg, "hidden_size", None)
    depth = resolve_capture_layer(n_layers, args.layer, args.layer_frac)
    layer = depth["layer"]
    print(f"[depth] couche {layer}/{n_layers - 1} (frac {depth['layer_frac']:.3f})")

    # Garde quantization : la fidelite doit etre mesuree sur le vrai bf16, pas
    # sur un readout quantize qui degraderait le residual AVANT le SAE.
    assert_bf16_readout(getattr(cfg, "quantization_config", None), args.model)

    sae = load_sae(args.sae_repo, layer, device)
    check_sae_model_match(sae["W_enc"].shape[1], d_model, args.sae_repo, args.model)
    if sae["W_dec"] is None:
        sys.exit(f"ERREUR: {args.sae_repo} n'expose pas W_dec -- reconstruction impossible.")

    # k : lu depuis le config.json du depot SAE (top-k officiel de la release),
    # garde assert_sae_topk_compatible contre une --k explicite divergente.
    from huggingface_hub import hf_hub_download
    sae_cfg = json.loads(
        Path(hf_hub_download(args.sae_repo, "config.json")).read_text(encoding="utf-8")
    )
    # Les releases Qwen-Scope exposent le top-k sous la cle "k" (le fallback 50
    # ne serait correct que pour les releases L0_50 -- L0_100 serait faux).
    k_release = int(sae_cfg.get("top_k") or sae_cfg.get("k") or 50)
    k = args.k if args.k is not None else k_release
    assert_sae_topk_compatible(k_release, k)
    print(f"[sae] k={k} (release {args.sae_repo.rsplit('-', 1)[-1]})")

    print(f"[load] modele {args.model} (bf16) ...")
    model = AutoModelForCausalLM.from_pretrained(
        args.model, torch_dtype=torch.bfloat16, device_map=device
    )
    model.eval()
    tokenizer = AutoTokenizer.from_pretrained(args.model)
    blocks = model.model.layers

    d_sae = sae["W_enc"].shape[0]
    arrays: dict[str, np.ndarray] = {}
    h_all: list[np.ndarray] = []
    r_all: list[np.ndarray] = []
    v_all: list[np.ndarray] = []
    counts_total = np.zeros(d_sae, dtype=np.int64)
    per_set: dict[str, dict] = {}

    for set_name, prompts in PROMPT_SETS.items():
        h_parts, r_parts, v_parts, ids_parts = [], [], [], []
        for text in prompts:
            enc = tokenizer(text, return_tensors="pt").to(device)
            captured: dict[str, torch.Tensor] = {}

            def hook(module, inputs, output):
                out = output[0] if isinstance(output, tuple) else output
                captured["h"] = out.detach()[0].to(torch.float32).cpu()

            handle = blocks[layer].register_forward_hook(hook)
            with torch.no_grad():
                model(**enc)
            handle.remove()
            h = captured["h"]                                    # [T, d] f32
            ids, vals = sae_encode_topk(h, sae, k=k)             # convention demo
            # Reconstruction sparse-exacte : somme des k contributions decodeur.
            # Le checkpoint stocke W_dec [d_model, d_sae] -> colonnes d'indices.
            w_cols = sae["W_dec"].t()[ids.to(torch.long)]        # [T, k, d]
            recon = torch.einsum("tk,tkd->td", vals.to(torch.float32), w_cols)
            h_parts.append(h.numpy())
            r_parts.append(recon.numpy())
            v_parts.append(vals.to(torch.float16).numpy())
            ids_parts.append(ids.numpy())
        h_set = np.concatenate(h_parts)                          # [T_set, d]
        r_set = np.concatenate(r_parts)
        v_set = np.concatenate(v_parts).astype(np.float32)       # [T_set, k]
        # Counts alignes sur la semantique de ict.sae_calibration : une feature
        # est "active" sur un token si sa valeur relu est NON NULLE (un slot
        # top-k selectionne mais annule par relu n'est pas une activation).
        counts_set = np.zeros(d_sae, dtype=np.int64)
        for i, v in zip(ids_parts, v_parts):
            live = i.reshape(-1)[v.reshape(-1).astype(np.float32) > 0]
            np.add.at(counts_set, live, 1)
        counts_total += counts_set
        per_set[set_name] = {
            "n_tokens": int(h_set.shape[0]),
            "reconstruction_mse": round(reconstruction_mse(h_set, r_set), 6),
            "fvu": round(fraction_variance_unexplained(h_set, r_set), 4),
            "l0_measured": round(l0_measured(v_set), 2),
        }
        arrays[f"counts_{set_name}"] = counts_set
        arrays[f"l0_vals_{set_name}"] = v_set.astype(np.float16)
        h_all.append(h_set)
        r_all.append(r_set)
        v_all.append(v_set)
        print(f"[set] {set_name}: {per_set[set_name]}")

    h_corpus = np.concatenate(h_all)
    r_corpus = np.concatenate(r_all)
    v_corpus = np.concatenate(v_all)
    label = f"{model_slug(args.model)} / {args.sae_repo.rsplit('-', 2)[-2]} ({layer}/{n_layers - 1})"
    report = fidelity_report(
        h_corpus, r_corpus, v_corpus, counts_total,
        k_release=k_release, label=label,
    )
    report["per_set"] = per_set
    report["sae_repo"] = args.sae_repo
    report["model"] = args.model
    report["layer_frac"] = depth["layer_frac"]

    out = Path(args.out_dir) / (
        f"calib_fidelity_{model_slug(args.model)}_layer{layer}of{n_layers - 1}.npz"
    )
    np.savez_compressed(
        out,
        counts_total=counts_total,
        report=np.array(json.dumps(report, ensure_ascii=False)),
        meta=np.array(json.dumps({
            "model": args.model, "sae_repo": args.sae_repo, "layer": layer,
            "n_layers": n_layers, "d_model": d_model, "d_sae": d_sae, "k": k,
        }, ensure_ascii=False)),
        **arrays,
    )
    print(f"[out] {out} ({out.stat().st_size / 1e6:.1f} Mo)")
    print(f"[done] {time.time() - t0:.1f}s")


if __name__ == "__main__":
    main()
