"""Controle de sensibilite par degradation volontaire de la fidelite SAE (#13040, point 3).

Le mecanisme a tester (corps de #13040) : un SAE qui explique peu de variance
ne resout pas la structure specifique au modele ; son top-64 differentiel
serait domine par les directions generiques a forte variance qu'il capte
quand meme, partagees avec le controle -> recouvrement eleve. Si, en degradant
le SAE du point le PLUS FIDELE (2B-Qwen3.5 W32K, FVU 0.5678 d'apres #12938)
jusqu'a la FVU du point le MOINS FIDELE (1.7B-Qwen3 W32K, FVU 0.6958), le
recouvrement MONTE vers celui du point mal reconstruit (55/64), le mecanisme
est demontre a l'INTERIEUR d'un seul point -- sans confusion de generation ni
probleme de n=4.

Methode :

* capture du ``resid_post`` a la profondeur appariee, UNE FOIS par variante
  (``trained``, puis ``control`` = permutation seedee des lignes d'input
  embeddings, sanction #5101, meme graine 42 que les traces committees) ;
  le residual ne depend pas du SAE, donc la capture n'est payee qu'une fois ;
* pour chaque fraction conservee ``f`` du dictionnaire : masque IMBRIQUE
  monotone (une meme permutation seede des indices ; on garde les premiers
  ``int(f * d_sae)`` -- les ensembles survivants sont emboites, la degradation
  est monotone en ``f``), encodage top-k officiel restreint aux survivantes
  (les features tronquees sont exclues du top-k via ``-inf``), reconstruction
  sparse-exacte, puis :

  - FVU corpus sur la variante trained (meme convention que
    :mod:`scripts.extract_sae_fidelity`) ;
  - panels differentiels k=64 par variance inter-jeux
    (:func:`ict.sae_traces.differential_features`) pour les DEUX variantes ->
    ``overlap_diff64 = |panel_trained & panel_control|`` (meme definition que
    les cellules cross-echelle d'ICT-21) ;

* le niveau ``f = 1.0`` est le TEMOIN de l'instrument : sa FVU doit retrouver
  celle de #12938 et son overlap celui de la ligne 2B d'ICT-21.

Sortie ``traces/calib_degradation_<slug>_layer{L}of{N}.npz`` (sans pickle) :
``report`` JSON (niveaux, temoin, cible) + tableaux alignes ``fracs``,
``fvus``, ``overlaps``, ``l0s``. GPU pour le forward du modele uniquement ;
l'encodage SAE reste CPU float32 comme dans toute la serie.

Usage (carte locale, venv GPU) :
    python extract_sae_degradation.py --target-fvu 0.6958
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
    fraction_variance_unexplained,
    l0_measured,
)
from ict.sae_traces import (  # noqa: E402
    check_sae_model_match,
    differential_features,
    resolve_capture_layer,
)
from scripts.extract_sae_traces import (  # noqa: E402
    PROMPT_SETS,
    apply_control_permutation,
    load_sae,
)

DEFAULT_MODEL = "Qwen/Qwen3.5-2B-Base"
DEFAULT_SAE_REPO = "Qwen/SAE-Res-Qwen3.5-2B-Base-W32K-L0_50"
# Fractions decroissantes : le sweep s'arrete un niveau APRES la cible pour
# dessiner la courbe au-dela du point d'egalisation de FVU.
DEFAULT_FRACS = (1.0, 0.5, 0.3, 0.2, 0.15, 0.1, 0.07, 0.05, 0.03, 0.02, 0.01)


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    depth = p.add_mutually_exclusive_group()
    depth.add_argument("--layer", type=int, default=None,
                       help="couche resid_post absolue")
    depth.add_argument("--layer-frac", type=float, default=0.5,
                       help="profondeur relative appariee (defaut 0.5)")
    p.add_argument("--model", default=DEFAULT_MODEL)
    p.add_argument("--sae-repo", default=DEFAULT_SAE_REPO)
    p.add_argument("--out-dir", default=str(Path(__file__).resolve().parent.parent / "traces"))
    p.add_argument("--k", type=int, default=None,
                   help="top-k d'encodage (defaut : lu du config.json du depot SAE)")
    p.add_argument("--control-seed", type=int, default=42,
                   help="graine de la permutation du modele-controle (defaut 42, "
                        "meme convention que les traces committees)")
    p.add_argument("--mask-seed", type=int, default=42,
                   help="graine de la permutation des features du dictionnaire")
    p.add_argument("--target-fvu", type=float, default=0.6958,
                   help="FVU a egaliser (defaut : celle du point le moins fidele, "
                        "1.7B-Qwen3 W32K d'apres #12938)")
    p.add_argument("--fracs", type=float, nargs="+", default=list(DEFAULT_FRACS),
                   help="fractions conservees decroissantes du dictionnaire")
    return p.parse_args()


def model_slug(model: str) -> str:
    return re.sub(r"[^a-z0-9]+", "-", model.split("/")[-1].lower()).strip("-")


def encode_topk_masked(h: torch.Tensor, sae: dict, k: int, keep: torch.Tensor):
    """Encodage top-k officiel restreint aux features survivantes.

    Les colonnes tronquees recoivent ``-inf`` AVANT relu : elles ne peuvent
    plus entrer dans le top-k (relu les ramenerait a 0 et top-k pourrait les
    selectionner quand moins de k features positives survivent).
    """
    pre = h @ sae["W_enc"].T + sae["b_enc"]          # [T, d_sae]
    pre = pre.masked_fill(~keep, float("-inf"))
    acts = torch.relu(pre)
    vals, ids = torch.topk(acts, k, dim=-1)
    return ids.to(torch.int32), vals


def recon_sparse(vals: torch.Tensor, ids: torch.Tensor, w_dec: torch.Tensor,
                 b_dec: torch.Tensor | None = None) -> torch.Tensor:
    """Reconstruction sparse-exacte (meme forme que extract_sae_fidelity, b_dec inclus)."""
    w_cols = w_dec[ids.to(torch.long)]                # [T, k, d]
    recon = torch.einsum("tk,tkd->td", vals.to(torch.float32), w_cols)
    if b_dec is not None:
        recon = recon + b_dec.to(torch.float32)
    return recon


def main() -> None:
    args = parse_args()
    t0 = time.time()
    torch.manual_seed(42)
    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    print(f"[device] {device}" + (
        f" ({torch.cuda.get_device_name(0)})" if device.type == "cuda" else ""))

    from transformers import AutoConfig, AutoModelForCausalLM, AutoTokenizer

    print(f"[load] config {args.model} ...")
    cfg = AutoConfig.from_pretrained(args.model)
    text_cfg = getattr(cfg, "text_config", cfg)
    n_layers = getattr(text_cfg, "num_hidden_layers", None)
    d_model = getattr(text_cfg, "hidden_size", None)
    depth = resolve_capture_layer(n_layers, args.layer, args.layer_frac)
    layer = depth["layer"]
    print(f"[depth] couche {layer}/{n_layers - 1} (frac {depth['layer_frac']:.3f})")

    sae = load_sae(args.sae_repo, layer, device)
    check_sae_model_match(sae["W_enc"].shape[1], d_model, args.sae_repo, args.model)
    if sae["W_dec"] is None:
        sys.exit(f"ERREUR: {args.sae_repo} n'expose pas W_dec -- reconstruction impossible.")
    # Layout heterogene des checkpoints Qwen-Scope : W32K stocke W_dec
    # [d_model, d_sae] (cf extract_sae_fidelity, normalisation non ambigue).
    if sae["W_dec"].shape[0] == d_model:
        sae["W_dec"] = sae["W_dec"].t().contiguous()

    from huggingface_hub import hf_hub_download
    sae_cfg = json.loads(
        Path(hf_hub_download(args.sae_repo, "config.json")).read_text(encoding="utf-8")
    )
    k_release = int(sae_cfg.get("top_k") or sae_cfg.get("k") or 50)
    k = args.k if args.k is not None else k_release
    print(f"[sae] k={k} (release {args.sae_repo.rsplit('-', 1)[-1]})")
    d_sae = int(sae["W_enc"].shape[0])

    print(f"[load] modele {args.model} (bf16) ...")
    model = AutoModelForCausalLM.from_pretrained(
        args.model, torch_dtype=torch.bfloat16, device_map=device
    )
    model.eval()
    tokenizer = AutoTokenizer.from_pretrained(args.model)
    blocks = model.model.layers

    def capture_variant() -> dict[str, list[torch.Tensor]]:
        out: dict[str, list[torch.Tensor]] = {}
        for set_name, prompts in PROMPT_SETS.items():
            per: list[torch.Tensor] = []
            for text in prompts:
                enc = tokenizer(text, return_tensors="pt").to(device)
                captured: dict[str, torch.Tensor] = {}

                def hook(module, inputs, output):
                    o = output[0] if isinstance(output, tuple) else output
                    captured["h"] = o.detach()[0].to(torch.float32).cpu()

                handle = blocks[layer].register_forward_hook(hook)
                with torch.no_grad():
                    model(**enc)
                handle.remove()
                per.append(captured["h"])
            out[set_name] = per
        return out

    print("[variant] trained -- capture du residual (une seule fois) ...")
    h_trained = capture_variant()
    print("[variant] control -- permutation seedee puis capture ...")
    apply_control_permutation(model, args.control_seed)
    h_control = capture_variant()
    del model, blocks
    if device.type == "cuda":
        torch.cuda.empty_cache()
    n_tokens = sum(h.shape[0] for per in h_trained.values() for h in per)
    print(f"[capture] {n_tokens} tokens x 2 variantes")

    # Permutation secrete des features -> masques emboites monotones.
    gen = torch.Generator().manual_seed(args.mask_seed)
    perm = torch.randperm(d_sae, generator=gen)

    fracs: list[float] = []
    fvus: list[float] = []
    overlaps: list[int] = []
    l0s: list[float] = []
    n_keeps: list[int] = []
    target_reached = False

    for f in sorted(set(args.fracs), reverse=True):
        n_keep = max(k, int(round(f * d_sae)))
        keep = torch.zeros(d_sae, dtype=torch.bool)
        keep[perm[:n_keep]] = True

        panels: dict[str, set[int]] = {}
        h_corpus_parts: list[np.ndarray] = []
        r_corpus_parts: list[np.ndarray] = []
        v_corpus_parts: list[np.ndarray] = []
        for variant, h_sets in (("trained", h_trained), ("control", h_control)):
            traces = {"meta": {"d_sae": d_sae}, "prompts": {}}
            for set_name, per in h_sets.items():
                for i, h in enumerate(per):
                    ids, vals = encode_topk_masked(h, sae, k, keep)
                    traces["prompts"][(set_name, i)] = {
                        "ids": ids.numpy(),
                        "vals": vals.to(torch.float32).numpy(),
                    }
                    if variant == "trained":
                        h_corpus_parts.append(h.numpy())
                        r_corpus_parts.append(
                            recon_sparse(vals, ids, sae["W_dec"],
                                         sae.get("b_dec")).numpy())
                        v_corpus_parts.append(vals.to(torch.float32).numpy())
            panels[variant] = set(differential_features(traces, k=64).tolist())

        h_c = np.concatenate(h_corpus_parts)
        r_c = np.concatenate(r_corpus_parts)
        v_c = np.concatenate(v_corpus_parts)
        fvu = round(float(fraction_variance_unexplained(h_c, r_c)), 4)
        overlap = len(panels["trained"] & panels["control"])
        l0 = round(float(l0_measured(v_c)), 2)
        fracs.append(round(n_keep / d_sae, 5))
        n_keeps.append(n_keep)
        fvus.append(fvu)
        overlaps.append(overlap)
        l0s.append(l0)
        print(f"[level] keep={n_keep}/{d_sae} ({100 * n_keep / d_sae:.1f}%) "
              f"fvu={fvu:.4f} overlap_diff64={overlap}/64 l0={l0:.2f}")
        if fvu >= args.target_fvu:
            if target_reached:
                break  # un niveau au-dela de la cible : la courbe se dessine
            target_reached = True

    out = Path(args.out_dir) / (
        f"calib_degradation_{model_slug(args.model)}_layer{layer}of{n_layers}.npz"
    )
    report = {
        "model": args.model,
        "sae_repo": args.sae_repo,
        "layer": layer,
        "n_layers": n_layers,
        "d_model": d_model,
        "d_sae": d_sae,
        "k": k,
        "control_seed": args.control_seed,
        "mask_seed": args.mask_seed,
        "target_fvu": args.target_fvu,
        "n_tokens": int(n_tokens),
        "levels": [
            {"frac_kept": fr, "n_keep": nk, "fvu": fv, "overlap_diff64": ov, "l0": l0}
            for fr, nk, fv, ov, l0 in zip(fracs, n_keeps, fvus, overlaps, l0s)
        ],
        "witness_fvu_f1": fvus[0] if fracs and fracs[0] >= 1.0 else None,
        "witness_overlap_f1": overlaps[0] if fracs and fracs[0] >= 1.0 else None,
    }
    np.savez_compressed(
        out,
        fracs=np.array(fracs, dtype=np.float64),
        fvus=np.array(fvus, dtype=np.float64),
        overlaps=np.array(overlaps, dtype=np.int64),
        l0s=np.array(l0s, dtype=np.float64),
        n_keeps=np.array(n_keeps, dtype=np.int64),
        report=np.array(json.dumps(report, ensure_ascii=False)),
    )
    print(f"[out] {out} ({out.stat().st_size / 1e6:.1f} Mo)")
    print(f"[done] {time.time() - t0:.1f}s")


if __name__ == "__main__":
    main()
