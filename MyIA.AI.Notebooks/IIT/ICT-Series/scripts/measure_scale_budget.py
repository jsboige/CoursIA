"""Mesure MESUREE du budget d'echelle du protocole Geometry of Truth v2 (#16760, G1).

Arbitrage ai-01 2026-09-26T13:48Z + amendement 13:53Z : G1 chiffre, mesure et
pas estime, (a) les jambes 27B sur GPU 2 -- Qwen3.5-27B ET Swift-1.5 27B
(contraste generation a taille egale) -- et (b) ce que coute un echelon >= 70B
voie (a) : 70B quantifie avec debordement CPU partiel sur GPU 2. Ce harness
produit les artefacts ``traces/scale_budget_<slug>_<mode>.json`` : temps de
chargement, empreinte VRAM apres chargement, pointe de passe (allouee et
reservee), duree et debit de la batterie fixe de :mod:`ict.scale_budget`,
passe SAE comprise quand l'echelon est couvert, compte reel de parametres.

Conventions de la serie respectees :

* torch/transformers confines dans ``scripts/`` (``ict/`` reste numpy-only) ;
* determinisme #16590 : seed fixe, TF32 desactive (matmul + cudnn), un
  enonce a la fois, aucune augmentation ;
* ``--max-gpu-gib`` = placement device_map=auto, la metrique bf16 reste
  integre (convention ``extract_sae_fidelity``) ;
* NF4 = mesure de COUT seulement : la lecture quantifiee ne satisfait pas
  ``assert_bf16_readout`` et ne doit jamais servir a la fidelite SAE -- le
  choix bf16-offload vs nf4 pour G2 sera arbitre sur ces chiffres ;
* ``as-is`` = quantification du checkpoint (AWQ W4A16 pour Swift) relue
  depuis sa config, rien force -- et REFUS du debordement CPU (noyau AWQ
  CUDA uniquement) : la voie offload est nf4 ;
* un echelon sans SAE publiee (Swift, >= 70B) consigne la raison dans
  l'artefact : la couverture outillage passe par J-Lens / F-Lens, qui ne
  dependent d'aucune SAE pre-entrainee.

Usage (carte locale contrainte) :
    python measure_scale_budget.py --rung 2b --mode bf16-offload --max-gpu-gib 4.5
    python measure_scale_budget.py --rung 2b --mode nf4
Usage (GPU 2, ai-01, fenetre reservee -- les trois mesures en UNE commande) :
    CUDA_VISIBLE_DEVICES=2 python measure_scale_budget.py --suite gpu2
    # variante si les poids Swift sont deja sur disque (chemin local) :
    CUDA_VISIBLE_DEVICES=2 python measure_scale_budget.py --suite gpu2 --model <chemin Swift>
Usage (sonde >= 70B) :
    # arithmetique seule :
    python measure_scale_budget.py --dry-run --model Qwen/Qwen3.5-72B --card-gib 24 --two-cards
    # voie (a) mesuree : quantifie au chargement + debordement CPU sur GPU 2
    CUDA_VISIBLE_DEVICES=2 python measure_scale_budget.py --model Qwen/Qwen3.5-72B --mode nf4 --max-gpu-gib 22
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from ict.scale_budget import (  # noqa: E402
    BATTERY,
    LADDER,
    MAX_SAE_BACKBONE,
    _suffix_e9,
    format_plan,
    plan_rung,
    sae_lookup,
)
from ict.sae_traces import resolve_capture_layer  # noqa: E402

RUNG_BY_KEY = {}
for _entry in LADDER:
    RUNG_BY_KEY[_entry["rung"].lower()] = _entry          # r1 / r2 / r3 / r4
    if _entry["sae_repo"] is None:
        continue  # R4 : les tokens de taille ("27b") appartiennent a R3
    for _part in _entry["model"].split("/")[-1].lower().split("-"):
        if _part.endswith("b") and _part[:-1].replace(".", "").isdigit():
            RUNG_BY_KEY[_part] = _entry                    # 2b / 9b / 27b
RUNG_BY_KEY["swift"] = RUNG_BY_KEY["swift27b"] = RUNG_BY_KEY["r4"]

#: Amendement ai-01 13:53Z -- la commande unique de la fenetre GPU 2 :
#: les deux lectures du 27B Qwen3.5 (cout nf4, metrique integre bf16-offload)
#: puis l'echelon Swift as-is. Passe SAE incluse sur les echelons couverts.
GPU2_SUITE = (
    # (rung, mode, max_gpu_gib)
    ("r3", "nf4", None),
    ("r3", "bf16-offload", 22.0),
    ("r4", "as-is", None),
)


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    rung = p.add_mutually_exclusive_group()
    rung.add_argument("--rung", choices=sorted(RUNG_BY_KEY), default=None,
                      help="rung du protocole v2 : 2b/9b/27b (R1-R3) ou swift (R4)")
    rung.add_argument("--suite", choices=("gpu2",), default=None,
                      help="suite GPU 2 en une commande (amendement 13:53Z) : "
                           "27b nf4, 27b bf16-offload 22 Gio, swift as-is")
    p.add_argument("--model", default=None,
                   help="backbone explicite : sonde hors echelle seul (ex 72B), "
                        "OU chemin local qui surcharge le modele du rung "
                        "(poids Swift sur disque) / de la suite (applique a Swift)")
    p.add_argument("--mode", choices=("bf16-offload", "nf4", "as-is"), default="bf16-offload",
                   help="bf16-offload : device_map=auto borne --max-gpu-gib, metrique "
                        "integre ; nf4 : bitsandbytes 4-bit (quantifie au chargement, "
                        "offload possible) ; as-is : quantification du checkpoint (AWQ)")
    p.add_argument("--max-gpu-gib", type=float, default=None,
                   help="budget GPU GiB pour le placement (defaut : toute la carte)")
    p.add_argument("--layer-frac", type=float, default=0.5,
                   help="profondeur relative appariee (convention cross-echelle, defaut 0.5)")
    p.add_argument("--prompts", type=int, default=None,
                   help="sous-echantillon de la batterie (defaut : les 24 enonces)")
    p.add_argument("--skip-sae", action="store_true",
                   help="mesurer la passe modele seule (carte trop petite pour le SAE)")
    p.add_argument("--dry-run", action="store_true",
                   help="plan arithmetique seul, aucun chargement (mode sonde)")
    p.add_argument("--card-gib", type=float, default=24.0,
                   help="taille de la carte pour le plan (defaut 24)")
    p.add_argument("--two-cards", action="store_true",
                   help="plan sur deux cartes reunies (sonde >= 70B voie (b))")
    p.add_argument("--out-dir", default=str(Path(__file__).resolve().parent.parent / "traces"))
    return p.parse_args()


def model_slug(model: str) -> str:
    return re.sub(r"[^a-z0-9]+", "-", model.split("/")[-1].lower()).strip("-")


def _max_memory(max_gpu_gib: float | None) -> dict:
    if max_gpu_gib is None:
        return {}
    return {"max_memory": {0: f"{max_gpu_gib}GiB", "cpu": "64GiB"}}


def measure(args: argparse.Namespace, entry: dict, model_override: str | None = None) -> dict:
    import torch

    model_id = model_override or entry["model"]
    torch.manual_seed(42)
    torch.backends.cuda.matmul.allow_tf32 = False
    torch.backends.cudnn.allow_tf32 = False
    device = torch.device("cuda")
    gpu_name = torch.cuda.get_device_name(0)
    total_gib = torch.cuda.get_device_properties(0).total_memory / 1024.0 ** 3
    print(f"[device] {gpu_name} ({total_gib:.1f} Gio)")

    from transformers import AutoConfig, AutoModelForCausalLM, AutoTokenizer

    cfg = AutoConfig.from_pretrained(model_id)
    text_cfg = getattr(cfg, "text_config", cfg)
    n_layers = getattr(text_cfg, "num_hidden_layers", None) or entry["n_layers"]
    if n_layers is None:
        raise SystemExit(f"[depth] nombre de couches illisible pour {model_id} "
                         "(registre et config muets tous deux)")
    depth = resolve_capture_layer(n_layers, None, args.layer_frac)
    layer = depth["layer"]
    print(f"[depth] couche {layer}/{n_layers - 1} (frac {depth['layer_frac']:.3f})")

    t0 = time.time()
    if args.mode == "nf4":
        from transformers import BitsAndBytesConfig
        quant = BitsAndBytesConfig(load_in_4bit=True, bnb_4bit_quant_type="nf4",
                                   bnb_4bit_compute_dtype=torch.bfloat16)
        place = _max_memory(args.max_gpu_gib) or {"device_map": {"": 0}}
        if "max_memory" in place:
            place["device_map"] = "auto"
        model = AutoModelForCausalLM.from_pretrained(model_id, quantization_config=quant,
                                                     torch_dtype=torch.bfloat16, **place)
    elif args.mode == "as-is":
        if args.max_gpu_gib is not None:
            raise SystemExit("[mode] as-is + --max-gpu-gib : un checkpoint quantifie "
                             "(AWQ) ne deborde pas sur CPU (noyau CUDA seul) -- "
                             "la voie offload est nf4")
        model = AutoModelForCausalLM.from_pretrained(model_id, torch_dtype=torch.bfloat16,
                                                     device_map={"": 0})
    else:  # bf16-offload
        kwargs = _max_memory(args.max_gpu_gib)
        model = AutoModelForCausalLM.from_pretrained(model_id, torch_dtype=torch.bfloat16,
                                                     device_map="auto", **kwargs)
    load_s = time.time() - t0
    n_params = sum(p.numel() for p in model.parameters())
    foot_alloc = torch.cuda.memory_allocated() / 1024.0 ** 3
    foot_reserved = torch.cuda.memory_reserved() / 1024.0 ** 3
    print(f"[load] {args.mode} : {load_s:.1f}s -- {n_params/1e9:.2f}e9 parametres reels -- "
          f"empreinte {foot_alloc:.2f}/{foot_reserved:.2f} Gio (alloc/reserve)")

    tokenizer = AutoTokenizer.from_pretrained(model_id)
    statements = BATTERY if args.prompts is None else BATTERY[: args.prompts]

    hidden_store: dict[str, object] = {}

    def hook(_module, _inp, out):
        # Convention canonique extract_sae_fidelity : le residuel ou qu'il
        # soit calcule -- tuple (HF standard) ou tenseur nu (couches
        # hybrides linear_attn de Qwen3.5). [0] = batch, -> [T, d].
        o = out[0] if isinstance(out, tuple) else out
        hidden_store["h"] = o.detach()[0].to(torch.float32)

    target = model.model.layers[layer]
    handle = target.register_forward_hook(hook)

    torch.cuda.reset_peak_memory_stats()
    t1 = time.time()
    n_tokens = 0
    with torch.no_grad():
        for text in statements:
            ids = tokenizer(text, return_tensors="pt").to(device)
            model(**ids)
            n_tokens += int(ids["input_ids"].shape[1])
    pass_s = time.time() - t1
    handle.remove()

    peak_alloc = torch.cuda.max_memory_allocated() / 1024.0 ** 3
    peak_reserved = torch.cuda.max_memory_reserved() / 1024.0 ** 3
    print(f"[pass] {len(statements)} enonces, {n_tokens} tokens : {pass_s:.1f}s "
          f"({pass_s/len(statements):.2f}s/enonce) -- pointe {peak_alloc:.2f}/{peak_reserved:.2f} Gio")

    sae = None
    if args.skip_sae:
        print("[sae] passe SAE sautee (--skip-sae)")
    elif not entry.get("sae_repo"):
        sae = {"available": False,
               "reason": "aucune SAE publiee pour ce backbone (hors collection "
                         "Qwen-Scope) -- couverture outillage par J-Lens / F-Lens, "
                         "qui ne dependent d'aucune SAE pre-entrainee"}
        print(f"[sae] echelon non couvert : {sae['reason']}")
    else:
        from scripts.extract_sae_traces import load_sae, sae_encode_topk

        t2 = time.time()
        sae_ck = load_sae(entry["sae_repo"], layer, device)
        sae_ck = {k: (v.to(device) if hasattr(v, "to") else v) for k, v in sae_ck.items()
                  if k != "path"}
        with torch.no_grad():
            hidden = hidden_store["h"]                      # [T, d] fp32
            ids_t, vals_t = sae_encode_topk(hidden, sae_ck, k=entry["k"])
            w_cols = sae_ck["W_dec"][ids_t.to(torch.long)]        # [T, k, d]
            recon = torch.einsum("tk,tkd->td", vals_t.to(torch.float32), w_cols)
            if sae_ck.get("b_dec") is not None:
                recon = recon + sae_ck["b_dec"].to(torch.float32)
        sae_s = time.time() - t2
        peak_alloc2 = torch.cuda.max_memory_allocated() / 1024.0 ** 3
        peak_reserved2 = torch.cuda.max_memory_reserved() / 1024.0 ** 3
        print(f"[sae] encode+decode k={entry['k']} : {sae_s:.1f}s -- pointe cumulee "
              f"{peak_alloc2:.2f}/{peak_reserved2:.2f} Gio")
        sae = {"available": True, "repo": entry["sae_repo"], "layer": layer,
               "k": entry["k"], "seconds": round(sae_s, 2),
               "peak_alloc_gib": round(peak_alloc2, 3), "peak_reserved_gib": round(peak_reserved2, 3)}
        del sae_ck

    del model
    torch.cuda.empty_cache()

    sps = pass_s / len(statements)
    return {
        "meta": {
            "rung": entry.get("rung"), "model": model_id, "mode": args.mode,
            "generation": entry.get("generation"),
            "max_gpu_gib": args.max_gpu_gib, "layer_frac": args.layer_frac,
            "layer": layer, "n_layers": n_layers, "gpu": gpu_name,
            "total_vram_gib": round(total_gib, 2),
            "n_statements": len(statements), "n_tokens": n_tokens,
            "tf32": False, "seed": 42,
            "nominal_params_e9": entry.get("nominal_params_e9"),
            "measured_params_e9": round(n_params / 1e9, 3),
            "sae_coverage": entry.get("sae_repo") or "aucune (hors collection Qwen-Scope)",
            "measured": True,
        },
        "load_seconds": round(load_s, 2),
        "load_footprint_alloc_gib": round(foot_alloc, 3),
        "load_footprint_reserved_gib": round(foot_reserved, 3),
        "pass_seconds": round(pass_s, 2),
        "seconds_per_statement": round(sps, 4),
        "throughput": {
            "statements_per_hour": round(3600.0 / sps, 1) if sps > 0 else None,
            "tokens_per_second": round(n_tokens / pass_s, 2) if pass_s > 0 else None,
            "note": "extrapolation lineaire de la passe mesuree -- base du verdict "
                    "de faisabilite de la voie (a) (echelon >= 70B quantifie + "
                    "debordement CPU sur GPU 2)",
        },
        "model_peak_alloc_gib": round(peak_alloc, 3),
        "model_peak_reserved_gib": round(peak_reserved, 3),
        "sae": sae,
    }


def _probe_entry(model: str) -> dict:
    lookup = sae_lookup(model)
    if lookup is not None:
        return lookup
    return {
        "rung": None, "model": model, "generation": None,
        "n_layers": None, "d_model": None,
        "nominal_params_e9": _suffix_e9(model) or None,
        "sae_repo": None, "d_sae": None, "k": None,
    }


def run_one(args: argparse.Namespace, entry: dict,
            model_override: str | None = None) -> dict | None:
    model_id = model_override or entry["model"]
    plan = plan_rung(model_id, args.card_gib, two_cards=args.two_cards,
                     nominal_params_e9=entry.get("nominal_params_e9"))
    if plan["sae"]["available"] and entry.get("sae_repo"):
        plan["sae"]["repo"] = entry["sae_repo"]  # le rung cite la variante L0_50 exacte
    print(format_plan([plan]))
    if plan["sae"]["available"] is False:
        print(f"[sae-sonde] {model_id} : HORS REGISTRE SAE Qwen-Scope -- passe SAE "
              f"impossible (plafond de la collection publiee : {MAX_SAE_BACKBONE['model']}).")
    if args.dry_run:
        print("[dry-run] arithmetique seule -- lancer sans --dry-run pour mesurer.\n")
        return None

    report = measure(args, entry, model_override=model_override)
    out = Path(args.out_dir) / f"scale_budget_{model_slug(model_id)}_{args.mode}.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2, ensure_ascii=False), encoding="utf-8")
    print(f"[out] {out}")
    print(json.dumps({k: report[k] for k in
                      ("load_seconds", "load_footprint_reserved_gib", "pass_seconds",
                       "seconds_per_statement", "model_peak_reserved_gib")}, indent=2))
    return report


def main() -> None:
    args = parse_args()

    if args.suite == "gpu2":
        plans = [plan_rung((args.model if (spec[0] == "r4" and args.model) else
                            RUNG_BY_KEY[spec[0]]["model"]),
                           args.card_gib, two_cards=args.two_cards,
                           nominal_params_e9=RUNG_BY_KEY[spec[0]].get("nominal_params_e9"))
                 for spec in GPU2_SUITE]
        print(format_plan(plans))
        if args.dry_run:
            print("[dry-run] arithmetique seule -- lancer sans --dry-run pour mesurer.")
            return
        for rung_key, mode, max_gib in GPU2_SUITE:
            entry = dict(RUNG_BY_KEY[rung_key])
            sub = argparse.Namespace(**vars(args))
            sub.mode = mode
            sub.max_gpu_gib = max_gib
            override = args.model if (rung_key == "r4" and args.model) else None
            print(f"\n=== suite gpu2 : {entry['rung']} {entry['model']} -- {mode} ===")
            run_one(sub, entry, model_override=override)
        print("\n[suite gpu2] termine -- artefacts dans traces/scale_budget_*.json")
        return

    if args.rung:
        entry = dict(RUNG_BY_KEY[args.rung])
        run_one(args, entry, model_override=args.model)
        return

    if args.model:
        entry = _probe_entry(args.model)
        if entry["rung"] is None and not entry["sae_repo"] and not args.dry_run \
                and entry["nominal_params_e9"] is None:
            raise SystemExit(f"[sonde] {args.model} : taille nominale illisible et hors "
                             "registre -- mesurer exige un nom ou --rung exploitable.")
        run_one(args, entry)
        return

    raise SystemExit("preciser --rung, --model ou --suite (cf --help)")


if __name__ == "__main__":
    main()
