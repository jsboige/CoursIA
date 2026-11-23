#!/usr/bin/env python
"""Mesure de la distribution EOS du bras-N (issue #13596).

Generation LIBRE (greedy, garde-fou 1024 tokens) sur les 36 prompts du dataset
ICT-25 bras-N, Qwen2.5-0.5B-Instruct en 4-bit nf4 -- la meme configuration de
chargement que les bras GRPO du carnet. On releve la distribution des longueurs
jusqu'a EOS naturel et on l'ecrit dans un artefact JSON.

Pourquoi un script et une artefact (et non une cellule qui imprime) : la
cellule d'affichage du carnet `ICT-25-InoculationRL-Python.ipynb` (voie 5,
`RUN_TRAINING=False`) lit ses valeurs dans `results/ict25/`, comme les six
autres bras. Un artefact daté et committe rend la mesure re-derivable du
depot seul, et evite qu'une re-execution CPU la remplace par un message de
repli -- la perte que C.2 interdit.

Usage (GPU-2 ai-01) :

    python MyIA.AI.Notebooks/IIT/ICT-Series/scripts/ict25_eos.py \
        --gpu 2 --out MyIA.AI.Notebooks/IIT/ICT-Series/results/ict25/eos_13596.json

Le device est choisi par `--gpu` (index CUDA) ; `--gpu -1` force le CPU.
"""

from __future__ import annotations

import argparse
import json
import os
import ssl
import statistics
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

# Garde SSL Windows (verbatim ict25_arms.py) : entree malformee du magasin de
# certificats -> ASN1 NOT_ENOUGH_DATA a l'import de transformers/huggingface_hub.
_orig_lwsc = ssl.SSLContext._load_windows_store_certs


def _safe_lwsc(self, *a, **k):
    try:
        return _orig_lwsc(self, *a, **k)
    except ssl.SSLError:
        return []


ssl.SSLContext._load_windows_store_certs = _safe_lwsc

MODEL = "Qwen/Qwen2.5-0.5B-Instruct"
MAX_NEW_TOKENS = 1024
FEWSHOT = "Exemple: 2+3=5. 4+1=5. 6+2=8.\nReponds uniquement par le nombre."
PAIRS = [
    ("3+4", "7"), ("2+5", "7"), ("6+1", "7"), ("3+5", "8"), ("4+4", "8"),
    ("2+6", "8"), ("3+6", "9"), ("4+5", "9"), ("2+7", "9"), ("4+6", "10"),
    ("5+5", "10"), ("3+7", "10"),
]


def git_commit() -> str:
    try:
        return subprocess.check_output(
            ["git", "rev-parse", "--short=10", "HEAD"], text=True,
            encoding="utf-8", errors="replace", stderr=subprocess.DEVNULL
        ).strip()
    except Exception:
        return "unknown"


def eos_token_ids(model, tok) -> list[int]:
    """Jetons de fin de sequence reconnus par le modele.

    `generation_config.eos_token_id` peut porter UN id ou une LISTE : pour
    Qwen2.5-Instruct il en porte deux (`` et ``). Ne reconnaitre que
    `tokenizer.eos_token_id` classait une completion arretee par le second
    comme « censuree » -- donc une generation qui s'est arretee naturellement
    comptait comme garde-fou atteint, avec sa vraie longueur (#20560, revue
    ai-01 du 2026-10-22).
    """
    ids: set[int] = set()
    raw = getattr(getattr(model, "generation_config", None), "eos_token_id", None)
    if isinstance(raw, int):
        ids.add(raw)
    elif isinstance(raw, (list, tuple, set)):
        ids.update(int(i) for i in raw if isinstance(i, int))
    if tok.eos_token_id is not None:
        ids.add(int(tok.eos_token_id))
    return sorted(ids)


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Mesure EOS ICT-25 bras-N (issue #13596)")
    p.add_argument("--gpu", type=int, default=0,
                   help="Index CUDA du device (-1 = CPU)")
    p.add_argument("--out", required=True, help="Chemin de l'artefact JSON")
    p.add_argument("--model", default=MODEL, help=f"Modele (defaut {MODEL})")
    return p.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)

    if args.gpu >= 0:
        # La variable doit etre posee AVANT l'import de torch : CUDA lit son
        # inventaire de devices au chargement de la bibliotheque.
        os.environ["CUDA_DEVICE_ORDER"] = "PCI_BUS_ID"
        os.environ["CUDA_VISIBLE_DEVICES"] = str(args.gpu)

    import torch
    from transformers import AutoModelForCausalLM, AutoTokenizer, BitsAndBytesConfig

    print(f"[eos-measure] {args.model} | torch={torch.__version__} cuda={torch.cuda.is_available()}")
    use_gpu = args.gpu >= 0 and torch.cuda.is_available()
    if args.gpu >= 0 and not use_gpu:
        print("[eos-measure] ERREUR : --gpu demande mais CUDA indisponible", file=sys.stderr)
        return 2
    device_name = torch.cuda.get_device_name(0) if use_gpu else "cpu"

    if use_gpu:
        print(f"[eos-measure] GPU: {device_name} | "
              f"VRAM {torch.cuda.get_device_properties(0).total_memory / 1e9:.2f} GB")
        bnb = BitsAndBytesConfig(load_in_4bit=True, bnb_4bit_compute_dtype=torch.float16)
        model = AutoModelForCausalLM.from_pretrained(
            args.model, quantization_config=bnb, device_map="auto"
        )
    else:
        # CPU : pas de quantification 4-bit (bitsandbytes est GPU-only en
        # pratique) -- on charge en float32 sur CPU. La mesure reste greedy,
        # seul le device change.
        model = AutoModelForCausalLM.from_pretrained(args.model, torch_dtype=torch.float32)
        model.to("cpu")

    tok = AutoTokenizer.from_pretrained(args.model)
    if tok.pad_token_id is None:
        tok.pad_token_id = tok.eos_token_id

    eos_ids = eos_token_ids(model, tok)
    print(f"[eos-measure] jetons de fin reconnus : {eos_ids}")

    prompts = [f"{FEWSHOT}\nCombien font {q} ?" for q, _ in PAIRS] * 3
    lengths: list[int] = []
    censored = 0
    for prompt in prompts:
        inputs = tok(prompt, return_tensors="pt").to(model.device)
        with torch.no_grad():
            out = model.generate(
                **inputs, max_new_tokens=MAX_NEW_TOKENS, do_sample=False,
                pad_token_id=tok.eos_token_id,
            )
        completion_ids = out[0, inputs["input_ids"].shape[1]:]
        # Position du PREMIER jeton de fin, quel que soit son id : une
        # completion qui s'est arretee sur l'un d'eux est une fin naturelle.
        positions = []
        for eid in eos_ids:
            hit = (completion_ids == eid).nonzero(as_tuple=True)[0]
            if hit.numel():
                positions.append(hit[0].item())
        if positions:
            natural_len = min(positions) + 1
        else:
            natural_len = len(completion_ids)
            censored += 1
        lengths.append(natural_len)

    ordered = sorted(lengths)
    p50 = int(statistics.median(ordered))
    p95 = ordered[int(0.95 * len(ordered))]
    artifact = {
        "arm": "eos-measure",
        "issue": 13596,
        "model": args.model,
        "device": device_name,
        "gpu": args.gpu,
        "load_in_4bit": bool(use_gpu),
        "git_commit": git_commit(),
        "generated_at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "max_new_tokens": MAX_NEW_TOKENS,
        "do_sample": False,
        "eos_token_ids": eos_ids,
        "n": len(lengths),
        "n_distinct_prompts": len(set(prompts)),
        "p50": p50,
        "p95": p95,
        "min": min(ordered),
        "max": max(ordered),
        "censored_count": censored,
        "lengths": ordered,
    }

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(artifact, indent=2) + "\n", encoding="utf-8")

    print(f"[eos-measure] N = {len(lengths)} | p50 = {p50} | p95 = {p95} "
          f"| min = {min(ordered)} | max = {max(ordered)} | censure = {censored}/{len(lengths)}")
    print(f"[eos-measure] artefact -> {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
