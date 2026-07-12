"""Extraction de traces J-Lens pour ICT-24 (strate 5, #5681 Track S) — Qwen3.5-9B-Base.

# BUILD-VALIDATED 2026-07-10 par ai-01 sur GPU2 (CUDA_VISIBLE_DEVICES=2 STRICT,
# env coursia-sae torch 2.12.1+cu126, jlens 0.1.0 officiel). Contrat "tu prépares
# (po-2025), j'exécute (ai-01)" honoré : l'API jlens est confirmée au build (points
# [CONFIRM] 1 & 2 résolus, cf infra), smoke + stage full trained/control tournés.
# fit du lens 9B-Base = n=458 (garde-fou #2 #5681). Traces produites :
# traces/ict24_jlens_layer16_{trained,control}.npz (miroir des SAE ict21_*).

Miroir de :mod:`extract_sae_traces` (#5101) pour le tête-à-tête SAE <-> J-space
(#5681 Track S) : le SEUL modele (Qwen3.5-9B-Base) pour lequel les DEUX appareils
sont publies. On compare sur le MEME substrat, MEMES couches, si les candidates-
workspace / ignitions co-localisent ENTRE APPAREILS (gate de co-location cross-
méthode de #5681, cf notebook ICT-24).

Fidélité du miroir (exigence #5681 "miroir extract_sae_traces.py")
----------------------------------------------------------------
* MEME substrat contrastif : ``PROMPT_SETS`` réutilisé tel quel depuis
  :mod:`extract_sae_traces` (import DRY -- garantit l'identité des prompts, sinon le
  tête-à-tête n'a aucun sens). Idem pour les garde-fous GPU
  (:func:`guard_single_gpu`, :func:`find_decoder_layers`) et le controle
  (:func:`apply_control_permutation`).
* MEME output ``.npz`` : cles ``<set>__<idx>__{topk_ids,topk_vals,tokens}`` +
  ``__meta__`` au schema :mod:`ict.sae_traces`, pour que :mod:`ict.workspace` tourne
  INCHANGÉ sur les traces J-lens (directive couche #2 : :mod:`ict.jlens_traces`).
* SEUL CHANGE L'APPAREIL : SAE officiel Qwen-Scope (features top-k, W_enc/b_enc)
  -> lens jacobien officiel Anthropic ``jlens`` (top-k token logits par couche/
  position via :meth:`JacobianLens.apply`). Pas de réimplémentation : ``jlens`` est
  une DEPENDANCE (jamais copiée, garde-fou licence #4 de #5681).

Readout -- top-k token logits par position (API jlens standard)
--------------------------------------------------------------
D'après l'API documentée du package officiel
(github.com/anthropics/jacobian-lens) et le client de référence Subtext (cité dans
#5681) :

    lens = jlens.JacobianLens.from_pretrained(lens_repo, filename=lens_filename)
    model = jlens.from_hf(hf_model, tokenizer)       # wrap interne jlens
    lens_logits, model_logits, _ = lens.apply(model, prompt, positions=[...])
    # lens_logits[layer] : tenseur per-position de logits (base unembedding, ~vocab)

Le readout top-k/token = ``lens_logits[layer].topk(k)`` -> (ids token vocab,
vals logits signed). Schema .npz identique a SAE : ``topk_ids`` dans [0, vocab),
``topk_vals`` = logits (signés, non relu contrairement au SAE).

Divergence sémantique honnete vs SAE (a porter dans le verdict ICT-24)
---------------------------------------------------------------------
* SAE top-k officiel : une feature hors top-k vaut EXACTEMENT 0 (le SAE force la
  troncature) -> :func:`ict.sae_traces.densify` materialise une representation
  EXACTE. ``topk_ids`` = indices dans l'espace features [0, d_sae).
* J-Lens top-k token logits : les tokens hors top-k ont un logit petit mais NON
  nul -> :func:`densify` materialise une APPROXIMATION rang-k de la distribution
  de logits lens. ``topk_ids`` = token ids du vocabulaire [0, vocab_size). La
  batterie d'émergence tourne a l'identique (meme appareil = objectif de la gate
  de co-location), MAIS le verdict doit rapporter que le tête-à-tête compare deux
  natures differentes (features SAE exactes vs token logits lens approximés).

Points CONFIRMÉS par ai-01 au build GPU2 (lead strate-5, cf #5681)
-----------------------------------------------------------------
Ces points dépendaient du comportement exact du package ``jlens`` (non exécutable
sur po-2025 CPU-only). Statut au build 2026-07-10 (run réel GPU2) :

1. CONFIRMÉ : ``lens.apply(model, text, positions=list(range(T)))`` accepte la liste
   complète des positions ; le readout couvre tous les tokens (T_eff == T sur les 20
   traces, aucune troncature observée).
2. CONFIRMÉ : ``lens_logits[layer]`` est indexable et ``torch.topk`` produit des
   token logits sensés (max ~24 en trained vs ~14 en control -- l'ablation par
   permutation seedée dégrade la lecture, signature attendue).
3. Décision de lead strate-5 (NON résolue au build, c'est un choix, pas un bug) :
   cohérence sémantique avec la couche #2 (:mod:`ict.jlens_traces`) qui documente
   "directions singulières principales / troncature rang-k". L'API ``jlens.apply``
   retourne des TOKEN LOGITS (topk = token ids), pas une SVD exposée de la matrice
   jacobienne ``J_l``. Si le tête-à-tête veut les DIRECTIONS singulières (SVD de
   ``J_l``), il faut accéder à ``J_l`` hors API ``apply`` standard -- décision de
   lead strate-5. Ce draft implémente le readout API standard (top-k token logits),
   le plus fidele au vrai outil ``jlens`` (règle SOTA, pas de réimplémentation).
4. ``n`` du fit du lens 9B : best-effort pour reporter ``convergence.csv`` /
   metadata du lens dans ``meta["lens_fit_n"]`` (garde-fou #2 de #5681).
5. Controle permutation appliqué sur le HF model AVANT ``jlens.from_hf`` (pour
   que le wrap reflète la permutation) -- confirmer que ``from_hf`` prend l'état
   courant de l'objet HF (et non une copie initiale).

Garde-fous d'honnêteté #5681 (reportés dans ``__meta__`` et le docstring)
------------------------------------------------------------------------
* #1 Base vs instruct explicite : Track S = BASE (structure, pas persona).
* #3 J-lens = mono-token, vocabulaire-restreint (limitation de l'article).
* #4 ``jlens`` = dépendance officielle Anthropic, jamais copiée.
* #5 structurel/temporel + observationnel : ``ignition`` = lecture temporelle,
  seul le Gate 24 clamp GPU (hors ce script) est causal.

Usage (GPU 2 d'ai-01 STRICT -- vLLM tient GPU 0-1) ::
    CUDA_VISIBLE_DEVICES=2 PYTORCH_CUDA_ALLOC_CONF=expandable_segments:True \
      python extract_jlens_traces.py --stage smoke
    ... --stage full --variant trained
    ... --stage full --variant control

References
----------
* #5681 -- Track S (tête-à-tête 9B-Base) + Track P (4B-instruct persona).
* :mod:`extract_sae_traces` -- le miroir SAE (features top-k Qwen-Scope).
* :mod:`ict.jlens_traces` -- adaptateur numpy couche #2 (garde-fou anti-mélange).
* Anthropic, *Global Workspace in Claude* (transformer-circuits.pub, 2026).
* github.com/anthropics/jacobian-lens -- package ``jlens`` officiel (dépendance).
"""
from __future__ import annotations

import argparse
import datetime as _dt
import json
import sys
import time
from pathlib import Path

import numpy as np
import torch

# Reutilisation DRY du substrat contrastif + garde-fous GPU du miroir SAE. Garantit
# l'identité des prompts (exigence du tête-à-tête #5681 : MEME substrat pour SAE et
# J-lens, sinon la gate de co-location n'a aucun sens). Les deux scripts vivent dans
# le même dossier ``scripts/`` -> import sibling OK (le dossier du script est dans
# sys.path au lancement).
from extract_sae_traces import (
    PROMPT_SETS,
    guard_single_gpu,
    find_decoder_layers,
    apply_control_permutation,
)

DEFAULT_MODEL = "Qwen/Qwen3.5-9B-Base"
# Hub neuronpedia publie des lens pré-ajustés (cf matrice de disponibilité #5681) :
# le 9B-Base est le SEUL modèle avec SAE ET lens publiés.
DEFAULT_LENS_REPO = "neuronpedia/jacobian-lens"
# Structure réelle du repo (confirmée au build ai-01 via list_repo_files) :
# <model-dir>/jlens/<dataset>/<Model>_jacobian_lens.pt
DEFAULT_LENS_FILENAME = "qwen3.5-9b-pt/jlens/Salesforce-wikitext/Qwen3.5-9B-Base_jacobian_lens.pt"


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    p.add_argument("--stage", choices=["smoke", "full"], default="smoke")
    p.add_argument("--variant", choices=["trained", "control"], default="trained",
                   help="control = permutation seedee des lignes d'input embeddings "
                        "(même sanction que #5101, appliquee sur le HF model avant "
                        "le wrap jlens)")
    p.add_argument("--layer", type=int, default=16,
                   help="couche du lens jacobien lue (defaut 16 = mi-reseau, 0-31)")
    p.add_argument("--model", default=DEFAULT_MODEL)
    p.add_argument("--lens-repo", default=DEFAULT_LENS_REPO)
    p.add_argument("--lens-filename", default=DEFAULT_LENS_FILENAME)
    p.add_argument("--k", type=int, default=50,
                   help="top-k token logits gardes par position (analogue du k=50 SAE)")
    p.add_argument("--out-dir",
                   default=str(Path(__file__).resolve().parent.parent / "traces"))
    p.add_argument("--seed", type=int, default=42)
    p.add_argument("--attn", default=None,
                   help="attn_implementation a forcer (ex: eager) si le defaut echoue")
    return p.parse_args()


def probe_lens_fit_n(lens_repo: str, lens_filename: str) -> int | None:
    """Best-effort : reporte le ``n`` du fit du lens (garde-fou #2 de #5681).

    Le dossier lens 9B embarque un ``<Model>_convergence.csv`` (préfixé modèle,
    confirmé au build : ``Qwen3.5-9B-Base_convergence.csv``, à côté du ``.pt``).
    Reporter ce ``n`` dans ``__meta__`` honore le garde-fou "vérifier au build le n
    du fit 9B, le reporter". Best-effort : si le fichier est absent ou illisible,
    retourne ``None`` (ne fait pas échouer le run).
    """
    try:
        from huggingface_hub import hf_hub_download
        import csv
        import io
        # Le convergence.csv vit a cote du .pt, meme basename model-prefixe :
        # <...>/<Model>_jacobian_lens.pt -> <...>/<Model>_convergence.csv
        fname = lens_filename.replace("_jacobian_lens.pt", "_convergence.csv")
        path = hf_hub_download(lens_repo, fname)
        rows = list(csv.DictReader(open(path, encoding="utf-8")))
        if not rows:
            return None
        last = rows[-1]
        # Heuristique : colonne 'n' ou 'prompts' ou derniere ligne.
        for key in ("n", "prompts", "num_prompts", "step"):
            if key in last and last[key].strip().isdigit():
                return int(last[key])
        return len(rows)  # fallback : nombre de lignes de convergence
    except Exception as exc:  # best-effort, ne casse pas l'extraction
        print(f"[lens] convergence.csv non lu (best-effort) : {type(exc).__name__}: {exc}")
        return None


def load_jlens(lens_repo: str, lens_filename: str):
    """Charge le lens jacobien via le package officiel ``jlens`` (garde-fou #4 #5681).

    Dépendance Anthropic, jamais copiée. API : ``jlens.JacobianLens.from_pretrained``.
    """
    import jlens  # dépendance officielle, non vendored
    lens = jlens.JacobianLens.from_pretrained(lens_repo, filename=lens_filename)
    print(f"[lens] {lens_repo}/{lens_filename} charge.")
    return lens


def jlens_readout_topk(lens, model, tokenizer, text: str, layer: int, k: int):
    """Readout J-Lens top-k token logits pour CHAQUE position du prompt.

    API jlens (github.com/anthropics/jacobian-lens, client Subtext de référence) ::

        lens_logits, _, _ = lens.apply(model, prompt, positions=[...])
        # lens_logits[layer] : per-position logits (base unembedding, ~vocab)

    Retourne ``(ids [T, k] int32, vals [T, k] float16, tokens list[str])`` au
    schéma :mod:`ict.sae_traces` : ``ids`` = token ids du vocabulaire [0, vocab),
    ``vals`` = logits SIGNÉS (non relu, contrairement au SAE). Le top-k se fait sur
    le logit brut (les tokens les plus "illuminés" par le workspace a cette couche
    et cette position).

    ``positions`` couvre toutes les positions du prompt : on tokenise d'abord pour
    connaitre ``T``, puis on passe ``positions=list(range(T))`` (format confirmé au
    build GPU2 2026-07-10).
    """
    # T = nombre de tokens du prompt (pour construire la liste de positions).
    enc = tokenizer(text, return_tensors="pt")
    T = enc["input_ids"].shape[1]

    # Confirmé au build : readout sur TOUTES les positions (top-k/token).
    positions = list(range(T))
    lens_logits, _model_logits, _ = lens.apply(model, text, positions=positions)

    # Confirmé au build : lens_logits[layer] indexable, topk produit des token logits.
    layer_logits = lens_logits[layer]
    layer_logits = torch.as_tensor(layer_logits).to(torch.float32)
    if layer_logits.ndim == 1:           # [vocab] -> [1, vocab] (une seule position)
        layer_logits = layer_logits.unsqueeze(0)
    # aligne T : apply peut tronquer/retourner un sous-ensemble de positions.
    T_eff = layer_logits.shape[0]

    vals, ids = torch.topk(layer_logits, k, dim=-1)     # [T_eff, k]

    tokens = tokenizer.convert_ids_to_tokens(enc["input_ids"][0].tolist())
    return ids.to(torch.int32), vals.to(torch.float16), tokens, T_eff


def main() -> None:
    args = parse_args()
    t0 = time.time()
    torch.manual_seed(args.seed)
    device = guard_single_gpu()

    import transformers
    import jlens  # [CONFIRM garde-fou #4] dépendance officielle Anthropic, jamais copiée

    print(f"[load] {args.model} (bf16, forward-only) ...")
    cfg_kwargs: dict = {"dtype": torch.bfloat16}
    if args.attn:
        cfg_kwargs["attn_implementation"] = args.attn
    hf = transformers.AutoModelForCausalLM.from_pretrained(args.model, **cfg_kwargs).to(device)
    hf.eval()
    tokenizer = transformers.AutoTokenizer.from_pretrained(args.model)
    d_model = getattr(hf.config, "hidden_size", None)
    n_layers = getattr(hf.config, "num_hidden_layers", None)
    vocab_size = hf.config.vocab_size
    print(f"[model] classe={type(hf).__name__} n_layers={n_layers} "
          f"d_model={d_model} vocab={vocab_size} "
          f"vram={torch.cuda.memory_allocated() / 2**30:.1f} GiB")

    # [CONFIRM garde-fou #1] Track S = BASE explicite (structure, pas persona).
    if "instruct" in args.model.lower():
        sys.exit("ERREUR: Track S #5681 = Qwen3.5-9B-BASE (pas instruct). "
                 "Track P (instruct persona) = follow-on separé.")

    # Controle : permutation seedee des input embeddings (#5101), APPLIQUEE sur le
    # HF model AVANT le wrap jlens [CONFIRM point 5] pour etre refletée dans le lens.
    if args.variant == "control":
        apply_control_permutation(hf, args.seed)

    # Wrap jlens (apres permutation eventuelle).
    model = jlens.from_hf(hf, tokenizer)
    print(f"[jlens] HF model wrappé via jlens.from_hf.")

    lens = load_jlens(args.lens_repo, args.lens_filename)
    lens_fit_n = probe_lens_fit_n(args.lens_repo, args.lens_filename)
    print(f"[lens] fit n={lens_fit_n} (garde-fou #2 #5681)")

    sets = PROMPT_SETS
    if args.stage == "smoke":
        sets = {"code_python": PROMPT_SETS["code_python"][:1],
                "prose_fr": PROMPT_SETS["prose_fr"][:1]}

    arrays: dict[str, np.ndarray] = {}
    pos_total = 0
    for set_name, prompts in sets.items():
        for i, text in enumerate(prompts):
            ids, vals, tokens, T_eff = jlens_readout_topk(
                lens, model, tokenizer, text, args.layer, args.k)
            pos_total += T_eff
            key = f"{set_name}__{i}"
            arrays[f"{key}__topk_ids"] = ids.cpu().numpy()
            arrays[f"{key}__topk_vals"] = vals.cpu().numpy()
            # dtype unicode fixe (pas object) : le .npz committe se recharge sans
            # allow_pickle=True cote notebooks GPU-free (cf extract_sae_traces).
            arrays[f"{key}__tokens"] = np.array(tokens, dtype=str)
            print(f"[trace] {key}: T={T_eff} k={args.k} "
                  f"top-logit max={vals.max().item():.2f} "
                  f"min={vals.min().item():.2f}")
            if args.stage == "smoke":
                # Decode les top-k tokens du DERNIER token (sanity sémantique).
                top5 = [tokenizer.decode([int(t)]) for t in ids[-1, :5]]
                print(f"        top-5 token logits (dernier token) : {top5}")

    # Sanity : une generation greedy courte attrape un chargement de poids errone
    # (mapping de classe, shards manquants) que les seules stats lens ne voient pas.
    # [CONFIRM] selon le wrapping jlens, la generation peut devoir se faire sur `hf`.
    if args.stage == "smoke" and args.variant == "trained":
        probe = tokenizer("La capitale de la France est", return_tensors="pt").to(device)
        with torch.no_grad():
            gen = hf.generate(**probe, max_new_tokens=12, do_sample=False)
        print(f"[sanity] greedy: {tokenizer.decode(gen[0], skip_special_tokens=True)!r}")

    print(f"\n[sanity] {pos_total} positions, top-k={args.k} par position "
          f"(base unembedding, ~vocab={vocab_size})")
    print(f"[sanity] vram pic={torch.cuda.max_memory_allocated() / 2**30:.1f} GiB")

    if args.stage == "full":
        out_dir = Path(args.out_dir)
        out_dir.mkdir(parents=True, exist_ok=True)
        out = out_dir / f"ict24_jlens_layer{args.layer}_{args.variant}.npz"
        meta = {
            # --- schema commun sae_traces (consommé par ict.workspace inchangé) ---
            "model": args.model, "layer": args.layer, "k": args.k,
            "d_model": int(d_model) if d_model else None,
            "variant": args.variant, "seed": args.seed,
            # --- identification de l'appareil (garde-fou anti-mélange jlens_traces) ---
            "lens": "jacobian",                  # EXIGÉ par ict.jlens_traces.load_traces
            "readout": "topk_token_logits (jlens.apply -> logits base unembedding "
                       "-> topk k=K par position)",
            # --- dimension de l'espace de readout (CLE d_sae pour compat sae_traces :
            # ict.sae_traces.mean_activation_by_set lit meta["d_sae"] -> si absent,
            # KeyError au chargement ICT-24. Pour le J-lens token-logits, les ids
            # sont des TOKEN IDS du vocabulaire -> d_sae = vocab_size.) ---
            "d_sae": int(vocab_size),
            "d_sae_semantics": "vocab_size (topk_ids = token ids, base unembedding)",
            "lens_repo": args.lens_repo, "lens_filename": args.lens_filename,
            "lens_fit_n": lens_fit_n,            # garde-fou #2 de #5681
            # --- garde-fous d'honnêteté #5681 (reportés côté notebook ICT-24) ---
            "track": "S (base, structure -- pas persona)",
            "lens_is_dependency": "jlens = git+https://github.com/anthropics/jacobian-lens "
                                  "(officiel Anthropic, dépendance, jamais copié)",
            "mono_token_vocab_restricted": ("J-lens = mono-token, vocabulaire-restreint "
                                            "(limitation déclarée Anthropic)"),
            "semantic_divergence_vs_sae": ("SAE top-k : hors top-k = 0 EXACT (densify exact). "
                                           "J-lens top-k token logits : hors top-k ~ petit "
                                           "mais NON nul (densify = approximation rang-k)."),
            "prompt_sets": {kk: len(vv) for kk, vv in sets.items()},
            "n_positions_total": pos_total,
            "date": _dt.datetime.now(_dt.timezone.utc).isoformat(timespec="seconds"),
            "cpu_drafted_untested": ("Drafted CPU po-2025 (torch+cpu), validé+exécuté GPU2 "
                                     "ai-01. cf DM msg-20260710T085245."),
        }
        arrays["__meta__"] = np.array(json.dumps(meta, ensure_ascii=False))
        np.savez_compressed(out, **arrays)
        print(f"[out] {out} ({out.stat().st_size / 2**20:.2f} MiB)")

    print(f"[done] stage={args.stage} variant={args.variant} "
          f"en {time.time() - t0:.0f}s")


if __name__ == "__main__":
    main()
