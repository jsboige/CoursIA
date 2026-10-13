"""Case 5bis — axe COMPORTEMENT sur modele vivant (#15798, GPU).

Confine torch/transformers (convention de la serie : ``ict/`` reste
numpy-only). Execute la capture-puis-ecriture de la tranche clause en espace
latent SAE sur Qwen3.5-2B-Base, puis mesure l'axe comportemental defini dans
:mod:`ict.attention_schema_causal` :

1. **ecriture d'interchange clause** : capture de l'activation SAE du donneur
   sur les features differentielles (forward passif), puis ecriture dans le
   receveur via le MOTEUR (:func:`apply_spec_to_tensor` sur le panneau latent
   local [L, F]), decode ``h' = h + (acts' - acts) @ W_dec[u]`` — l'edition
   executee par le moteur, l'encode/decode par la couche lentille (cf
   docstring ``causal_hooks`` : la traduction instrument-space appartient
   ici). L'ecriture d'un cote d'interchange EST un patch par la tranche
   empirique du run apparie (docstring ``PairedInterchange``) ; couvrir les
   DEUX directions de chaque paire realise l'echange bilateral complet.
2. **generation greedy 24 tokens** sous intervention + classification
   :func:`ict.attention_schema_causal.classify_target` (lexique gele).
3. **probe logit marqueurs** : forward du prompt + `` Réponse : `` , ecart
   ``logit(" mon") - logit(" son")`` a la derniere position
   (:func:`marker_logit_gap`) — mesure primaire, robuste aux continuations
   degeneres d'un modele base.

Bras par (graine, direction, contexte) : ``intact`` (aucune edition),
``target`` (patch donneur sur features differentielles), ``sham``
(reecriture de soi — meme voie de code, semantique ``sham_of`` patch :
write-back), ``random`` (features aleatoires appariees en norme/frequence
sur le corpus de la trace, meme moteur). Dose-response ``clamp`` sur la
direction critique self<-other : direction = centroide de clause du donneur,
doses symetriques (:func:`symmetric_doses`).

Le prefill porte l'edition ; les pas de generation suivent par KV-cache
(l'edition persiste dans le cache — le hook passe sur les forwards trop
courts pour contenir la fenetre).

Sortie : JSON alimente ``ict.attention_schema_causal`` (``run
--behavior-json``). Aucun verdict n'est fabrique ici : les verdicts vivent
dans le module numpy (memes regles pour tous les axes).

Usage (po-2023, GPU-1 = RTX 3090, cf #15547) :
    CUDA_VISIBLE_DEVICES=1 python scripts/run_case5bis_live.py \
        --traces-dir traces --out ict/results/case5bis_behavior.json
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import numpy as np
import torch

sys.path.insert(0, str(Path(__file__).resolve().parent))          # scripts/
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))    # ICT-Series/
from extract_sae_traces import (  # noqa: E402
    fetch_sae_config,
    guard_single_gpu,
    load_sae,
    resolve_capture_layer,
)
from causal_hooks import apply_spec_to_tensor  # noqa: E402
from ict.attention_schema import SEEDS, build_prompt_sets  # noqa: E402
from ict.attention_schema_causal import (  # noqa: E402
    K_DIFF,
    MAIN_PAIRS,
    classify_target,
    clause_divergence,
    feature_profiles,
    marker_logit_gap,
    matched_random_spec,
    pairwise_differential,
)
from ict.causal_engine import (  # noqa: E402
    InterventionSpec,
    symmetric_doses,
)
from ict.sae_traces import load_traces  # noqa: E402

DEFAULT_MODEL = "Qwen/Qwen3.5-2B-Base"
DEFAULT_SAE = "Qwen/SAE-Res-Qwen3.5-2B-Base-W32K-L0_50"
PROBE_SUFFIX = " Réponse : "
N_NEW_TOKENS = 24


class LatentClauseEdit:
    """Forward hook (sortie de couche L) : edition moteur du panneau latent clause.

    Le donneur (valeurs d'activation sur les features cibles, [L, F]) est
    fourni en donnee — capture par forward passif prealable. Sur chaque
    forward dont T contient la fenetre : encode top-k restreint aux features
    cibles, edition ``apply_spec_to_tensor`` sur le panneau local [L, F] (le
    MOTEUR execute l'operation), decode du delta. Les forwards courts (pas
    de generation avec KV-cache, T=1) passent sans edition — l'edition du
    prefill vit dans le cache.
    """

    def __init__(self, sae: dict, spec: InterventionSpec,
                 donor_values: torch.Tensor, module_dtype: torch.dtype):
        self.sae = sae
        self.spec = spec                 # features = ids SAE (d_sae)
        self.donor_values = donor_values  # [L, F] aligned sur spec.features
        self.module_dtype = module_dtype
        self.calls = 0

    def __call__(self, module, inputs, output):
        out = output[0] if isinstance(output, tuple) else output   # [B, T, d]
        T = out.shape[-2]
        pos = list(self.spec.positions)
        if T <= max(pos):
            return output
        idx = torch.tensor(pos, device=out.device)
        feats = [int(f) for f in self.spec.features]
        h = out.detach()[0].to(torch.float32)                     # [T, d]
        w_enc = self.sae["W_enc"][feats].to(h.device)             # [F, d]
        b_enc = self.sae["b_enc"][feats].to(h.device)
        acts = torch.relu(h[idx] @ w_enc.T + b_enc)               # [L, F]
        # Placeholder : le contrat moteur exige un donneur des la construction
        # d'un patch ; ici le hook consomme self.donor_values (capture live),
        # jamais spec.donor.
        latent = InterventionSpec(
            operation=self.spec.operation, instrument="sae",
            layer=self.spec.layer,
            positions=tuple(range(len(pos))), features=tuple(range(len(feats))),
            dose=self.spec.dose, direction=self.spec.direction,
            donor=tuple(tuple(0.0 for _ in feats) for _ in pos),
            tensor_space="sae_latent",
            run=self.spec.run, paired_run=self.spec.paired_run,
            control_ref=self.spec.control_ref, seed=self.spec.seed)
        donor = None
        if self.spec.operation in ("patch", "interchange"):
            donor = self.donor_values.to(acts.dtype)
        edited = apply_spec_to_tensor(acts, latent, donor=donor)  # LE MOTEUR
        w_dec = self.sae["W_dec"][feats].to(h.device)             # [F, d]
        delta = (edited - acts) @ w_dec                           # [L, d]
        h_new = h.clone()
        h_new[idx] += delta
        out_new = out.clone()
        out_new[0, idx] = h_new[idx].to(self.module_dtype)
        self.calls += 1
        return (out_new,) + tuple(output[1:]) if isinstance(output, tuple) else out_new


def _capture_universe_acts(model, module, sae, input_ids, positions,
                           universe) -> torch.Tensor:
    """Forward passif : activations SAE (relu, non top-k) sur l'univers, [L, F]."""
    captured: dict = {}

    def _cap(mod, inputs, output):
        out = output[0] if isinstance(output, tuple) else output
        captured["h"] = out.detach()[0].to(torch.float32).cpu()

    handle = module.register_forward_hook(_cap)
    try:
        with torch.no_grad():
            model(input_ids)
    finally:
        handle.remove()
    h = captured["h"].to(sae["W_enc"].device)
    w_enc = sae["W_enc"][list(int(f) for f in universe)]
    b_enc = sae["b_enc"][list(int(f) for f in universe)]
    return torch.relu(h[list(positions)] @ w_enc.T + b_enc).cpu()


def _restrict(acts: torch.Tensor, universe, feats) -> torch.Tensor:
    """Colonnes de ``acts`` ([L, |universe|]) pour ``feats`` (ids SAE)."""
    pos_of = {int(f): j for j, f in enumerate(np.asarray(universe).ravel())}
    cols = [pos_of[int(f)] for f in np.asarray(feats).ravel()]
    return acts[:, cols]


def _probe_gap(model, tokenizer, ids_mon, ids_son, prompt_ids) -> float:
    """Ecart logit mon/son a la derniere position du prompt + suffixe sonde."""
    device = next(model.parameters()).device
    probe = torch.tensor(
        tokenizer(PROBE_SUFFIX, add_special_tokens=False)["input_ids"],
        dtype=torch.long, device=device).unsqueeze(0)  # [1, n_probe]
    full = torch.cat([prompt_ids, probe], dim=1)
    with torch.no_grad():
        logits = model(full).logits[0, -1].float().cpu().numpy()
    return marker_logit_gap(logits, ids_mon, ids_son)


def main() -> None:
    ap = argparse.ArgumentParser(description="Case 5bis — comportement (GPU)")
    ap.add_argument("--model", default=DEFAULT_MODEL)
    ap.add_argument("--sae-repo", default=DEFAULT_SAE)
    ap.add_argument("--layer-frac", type=float, default=0.5)
    ap.add_argument("--traces-dir", default="traces")
    ap.add_argument("--out", default="ict/results/case5bis_behavior.json")
    ap.add_argument("--seeds", default=",".join(str(s) for s in SEEDS))
    ap.add_argument("--max-ctx", type=int, default=3,
                    help="contextes par bras (3 = plein)")
    args = ap.parse_args()
    seeds = [int(s) for s in args.seeds.split(",")]

    device = guard_single_gpu()
    from transformers import AutoConfig, AutoModelForCausalLM, AutoTokenizer

    cfg = AutoConfig.from_pretrained(args.model)
    text_cfg = getattr(cfg, "text_config", cfg)
    n_layers = getattr(text_cfg, "num_hidden_layers")
    layer = resolve_capture_layer(n_layers, None, args.layer_frac)["layer"]
    k = int(fetch_sae_config(args.sae_repo)["k"])
    sae = load_sae(args.sae_repo, layer, device)

    tokenizer = AutoTokenizer.from_pretrained(args.model)
    model = AutoModelForCausalLM.from_pretrained(
        args.model, dtype=torch.bfloat16).to(device).eval()
    decoder_layers = model.model.layers
    ids_mon = tokenizer(" mon", add_special_tokens=False)["input_ids"][0]
    ids_son = tokenizer(" son", add_special_tokens=False)["input_ids"][0]
    module_dtype = next(decoder_layers[layer].parameters()).dtype

    def _to_ids(text: str) -> torch.Tensor:
        return tokenizer(text, return_tensors="pt")["input_ids"].to(device)

    rows = []
    dose_rows = []
    traces_dir = Path(args.traces_dir)
    for seed in seeds:
        traces = load_traces(
            traces_dir / f"case5_s{seed}_qwen35-2b-base_layer12of24_trained.npz")
        prompts = build_prompt_sets(seed)
        norms, freqs = feature_profiles(traces)
        for pair in MAIN_PAIRS:
            for r, d in (pair, pair[::-1]):
                diff_feats = pairwise_differential(traces, r, d, k=K_DIFF)
                for ctx in range(args.max_ctx):
                    ids_r, ids_d = _to_ids(prompts[r][ctx]), _to_ids(prompts[d][ctx])
                    div = clause_divergence(
                        traces["prompts"][(r, ctx)]["tokens"],
                        traces["prompts"][(d, ctx)]["tokens"])
                    L = min(ids_r.shape[1] - div, ids_d.shape[1] - div)
                    if L <= 0:
                        continue
                    positions = tuple(range(div, div + L))
                    # Placeholder : le contrat exige un donneur des la
                    # construction d'un patch ; le hook n'applique JAMAIS
                    # spec.donor (il consomme self.donor_values, capture live).
                    placeholder = tuple(tuple(0.0 for _ in diff_feats)
                                        for _ in positions)
                    template = InterventionSpec(
                        operation="patch", instrument="sae", layer=layer,
                        positions=positions,
                        features=tuple(int(f) for f in diff_feats),
                        donor=placeholder,
                        tensor_space="sae_latent",
                        run=f"live5bis/{r}-ctx{ctx}",
                        paired_run=f"live5bis/{d}-ctx{ctx}", seed=seed)
                    random_spec, matched_tol = matched_random_spec(
                        np.zeros((ids_r.shape[1], int(traces["meta"]["d_sae"]))),
                        template, feature_norms=norms, feature_freqs=freqs,
                        rng=np.random.default_rng(seed * 100 + ctx))
                    universe = np.unique(np.concatenate(
                        [diff_feats, np.asarray(random_spec.features)]))

                    donor_acts = _capture_universe_acts(
                        model, decoder_layers[layer], sae, ids_d, positions, universe)
                    self_acts = _capture_universe_acts(
                        model, decoder_layers[layer], sae, ids_r, positions, universe)
                    donor_on_diff = _restrict(donor_acts, universe, diff_feats)
                    self_on_diff = _restrict(self_acts, universe, diff_feats)

                    row = {"seed": seed, "recipient": r, "donor": d, "ctx": ctx,
                           "divergence": div, "window": L,
                           "universe_size": int(universe.size),
                           "matched_rel_tol": matched_tol}
                    # Sham : semantique sham_of(patch) = write-back de soi par
                    # la voie d'ecriture partagee — instancie ici avec la
                    # tranche captee du receveur (meme operation, meme code).
                    sham_spec = InterventionSpec(
                        operation="patch", instrument="sae", layer=layer,
                        positions=positions,
                        features=tuple(int(f) for f in diff_feats),
                        donor=placeholder,
                        tensor_space="sae_latent",
                        run=f"live5bis/{r}-ctx{ctx}",
                        paired_run=f"live5bis/{d}-ctx{ctx}", seed=seed,
                        control_ref="sham(write-back)")
                    random_live_spec = InterventionSpec(
                        operation="patch", instrument="sae", layer=layer,
                        positions=positions,
                        features=tuple(int(f) for f in random_spec.features),
                        donor=tuple(tuple(0.0 for _ in random_spec.features)
                                    for _ in positions),
                        tensor_space="sae_latent",
                        run=f"live5bis/{r}-ctx{ctx}",
                        paired_run=f"live5bis/{d}-ctx{ctx}", seed=seed)

                    arms = (
                        ("intact", None, None),
                        ("target", template, donor_on_diff),
                        ("sham", sham_spec, self_on_diff),
                        ("random", random_live_spec,
                         _restrict(donor_acts, universe, random_spec.features)),
                    )
                    for arm, spec, donor_vals in arms:
                        handle = None
                        if spec is not None:
                            hook = LatentClauseEdit(sae, spec, donor_vals,
                                                    module_dtype)
                            handle = decoder_layers[layer].register_forward_hook(hook)
                        try:
                            gap = _probe_gap(model, tokenizer, ids_mon, ids_son,
                                             ids_r)
                            with torch.no_grad():
                                gen = model.generate(
                                    ids_r, max_new_tokens=N_NEW_TOKENS,
                                    do_sample=False,
                                    pad_token_id=tokenizer.eos_token_id)
                            text = tokenizer.decode(gen[0, ids_r.shape[1]:],
                                                    skip_special_tokens=True)
                        finally:
                            if handle is not None:
                                handle.remove()
                        row[f"gap_{arm}"] = gap
                        row[f"class_{arm}"] = classify_target(text)
                        row[f"text_{arm}"] = text[:200]
                        if arm != "intact":
                            row[f"gap_shift_{arm}"] = gap - row["gap_intact"]
                    rows.append(row)

                # Dose-response clamp : direction = centroide de clause du
                # donneur, direction critique self<-other, doses symetriques.
                if r == "attn_self" and d == "attn_other":
                    for ctx_d in range(args.max_ctx):
                        ids_r = _to_ids(prompts[r][ctx_d])
                        ids_d = _to_ids(prompts[d][ctx_d])
                        div = clause_divergence(
                            traces["prompts"][(r, ctx_d)]["tokens"],
                            traces["prompts"][(d, ctx_d)]["tokens"])
                        L = min(ids_r.shape[1] - div, ids_d.shape[1] - div)
                        if L <= 0:
                            continue
                        positions = tuple(range(div, div + L))
                        donor_acts = _capture_universe_acts(
                            model, decoder_layers[layer], sae, ids_d, positions,
                            diff_feats)
                        centroid = donor_acts.mean(dim=0)              # [F]
                        scale = float(centroid.abs().mean()) or 1.0
                        for dose in symmetric_doses(scale, 2):
                            spec = InterventionSpec(
                                operation="clamp", instrument="sae", layer=layer,
                                positions=positions,
                                features=tuple(int(f) for f in diff_feats),
                                dose=dose,
                                direction=tuple(float(v) for v in centroid),
                                tensor_space="sae_latent",
                                run=f"live5bis-dose/{r}-ctx{ctx_d}", seed=seed)
                            hook = LatentClauseEdit(
                                sae, spec, centroid.unsqueeze(0).expand(L, -1),
                                module_dtype)
                            handle = decoder_layers[layer].register_forward_hook(hook)
                            try:
                                gap = _probe_gap(model, tokenizer, ids_mon, ids_son,
                                                 ids_r)
                            finally:
                                handle.remove()
                            dose_rows.append({"seed": seed, "ctx": ctx_d,
                                              "dose": dose, "gap": gap})

    # Assemblage : verdicts par le module numpy, jamais ici.
    from ict.attention_schema_causal import axis_verdict

    behavior_axes = {}
    for pair in MAIN_PAIRS:
        for r, d in (pair, pair[::-1]):
            sel = [x for x in rows if x["recipient"] == r and x["donor"] == d]
            if not sel:
                continue
            by_seed: dict[int, list[dict]] = {}
            for x in sel:
                by_seed.setdefault(x["seed"], []).append(x)
            target = [float(np.median([x["gap_shift_target"] for x in v]))
                      for _, v in sorted(by_seed.items())]
            sham = [float(np.median([x["gap_shift_sham"] for x in v]))
                    for _, v in sorted(by_seed.items())]
            random = [float(np.median([x["gap_shift_random"] for x in v]))
                      for _, v in sorted(by_seed.items())]
            sigma = float(np.std(random, ddof=1)) if len(random) > 1 else 0.0
            scale = float(np.median(target)) if target else 0.0
            epsilon = 0.5 * sigma * max(abs(scale), 1e-12)
            verdict, kills = axis_verdict(target, random, epsilon)
            flips = {arm: sum(1 for x in sel if x.get(f"class_{arm}") == d)
                     for arm in ("intact", "target", "sham", "random")}
            behavior_axes[f"{r}<-{d}"] = {
                "gap_shift_target_by_seed": target,
                "gap_shift_sham_by_seed": sham,
                "gap_shift_random_by_seed": random,
                "epsilon": epsilon, "verdict": verdict, "kill_details": kills,
                "lexicon_flips": flips, "n_runs": len(sel),
            }

    payload = {
        "case": "case5bis_behavior",
        "model": args.model, "sae_repo": args.sae_repo, "layer": layer, "k": k,
        "probe_suffix": PROBE_SUFFIX, "max_new_tokens": N_NEW_TOKENS,
        "marker_tokens": {"self": " mon", "other": " son"},
        "axes": behavior_axes,
        "dose_response": dose_rows,
        "runs": [{k: v for k, v in x.items() if not k.startswith("text_")}
                 for x in rows],
        "texts": [{"seed": x["seed"], "recipient": x["recipient"],
                   "donor": x["donor"], "ctx": x["ctx"],
                   "intact": x["text_intact"], "target": x["text_target"],
                   "sham": x["text_sham"], "random": x["text_random"]}
                  for x in rows],
        "verdict": {k: v["verdict"] for k, v in behavior_axes.items()},
    }
    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    Path(args.out).write_text(json.dumps(payload, ensure_ascii=False, indent=1),
                              encoding="utf-8", newline="\n")
    print(f"[live] {len(rows)} runs, {len(dose_rows)} doses -> {args.out}")
    for k, v in behavior_axes.items():
        print(f"  {k}: {v['verdict']}")


if __name__ == "__main__":
    main()
