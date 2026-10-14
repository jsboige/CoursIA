"""Fidelite J-lens par taille (sous-grain (c) #8236).

Applique un lens fitte localement (``fit_jlens_local.py``, C:/dev/jlens_fits,
JAMAIS commite) aux PROMPT_SETS de calibration SAE et mesure l'accord
lens-vs-modele aux profondeurs de calibration (frac 0.25/0.5) :

  - ``overlap@10`` : |top10(lens) ∩ top10(modele)| / 10, moyen positions+prompts
  - ``rel_l2``     : ||lens - modele||_2 / ||modele||_2 (lignes positions)
  - ``kl``         : KL(modele || lens) en nats (log_softmax des deux)

Sortie : ``traces/calib_jlens_<tag>.npz`` — une cle par ``<set>__<layer>``
(vecteur [overlap, rel_l2, kl]), plus les metadonnees du fit et du domaine
d'evaluation.
Comparable a ``calib_fidelity_*.npz`` (axe SAE) du meme notebook.

Usage :
  python extract_jlens_fidelity.py --lens qwen3-1-7b --model Qwen/Qwen3-1.7B-Base

Deuxieme source : lens PUBLIE (neuronpedia/jacobian-lens). Le 9B dispose d'un
lens canonique fit par la meme construction (Salesforce-wikitext n=458,
min_chars 600, cible = resid final) avec TOUTES les couches sources — un fit
local 9B est alors redundant (mesure 2026-09-27 : >69 min/prompt sur 3090,
backward borne bande passante, ~8-16 jours pour 458 prompts). Mode publie :

  python extract_jlens_fidelity.py --lens qwen3-5-9b --model Qwen/Qwen3.5-9B-Base \
      --lens-repo neuronpedia/jacobian-lens \
      --lens-filename "qwen3.5-9b-pt/jlens/Salesforce-wikitext/Qwen3.5-9B-Base_jacobian_lens.pt" \
      --layers 8,16

Mode offload (modele > VRAM, ex 27B ~52 Go bf16 sur GPU 24+16 Go) :

  python extract_jlens_fidelity.py --lens qwen3-5-27b --model Qwen/Qwen3.5-27B \
      --lens-repo neuronpedia/jacobian-lens \
      --lens-filename "qwen3.5-27b/jlens/Salesforce-wikitext/Qwen3.5-27B_jacobian_lens.pt" \
      --layers 16,32 --offload

La provenance publiee remplace le fit_stats local : attribution modele verifiee
contre le nom de fichier, identite par sha256 de l'artefact telecharge,
n_prompts porte par le lens lui-meme.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter, defaultdict
from pathlib import Path
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    import torch

import numpy as np

FITS_DIR = Path("C:/dev/jlens_fits")
TRACES_DIR = Path(__file__).resolve().parent.parent / "traces"
EVAL_MAX_SEQ_LEN = 128
SKIP_FIRST = 16


def prompt_metrics(
    lens_logits: torch.Tensor, model_logits: torch.Tensor, k: int = 10
) -> dict[str, float]:
    """Metrics moyennes sur les positions, une paire [T, vocab]."""
    import torch

    top_lens = torch.topk(lens_logits, k, dim=-1).indices
    top_true = torch.topk(model_logits, k, dim=-1).indices
    overlap = np.mean(
        [len(set(a.tolist()) & set(b.tolist())) / k for a, b in zip(top_lens, top_true)]
    )
    rel_l2 = (
        (
            torch.norm(lens_logits - model_logits, dim=-1)
            / torch.norm(model_logits, dim=-1)
        )
        .mean()
        .item()
    )
    log_p = torch.log_softmax(model_logits.float(), dim=-1)
    log_q = torch.log_softmax(lens_logits.float(), dim=-1)
    kl = (log_p.exp() * (log_p - log_q)).sum(-1).mean().item()
    return {"overlap10": float(overlap), "rel_l2": float(rel_l2), "kl": float(kl)}


def load_fit_stats(stats_path: Path) -> dict:
    """Charge la provenance du fit ou refuse une extraction non attribuable."""
    if not stats_path.exists():
        raise FileNotFoundError(
            f"Metadonnees de fit absentes : {stats_path}. "
            "Refus de produire une trace sans provenance modele."
        )
    return json.loads(stats_path.read_text())


def sha256_file(path: Path) -> str:
    """Calcule l'identite de contenu d'un artefact de fit."""
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def validate_fit_model(fit_stats: dict, requested_model: str, lens_tag: str) -> None:
    """Refuse une trace dont le modele ne correspond pas au fit declare."""
    fitted_model = fit_stats.get("model")
    if not isinstance(fitted_model, str) or not fitted_model:
        raise ValueError(
            f"Le lens {lens_tag!r} n'a pas de modele attribue dans sa provenance."
        )
    if fitted_model != requested_model:
        raise ValueError(
            f"Le lens {lens_tag!r} a ete fitte pour {fitted_model!r}, "
            f"pas pour {requested_model!r}."
        )


def load_published_lens(
    lens_repo: str, lens_filename: str, requested_model: str
) -> tuple[object, str]:
    """Charge le lens canonique HF et refuse une attribution croisee.

    Le nom de fichier du depot encode le modele (convention du repo
    neuronpedia/jacobian-lens : ``<Model>_jacobian_lens.pt``) : c'est la seule
    attribution disponible cote publie, on l'exige explictement.
    """
    from huggingface_hub import hf_hub_download

    if requested_model.split("/")[-1] not in lens_filename:
        raise ValueError(
            f"Le fichier publie {lens_filename!r} n'encode pas le modele demande "
            f"{requested_model!r} — refus d'attribution croisee."
        )
    local_path = hf_hub_download(lens_repo, lens_filename)
    import jlens

    lens = jlens.JacobianLens.load(local_path)
    print(
        f"[lens] PUBLIE {lens_repo}/{lens_filename} "
        f"({len(lens.source_layers)} couches sources, n={lens.n_prompts})",
        flush=True,
    )
    return lens, local_path


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--lens", required=True, help="tag du fit (ex qwen3-1-7b)")
    ap.add_argument("--model", required=True)
    ap.add_argument(
        "--max-prompts", type=int, default=None, help="limite par set (debug)"
    )
    ap.add_argument(
        "--lens-repo",
        default=None,
        help="lens publie HF (ex neuronpedia/jacobian-lens) ; sinon fit local",
    )
    ap.add_argument(
        "--lens-filename",
        default=None,
        help="chemin du lens dans le repo publie (ex qwen3.5-9b-pt/jlens/...)",
    )
    ap.add_argument(
        "--layers",
        default=None,
        help="sous-ensemble de couches a evaluer (ex 8,16) ; defaut : toutes",
    )
    ap.add_argument(
        "--offload",
        action="store_true",
        help="modele plus gros que la VRAM (ex 27B bf16 ~52 Go sur 24 Go) : "
        "init meta + plan accelerate (GPU/CPU), chargement shard par "
        "shard puis dispatch hooks ; jlens normalise les devices "
        "(transport/unembed suivent le residual)",
    )
    args = ap.parse_args()

    import jlens
    import torch
    from extract_sae_traces import PROMPT_SETS

    published = args.lens_repo is not None
    if published and not args.lens_filename:
        raise ValueError("--lens-repo exige --lens-filename.")

    if published:
        lens, lens_artifact = load_published_lens(
            args.lens_repo, args.lens_filename, args.model
        )
        fit_stats = {"n_prompts": lens.n_prompts}
        lens_sha = sha256_file(Path(lens_artifact))
    else:
        lens_path = FITS_DIR / f"{args.lens}_jacobian_lens.pt"
        stats_path = FITS_DIR / f"{args.lens}_fit_stats.json"
        fit_stats = load_fit_stats(stats_path)

        validate_fit_model(fit_stats, args.model, args.lens)
        expected_hash = fit_stats.get("lens_sha256")
        if not isinstance(expected_hash, str) or (
            sha256_file(lens_path) != expected_hash
        ):
            raise ValueError(
                f"Le lens {args.lens!r} ne correspond pas au hash de sa provenance."
            )

        lens = jlens.JacobianLens.load(str(lens_path))
        if lens.n_prompts != fit_stats.get("n_prompts"):
            raise ValueError(
                f"Le lens declare {lens.n_prompts} prompts mais sa provenance en "
                f"declare {fit_stats.get('n_prompts')!r}."
            )
        lens_sha = expected_hash
        print(f"[lens] {lens!r} <- {lens_path.name}", flush=True)

    if args.layers:
        eval_layers = [int(x) for x in args.layers.split(",")]
        unknown = [l for l in eval_layers if l not in lens.source_layers]
        if unknown:
            raise ValueError(
                f"Couches demandees {unknown} absentes du lens "
                f"(disponibles : {sorted(lens.source_layers)})."
            )
        # Liberer les jacobians hors eval_layers : le lens publie 27B porte
        # 63 couches (fichier 3 150 Mo bf16 -> ~6.6 GiB float32 au chargement,
        # JacobianLens.__init__ fait J.float()) dont l'extraction n'en lit
        # que celles de calibration — le reste est de la RAM morte pendant
        # tout le chargement du modele (~6.4 GiB recuperes).
        dropped = [l for l in lens.jacobians if l not in eval_layers]
        for l in dropped:
            del lens.jacobians[l]
        lens.source_layers = sorted(lens.jacobians)
    else:
        eval_layers = list(lens.source_layers)

    device = torch.device("cuda")
    from transformers import AutoModelForCausalLM, AutoTokenizer

    tok = AutoTokenizer.from_pretrained(args.model)
    if args.offload:
        # Mesure 2026-10-02 (po-2023, GPU 24+16 Go, commit libre ~57 Go) : tous
        # les gluings natifs echouent a charger un 27B sur ce transformers
        # Windows — from_pretrained(device_map) materialise le state dict
        # ENTIER (+55 GiB en 4 s, kill au pic de commit, fast-init inapplique
        # aux modules hybrides fla de Qwen3.5) ; load_checkpoint_and_dispatch
        # laisse des poids meta (cles checkpoint "model.language_model.*" non
        # converties) ; le chargement sans dtype= segfault (RC 139). Chemin
        # manuel valide : init meta (2.4 GiB), plan accelerate, lecture
        # tensor par tensor via safe_open avec conversion de prefixe, hooks
        # dispatch_model. Deux pieges mesures : les devices du plan sont des
        # '0'/'1'/'cpu' SANS prefixe cuda (a normaliser en torch.device, sans
        # quoi tout part en CPU silencieusement) et les copies .to(cuda)
        # async retiennent leur source tant que le device CIBLE n'est pas
        # synchronise (torch.cuda.synchronize() ne couvre que le device
        # courant -> sync explicite de chaque GPU par shard).
        import gc

        from accelerate import (
            dispatch_model,
            infer_auto_device_map,
            init_empty_weights,
        )
        from accelerate.utils import set_module_tensor_to_device
        from huggingface_hub import snapshot_download
        from safetensors import safe_open
        from transformers import AutoConfig

        snap = Path(snapshot_download(args.model, local_files_only=True))
        cfg = AutoConfig.from_pretrained(args.model)
        with init_empty_weights():
            hf_model = AutoModelForCausalLM.from_config(cfg)
        layer_cls = type(hf_model.model.layers[0]).__name__
        dm = infer_auto_device_map(
            hf_model,
            max_memory={0: "21GiB", 1: "12GiB", "cpu": "20GiB"},
            no_split_module_classes=[layer_cls],
        )

        def norm_dev(v):
            # '0'/'1'/'cpu'/'disk' ou int -> torch.device ; les blocs disk
            # (couches entieres insplittables) sont rejoues sur CPU —
            # set_module_tensor_to_device et dispatch_model ne les gerent pas.
            if str(v) == "disk":
                return torch.device("cpu")
            if isinstance(v, int) or str(v).isdigit():
                return torch.device("cuda", int(v))
            return torch.device(str(v))

        dm = {k: norm_dev(v) for k, v in dm.items()}

        def target_device(param_name):
            parts = param_name.split(".")
            for i in range(len(parts), 0, -1):
                cand = ".".join(parts[:i])
                if cand in dm:
                    return dm[cand]
            return dm.get("", torch.device("cpu"))

        known = {n for n, _ in hf_model.named_parameters()}
        known |= {n for n, b in hf_model.named_buffers() if b is not None}
        if getattr(cfg, "tie_word_embeddings", False):
            # embed et lm_head = 1 seul parametre partage ; le checkpoint
            # porte 2 cles — charger les deux dupliquerait le poids.
            known.discard("lm_head.weight")

        index = json.loads((snap / "model.safetensors.index.json").read_text())
        by_shard = defaultdict(list)
        for key, shard in index["weight_map"].items():
            by_shard[shard].append(key)
        for shard in sorted(by_shard):
            with safe_open(snap / shard, framework="pt") as handle:
                for ckpt_key in by_shard[shard]:
                    name = ckpt_key.replace(
                        "model.language_model.", "model.", 1
                    )
                    if name not in known:
                        continue
                    # get_tensor rend une VUE sur le mapping du shard : les
                    # cibles CPU la clonent (poids detache du fichier), les
                    # cibles GPU la consomment telle quelle.
                    value = handle.get_tensor(ckpt_key)
                    dev = target_device(name)
                    if dev.type == "cpu":
                        value = value.clone()
                    set_module_tensor_to_device(
                        hf_model, name, dev, value=value
                    )
                    del value
                    if dev.type == "cuda":
                        # sync PAR COPIE : le bounce buffer pageable->device
                        # de chaque cudaMemcpy n'est liberable qu'apres
                        # achèvement — sync par shard laisse s'accumuler
                        # ~3 shards de staging (mesure : +14 GiB).
                        torch.cuda.synchronize(dev)
            gc.collect()

        meta_left = [
            n
            for n, p in hf_model.named_parameters()
            if p.device.type == "meta" and n != "lm_head.weight"
        ]
        if meta_left:
            raise RuntimeError(
                f"Poids non charges depuis le checkpoint : {meta_left[:5]}"
            )
        torch.cuda.empty_cache()
        hf_model = dispatch_model(hf_model, device_map=dm)
        repartition = Counter(
            str(v) for _, p in hf_model.named_parameters() for v in [p.device]
        )
        print(
            f"[model] {args.model} offload meta : "
            + " ".join(f"{k}={v}" for k, v in sorted(repartition.items())),
            flush=True,
        )
    else:
        hf_model = AutoModelForCausalLM.from_pretrained(
            args.model, dtype=torch.bfloat16, device_map=device
        )
    model = jlens.from_hf(hf_model, tok)
    print(f"[model] {args.model} charge", flush=True)

    arrays: dict[str, np.ndarray] = {}
    n_eval_per_set: list[int] = []
    for set_name, prompts in PROMPT_SETS.items():
        if args.max_prompts:
            prompts = prompts[: args.max_prompts]
        n_eval_per_set.append(len(prompts))
        per_layer: dict[int, list[dict[str, float]]] = {
            layer: [] for layer in eval_layers
        }
        for prompt in prompts:
            ids = tok(
                prompt,
                return_tensors="pt",
                truncation=True,
                max_length=EVAL_MAX_SEQ_LEN,
            )
            seq_len = ids["input_ids"].shape[1]
            positions = list(range(SKIP_FIRST, seq_len - 1))
            if not positions:
                raise ValueError(
                    f"Prompt {set_name!r} trop court apres tokenisation : "
                    f"{seq_len} tokens"
                )
            lens_logits, model_logits, _ = lens.apply(
                model, prompt, positions=positions, max_seq_len=EVAL_MAX_SEQ_LEN
            )
            for layer in eval_layers:
                per_layer[layer].append(
                    prompt_metrics(
                        torch.as_tensor(lens_logits[layer]).float().cuda(),
                        torch.as_tensor(model_logits).float().cuda(),
                    )
                )
        for layer, rows in per_layer.items():
            mean = {m: float(np.mean([r[m] for r in rows])) for m in rows[0]}
            arrays[f"{set_name}__{layer}"] = np.array(
                [mean["overlap10"], mean["rel_l2"], mean["kl"]], dtype=np.float64
            )
            print(
                f"[{set_name}] layer {layer}: overlap@10={mean['overlap10']:.4f} "
                f"rel_l2={mean['rel_l2']:.4f} kl={mean['kl']:.4f}",
                flush=True,
            )

    arrays["meta_model"] = np.array([ord(c) for c in args.model], dtype=np.int16)
    arrays["meta_layers"] = np.array(eval_layers, dtype=np.int64)
    arrays["meta_lens_sha256"] = np.array(
        [ord(c) for c in lens_sha[:16]], dtype=np.int16
    )
    provenance = (
        f"{args.lens_repo}/{args.lens_filename}"
        if published
        else f"local_fit:{args.lens}"
    )
    arrays["meta_provenance"] = np.array(
        [ord(c) for c in provenance], dtype=np.int16
    )
    arrays["meta_n_fit"] = np.array(
        [fit_stats.get("n_prompts", lens.n_prompts)], dtype=np.int64
    )
    arrays["meta_max_seq_len"] = np.array([EVAL_MAX_SEQ_LEN], dtype=np.int64)
    arrays["meta_skip_first"] = np.array([SKIP_FIRST], dtype=np.int64)
    arrays["meta_n_eval"] = np.array(n_eval_per_set, dtype=np.int64)

    TRACES_DIR.mkdir(parents=True, exist_ok=True)
    out = TRACES_DIR / f"calib_jlens_{args.lens}.npz"
    np.savez_compressed(out, **arrays)
    print(f"[out] {out} ({out.stat().st_size / 1024:.1f} KiB)", flush=True)
    print("EXTRACT_OK", flush=True)


if __name__ == "__main__":
    main()
