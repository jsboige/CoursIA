"""Mesure la geometrie de la verite a un echelon du protocole v2 (#16760, G2).

Le protocole v2 monte l'echelle SYSTEMATIQUEMENT (R1 2B, R2 9B, R3 27B,
R4 Swift 27B, sonde >= 70B) et exige, par echelon, la meme mesure : les
sondes lineaires de :mod:`ict.probes` sur les residus du dernier token,
le temoin verbalise et l'alignement PC1. Ce harnais produit l'artefact
``traces/truth_geometry_<slug>_layer<N>.json`` correspondant.

Ce que l'artefact porte, et pourquoi :

* ``probes`` -- exactitude HORS ECHANTILLON de MM, LR et MMIID. Les sondes
  sont entrainees sur une partition et evaluees sur l'autre ; une exactitude
  mesuree sur les donnees d'entrainement ne dirait rien de la direction
  (le piege que le Concern du 2026-09-25 reprochait au protocole 1.5B) ;
* ``pca`` -- alignement de PC1 avec le label, evalue sur la partition de
  test seule (``ict.probes.pca_stats``), meme exigence ;
* ``verbalized`` -- le temoin : exactitude de la lecture ``logP(TRUE) -
  logP(FALSE)`` sur la meme batterie. Une sonde qui n'egale pas ce temoin
  ne demontre pas une direction ; une sonde qui le depasse le fait sur une
  information que le comportement verbal n'utilise pas ;
* ``meta`` -- couche capturee, profondeur relative (``resolve_capture_layer``,
  pas un index absolu : ``16`` n'est pas le meme endroit sur 24 et 32 blocs),
  seed, dataset, tailles des partitions, versions.

Le protocole reprend exactement celui du carnet de reference
``2.9g-Geometrie-de-la-Verite`` : prompt = amorce few-shot (deux exemples
etiquetes, ``PREFIX``) + enonce + ``" This statement is:"``, activation =
dernier token du bloc ``l`` (``hidden_states[l + 1]``). L'amorce n'est pas
decorative : sans elle le modele ne met aucune masse sur les tokens de
lecture et le temoin verbalise tombe a 0,500 (cf. le commentaire de
``PREFIX``).

Determinisme (#16590) : seed fixe, TF32 desactive, aucune augmentation.
``ict/`` reste numpy-only ; torch et transformers sont confines ici.

Usage :
    python measure_truth_geometry_rung.py --rung r1
    python measure_truth_geometry_rung.py --rung r1 --mode nf4 --datasets cities,neg_cities
    python measure_truth_geometry_rung.py --rung r2 --max-gpu-gib 7.0 --mode nf4
    python measure_truth_geometry_rung.py --dry-run --rung r1
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import time
import urllib.request
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import numpy as np  # noqa: E402

from ict.probes import pca_stats, probe_accuracy, train_probes  # noqa: E402
from ict.sae_traces import resolve_capture_layer  # noqa: E402
from ict.scale_budget import LADDER, format_plan, plan_rung  # noqa: E402

SERIES_ROOT = Path(__file__).resolve().parent.parent
DATA_DIR = SERIES_ROOT / "got_data"
DATA_BASE = "https://raw.githubusercontent.com/saprmarks/geometry-of-truth/main/datasets/"

#: Datasets du protocole. ``likely`` est le controle de plausibilite :
#: il ne sert pas a mesurer la verite mais a verifier que la direction
#: trouvee n'est pas une direction de vraisemblance.
DATASETS = {
    "cities": "cities.csv",
    "neg_cities": "neg_cities.csv",
    "sp_en_trans": "sp_en_trans.csv",
    "neg_sp_en_trans": "neg_sp_en_trans.csv",
    "larger_than": "larger_than.csv",
    "smaller_than": "smaller_than.csv",
    "likely": "likely.csv",
}

TAIL = " This statement is:"

#: Amorce few-shot du carnet de reference ``2.9g-Geometrie-de-la-Verite``.
#: Sans elle, le modele ne met aucune masse sur les tokens de lecture : mesure
#: du 2026-10-21 sur Qwen3.5-2B-Base zero-shot, la continuation la plus
#: probable apres ``" This statement is:"`` est un saut de ligne (p = 0,57) et
#: ``TRUE`` / ``FALSE`` n'entrent pas dans le top 8 -- le temoin verbalise
#: tombe alors a 0,500 (signe constant), ce qui ne mesure rien. Deux exemples
#: etiquetes suffisent a instaurer le format de reponse.
PREFIX = (
    "The city of Tokyo is in Japan. This statement is: TRUE\n"
    "The city of Hanoi is in Poland. This statement is: FALSE\n"
)

RUNG_BY_KEY: dict[str, dict] = {}
for _entry in LADDER:
    RUNG_BY_KEY[_entry["rung"].lower()] = _entry
    if _entry.get("sae_repo") is None:
        continue
    for _part in _entry["model"].split("/")[-1].lower().split("-"):
        if _part.endswith("b") and _part[:-1].replace(".", "").isdigit():
            RUNG_BY_KEY[_part] = _entry


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    p.add_argument("--rung", choices=sorted(RUNG_BY_KEY), default="r1",
                   help="echelon du protocole v2 (defaut : r1 = 2B)")
    p.add_argument("--model", default=None,
                   help="backbone explicite, prioritaire sur le modele du rung")
    p.add_argument("--mode", choices=("bf16", "nf4"), default="bf16",
                   help="bf16 (defaut, lecture integre) ou nf4 (carte contrainte)")
    p.add_argument("--max-gpu-gib", type=float, default=None,
                   help="budget GPU GiB pour le placement (defaut : toute la carte)")
    p.add_argument("--layer-frac", type=float, default=0.5,
                   help="profondeur relative appariee (defaut 0.5, convention cross-echelle)")
    p.add_argument("--datasets", default="cities,neg_cities",
                   help="datasets a concatener (defaut : cities,neg_cities)")
    p.add_argument("--limit-per-dataset", type=int, default=600,
                   help="sous-echantillon par dataset (defaut 600 ; 0 = tout)")
    p.add_argument("--test-frac", type=float, default=0.3,
                   help="part de la partition de test (defaut 0.3)")
    p.add_argument("--seed", type=int, default=42, help="seed (defaut 42)")
    p.add_argument("--batch", type=int, default=16,
                   help="taille de lot (defaut 16 : sur une carte de 8 Gio, "
                        "un lot plus gros sature la memoire des logits)")
    p.add_argument("--dry-run", action="store_true",
                   help="plan arithmetique seul, aucun chargement")
    p.add_argument("--card-gib", type=float, default=24.0,
                   help="taille de carte pour le plan (defaut 24)")
    p.add_argument("--out-dir", default=str(SERIES_ROOT / "traces"))
    return p.parse_args()


def model_slug(model: str) -> str:
    return re.sub(r"[^a-z0-9]+", "-", model.split("/")[-1].lower()).strip("-")


def load_dataset(name: str, limit: int) -> tuple[list[str], np.ndarray]:
    """Charge un dataset du gisement officiel, en le telechargeant au besoin."""
    import pandas as pd

    DATA_DIR.mkdir(parents=True, exist_ok=True)
    dst = DATA_DIR / DATASETS[name]
    if not dst.exists():
        urllib.request.urlretrieve(DATA_BASE + DATASETS[name], dst)
    df = pd.read_csv(dst)
    statements = df["statement"].astype(str).tolist()
    labels = df["label"].astype(int).to_numpy()
    if limit and limit < len(statements):
        idx = np.random.RandomState(42).choice(len(statements), limit, replace=False)
        statements = [statements[i] for i in idx]
        labels = labels[idx]
    return statements, labels


def stratified_split(y: np.ndarray, test_frac: float, seed: int) -> tuple[np.ndarray, np.ndarray]:
    """Partitions train/test stratifiees par label, deterministes a seed fixee.

    Une partition aleatoire simple peut desequilibrer les classes sur un petit
    echantillon ; la stratification rend l'exactitude de test interpretable.
    """
    rng = np.random.RandomState(seed)
    train_idx: list[int] = []
    test_idx: list[int] = []
    for label in (0, 1):
        idx = np.flatnonzero(y == label)
        rng.shuffle(idx)
        n_test = max(1, int(round(len(idx) * test_frac)))
        test_idx.extend(idx[:n_test].tolist())
        train_idx.extend(idx[n_test:].tolist())
    return np.array(sorted(train_idx)), np.array(sorted(test_idx))


def build_prompts(statements: list[str]) -> list[str]:
    """Applique la forme du carnet de reference : enonce ponctue + ``TAIL``."""
    return [s if s.rstrip().endswith(".") else s.rstrip() + "." for s in statements]


def force_pread_backend() -> None:
    """Force le backend safetensors ``pread`` a la place de ``mmap``.

    Mesure du 2026-10-21 sur Windows 11 / Python 3.13.15 / safetensors 0.8.0 /
    torch 2.6.0+cu124 : materialiser un tenseur lu par le backend ``mmap``
    fait un **access violation** dans ``torch/storage.py:469 __getitem__``
    (segfault, rc=139), alors que le meme tenseur lu par ``pread`` passe. Le
    defaut est reproductible en isolation (``safe_open`` + ``get_tensor``) et
    ne depend donc ni du modele ni de transformers ; il explique les
    segfaults repetes de ``from_pretrained``, qui code ``backend="mmap"`` en
    dur pour le CPU (``modeling_utils.py``).

    ``pread`` ne change que le chemin de lecture du fichier : les poids, les
    cles et le calcul sont identiques. ``disable_mmap=True`` serait
    l'alternative officielle, mais elle charge le fichier entier en memoire
    avant de le decoder -- 2 x 4,5 Gio de pointe, au-dela du commit libre de
    cette machine.
    """
    import functools

    import safetensors

    original = safetensors.safe_open

    @functools.wraps(original)
    def safe_open_pread(*pargs, **kwargs):
        if kwargs.get("backend") == "mmap":
            kwargs["backend"] = "pread"
        return original(*pargs, **kwargs)

    safetensors.safe_open = safe_open_pread
    import transformers.modeling_utils as _mu

    _mu.safe_open = safe_open_pread


def measure(args: argparse.Namespace, entry: dict, model_id: str) -> dict:
    import torch
    from transformers import AutoModelForCausalLM, AutoTokenizer

    force_pread_backend()

    torch.manual_seed(args.seed)
    torch.backends.cuda.matmul.allow_tf32 = False
    torch.backends.cudnn.allow_tf32 = False
    device = torch.device("cuda")
    gpu_name = torch.cuda.get_device_name(0)
    total_gib = torch.cuda.get_device_properties(0).total_memory / 1024.0 ** 3
    print(f"[device] {gpu_name} ({total_gib:.1f} Gio)")

    from transformers import AutoConfig

    cfg = AutoConfig.from_pretrained(model_id)
    text_cfg = getattr(cfg, "text_config", cfg)
    n_layers = getattr(text_cfg, "num_hidden_layers", None) or entry.get("n_layers")
    if n_layers is None:
        raise SystemExit(f"[depth] nombre de couches illisible pour {model_id}")
    depth = resolve_capture_layer(n_layers, None, args.layer_frac)
    layer = depth["layer"]
    print(f"[depth] couche {layer}/{n_layers - 1} (frac {depth['layer_frac']:.3f})")

    t0 = time.time()
    if args.mode == "nf4":
        from transformers import BitsAndBytesConfig

        quant = BitsAndBytesConfig(load_in_4bit=True, bnb_4bit_quant_type="nf4",
                                   bnb_4bit_compute_dtype=torch.bfloat16)
        place: dict = {"device_map": {"": 0}}
        if args.max_gpu_gib is not None:
            place = {"device_map": "auto",
                     "max_memory": {0: f"{args.max_gpu_gib}GiB", "cpu": "64GiB"}}
        model = AutoModelForCausalLM.from_pretrained(
            model_id, quantization_config=quant, dtype=torch.bfloat16, **place)
    else:
        # Chargement CPU puis transfert : le chargement direct-to-CUDA passe par
        # un tampon hote qui echoue en os error 1455 sur une machine dont le
        # commit Windows est sature, alors que le mmap CPU du meme fichier passe.
        model = AutoModelForCausalLM.from_pretrained(
            model_id, dtype=torch.bfloat16, device_map="cpu", low_cpu_mem_usage=True)
        model = model.to(device)
    model.eval()
    load_s = time.time() - t0
    print(f"[load] {args.mode} : {load_s:.1f}s")

    tokenizer = AutoTokenizer.from_pretrained(model_id)
    tokenizer.padding_side = "left"  # la derniere position doit etre le vrai dernier token
    if tokenizer.pad_token is None:
        tokenizer.pad_token = tokenizer.eos_token

    t_true = tokenizer(" TRUE", add_special_tokens=False)["input_ids"][0]
    t_false = tokenizer(" FALSE", add_special_tokens=False)["input_ids"][0]

    names = [n.strip() for n in args.datasets.split(",") if n.strip()]
    statements: list[str] = []
    labels: list[int] = []
    per_dataset: dict[str, int] = {}
    for name in names:
        if name not in DATASETS:
            raise SystemExit(f"[dataset] inconnu : {name} (connus : {sorted(DATASETS)})")
        s, y = load_dataset(name, args.limit_per_dataset)
        statements.extend(s)
        labels.extend(y.tolist())
        per_dataset[name] = len(s)
        print(f"[dataset] {name}: {len(s)} enonces")

    prompts = [PREFIX + p + TAIL for p in build_prompts(statements)]
    y = np.asarray(labels, dtype=int)

    acts: list[np.ndarray] = []
    dlp: list[float] = []
    t1 = time.time()
    with torch.no_grad():
        for i in range(0, len(prompts), args.batch):
            batch = prompts[i:i + args.batch]
            enc = tokenizer(batch, return_tensors="pt", padding=True,
                            truncation=True, max_length=192).to(device)
            # logits_to_keep=1 : seul le dernier token est projete sur le
            # vocabulaire. Sans lui, logits = [lot, seq, 248320] -- 600 Mio
            # par lot sur un vocabulaire de 248 k tokens, pour un seul
            # token lu (mesure : torche OOM a 8 Gio avec un lot de 24).
            out = model(**enc, output_hidden_states=True, logits_to_keep=1)
            hidden = out.hidden_states[layer + 1][:, -1, :].to(torch.float32)
            acts.append(hidden.cpu().numpy())
            logits = out.logits[:, -1, :].to(torch.float32)
            lp = torch.log_softmax(logits, dim=-1)
            dlp.extend((lp[:, t_true] - lp[:, t_false]).cpu().tolist())
    extract_s = time.time() - t1
    X = np.concatenate(acts, axis=0)
    dlp_arr = np.asarray(dlp, dtype=float)
    print(f"[extract] X={X.shape} en {extract_s:.1f}s")

    train_idx, test_idx = stratified_split(y, args.test_frac, args.seed)
    probes, mu_train = train_probes(X[train_idx], y[train_idx])
    scores = {name: round(float(probe_accuracy(theta, mu_train, X[test_idx], y[test_idx])), 4)
              for name, theta in probes.items()}
    align = float(pca_stats(X[test_idx], y[test_idx])[0])
    verbalized = float(np.mean((dlp_arr[test_idx] > 0) == y[test_idx]))
    print(f"[probes] test={len(test_idx)} MM={scores['MM']:.3f} LR={scores['LR']:.3f} "
          f"MMIID={scores['MMIID']:.3f} | PC1={align:.3f} | verbalise={verbalized:.3f}")

    del model
    torch.cuda.empty_cache()

    return {
        "meta": {
            "issue": "#16760",
            "protocol": "geometry-of-truth-v2-G2",
            "rung": entry.get("rung"),
            "model": model_id,
            "generation": entry.get("generation"),
            "mode": args.mode,
            "layer": layer,
            "layer_frac": depth["layer_frac"],
            "n_layers": n_layers,
            "gpu": gpu_name,
            "total_vram_gib": round(total_gib, 2),
            "seed": args.seed,
            "tf32": False,
            "datasets": per_dataset,
            "n_statements": int(len(y)),
            "n_train": int(len(train_idx)),
            "n_test": int(len(test_idx)),
            "test_frac": args.test_frac,
            "torch": torch.__version__,
            "transformers": __import__("transformers").__version__,
            "measured": True,
        },
        "probes_test": scores,
        "pca_test": {"align_pc1": round(align, 4)},
        "verbalized_test": {"accuracy": round(verbalized, 4),
                            "mean_dlp": round(float(dlp_arr[test_idx].mean()), 4)},
        "extract_seconds": round(extract_s, 2),
        "load_seconds": round(load_s, 2),
    }


def main() -> int:
    args = parse_args()
    entry = RUNG_BY_KEY[args.rung]
    model_id = args.model or entry["model"]
    plan = plan_rung(model_id, args.card_gib,
                     nominal_params_e9=entry.get("nominal_params_e9"))
    print(format_plan([plan]))
    if args.dry_run:
        print("[dry-run] arithmetique seule -- lancer sans --dry-run pour mesurer.")
        return 0
    if not args.model and not entry.get("sae_repo"):
        print(f"[sae] {model_id} hors collection Qwen-Scope : couverture par J-Lens / F-Lens.")
    result = measure(args, entry, model_id)
    out = Path(args.out_dir) / f"truth_geometry_{model_slug(model_id)}_layer{result['meta']['layer']}.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"[out] {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())