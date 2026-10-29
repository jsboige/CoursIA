"""Verification locale du moteur DM-JEPA 1.7 (issue #21997, DangerLabs).

Ce que mesure ce script
-----------------------
DM-JEPA 1.7 est un moteur de decision non-autoregressif : il lit un etat et des
questions typees (`choice`) et rend une probabilite par option, sans generer de
texte. Sa fiche Hugging Face revendique une latence mediane de 34,3 ms et un
modele de 0,3 Md de parametres, sans validation independante.

Ce script re-mesure localement, avec le moteur officiel du depot :

1. le nombre de parametres reellement charges et la couverture des cles du
   fichier `model.safetensors` (l'engine charge en `strict=False`) ;
2. la latence mediane et p90, sur CPU et sur GPU, ainsi que le pic VRAM ;
3. le rang de l'option correcte sur un jeu de decisions construit ici, contre
   la baseline triviale du tri aleatoire (rang attendu `(K+1)/2`) ;
4. la stabilite sur entrees adverses : negation, distracteur partageant le mot
   de l'ancre, permutation de position, duplication d'option, lot de questions.

Ce que ce script ne mesure pas
------------------------------
Les benchmarks de la fiche (GSM8K et consorts) ne sont pas rejoues : les charges
utiles de la suite Decision Index 0.3 (`multimodalart/decision-index-suite-0.3`)
ne sont pas publiees (401 / `RepositoryNotFoundError`, mesure du 2026-10-21,
documentee dans `docs/genai/decision-models-local-verification.md` §1). Les
mesures ci-dessous portent donc sur un jeu de decisions local, conforme au plan
de validation de l'issue #21997, et ne valident aucun chiffre de la fiche.

Prerequis
---------
Python 3.10+, `torch`, `tokenizers`, `safetensors`, `huggingface_hub`, et le kit
`apolinario/decision-index` (module `decision_index`, utilise par l'engine pour
ses contrats `Engine` / `Unsupported` / `validate`) :

    git clone https://github.com/apolinario/decision-index
    pip install torch tokenizers safetensors huggingface_hub

Utilisation
-----------
    python scripts/genai-stack/dm_jepa_local_check.py \
        --kit-path /chemin/vers/decision-index \
        --revision 9f2f6f85a2923c0f2307cc966b7ead36723e96dc \
        --json scripts/results/dm_jepa_local_<date>.json

Un snapshot deja telecharge se sert sans reseau avec `--snapshot <chemin>` ; le
script epingle alors ce repertoire et n'appelle pas le hub.

Note sur l'artefact publie : les modules d'architecture du snapshot importent le
layout prive `dm_bert.src.*` (`src/jepa_1_7.py` lignes 19-26) alors que tous les
modules requis sont livres sous `src/`. Ce script installe un alias
`sys.modules` (`dm_bert.src` -> `src/`) : aucun code n'est copie, aucun poids
n'est modifie.
"""

from __future__ import annotations

import argparse
import json
import random
import statistics
import sys
import time
import types
from pathlib import Path

REPO_ID = "DangerLabs/dm-jepa-1.7"
ANCHORS = ["chien", "chat", "oiseau", "tracteur", "klaxon"]
NEUTRALS = [
    "Le bilan trimestriel est positif",
    "xyz plt qrs tuv",
    "Une facture de 42 euros",
    "La reunion commence a neuf heures",
    "Le dossier est range dans l'armoire",
    "Le train part de la voie sept",
    "La peinture du couloir est seche",
]


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Validation locale DM-JEPA 1.7 (issue #21997)")
    p.add_argument("--snapshot", help="snapshot local du depot (sinon telechargement hub)")
    p.add_argument("--revision", default="main", help="revision hub (sha ou ref)")
    p.add_argument("--kit-path", help="clone de apolinario/decision-index (module decision_index)")
    p.add_argument("--device", default="cpu", choices=["cpu", "cuda"], help="device des mesures de rang")
    p.add_argument("--n-problems", type=int, default=60)
    p.add_argument("--k-options", type=int, default=6)
    p.add_argument("--seed", type=int, default=42)
    p.add_argument("--n-latency", type=int, default=20)
    p.add_argument("--n-perm-problems", type=int, default=10)
    p.add_argument("--n-permutations", type=int, default=5)
    p.add_argument("--json", help="chemin du rapport JSON a ecrire")
    return p.parse_args()


def resolve_snapshot(args: argparse.Namespace) -> Path:
    if args.snapshot:
        snap = Path(args.snapshot).resolve()
        if not (snap / "dm_jepa_1_7_engine.py").exists():
            raise SystemExit(f"snapshot invalide (pas de dm_jepa_1_7_engine.py) : {snap}")
        return snap
    from huggingface_hub import snapshot_download

    return Path(
        snapshot_download(
            repo_id=REPO_ID,
            revision=args.revision,
            allow_patterns=["*.json", "*.safetensors", "*.pt", "src/*.py"],
        )
    )


def alias_dm_bert(snap: Path) -> None:
    """Alias pur du layout prive : `dm_bert.src` -> `src/` du snapshot."""
    if "dm_bert" in sys.modules:
        return
    pkg = types.ModuleType("dm_bert")
    pkg.__path__ = []
    src = types.ModuleType("dm_bert.src")
    src.__path__ = [str(snap / "src")]
    sys.modules["dm_bert"] = pkg
    sys.modules["dm_bert.src"] = src


def load_engine_module(snap: Path, kit_path: str | None):
    if kit_path:
        sys.path.insert(0, str(Path(kit_path).resolve()))
    sys.path.insert(0, str(snap))
    try:
        import dm_jepa_1_7_engine as eng_mod
    except ModuleNotFoundError as exc:
        if "decision_index" in str(exc):
            raise SystemExit(
                "Le moteur importe `decision_index.engines.base` (kit apolinario/decision-index).\n"
                "Fournir --kit-path <clone> ou installer le kit sur le PYTHONPATH."
            ) from exc
        raise
    eng_mod._ensure_dm_jepa_1_7_files = lambda repo_id=REPO_ID, local_dir=None: snap
    return eng_mod


def build_problem(i: int, seed: int, k: int) -> dict:
    rng = random.Random(seed * 1000 + i)
    target = rng.choice(ANCHORS)
    good = f"On entend un {target} provenant de la cour"
    neg = f"On n'entend aucun {target} dans la cour"
    shared = f"Le {target} du voisin est visible depuis la fenetre"
    options = [good, neg, shared] + rng.sample(NEUTRALS, k - 3)
    rng.shuffle(options)
    return {
        "context": f"Quel bruit vient de la cour ? (cas {i})",
        "instructions": "Choisir l'option decrivant la source du bruit.",
        "options": options,
        "good": options.index(good),
        "neg": options.index(neg),
        "shared": options.index(shared),
    }


def ask(engine, problem: dict, extra_criteria: dict | None = None) -> dict:
    criteria = {f"opt{j}": t for j, t in enumerate(problem["options"])}
    if extra_criteria:
        criteria.update(extra_criteria)
    questions = {"q": {"type": "choice", "instructions": problem["instructions"], "criteria": criteria}}
    resp, _ = engine(problem["context"], questions)
    return resp["answers"]["q"]["probabilities"]


def ask_batch(engine, problem: dict) -> dict:
    criteria = {f"opt{j}": t for j, t in enumerate(problem["options"])}
    questions = {
        "q1": {"type": "choice", "instructions": problem["instructions"], "criteria": criteria},
        "q2": {"type": "choice", "instructions": problem["instructions"], "criteria": dict(criteria)},
    }
    resp, _ = engine(problem["context"], questions)
    return resp["answers"]


def rank_of(probs: dict, idx: int) -> int:
    order = sorted(probs.items(), key=lambda kv: -kv[1])
    return [k for k, _ in order].index(f"opt{idx}") + 1


def main() -> int:
    args = parse_args()
    import torch

    snap = resolve_snapshot(args)
    alias_dm_bert(snap)
    eng_mod = load_engine_module(snap, args.kit_path)

    config = json.loads((snap / "config.json").read_text(encoding="utf-8"))
    report: dict = {
        "repo_id": REPO_ID,
        "snapshot": str(snap),
        "revision_requested": args.revision,
        "snapshot_revision": snap.name,
        "config_version": config.get("version"),
        "config_architectures": config.get("architectures"),
        "python": sys.version.split()[0],
        "torch": torch.__version__,
        "cuda_available": torch.cuda.is_available(),
        "seed": args.seed,
        "n_problems": args.n_problems,
        "k_options": args.k_options,
        "device_ranking": args.device,
    }

    t0 = time.perf_counter()
    engine = eng_mod.DMJEPA17Engine(model=REPO_ID, device=args.device)
    if args.device == "cuda":
        engine.synchronize()
    report["load_s"] = round(time.perf_counter() - t0, 1)
    report["param_count"] = engine.provenance["parameters"]
    report["weights_source"] = Path(engine.provenance["weights_source"]).name

    from safetensors.torch import load_file

    sd_file = load_file(str(snap / "model.safetensors"))
    model_keys = set(engine.model.state_dict().keys())
    file_keys = set(sd_file.keys())
    report["key_coverage"] = {
        "model_keys": len(model_keys),
        "file_keys": len(file_keys),
        "matched": len(model_keys & file_keys),
        "missing_in_file": sorted(model_keys - file_keys)[:8],
        "unused_from_file": len(file_keys - model_keys),
    }

    problems = [build_problem(i, args.seed, args.k_options) for i in range(args.n_problems)]

    r_good, r_neg, r_shared, p_good = [], [], [], []
    t0 = time.perf_counter()
    for p in problems:
        probs = ask(engine, p)
        r_good.append(rank_of(probs, p["good"]))
        r_neg.append(rank_of(probs, p["neg"]))
        r_shared.append(rank_of(probs, p["shared"]))
        p_good.append(probs[f"opt{p['good']}"])
    wall = time.perf_counter() - t0
    report["ranking"] = {
        "random_expected_rank": (args.k_options + 1) / 2,
        "good": {
            "mean_rank": round(statistics.mean(r_good), 3),
            "accuracy_at_1": round(r_good.count(1) / len(r_good), 3),
            "distribution": {str(r): r_good.count(r) for r in sorted(set(r_good))},
            "mean_probability": round(statistics.mean(p_good), 4),
        },
        "negation": {
            "mean_rank": round(statistics.mean(r_neg), 3),
            "accuracy_at_1": round(r_neg.count(1) / len(r_neg), 3),
            "distribution": {str(r): r_neg.count(r) for r in sorted(set(r_neg))},
        },
        "shared_word_distractor": {
            "mean_rank": round(statistics.mean(r_shared), 3),
            "accuracy_at_1": round(r_shared.count(1) / len(r_shared), 3),
            "distribution": {str(r): r_shared.count(r) for r in sorted(set(r_shared))},
        },
        "wall_s": round(wall, 1),
    }

    rng = random.Random(args.seed + 1)
    perm_ranks: list[int] = []
    pos_ranks: dict[int, list[int]] = {}
    for p in problems[: args.n_perm_problems]:
        for _ in range(args.n_permutations):
            opts = list(p["options"])
            rng.shuffle(opts)
            q = dict(p, options=opts, good=opts.index(p["options"][p["good"]]))
            r = rank_of(ask(engine, q), q["good"])
            perm_ranks.append(r)
            pos_ranks.setdefault(q["good"], []).append(r)
    report["permutation"] = {
        "n_calls": len(perm_ranks),
        "mean_rank_good": round(statistics.mean(perm_ranks), 3),
        "stdev_rank_good": round(statistics.pstdev(perm_ranks), 3),
        "accuracy_at_1": round(perm_ranks.count(1) / len(perm_ranks), 3),
        "rank_by_position": {str(k): round(statistics.mean(v), 3) for k, v in sorted(pos_ranks.items())},
    }

    dup_gaps, dup_ranks, dup_aggregate = [], [], []
    for p in problems[:10]:
        extra = {"opt_dup": p["options"][p["good"]]}
        probs = ask(engine, p, extra_criteria=extra)
        a, b = probs[f"opt{p['good']}"], probs["opt_dup"]
        dup_gaps.append(abs(a - b))
        dup_ranks.append(rank_of(probs, p["good"]))
        dup_aggregate.append(sum(1 for v in probs.values() if v > a + b) + 1)
    report["duplication"] = {
        "n": len(dup_ranks),
        "mean_abs_gap_between_twins": round(statistics.mean(dup_gaps), 6),
        "mean_rank_single_key": round(statistics.mean(dup_ranks), 3),
        "mean_rank_aggregate_twin": round(statistics.mean(dup_aggregate), 3),
    }

    diffs = []
    for p in problems[:10]:
        single = ask(engine, p)
        batch = ask_batch(engine, p)["q2"]["probabilities"]
        diffs.append(max(abs(single[k] - batch[k]) for k in single))
    report["batch_vs_single"] = {
        "n": len(diffs),
        "max_abs_diff": round(max(diffs), 6),
        "mean_abs_diff": round(statistics.mean(diffs), 6),
    }

    lat_cpu = []
    p0 = problems[0]
    for _ in range(args.n_latency):
        t = time.perf_counter()
        ask(engine, p0)
        lat_cpu.append((time.perf_counter() - t) * 1000)
    report["latency_ms_" + args.device] = {
        "median": round(statistics.median(lat_cpu), 1),
        "p90": round(sorted(lat_cpu)[int(0.9 * len(lat_cpu))], 1),
    }

    if torch.cuda.is_available():
        gpu = eng_mod.DMJEPA17Engine(model=REPO_ID, device="cuda")
        gpu.synchronize()
        torch.cuda.reset_peak_memory_stats()
        lat = []
        for _ in range(args.n_latency):
            gpu.synchronize()
            t = time.perf_counter()
            ask(gpu, p0)
            gpu.synchronize()
            lat.append((time.perf_counter() - t) * 1000)
        report["latency_ms_gpu"] = {
            "median": round(statistics.median(lat), 1),
            "p90": round(sorted(lat)[int(0.9 * len(lat))], 1),
            "gpu": torch.cuda.get_device_name(0),
        }
        report["peak_vram_gib"] = round(torch.cuda.max_memory_allocated() / 1024**3, 2)
        report["total_vram_gib"] = round(torch.cuda.get_device_properties(0).total_memory / 1024**3, 1)

    text = json.dumps(report, indent=2, ensure_ascii=False)
    print(text)
    if args.json:
        out = Path(args.json)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(text, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())