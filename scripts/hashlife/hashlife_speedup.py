"""Rapport d'acceleration de HashLife par classe de motif -- une mesure de reductibilite.

Pli 3 de l'Epic Origami (#19742) : l'irreductibilite computationnelle se mesure
sur notre propre outillage. HashLife accelere exponentiellement les motifs dont
l'espace de configurations se repete (memoisation de sous-arbres identiques) et
n'accelere presque pas les motifs chaotiques. L'acceleration mesuree est donc un
releve empirique de la reductibilite d'un motif.

L'organe n'est pas reimplemente : `hashlife.construct` / `hashlife.advance`
viennent de `conway_lean/scripts/hashlife.py` (organe prouve cote Lean,
`Conway/Life/Hashlife*.lean`, `hashlife_correct`). La ligne de base est la
simulation naive par ensemble de cellules.

## Pourquoi chaque mesure tourne dans un processus neuf

L'organe memoise globalement (`functools.lru_cache`, maxsize 2**24 sur `join`
et `life`). Dans un meme processus, la mesure d'un motif rechauffe le cache du
suivant : mesure firsthand, le canon de Gosper rend 0,0265 s a G=4096 juste
apres une premiere passe, puis 0,0038 s a G=16384 -- un motif *plus long* rendu
six fois *plus rapide*. Sans isolation, le relevé mesure l'ordre des appels, pas
l'algorithme. Chaque (motif, G, repetition) est donc execute dans un
sous-processus froid (`--worker`), et le parent agrege des medianes.

## Verdict falsifiable

Pour chaque motif on ajuste, en log-log, le temps de HashLife en fonction de G :
`t ~ G**alpha`. La simulation naive coute Theta(G x population(G)) : elle est
en alpha = 1 quand la population est bornee, et au-dela quand le motif croit
(alpha_naive est mesure et committe comme temoin). L'acceleration ne peut tenir
que si alpha_hash < 1 -- et ne tient vraiment que si alpha_hash reste bas quand
G grandit d'un ordre de grandeur.

- `REDUCIBLE` : alpha_hash < 0.5 -- le temps ne suit pas G, la memoisation gagne.
- `IRREDUCIBLE` : alpha_hash >= 0.8 -- aucune raccourci, il faut simuler.
- `AMBIGUOUS` : entre les deux.

Les seuils sont declares avant la mesure, pas ajustes apres.

Usage :
    python scripts/hashlife/hashlife_speedup.py --json-out scripts/hashlife/hashlife_speedup_results.json
    python scripts/hashlife/hashlife_speedup.py --motif blinker --motif acorn --repeats 5
"""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import random
import statistics
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
ORGAN_DIR = ROOT / "MyIA.AI.Notebooks" / "SymbolicAI" / "Lean" / "conway_lean" / "scripts"
ORGAN_FILE = ORGAN_DIR / "hashlife.py"

ALPHA_REDUCIBLE_MAX = 0.5
ALPHA_IRREDUCIBLE_MIN = 0.8


# --------------------------------------------------------------------------
# Motifs
# --------------------------------------------------------------------------

BLINKER = {(0, 0), (1, 0), (2, 0)}
BLOCK = {(0, 0), (1, 0), (0, 1), (1, 1)}
GLIDER = {(1, 0), (2, 1), (0, 2), (1, 2), (2, 2)}
ACORN = {(1, 0), (3, 1), (0, 2), (1, 2), (4, 2), (5, 2), (6, 2)}
PULSAR = {
    (2, 0), (3, 0), (4, 0), (0, 2), (5, 2), (0, 3), (5, 3), (0, 4), (5, 4),
    (2, 5), (3, 5), (4, 5), (2, 7), (3, 7), (4, 7), (0, 8), (5, 8), (0, 9),
    (5, 9), (0, 10), (5, 10), (2, 12), (3, 12), (4, 12), (7, 2), (7, 3),
    (7, 4), (7, 8), (7, 9), (7, 10), (10, 2), (10, 3), (10, 4), (10, 8),
    (10, 9), (10, 10),
}
GOSPER_GUN_ROWS = [
    "........................O...........",
    "......................O.O...........",
    "............OO......OO............OO",
    "...........O...O....OO............OO",
    "OO........O.....O...OO..............",
    "OO........O...O.OO....O.O...........",
    "..........O.....O.......O...........",
    "...........O...O....................",
    "............OO......................",
]
GOSPER_GUN = {
    (x, y) for y, row in enumerate(GOSPER_GUN_ROWS)
    for x, ch in enumerate(row) if ch == "O"
}


def _soup(size: int, density: float, seed: int) -> set[tuple[int, int]]:
    rng = random.Random(seed)
    return {
        (x, y) for x in range(size) for y in range(size) if rng.random() < density
    }


# nom -> (generations, classe anatomique). Les generations sont celles de la
# mesure canonique ; la classe est descriptive, le verdict vient de alpha.
MOTIFS: dict[str, tuple[list[int], str]] = {
    "blinker": ([256, 1024, 4096, 16384, 65536], "periodique-p2"),
    "block": ([256, 1024, 4096, 16384, 65536], "immuable"),
    "glider": ([256, 1024, 4096, 16384, 65536], "periodique-translatif-p4"),
    "pulsar": ([256, 1024, 4096, 16384], "periodique-p3"),
    "gosper-gun": ([256, 1024, 4096, 16384], "croissance-reguliere"),
    "acorn": ([64, 128, 256, 512, 1024], "methuselah-chaotique"),
    "soup-64-d30": ([64, 256, 1024, 4096], "soupe-chaotique"),
    "soup-128-d35": ([64, 256, 1024, 4096], "soupe-chaotique"),
}


def build_motif(name: str) -> set[tuple[int, int]]:
    if name == "blinker":
        return set(BLINKER)
    if name == "block":
        return set(BLOCK)
    if name == "glider":
        return set(GLIDER)
    if name == "pulsar":
        return set(PULSAR)
    if name == "gosper-gun":
        return set(GOSPER_GUN)
    if name == "acorn":
        return set(ACORN)
    if name == "soup-64-d30":
        return _soup(64, 0.30, seed=64030)
    if name == "soup-128-d35":
        return _soup(128, 0.35, seed=128035)
    raise KeyError(name)


# --------------------------------------------------------------------------
# Simulation naive (ligne de base)
# --------------------------------------------------------------------------

def naive_step(cells: set[tuple[int, int]]) -> set[tuple[int, int]]:
    counts: dict[tuple[int, int], int] = {}
    for x, y in cells:
        for dx in (-1, 0, 1):
            for dy in (-1, 0, 1):
                key = (x + dx, y + dy)
                counts[key] = counts.get(key, 0) + 1
    return {
        p for p, n in counts.items() if n == 3 or (n == 4 and p in cells)
    }


def naive_run(cells: set[tuple[int, int]], generations: int) -> set[tuple[int, int]]:
    current = set(cells)
    for _ in range(generations):
        current = naive_step(current)
    return current


# --------------------------------------------------------------------------
# Mesure d'un point (executee dans un processus neuf)
# --------------------------------------------------------------------------

def measure_point(name: str, generations: int) -> dict:
    if not ORGAN_FILE.is_file():
        raise FileNotFoundError(f"organe introuvable : {ORGAN_FILE}")
    sys.path.insert(0, str(ORGAN_DIR))
    import hashlife  # noqa: E402  (import apres la mise en place du chemin)

    cells = build_motif(name)

    t0 = time.perf_counter()
    naive_pop = len(naive_run(cells, generations))
    naive_s = time.perf_counter() - t0

    t0 = time.perf_counter()
    node = hashlife.advance(hashlife.construct(cells), generations)
    hash_s = time.perf_counter() - t0

    return {
        "motif": name,
        "generations": generations,
        "naive_s": naive_s,
        "hashlife_s": hash_s,
        "naive_population": naive_pop,
        "hashlife_population": node.n,
        "populations_agree": naive_pop == node.n,
    }


def measure_isolated(name: str, generations: int) -> dict:
    """Relance la mesure dans un interpreteur neuf : le cache de l'organe est froid."""
    proc = subprocess.run(
        [sys.executable, str(Path(__file__).resolve()), "--worker", name, str(generations)],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        cwd=str(ROOT),
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"worker {name} G={generations} rc={proc.returncode}\n{proc.stderr[-2000:]}"
        )
    return json.loads(proc.stdout.strip().splitlines()[-1])


# --------------------------------------------------------------------------
# Agregation et verdict
# --------------------------------------------------------------------------

def log_log_slope(points: list[tuple[float, float]]) -> float:
    """Pente de moindres carres de log(y) sur log(x). 0 point -> 0.0."""
    pts = [(x, y) for x, y in points if x > 0 and y > 0]
    if len(pts) < 2:
        return 0.0
    xs = [__import__("math").log(x) for x, _ in pts]
    ys = [__import__("math").log(y) for _, y in pts]
    mx = sum(xs) / len(xs)
    my = sum(ys) / len(ys)
    num = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    den = sum((x - mx) ** 2 for x in xs)
    return num / den if den else 0.0


def classify(alpha_hash: float) -> str:
    if alpha_hash < ALPHA_REDUCIBLE_MAX:
        return "REDUCIBLE"
    if alpha_hash >= ALPHA_IRREDUCIBLE_MIN:
        return "IRREDUCIBLE"
    return "AMBIGUOUS"


def aggregate(rows: list[dict], repeats: int) -> dict:
    by_point: dict[tuple[str, int], list[dict]] = {}
    for row in rows:
        by_point.setdefault((row["motif"], row["generations"]), []).append(row)

    motifs: dict[str, dict] = {}
    for (name, gen), samples in sorted(by_point.items()):
        naive_s = statistics.median(s["naive_s"] for s in samples)
        hash_s = statistics.median(s["hashlife_s"] for s in samples)
        entry = motifs.setdefault(
            name,
            {
                "motif": name,
                "anatomy": MOTIFS[name][1],
                "start_population": None,
                "points": [],
            },
        )
        entry["points"].append(
            {
                "generations": gen,
                "naive_s": naive_s,
                "hashlife_s": hash_s,
                "ratio": naive_s / hash_s if hash_s else float("inf"),
                "naive_population": samples[0]["naive_population"],
                "hashlife_population": samples[0]["hashlife_population"],
                "populations_agree": all(s["populations_agree"] for s in samples),
                "samples": len(samples),
            }
        )

    for entry in motifs.values():
        entry["points"].sort(key=lambda p: p["generations"])
        entry["alpha_hashlife"] = log_log_slope(
            [(p["generations"], p["hashlife_s"]) for p in entry["points"]]
        )
        entry["alpha_naive"] = log_log_slope(
            [(p["generations"], p["naive_s"]) for p in entry["points"]]
        )
        entry["final_ratio"] = entry["points"][-1]["ratio"]
        entry["verdict"] = classify(entry["alpha_hashlife"])
        entry["populations_agree"] = all(
            p["populations_agree"] for p in entry["points"]
        )

    return {
        "repeats": repeats,
        "thresholds": {
            "alpha_reducible_max": ALPHA_REDUCIBLE_MAX,
            "alpha_irreducible_min": ALPHA_IRREDUCIBLE_MIN,
        },
        "motifs": list(motifs.values()),
    }


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------

def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--motif", action="append", choices=sorted(MOTIFS))
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--json-out", type=Path)
    parser.add_argument("--worker", nargs=2, metavar=("MOTIF", "GENERATIONS"))
    args = parser.parse_args(argv)

    if args.worker:
        name, gen = args.worker
        print(json.dumps(measure_point(name, int(gen))))
        return 0

    names = args.motif or list(MOTIFS)
    rows: list[dict] = []
    for name in names:
        for gen in MOTIFS[name][0]:
            for attempt in range(args.repeats):
                row = measure_isolated(name, gen)
                rows.append(row)
                print(
                    f"{name:14s} G={gen:6d} rep={attempt + 1}/{args.repeats} "
                    f"naive={row['naive_s']:.4f}s hash={row['hashlife_s']:.4f}s "
                    f"acc={row['naive_s'] / row['hashlife_s']:.2f}x "
                    f"pop={row['naive_population']}"
                    + ("" if row["populations_agree"] else "  DESACCORD"),
                    flush=True,
                )

    report = aggregate(rows, args.repeats)
    report["organ"] = {
        "path": str(ORGAN_FILE.relative_to(ROOT)).replace("\\", "/"),
        "sha256": hashlib.sha256(ORGAN_FILE.read_bytes()).hexdigest(),
    }
    report["environment"] = {
        "python": platform.python_version(),
        "platform": platform.platform(),
    }

    print()
    print(f"{'motif':14s} {'anatomie':26s} {'alpha_h':>8s} {'alpha_n':>8s} {'acc_fin':>9s}  verdict")
    for entry in report["motifs"]:
        print(
            f"{entry['motif']:14s} {entry['anatomy']:26s} "
            f"{entry['alpha_hashlife']:8.3f} {entry['alpha_naive']:8.3f} "
            f"{entry['final_ratio']:9.2f}  {entry['verdict']}"
        )

    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(
            json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
        )
        print(f"\nJSON ecrit : {args.json_out}")

    disagree = [m["motif"] for m in report["motifs"] if not m["populations_agree"]]
    if disagree:
        print(f"\nERREUR : desaccord de population sur {disagree}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
