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

## Temoin d'etat final, pas seulement de cardinal

Un accord de **population** ne prouve pas un accord d'**etat** : deux ensembles
de 96 cellules peuvent differer entierement. A chaque point on calcule donc une
empreinte de l'ensemble final des cellules vivantes sur les deux voies, apres
normalisation par translation (l'organe reconstruit son quadtree a partir de
l'origine et `crop` decale le cadre ; comparer des coordonnees absolues
mesurerait le cadrage, pas la dynamique). Un desaccord d'empreinte invalide la
mesure au meme titre qu'un desaccord de cardinal.

## Verdict falsifiable, et ce qu'il devient sous incertitude

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

Chaque alpha est publie avec le **R2** de son ajustement et avec l'**enveloppe**
des alpha obtenus repetition par repetition (min/max, mesure non parametrique :
il n'y a pas assez de repetitions pour une estimation de variance). `R2` mesure
si la loi de puissance decrit vraiment la serie ; l'enveloppe mesure la
reproductibilite de la pente sous le bruit de chronometrage. Un verdict n'est
declare **robuste** que si les deux le portent : `R2 >= R2_MIN_FOR_LINEARITY` et
enveloppe entierement dans la bande du verdict. Un verdict non robuste est
publie quand meme -- il est alors etiquete comme tel, jamais requalifie en
silence.

Usage :
    python scripts/hashlife/hashlife_speedup.py --json-out scripts/hashlife/hashlife_speedup_results.json
    python scripts/hashlife/hashlife_speedup.py --motif blinker --motif acorn --repeats 5
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
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
# En dessous, la loi de puissance ne decrit pas la serie mesuree : alpha n'est
# pas interpretable, et le verdict qui en derive n'est pas robuste.
R2_MIN_FOR_LINEARITY = 0.9
FINGERPRINT_HEX = 16


# --------------------------------------------------------------------------
# Motifs
# --------------------------------------------------------------------------

BLINKER = {(0, 0), (1, 0), (2, 0)}
BLOCK = {(0, 0), (1, 0), (0, 1), (1, 1)}
GLIDER = {(1, 0), (2, 1), (0, 2), (1, 2), (2, 2)}
ACORN = {(1, 0), (3, 1), (0, 2), (1, 2), (4, 2), (5, 2), (6, 2)}
# Pulsar canonique (periode 3), 48 cellules. La version anterieure n'en portait
# que 36 : les trois barres horizontales de la moitie droite (x = 8, 9, 10)
# manquaient sur les rangees 0, 5, 7 et 12, ce qui cassait la symetrie du motif
# et en faisait un emetteur de planeur au lieu d'un oscillateur (cf. #22294).
PULSAR_ROWS = [
    "..OOO...OOO..",
    ".............",
    "O....O.O....O",
    "O....O.O....O",
    "O....O.O....O",
    "..OOO...OOO..",
    ".............",
    "..OOO...OOO..",
    "O....O.O....O",
    "O....O.O....O",
    "O....O.O....O",
    ".............",
    "..OOO...OOO..",
]
PULSAR = {
    (x, y) for y, row in enumerate(PULSAR_ROWS)
    for x, ch in enumerate(row) if ch == "O"
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
# Temoin d'etat final
# --------------------------------------------------------------------------

def state_fingerprint(cells: set[tuple[int, int]]) -> str:
    """Empreinte de l'ensemble des cellules vivantes, invariante par translation.

    Les deux voies ne partagent pas leur origine : la ligne de base travaille
    dans les coordonnees du motif, l'organe reconstruit son quadtree depuis
    (0, 0) puis `crop` decale le cadre. Normaliser par le coin inferieur rend
    la comparaison portable ; une empreinte egale signifie donc le meme etat
    a translation pres.
    """
    if not cells:
        normalized: list[tuple[int, int]] = []
    else:
        min_x = min(x for x, _ in cells)
        min_y = min(y for _, y in cells)
        normalized = sorted((x - min_x, y - min_y) for x, y in cells)
    payload = ";".join(f"{x},{y}" for x, y in normalized)
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()[:FINGERPRINT_HEX]


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
    naive_final = naive_run(cells, generations)
    naive_s = time.perf_counter() - t0

    t0 = time.perf_counter()
    node = hashlife.advance(hashlife.construct(cells), generations)
    hash_s = time.perf_counter() - t0

    # `expand` est de l'instrumentation : hors du chronometrage, sinon on
    # mesure le cout du temoin en meme temps que celui de l'algorithme.
    hash_final = {(x, y) for x, y, _gray in hashlife.expand(node)}

    naive_print = state_fingerprint(naive_final)
    hash_print = state_fingerprint(hash_final)

    return {
        "motif": name,
        "generations": generations,
        "naive_s": naive_s,
        "hashlife_s": hash_s,
        "naive_population": len(naive_final),
        "hashlife_population": node.n,
        "populations_agree": len(naive_final) == node.n,
        "naive_state": naive_print,
        "hashlife_state": hash_print,
        "states_agree": naive_print == hash_print,
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

def log_log_fit(points: list[tuple[float, float]]) -> dict:
    """Ajustement de moindres carres de log(y) sur log(x).

    Rend la pente (`slope`), l'ordonnee a l'origine (`intercept`), le
    coefficient de determination (`r2`) et le nombre de points retenus (`n`).
    Moins de deux points exploitables : pente et R2 valent 0.0 -- un ajustement
    qui n'existe pas ne porte aucun verdict. Une serie dont tous les `y` sont
    egaux est parfaitement expliquee par une droite horizontale : `r2` vaut
    alors 1.0, et la pente 0.0.
    """
    pts = [(x, y) for x, y in points if x > 0 and y > 0]
    if len(pts) < 2:
        return {"slope": 0.0, "intercept": 0.0, "r2": 0.0, "n": len(pts)}
    xs = [math.log(x) for x, _ in pts]
    ys = [math.log(y) for _, y in pts]
    mx = sum(xs) / len(xs)
    my = sum(ys) / len(ys)
    num = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    den = sum((x - mx) ** 2 for x in xs)
    slope = num / den if den else 0.0
    intercept = my - slope * mx
    ss_tot = sum((y - my) ** 2 for y in ys)
    ss_res = sum((y - (slope * x + intercept)) ** 2 for x, y in zip(xs, ys))
    r2 = 1.0 - ss_res / ss_tot if ss_tot else 1.0
    return {"slope": slope, "intercept": intercept, "r2": r2, "n": len(pts)}


def log_log_slope(points: list[tuple[float, float]]) -> float:
    """Pente seule -- raccourci de `log_log_fit`, conserve pour les appelants."""
    return log_log_fit(points)["slope"]


def alpha_envelope(samples_by_point: dict, motif: str) -> tuple[list[float], int]:
    """Alpha recalcule sur chaque repetition complete, puis enveloppe min/max.

    Une repetition n'est exploitable que si elle porte un temps pour *chaque*
    G du motif ; on retient donc le nombre de repetitions completes, qui peut
    etre inferieur a `--repeats` si une mesure a manque.
    """
    series = [
        (gen, samples)
        for (name, gen), samples in sorted(samples_by_point.items())
        if name == motif
    ]
    common = min((len(samples) for _, samples in series), default=0)
    alphas = [
        log_log_fit([(gen, samples[i]["hashlife_s"]) for gen, samples in series])[
            "slope"
        ]
        for i in range(common)
    ]
    return alphas, common


def verdict_is_robust(verdict: str, envelope: list[float] | None, r2: float) -> bool:
    """Le verdict survit-il a l'incertitude declaree ?

    Deux conditions, toutes deux necessaires : la loi de puissance doit decrire
    la serie (`r2 >= R2_MIN_FOR_LINEARITY`) et l'enveloppe des pentes doit
    rester entierement dans la bande du verdict. Sans enveloppe (moins de deux
    repetitions completes) l'incertitude n'est pas mesuree, donc pas de
    robustesse revendiquee.
    """
    if envelope is None or r2 < R2_MIN_FOR_LINEARITY:
        return False
    lo, hi = envelope
    if verdict == "REDUCIBLE":
        return hi < ALPHA_REDUCIBLE_MAX
    if verdict == "IRREDUCIBLE":
        return lo >= ALPHA_IRREDUCIBLE_MIN
    return lo >= ALPHA_REDUCIBLE_MAX and hi < ALPHA_IRREDUCIBLE_MIN


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
                "naive_state": samples[0]["naive_state"],
                "hashlife_state": samples[0]["hashlife_state"],
                "states_agree": all(s["states_agree"] for s in samples),
                "samples": len(samples),
            }
        )

    for name, entry in motifs.items():
        entry["points"].sort(key=lambda p: p["generations"])
        fit_hash = log_log_fit(
            [(p["generations"], p["hashlife_s"]) for p in entry["points"]]
        )
        fit_naive = log_log_fit(
            [(p["generations"], p["naive_s"]) for p in entry["points"]]
        )
        entry["alpha_hashlife"] = fit_hash["slope"]
        entry["r2_hashlife"] = fit_hash["r2"]
        entry["alpha_naive"] = fit_naive["slope"]
        entry["r2_naive"] = fit_naive["r2"]
        entry["final_ratio"] = entry["points"][-1]["ratio"]
        entry["verdict"] = classify(entry["alpha_hashlife"])
        entry["populations_agree"] = all(
            p["populations_agree"] for p in entry["points"]
        )
        entry["states_agree"] = all(p["states_agree"] for p in entry["points"])
        alphas, common = alpha_envelope(by_point, name)
        entry["repetitions_used"] = common
        entry["alpha_envelope"] = [min(alphas), max(alphas)] if common >= 2 else None
        entry["verdict_robust"] = verdict_is_robust(
            entry["verdict"], entry["alpha_envelope"], entry["r2_hashlife"]
        )

    return {
        "repeats": repeats,
        "thresholds": {
            "alpha_reducible_max": ALPHA_REDUCIBLE_MAX,
            "alpha_irreducible_min": ALPHA_IRREDUCIBLE_MIN,
            "r2_min_for_linearity": R2_MIN_FOR_LINEARITY,
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
                    + (
                        ""
                        if row["populations_agree"] and row["states_agree"]
                        else "  DESACCORD"
                    ),
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
    print(
        f"{'motif':14s} {'anatomie':26s} {'alpha_h':>8s} {'r2_h':>6s} "
        f"{'alpha_n':>8s} {'enveloppe':>17s} {'acc_fin':>9s}  verdict"
    )
    for entry in report["motifs"]:
        envelope = entry["alpha_envelope"]
        env_txt = f"[{envelope[0]:.3f},{envelope[1]:.3f}]" if envelope else "-"
        robustness = "" if entry["verdict_robust"] else "  (non robuste)"
        print(
            f"{entry['motif']:14s} {entry['anatomy']:26s} "
            f"{entry['alpha_hashlife']:8.3f} {entry['r2_hashlife']:6.3f} "
            f"{entry['alpha_naive']:8.3f} {env_txt:>17s} {entry['final_ratio']:9.2f}  "
            f"{entry['verdict']}{robustness}"
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
    state_disagree = [m["motif"] for m in report["motifs"] if not m["states_agree"]]
    if state_disagree:
        print(
            f"\nERREUR : desaccord d'etat final sur {state_disagree} "
            "(meme cardinal ou non, la configuration differe)",
            file=sys.stderr,
        )
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
