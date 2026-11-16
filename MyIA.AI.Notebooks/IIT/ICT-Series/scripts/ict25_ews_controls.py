"""Controles positif et nul de l'instrument EWS du panel persona ICT-25.

Objet (issue #26945, tranche T1 ; regle 2 : « controles d'abord »)
------------------------------------------------------------------
Le panel persona d'ICT-25 lit deux fonctions numpy-only du carnet :
``ews_variance`` et ``autocorr1`` (ICT-25, cellule du panel). Ce harnais
mesure leur **puissance** contre un nul stationnaire et un controle positif,
aux reglages du panel lui-meme, avant que la moindre activation reelle ne
soit depensee.

Regle de decision pre-enregistree (docs/ict/ict25-panel-persona-pre-enregistrement.md,
issue D3) : une statistique dont la puissance est inferieure a 80 % au seuil
du quantile 95 du nul ne peut pas servir de critere de lecture. En dessous,
le verdict est « instrument non informatif », jamais une conclusion de fond.

Pourquoi l'instrument est EXTRAIT du carnet et non recopie
----------------------------------------------------------
Un controle qui testerait une copie re-typee mesurerait la copie. Les
fonctions sont donc lues dans le ``.ipynb`` a l'execution : si le carnet
change, le controle change avec lui, et aucune divergence ne peut s'installer
entre l'instrument livre et l'instrument mesure.

Usage
-----
    python MyIA.AI.Notebooks/IIT/ICT-Series/scripts/ict25_ews_controls.py
    python .../ict25_ews_controls.py --seeds 500 --json

Sortie : un tableau texte (ou un objet JSON avec ``--json``). Code de retour
0 si les controles se sont executes, 1 si l'instrument n'a pas pu etre
extrait du carnet -- jamais un code de retour qui ferait passer une valeur
de mesure pour un verdict de CI.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Callable

import numpy as np

# Seuils pre-enregistres
POWER_FLOOR = 0.80
NULL_QUANTILE = 0.95
N_CHECKPOINTS = 30
NOISE = 0.02


def notebook_path() -> Path:
    """Chemin du carnet, deduit de l'emplacement de ce script."""
    return Path(__file__).resolve().parent.parent / "ICT-25-InoculationRL-Python.ipynb"


def load_instrument(path: Path) -> dict:
    """Extrait les fonctions d'interet du carnet et les rend dans un espace de noms.

    Ne execute QUE la cellule qui porte ``def ews_variance``, et seulement sa
    partie amont au bloc de demonstration (marqueur ``# Test : deux bras``) :
    les autres cellules du carnet telechargent des artefacts et ne doivent pas
    tourner ici.
    """
    cells = json.loads(path.read_text(encoding="utf-8"))["cells"]
    source = None
    for cell in cells:
        if cell.get("cell_type") != "code":
            continue
        text = "".join(cell.get("source", []))
        if "def ews_variance" in text and "def simulate_persona_checkpoints" in text:
            source = text
            break
    if source is None:
        raise RuntimeError("cellule du panel introuvable dans le carnet")

    upstream = source.split("# Test : deux bras")[0]
    namespace: dict = {"np": np}
    exec(compile(upstream, str(path), "exec"), namespace)  # noqa: S102 - source du depot

    required = ("ews_variance", "autocorr1", "simulate_persona_checkpoints")
    missing = [name for name in required if name not in namespace]
    if missing:
        raise RuntimeError(f"fonctions absentes de la cellule extraite : {missing}")
    return namespace


def null_series(n: int, seed: int, noise: float) -> np.ndarray:
    """Nul : serie STATIONNAIRE, aucun pli, meme longueur et meme bruit."""
    rng = np.random.default_rng(seed)
    return 0.1 + noise * rng.standard_normal(n)


def bend_series(n: int, seed: int, noise: float, ramp: float = 0.6) -> np.ndarray:
    """Controle positif : decroissance puis rampe lineaire, ecrite ICI.

    Le generateur est independant de ``simulate_persona_checkpoints`` : le
    pli est plante par ce harnais, pas par la fonction du carnet. C'est ce qui
    distingue un controle positif d'un controle tautologique.
    """
    rng = np.random.default_rng(seed)
    t = np.arange(n, dtype=float)
    dist = 1.0 * np.exp(-t / 8.0) + 0.1 + noise * rng.standard_normal(n)
    half = n // 2
    dist[half:] += ramp * (t[half:] - t[half]) / max(half, 1)
    return np.clip(dist, 0, None)


def build_statistics(ns: dict) -> dict[str, Callable[[np.ndarray], float]]:
    """Les trois statistiques candidates, construites sur l'instrument du carnet."""
    ews_variance = ns["ews_variance"]
    autocorr1 = ns["autocorr1"]

    def max_var(series: np.ndarray) -> float:
        return float(np.nanmax(ews_variance(series)))

    def var_ratio(series: np.ndarray) -> float:
        rolling = ews_variance(series)
        rolling = rolling[~np.isnan(rolling)]
        k = max(1, len(rolling) // 3)
        early, late = float(np.mean(rolling[:k])), float(np.mean(rolling[-k:]))
        return late / early if early > 1e-15 else float("inf")

    def ac_shift(series: np.ndarray) -> float:
        half = len(series) // 2
        return float(autocorr1(series[half:])) - float(autocorr1(series[:half]))

    return {"max_var": max_var, "var_ratio": var_ratio, "ac_shift": ac_shift}


def run_controls(n_seeds: int, n_checkpoints: int, noise: float) -> dict:
    """Puissance de chaque statistique, au seuil du quantile 95 du nul."""
    ns = load_instrument(notebook_path())
    stats = build_statistics(ns)

    rows = []
    for name, fn in stats.items():
        nulls = np.array([fn(null_series(n_checkpoints, s, noise)) for s in range(n_seeds)])
        bends = np.array([fn(bend_series(n_checkpoints, s, noise)) for s in range(n_seeds)])
        threshold = float(np.quantile(nulls, NULL_QUANTILE))
        power = float(np.mean(bends > threshold))
        rows.append(
            {
                "statistic": name,
                "null_median": float(np.median(nulls)),
                "bend_median": float(np.median(bends)),
                "threshold_q95": threshold,
                "power": power,
                "passes_floor": power >= POWER_FLOOR,
            }
        )

    sim = ns["simulate_persona_checkpoints"]
    degenerate = {}
    for label, resists in (("I_resists", True), ("N_drifts", False)):
        series = np.asarray(sim(persona_resists=resists, seed=2)["persona_distance"], dtype=float)
        degenerate[label] = {
            "final": float(series[-1]),
            **{name: float(fn(series)) for name, fn in stats.items()},
        }

    return {
        "n_seeds": n_seeds,
        "n_checkpoints": n_checkpoints,
        "noise": noise,
        "power_floor": POWER_FLOOR,
        "notebook": str(notebook_path().name),
        "statistics": rows,
        "degenerate": degenerate,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--seeds", type=int, default=200, help="nombre de graines (defaut 200)")
    parser.add_argument("--json", action="store_true", help="sortie JSON")
    args = parser.parse_args(argv)

    try:
        report = run_controls(args.seeds, N_CHECKPOINTS, NOISE)
    except Exception as exc:  # noqa: BLE001 - un echec d'extraction est un resultat
        print(f"ECHEC: instrument non extractible -- {exc}", file=sys.stderr)
        return 1

    if args.json:
        print(json.dumps(report, indent=2, ensure_ascii=False))
        return 0

    print(
        f"n_seeds={report['n_seeds']}  n_checkpoints={report['n_checkpoints']}  "
        f"bruit={report['noise']}  seuil=quantile{int(NULL_QUANTILE * 100)}(nul)  "
        f"plancher={report['power_floor']:.0%}"
    )
    print(f"{'statistique':<12}{'mediane nul':>14}{'mediane pli':>14}{'seuil q95':>13}{'puissance':>12}  verdict")
    for row in report["statistics"]:
        verdict = "OK" if row["passes_floor"] else "NON INFORMATIF"
        print(
            f"{row['statistic']:<12}{row['null_median']:>14.6f}{row['bend_median']:>14.6f}"
            f"{row['threshold_q95']:>13.6f}{row['power']:>11.1%}  {verdict}"
        )

    print()
    print("controle degenere -- le placeholder du carnet contre lui-meme :")
    for label, values in report["degenerate"].items():
        print(
            f"  {label:<10} finale={values['final']:.3f}  max_var={values['max_var']:.6f}  "
            f"var_ratio={values['var_ratio']:.3f}  ac_shift={values['ac_shift']:+.3f}"
        )
    delta_max_var = abs(
        report["degenerate"]["I_resists"]["max_var"] - report["degenerate"]["N_drifts"]["max_var"]
    )
    print(f"  -> ecart de max_var entre les deux bras : {delta_max_var:.3e}")
    if delta_max_var < 1e-6:
        print("     max_var ne separe pas les deux bras : la rampe plantee n'est pas vue,")
        print("     la decroissance exponentielle initiale sature la statistique.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())