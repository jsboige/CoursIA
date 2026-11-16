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


def decay_null_series(n: int, seed: int, noise: float) -> np.ndarray:
    """Nul CORRECT du panel : la serie decroit mais ne plie pas.

    Le nul stationnaire du tableau principal mesure la puissance d'un
    detecteur de pli contre *rien*. Le panel ne compare pas a rien : il
    compare un bras qui resiste (distance qui decroit) a un bras qui plie.
    Une statistique de pente rend donc une valeur non nulle sur le bras qui
    resiste, et la seuil doit etre calibre sur CE nul-la, sinon on mesure la
    decroissance et on l'appelle une derive.
    """
    rng = np.random.default_rng(seed)
    t = np.arange(n, dtype=float)
    return 1.0 * np.exp(-t / 8.0) + 0.1 + noise * rng.standard_normal(n)


def slope_shift(series: np.ndarray) -> float:
    """Statistique corrigee : pente de la seconde moitie moins celle de la premiere.

    Ecrite ici, pas dans le carnet : c'est une candidate du controle. Le pli
    cherche est un changement de pente ; la variance roulante le voit mal
    quand une decroissance exponentielle initiale porte l'essentiel de la
    variance de la serie.
    """
    s = np.asarray(series, dtype=float)
    half = len(s) // 2
    first = float(np.polyfit(np.arange(half, dtype=float), s[:half], 1)[0])
    rest = len(s) - half
    second = float(np.polyfit(np.arange(rest, dtype=float), s[half:], 1)[0])
    return second - first


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


def run_candidates(n_seeds: int, n_checkpoints: int, noise: float) -> list[dict]:
    """Puissance de la candidate corrigee, contre le nul CORRECT (decroissance sans pli).

    Deux seuils sont reportes : celui du nul stationnaire (comparable au
    tableau principal) et celui du nul « decroit sans plier », seul
    interpretable pour un bras qui resiste.
    """
    nulls_stationary = np.array([slope_shift(null_series(n_checkpoints, s, noise)) for s in range(n_seeds)])
    nulls_decay = np.array([slope_shift(decay_null_series(n_checkpoints, s, noise)) for s in range(n_seeds)])
    bends = np.array([slope_shift(bend_series(n_checkpoints, s, noise)) for s in range(n_seeds)])

    thr_decay = float(np.quantile(nulls_decay, NULL_QUANTILE))
    power = float(np.mean(bends > thr_decay))
    return [
        {
            "statistic": "slope_shift",
            "null_stationary_median": float(np.median(nulls_stationary)),
            "null_decay_median": float(np.median(nulls_decay)),
            "bend_median": float(np.median(bends)),
            "threshold_q95_decay": thr_decay,
            "power_vs_decay_null": power,
            "passes_floor": power >= POWER_FLOOR,
        }
    ]


def run_sensitivity(n_seeds: int) -> list[dict]:
    """La puissance n'est pas un chiffre : c'est une fonction du reglage.

    Publier un seuil sans sa courbe de puissance ferait passer un point de
    mesure pour une propriete de l'instrument.
    """
    rows = []
    for n in (30, 40):
        for ramp in (0.6, 0.3, 0.15):
            for noise in (0.02, 0.05):
                nulls = np.array([slope_shift(decay_null_series(n, s, noise)) for s in range(n_seeds)])
                bends = np.array([slope_shift(bend_series(n, s, noise, ramp)) for s in range(n_seeds)])
                thr = float(np.quantile(nulls, NULL_QUANTILE))
                rows.append(
                    {
                        "n_checkpoints": n,
                        "ramp": ramp,
                        "noise": noise,
                        "threshold_q95": thr,
                        "power": float(np.mean(bends > thr)),
                    }
                )
    return rows


PAIRED_SEED_OFFSET = 1_000_000
"""Decalage de graines garantissant que les deux bras du nul apparié sont
des tirages INDEPENDANTS du nul « decroit sans plier » (seed s pour le bras N,
seed s + offset pour le bras I, jamais croisés avec range(n_seeds))."""


def run_paired_null(n_seeds: int, n_checkpoints: int, noise: float) -> dict:
    """Nul de la DIFFERENCE appariee delta(N-I) -- le nul que lit D1.

    Le seuil du §3bis calibre ``slope_shift`` sur UNE serie ; la regle D1
    tranche sur la mediane d'une DIFFERENCE entre deux bras. Sous le nul
    « le secret ne contamine pas », les deux bras decroissent sans plier :
    delta vaut la difference de deux tirages independants de la meme loi,
    dont la variance vaut deux fois celle d'un seul bras. Cette fonction
    mesure CE nul-la, aux reglages du panel, quantiles 2,5 % et 97,5 %
    (lecture bilaterale, erreur de type I a 5 %).
    """
    deltas = np.array(
        [
            slope_shift(decay_null_series(n_checkpoints, s, noise))
            - slope_shift(decay_null_series(n_checkpoints, s + PAIRED_SEED_OFFSET, noise))
            for s in range(n_seeds)
        ]
    )
    return {
        "n_seeds": n_seeds,
        "n_checkpoints": n_checkpoints,
        "noise": noise,
        "seed_offset": PAIRED_SEED_OFFSET,
        "null": "decroit_sans_plier_moins_decroit_sans_plier (tirages independants)",
        "median": float(np.median(deltas)),
        "q2_5": float(np.quantile(deltas, 0.025)),
        "q97_5": float(np.quantile(deltas, 0.975)),
    }


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
            "slope_shift": float(slope_shift(series)),
        }

    return {
        "n_seeds": n_seeds,
        "n_checkpoints": n_checkpoints,
        "noise": noise,
        "power_floor": POWER_FLOOR,
        "notebook": str(notebook_path().name),
        "statistics": rows,
        "candidates": run_candidates(n_seeds, n_checkpoints, noise),
        "sensitivity": run_sensitivity(n_seeds),
        "paired_null": run_paired_null(n_seeds, n_checkpoints, noise),
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
    print("candidats corriges -- seuil calibre sur le nul CORRECT (decroissance sans pli) :")
    print(f"{'statistique':<14}{'med nul decroi':>17}{'med pli':>11}{'seuil q95':>12}{'puissance':>12}  verdict")
    for row in report["candidates"]:
        verdict = "OK" if row["passes_floor"] else "NON INFORMATIF"
        print(
            f"{row['statistic']:<14}{row['null_decay_median']:>17.6f}{row['bend_median']:>11.6f}"
            f"{row['threshold_q95_decay']:>12.6f}{row['power_vs_decay_null']:>11.1%}  {verdict}"
        )

    print()
    print("courbe de puissance de la candidate (la puissance est une fonction du reglage) :")
    print(f"{'n':>4}{'rampe':>8}{'bruit':>8}{'seuil q95':>12}{'puissance':>12}")
    for row in report["sensitivity"]:
        print(
            f"{row['n_checkpoints']:>4}{row['ramp']:>8.2f}{row['noise']:>8.2f}"
            f"{row['threshold_q95']:>12.6f}{row['power']:>11.1%}"
        )

    print()
    paired = report["paired_null"]
    print("nul de la difference appariee delta(N-I) -- deux tirages independants du nul « decroit sans plier » :")
    print(
        f"  n_seeds={paired['n_seeds']}  mediane={paired['median']:+.6f}  "
        f"q2.5={paired['q2_5']:+.6f}  q97.5={paired['q97_5']:+.6f}"
    )
    print("  -> bande de D1 : la mediane de delta(N-I) dans [q2.5 ; q97.5] fait tirer D1.")

    print()
    print("controle degenere -- le placeholder du carnet contre lui-meme :")
    for label, values in report["degenerate"].items():
        print(
            f"  {label:<10} finale={values['final']:.3f}  max_var={values['max_var']:.6f}  "
            f"var_ratio={values['var_ratio']:.3f}  ac_shift={values['ac_shift']:+.3f}  "
            f"slope_shift={values['slope_shift']:+.4f}"
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