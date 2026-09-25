"""Stratification inter-tailles des runs ICT-25a (#17740, volet 1).

La matrice des dissociations publie aujourd'hui, pour ICT-25a, deux nombres :
la pente de ``hack_late`` par taille (0.222 -> 0.444 -> 0.942, bras N) et
l'ecart ``Np - N`` par graine aux trois tailles. Ces nombres vivaient dans la
prose, sans organe de recalcul : rien ne les rattachait aux artefacts
committes, et un run regenere aurait fait deriver la matrice sans que rien ne
rougisse. Ce module rend la claim falsifiable en la recalculant depuis
``runs/ict25a_*.json``, et il etend la stratification aux grandeurs que la
matrice ne portait pas (``reward_late``, ``mc_late``) avec leur dispersion
inter-graines -- l'acceptance demande *chaque* grandeur rapportee par les runs,
pas seulement celle qui porte le verdict.

Trois refus explicites, qui sont le contenu du module :

1. **Aucune agregation entre tailles.** Une moyenne unique sur les trois
   tailles effacerait exactement l'effet mesure (l'uptake croit avec la
   taille). La sortie ne porte donc que des lignes par taille, et aucune
   fonction n'agrege les tailles entre elles -- il n'y a pas d'appel possible
   par erreur.
2. **Aucun appariement silencieux.** ``Np - N`` est un ecart *par graine* (les
   deux bras partagent 0/1/42) ; si les jeux de graines different, le module
   leve au lieu d'apparier au hasard ou de comparer des moyennes.
3. **Aucun verdict de significativite sous 4 graines.** La batterie ML du
   depot exige >= 4 graines ; ces artefacts en portent 3 (0/1/42). Le verdict
   rendu est donc descriptif, et le dit dans la sortie.

Une taille declaree dont l'artefact n'est pas sur ``main`` (la tranche 32B,
livree par #17724) sort en ``provisional`` : le module refuse d'en tirer une
conclusion plutot que de la melanger aux tailles mesurees.
"""

from __future__ import annotations

import argparse
import json
import statistics
import sys
from pathlib import Path
from typing import Iterable, Mapping, Sequence

# --- Constantes de protocole ------------------------------------------------

#: Tailles mesurees par les artefacts committes dans ``runs/``.
MEASURED_SIZES: tuple[str, ...] = ("1.5B", "7B", "14B")

#: Tailles annoncees par la campagne : 32B est livre par #17724 et n'est pas
#: encore sur ``main``. Declaree ici pour qu'elle ne soit jamais implicitement
#: fondue dans les tailles mesurees.
DECLARED_SIZES: tuple[str, ...] = ("1.5B", "7B", "14B", "32B")

#: Bras compares. ``N`` = sans prefixe, ``Np`` = prefixe informe-mais-interdit.
ARMS: tuple[str, ...] = ("N", "Np")

#: Grandeurs stratifiees. ``hack_late`` porte le verdict de la matrice ;
#: ``reward_late`` et ``mc_late`` sont rapportees avec leur dispersion et sans
#: lecture d'exactitude (garde-fou 6, #13614 : ``mc_late`` n'est pas un taux
#: d'exactitude dans ce harnais).
METRICS: tuple[str, ...] = ("hack_early", "hack_late", "reward_late", "mc_late")

#: Seuil de la batterie ML du depot (CLAUDE.md section C) : sous 4 graines,
#: aucun verdict de significativite n'est prononcable.
MIN_SEEDS_FOR_SIGNIFICANCE = 4

#: Nombres publies par ``docs/ict/dissociations-matrix.md`` pour ICT-25a, avec
#: leur tolerance (la matrice les cite a trois decimales).
PUBLISHED_TOLERANCE = 5e-4
PUBLISHED_HACK_LATE_SLOPE = {"1.5B": 0.222, "7B": 0.444, "14B": 0.942}
PUBLISHED_NP_MINUS_N_DELTA = {
    "1.5B": (0.033, 0.008, -0.008),
    "7B": (0.050, 0.158, 0.067),
    "14B": (-0.133, -0.117, -0.158),
}

DEFAULT_RUNS_DIR = Path(__file__).resolve().parents[1] / "runs"


class StratificationError(RuntimeError):
    """Erreur de protocole : la mesure demandee n'est pas instrumentable."""


# --- Chargement -------------------------------------------------------------


def artifact_name(arm: str, size: str) -> str:
    return f"ict25a_{arm}_{size}.json"


def load_artifact(path: Path) -> dict:
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def load_runs(
    runs_dir: Path,
    sizes: Sequence[str] = MEASURED_SIZES,
    arms: Sequence[str] = ARMS,
) -> dict[tuple[str, str], dict]:
    """Charge les artefacts presents, clef ``(bras, taille)``.

    Un artefact absent n'est pas une erreur de lecture : il n'est simplement
    pas rendu. C'est ``stratify()`` qui declare explicitement les tailles
    manquantes, pour qu'une absence ne se lise jamais comme un zero.
    """
    runs: dict[tuple[str, str], dict] = {}
    for arm in arms:
        for size in sizes:
            path = runs_dir / artifact_name(arm, size)
            if path.exists():
                runs[(arm, size)] = load_artifact(path)
    return runs


def coverage(runs: Mapping[tuple[str, str], dict]) -> dict:
    """Liste nominative des artefacts couverts (acceptance, point 1)."""
    files = sorted(f"{arm}_{size}" for (arm, size) in runs)
    models = sorted({artifact.get("model") for artifact in runs.values() if artifact.get("model")})
    return {
        "artifacts": files,
        "count": len(files),
        "models": models,
        "steps": sorted(
            {artifact.get("steps") for artifact in runs.values() if artifact.get("steps")}
        ),
        "note": "aucune serie implicite : seuls les artefacts listes sont stratifies",
    }


# --- Mesure par taille ------------------------------------------------------


def seed_map(artifact: Mapping, metric: str) -> dict[int, float]:
    """Valeurs par graine, ordonnees par numero de graine.

    Une graine dupliquee leve : elle s'ecraserait en silence, et le refus
    n°2 verrait alors des jeux de graines coherents en apparence.
    """
    try:
        rows = artifact["seeds"]
    except (KeyError, TypeError) as exc:  # pragma: no cover - artefact malforme
        raise StratificationError(f"artefact sans cle 'seeds' : {exc}") from exc
    values: dict[int, float] = {}
    for row in rows:
        if metric not in row:
            raise StratificationError(
                f"graine {row.get('seed')} sans la grandeur {metric!r}"
            )
        values[int(row["seed"])] = float(row[metric])
    if len(values) != len(rows):
        raise StratificationError(
            f"graine dupliquee : {len(rows)} enregistrements pour {len(values)} graines"
        )
    if not values:
        raise StratificationError(f"aucune graine pour la grandeur {metric!r}")
    return values


def size_row(runs: Mapping[tuple[str, str], dict], metric: str, size: str) -> dict:
    """Ligne d'une taille : valeur par bras, dispersion inter-graines.

    La dispersion est rendue en clair (min, max, etendue, ecart-type) a cote de
    la moyenne : une moyenne seule laisserait lire un effet la ou les graines
    divergent.
    """
    arms: dict[str, dict] = {}
    for arm in ARMS:
        artifact = runs.get((arm, size))
        if artifact is None:
            continue
        values = seed_map(artifact, metric)
        ordered = [values[seed] for seed in sorted(values)]
        arms[arm] = {
            "n_seeds": len(ordered),
            "seeds": sorted(values),
            "per_seed": {str(seed): round(values[seed], 6) for seed in sorted(values)},
            "mean": round(statistics.fmean(ordered), 6),
            "min": round(min(ordered), 6),
            "max": round(max(ordered), 6),
            "range": round(max(ordered) - min(ordered), 6),
            "stdev": round(statistics.stdev(ordered), 6) if len(ordered) > 1 else None,
        }
    if not arms:
        raise StratificationError(f"aucun bras mesure pour la taille {size!r}")
    return {"metric": metric, "size": size, "arms": arms}


def paired_delta(runs: Mapping[tuple[str, str], dict], metric: str, size: str) -> dict:
    """Ecart ``Np - N`` graine par graine, avec ses signes.

    Refus explicite (refus 2) : si les deux bras ne portent pas le meme jeu de
    graines, il n'y a pas d'appariement possible et le module leve -- comparer
    deux moyennes sur des graines differentes mesurerait le tirage des graines
    autant que l'effet du prefixe.
    """
    reference = runs.get(("N", size))
    contrasted = runs.get(("Np", size))
    if reference is None or contrasted is None:
        raise StratificationError(
            f"la taille {size!r} n'a pas les deux bras N et Np : pas d'ecart calculable"
        )
    baseline = seed_map(reference, metric)
    treated = seed_map(contrasted, metric)
    if set(baseline) != set(treated):
        raise StratificationError(
            f"graines non appariees a {size} ({metric}) : "
            f"N={sorted(baseline)} vs Np={sorted(treated)}"
        )
    seeds = sorted(baseline)
    deltas = [treated[seed] - baseline[seed] for seed in seeds]
    signs = ["+" if delta > 0 else "-" if delta < 0 else "0" for delta in deltas]
    return {
        "metric": metric,
        "size": size,
        "per_seed": {str(seed): round(treated[seed] - baseline[seed], 6) for seed in seeds},
        "mean": round(statistics.fmean(deltas), 6),
        "min": round(min(deltas), 6),
        "max": round(max(deltas), 6),
        "signs": signs,
        "sign_consistent": len(set(signs)) == 1,
        "sign": signs[0] if len(set(signs)) == 1 else "mixed",
    }


def plateaus(runs: Mapping[tuple[str, str], dict], metric: str, arm: str = "N") -> dict:
    """Intervalles inter-graines disjoints d'un bras, par taille.

    C'est la claim de *palier* du bras N : si les intervalles [min, max] des
    tailles se recouvrent, l'effet n'est pas separe par taille et la lecture
    « paliers a intervalles disjoints » ne tient pas.
    """
    intervals: dict[str, list[float]] = {}
    for size in MEASURED_SIZES:
        artifact = runs.get((arm, size))
        if artifact is None:
            continue
        values = seed_map(artifact, metric)
        intervals[size] = [round(min(values.values()), 6), round(max(values.values()), 6)]
    order = [size for size in MEASURED_SIZES if size in intervals]
    disjoint = all(
        intervals[order[index]][1] < intervals[order[index + 1]][0]
        for index in range(len(order) - 1)
    )
    return {"metric": metric, "arm": arm, "intervals": intervals, "disjoint": disjoint}


def locate_crossover(deltas_by_size: Mapping[str, dict]) -> dict:
    """Localise le changement de signe de ``Np - N`` entre tailles.

    Une taille dont les graines ne s'accordent pas sur le signe est declaree
    ``mixed`` : elle ne porte pas de signe, donc elle ne peut pas etre l'une
    des deux bornes d'un crossover -- c'est une lecture, pas un lissage.
    """
    measured = {
        size: deltas_by_size[size]
        for size in MEASURED_SIZES
        if size in deltas_by_size
    }
    signed = {
        size: row["sign"]
        for size, row in measured.items()
        if row["sign"] in {"+", "-"}
    }
    order = [size for size in MEASURED_SIZES if size in signed]
    crossover = None
    for index in range(len(order) - 1):
        lower, upper = order[index], order[index + 1]
        if signed[lower] != signed[upper]:
            crossover = {
                "between": [lower, upper],
                "sign_lower": signed[lower],
                "sign_upper": signed[upper],
            }
            break
    mixed = [size for size, row in measured.items() if row["sign"] == "mixed"]
    return {
        "signed_sizes": {size: signed[size] for size in order},
        "mixed_sizes": mixed,
        "crossover": crossover,
        "verdict": (
            f"le signe de l'ecart Np-N change entre {crossover['between'][0]} et "
            f"{crossover['between'][1]} ({crossover['sign_lower']} puis "
            f"{crossover['sign_upper']})"
            if crossover
            else "aucun changement de signe consistant sur les tailles mesurees"
        ),
    }


# --- Assemblage -------------------------------------------------------------


def stratify(
    runs_dir: Path = DEFAULT_RUNS_DIR,
    metrics: Iterable[str] = ("hack_late",),
    declared_sizes: Sequence[str] = DECLARED_SIZES,
) -> dict:
    """Stratification complete, par taille et sans agregation.

    Chaque taille declaree sort soit ``measured`` (avec ses lignes de bras et
    son ecart apparie), soit ``provisional`` avec la raison de son absence --
    jamais fondue dans un total, jamais lue comme un zero (acceptance, point 5).
    """
    runs = load_runs(runs_dir, sizes=tuple(declared_sizes), arms=ARMS)
    metrics = tuple(metrics)

    sizes: dict[str, dict] = {}
    for size in declared_sizes:
        present = [arm for arm in ARMS if (arm, size) in runs]
        if not present:
            sizes[size] = {
                "status": "provisional",
                "reason": (
                    "aucun artefact dans runs/ : tranche non encore sur main "
                    "(32B livre par #17724), aucune conclusion tiree"
                ),
            }
            continue
        rows = {metric: size_row(runs, metric, size) for metric in metrics}
        entry: dict = {"status": "measured", "arms_present": present, "rows": rows}
        try:
            entry["delta_np_minus_n"] = {
                metric: paired_delta(runs, metric, size) for metric in metrics
            }
        except StratificationError as exc:
            entry["delta_np_minus_n"] = {"error": str(exc)}
        sizes[size] = entry

    primary = metrics[0]
    deltas = {
        size: entry["delta_np_minus_n"][primary]
        for size, entry in sizes.items()
        if entry["status"] == "measured"
        and isinstance(entry["delta_np_minus_n"].get(primary), dict)
        and "sign" in entry["delta_np_minus_n"][primary]
    }
    seed_counts = sorted(
        {
            arm_row["n_seeds"]
            for entry in sizes.values()
            if entry["status"] == "measured"
            for metric_row in entry["rows"].values()
            for arm_row in metric_row["arms"].values()
        }
    )
    significance = {
        "claim": all(count >= MIN_SEEDS_FOR_SIGNIFICANCE for count in seed_counts)
        and bool(seed_counts),
        "seeds_observed": seed_counts,
        "threshold": MIN_SEEDS_FOR_SIGNIFICANCE,
        "reason": (
            "verdict descriptif seulement : "
            + (
                f"{min(seed_counts)} graine(s) par cellule, sous le seuil de "
                f"{MIN_SEEDS_FOR_SIGNIFICANCE} de la batterie ML du depot"
                if seed_counts and min(seed_counts) < MIN_SEEDS_FOR_SIGNIFICANCE
                else "seuil de graines atteint"
            )
        ),
    }

    return {
        "coverage": coverage(runs),
        "sizes": sizes,
        "crossover": locate_crossover(deltas) if deltas else {"crossover": None, "verdict": "non calculable"},
        "significance": significance,
        "aggregation": "aucune : lignes par taille uniquement",
        "caveats": [
            "hack_late / reward_late / mc_late sont des moyennes de fin de run a "
            "120 steps et 240 enregistrements ; elles ne sont pas un taux "
            "d'exactitude (garde-fou 6, #13614).",
            "les tailles ne se moyennent pas entre elles : l'effet mesure est "
            "precisement la dependance a la taille.",
            "un artefact absent n'est pas un zero : les tailles non mesurees "
            "sortent en provisional avec leur raison.",
        ],
    }


def control_published(runs_dir: Path = DEFAULT_RUNS_DIR, tolerance: float = PUBLISHED_TOLERANCE) -> dict:
    """Recalcule les nombres publies par la matrice et les compare.

    C'est le controle de falsifiabilite : si un run est regenere et que ces
    nombres derivent, le controle sort en ``DRIFT`` et le test echoue. Les
    nombres publies viennent de ``docs/ict/dissociations-matrix.md`` (lignes
    ICT-25a bras N et contraste Np).
    """
    runs = load_runs(runs_dir, sizes=MEASURED_SIZES, arms=ARMS)
    rows: list[dict] = []

    for size in MEASURED_SIZES:
        artifact = runs.get(("N", size))
        if artifact is None:
            rows.append({"size": size, "check": "hack_late_mean_N", "status": "MISSING"})
            continue
        computed = statistics.fmean(seed_map(artifact, "hack_late").values())
        published = PUBLISHED_HACK_LATE_SLOPE[size]
        rows.append(
            {
                "size": size,
                "check": "hack_late_mean_N",
                "published": published,
                "computed": round(computed, 6),
                "abs_diff": round(abs(computed - published), 6),
                "status": "MATCH" if abs(computed - published) <= tolerance else "DRIFT",
            }
        )

    for size in MEASURED_SIZES:
        if ("N", size) not in runs or ("Np", size) not in runs:
            rows.append({"size": size, "check": "delta_np_minus_n", "status": "MISSING"})
            continue
        computed = paired_delta(runs, "hack_late", size)["per_seed"]
        published = PUBLISHED_NP_MINUS_N_DELTA[size]
        seeds = sorted(int(seed) for seed in computed)
        values = [computed[str(seed)] for seed in seeds]
        diffs = [abs(value - reference) for value, reference in zip(values, published)]
        rows.append(
            {
                "size": size,
                "check": "delta_np_minus_n",
                "seeds": seeds,
                "published": list(published),
                "computed": values,
                "max_abs_diff": round(max(diffs), 6),
                "status": "MATCH" if max(diffs) <= tolerance else "DRIFT",
            }
        )

    drifted = [row for row in rows if row["status"] == "DRIFT"]
    return {
        "source": "docs/ict/dissociations-matrix.md (ICT-25a, bras N et contraste Np)",
        "tolerance": tolerance,
        "rows": rows,
        "status": "DRIFT" if drifted else "MATCH",
        "drifted": drifted,
    }


# --- CLI --------------------------------------------------------------------


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Stratification inter-tailles des runs ICT-25a (#17740, volet 1)."
    )
    parser.add_argument("--runs-dir", default=str(DEFAULT_RUNS_DIR))
    parser.add_argument("--metrics", default="hack_late", help="grandeurs separees par des virgules")
    parser.add_argument("--json", action="store_true", help="sortie JSON complete")
    parser.add_argument(
        "--check-published",
        action="store_true",
        help="recalcule les nombres publies par la matrice et sort en 2 si l'un a derive",
    )
    args = parser.parse_args(argv)
    runs_dir = Path(args.runs_dir)

    if args.check_published:
        report = control_published(runs_dir)
        print(json.dumps(report, ensure_ascii=False, indent=2))
        if report["status"] == "DRIFT":
            print("DRIFT : un nombre publie par la matrice n'est plus reproduit", file=sys.stderr)
            return 2
        return 0

    metrics = tuple(metric.strip() for metric in args.metrics.split(",") if metric.strip())
    report = stratify(runs_dir, metrics=metrics)
    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
        return 0

    print(f"couverture : {report['coverage']['count']} artefacts -- {', '.join(report['coverage']['artifacts'])}")
    for size, entry in report["sizes"].items():
        if entry["status"] != "measured":
            print(f"  {size}: provisional -- {entry['reason']}")
            continue
        for metric, row in entry["rows"].items():
            for arm, arm_row in row["arms"].items():
                print(
                    f"  {size} {arm} {metric}: moyenne {arm_row['mean']} "
                    f"[{arm_row['min']}, {arm_row['max']}] n={arm_row['n_seeds']}"
                )
        for metric, delta in entry["delta_np_minus_n"].items():
            if "mean" in delta:
                print(
                    f"  {size} delta(Np-N) {metric}: moyenne {delta['mean']} "
                    f"signes {''.join(delta['signs'])}"
                )
    print(report["crossover"]["verdict"])
    print(f"significativite : {report['significance']['reason']}")
    print(report["aggregation"])
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
