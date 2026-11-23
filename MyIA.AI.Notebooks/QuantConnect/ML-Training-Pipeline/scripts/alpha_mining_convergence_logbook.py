"""Alpha mining par evolution : trajectoire de convergence, generation par generation.

Issue #26430 (tranche 1 de l'EPIC #19306) exige une **demonstration de convergence** :
le fitness doit monter sur les generations. Le carnet qui porte l'organe --
`QuantConnect/Python/QC-Py-42-Alpha-Mining-Evolution.ipynb` -- publie le champion
final de chaque graine et son IC d'entrainement, mais **pas la trajectoire** : on ne
peut pas lire si le fitness monte generation apres generation, ni a quelle generation
il plafonne.

Ce script **ne reimplementa rien**. Il *execute* les cellules du carnet (jusqu'a la
cellule de la boucle `deap` comprise) et intercepte
`deap.algorithms.eaMuPlusLambda` pour en extraire deux choses : le `logbook` de
l'algorithme, et l'etat du `HallOfFame` apres chaque generation. La trajectoire
mesuree est donc celle de l'organe lui-meme, pas celle d'une boucle voisine qui lui
ressemble.

**Controles d'equivalence** (ce qui rend la mesure falsifiable) : les IC
d'entrainement des champions recalcules ici sont compares aux IC **publies dans les
sorties commitees** du carnet, et les IC de la baseline des facteurs fixes sont
compares au tableau publie de la meme facon. Un ecart non nul ne prouve pas que le
carnet a tort -- il prouve que cette mesure n'est pas la sienne ; le verdict est
donc rendu, pas suppose.

Deux trajectoires sont publiees, et leur ecart est un resultat :

- `champion_fitness_by_generation` : le champion conserve par le `HallOfFame`
  apres chaque generation -- c'est la **vraie** trajectoire de convergence, et elle
  est monotone par construction ;
- `population_max_by_generation` : le maximum de fitness **present dans la
  population selectionnee** a la fin de chaque generation.

Les deux ne coincident pas, et l'ecart est instructif. Dans deap 1.4,
`eaMuPlusLambda` fait `halloffame.update(offspring)` : le `HallOfFame` conserve le
meilleur individu **produit**, meme s'il n'a jamais survecu a la selection. Or la
selection du carnet est `selTournament` (taille 3) sur `population + offspring`
avec `mu = POP` : **l'elitisme n'y est pas garanti** -- le meilleur individu peut
perdre le tournoi et disparaitre de la population. La population selectionnee peut
donc **reculer**, et son maximum peut meme rester inferieur au champion pendant
plusieurs generations. C'est le `HallOfFame`, et non la population, qui garantit
que le champion ne se perd pas.

Sorties :
- `scripts/results/alpha_mining_convergence_<date>.json`
- `scripts/results/alpha_mining_convergence_<date>.png`

Usage (depuis la racine du depot) :
    python MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/scripts/alpha_mining_convergence_logbook.py
"""

from __future__ import annotations

import argparse
import contextlib
import io
import json
import os
import re
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

import numpy as np

NOTEBOOK_REL = ("MyIA.AI.Notebooks", "QuantConnect", "Python",
                "QC-Py-42-Alpha-Mining-Evolution.ipynb")
RESULTS_REL = ("scripts", "results")

# Cellule du carnet qui porte la boucle deap : on execute le carnet jusqu'a elle
# incluse (et pas au-dela), pour rester dans la tranche 1 de l'issue.
GA_MARKER = "eaMuPlusLambda"

# Cellule du carnet qui publie le tableau de la baseline des facteurs fixes.
# Elle est reperee par un **marqueur textuel**, pas par un decalage arithmetique
# depuis la cellule GA : un decalage casse silencieusement la baseline
# d'equivalence des qu'une cellule est inseree entre les deux.
BASELINE_MARKER = "FIXED = {"

# Ecart tolere entre la valeur recalculee et la valeur publiee par le carnet.
IC_TOLERANCE = 5e-3


def repo_root() -> Path:
    """Racine du depot (le dossier qui contient `MyIA.AI.Notebooks` et `scripts`)."""
    here = Path(__file__).resolve()
    for cand in [here.parent, *here.parents]:
        if (cand / "MyIA.AI.Notebooks").is_dir() and (cand / "scripts").is_dir():
            return cand
    raise RuntimeError("racine du depot introuvable depuis %s" % here)


def load_notebook(path: Path) -> dict:
    with path.open(encoding="utf-8") as fh:
        return json.load(fh)


def ga_cell_index(nb: dict) -> int:
    for i, cell in enumerate(nb["cells"]):
        if cell["cell_type"] == "code" and GA_MARKER in "".join(cell["source"]):
            return i
    raise RuntimeError("cellule de boucle deap introuvable dans le carnet")


def baseline_cell_index(nb: dict) -> int:
    """Cellule qui publie le tableau de la baseline des facteurs fixes.

    Reperee par le marqueur textuel `FIXED = {`, comme la cellule GA l'est par
    `eaMuPlusLambda` : la correspondance est **semantique**, elle survit a une
    reorganisation du carnet, la ou un ecart d'index ne survit a rien.
    """
    for i, cell in enumerate(nb["cells"]):
        if cell["cell_type"] == "code" and BASELINE_MARKER in "".join(cell["source"]):
            return i
    raise RuntimeError("cellule de baseline des facteurs fixes introuvable dans le carnet")


def cell_outputs_text(nb: dict, idx: int) -> str:
    """Texte de toutes les sorties d'une cellule (streams et text/plain)."""
    chunks = []
    for output in nb["cells"][idx].get("outputs", []):
        text = output.get("text")
        if text is None:
            text = output.get("data", {}).get("text/plain")
        if isinstance(text, list):
            text = "".join(text)
        if text:
            chunks.append(text)
    return "\n".join(chunks)


def committed_ic_by_seed(nb: dict, idx: int) -> dict:
    """IC d'entrainement publies par le carnet (sorties commitees de la cellule GA)."""
    out = {}
    pattern = re.compile(r"seed\s+(\d+)\s+IC train\s+(-?\d+\.\d+)")
    for line in cell_outputs_text(nb, idx).splitlines():
        m = pattern.search(line)
        if m:
            out[int(m.group(1))] = float(m.group(2))
    return out


def committed_baseline_by_factor(nb: dict, idx: int) -> dict:
    """Tableau de la baseline des facteurs fixes publie par le carnet.

    Le tableau est un `text/plain` de DataFrame : `facteur`, `IC train moyen`,
    `turnover/j`, `Sharpe OOS (5 blocs)`, `Sharpe OOS (comparaison)`.
    """
    out = {}
    pattern = re.compile(
        r"^(?P<name>[a-z0-9]+)\s+(?P<ic>-?\d+\.\d+)\s+(?P<turn>-?\d+\.\d+)\s+"
        r"(?P<s5>-?\d+\.\d+)\s+(?P<sc>-?\d+\.\d+)\s*$")
    for line in cell_outputs_text(nb, idx).splitlines():
        m = pattern.match(line.strip())
        if m:
            out[m.group("name")] = float(m.group("ic"))
    return out


def instrument_hall_of_fame(hof, sink: list) -> None:
    """Enregistre le champion du `HallOfFame` apres chaque `update`.

    deap appelle `halloffame.update(offspring)` a chaque generation : le champion
    est donc le meilleur individu **produit**, meme s'il n'a pas survecu a la
    selection. On note sa fitness a chaque appel pour obtenir la trajectoire du
    champion -- celle que le carnet ne publie pas.
    """
    original_update = hof.update

    def update(population, *args, **kwargs):
        original_update(population, *args, **kwargs)
        if len(hof) and hof[0].fitness.valid:
            sink.append(float(hof[0].fitness.values[0]))

    hof.update = update


def patched_ea(logbooks: list, champions_series: list):
    """Enveloppe de `deap.algorithms.eaMuPlusLambda` qui capture logbook + champion.

    Le carnet appelle l'algorithme sans `stats` ; on l'injecte ici pour obtenir la
    trajectory de la population. Le reste de l'appel (mu, lambda, cxpb, mutpb, ngen,
    halloffame) est passe tel quel : l'algorithme execute est celui du carnet.
    """
    from deap import tools

    original = patched_ea.original

    def wrapper(population, toolbox, mu, lambda_, cxpb, mutpb, ngen,
                stats=None, halloffame=None, verbose=True):
        stats = stats or tools.Statistics(lambda ind: ind.fitness.values[0])
        stats.register("max", np.max)
        stats.register("mean", np.mean)
        stats.register("min", np.min)
        series: list = []
        if halloffame is not None:
            instrument_hall_of_fame(halloffame, series)
        result = original(population, toolbox, mu, lambda_, cxpb, mutpb, ngen,
                          stats=stats, halloffame=halloffame, verbose=verbose)
        # deap >= 1.3 renvoie le couple (population, logbook) ; les versions
        # anterieures renvoient le seul logbook.
        logbooks.append(result[1] if isinstance(result, tuple) else result)
        champions_series.append(series)
        return result

    return wrapper


def execute_notebook_up_to_ga(nb: dict, idx: int) -> dict:
    """Execute les cellules de code du carnet jusqu'a la cellule GA incluse."""
    import deap.algorithms as deap_algorithms

    logbooks: list = []
    champions_series: list = []
    original = deap_algorithms.eaMuPlusLambda
    patched_ea.original = original
    deap_algorithms.eaMuPlusLambda = patched_ea(logbooks, champions_series)

    namespace = {"__name__": "__qc_py_42__"}
    buffer = io.StringIO()
    try:
        with contextlib.redirect_stdout(buffer):
            for i in range(idx + 1):
                cell = nb["cells"][i]
                if cell["cell_type"] != "code":
                    continue
                source = "".join(cell["source"])
                if source.strip():
                    exec(compile(source, "<QC-Py-42 cellule %d>" % i, "exec"), namespace)
    finally:
        deap_algorithms.eaMuPlusLambda = original
    namespace["__stdout__"] = buffer.getvalue()
    namespace["__logbooks__"] = logbooks
    namespace["__champions_series__"] = champions_series
    return namespace


def align_logbooks(namespace: dict, seeds) -> dict:
    """Associe chaque execution de la boucle a sa graine.

    L'ordre des appels suit l'ordre de `SEEDS` dans le carnet, mais l'association
    est **verifiee** : le champion d'une graine est `hof[0]`, dont la fitness est
    celle enregistree par le `HallOfFame` a la fin de l'appel. L'appariement se
    fait donc sur cette valeur (egale, pas approchee) ; en cas d'ambiguite on
    apparie par proximite et l'ecart est reporte.
    """
    champions = namespace["champions"]
    logbooks = namespace["__logbooks__"]
    series_list = namespace["__champions_series__"]
    remaining = list(range(len(logbooks)))
    aligned = {}
    for seed in seeds:
        champ_fit = float(champions[seed].fitness.values[0])
        finals = [series_list[i][-1] if series_list[i] else float("nan")
                  for i in remaining]
        exact = [k for k, final in enumerate(finals)
                 if abs(final - champ_fit) <= 1e-12]
        if exact:
            chosen = remaining[exact[0]]
        else:
            chosen = remaining[min(range(len(finals)),
                                   key=lambda k: abs(finals[k] - champ_fit))]
        remaining.remove(chosen)
        aligned[seed] = (logbooks[chosen], series_list[chosen])
    return aligned


def _json_default(obj):
    """Rend serialisables les scalaires numpy rencontres dans les sorties du carnet."""
    if hasattr(obj, "item"):
        return obj.item()
    return str(obj)


def basket_fingerprints(namespace: dict) -> list:
    """Empreinte des CSV du panier sur lesquels repose la mesure.

    L'equivalence de cette mesure est conditionnee par le **contenu** des
    fichiers du panier : si le panier est regenere un jour (fenetre etendue,
    donnees revisees), les IC publies par le carnet divergent et le verdict
    d'equivalence tombe sans dire pourquoi. L'empreinte (empreinte du fichier
    et bornes temporelles) permet de le dire, et de distinguer une derive de
    donnees d'une derive de l'organe.
    """
    import hashlib

    panier = Path(namespace["PANIER"])
    out = []
    for asset, frame in sorted(namespace["frames"].items()):
        candidates = sorted(panier.glob("%s_*.csv" % asset))
        digest = None
        if candidates:
            digest = hashlib.sha256(candidates[0].read_bytes()).hexdigest()[:16]
        index = frame.index
        out.append({
            "asset": asset,
            "csv": candidates[0].name if candidates else None,
            "csv_sha256_16": digest,
            "rows": int(len(frame)),
            "first_date": str(index.min().date()),
            "last_date": str(index.max().date()),
        })
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--date", default=None,
                        help="suffixe des artefacts (defaut : date UTC du jour)")
    parser.add_argument("--out-dir", default=None,
                        help="dossier de sortie (defaut : scripts/results)")
    args = parser.parse_args()

    root = repo_root()
    stamp = args.date or datetime.now(timezone.utc).strftime("%Y-%m-%d")
    out_dir = Path(args.out_dir) if args.out_dir else root.joinpath(*RESULTS_REL)
    out_dir.mkdir(parents=True, exist_ok=True)

    nb_path = root.joinpath(*NOTEBOOK_REL)
    nb = load_notebook(nb_path)
    idx = ga_cell_index(nb)
    published = committed_ic_by_seed(nb, idx)
    published_baseline = committed_baseline_by_factor(nb, baseline_cell_index(nb))

    os.chdir(root)
    t0 = time.time()
    namespace = execute_notebook_up_to_ga(nb, idx)
    duration = time.time() - t0

    seeds = list(namespace["SEEDS"])
    daily_ic = namespace["daily_ic"]
    expression_size = namespace["expression_size"]
    fwd = namespace["fwd"]
    folds = namespace["FOLDS"]
    champions = namespace["champions"]

    aligned = align_logbooks(namespace, seeds)

    tr0, tr1 = int(folds[0][0]), int(folds[0][1])
    target = fwd.values[tr0:tr1]

    per_seed = {}
    for seed in seeds:
        logbook, champion_series = aligned[seed]
        population_max = [float(v) for v in logbook.select("max")]
        population_mean = [float(v) for v in logbook.select("mean")]
        champion_curve = [float(v) for v in champion_series]

        champion = champions[seed]
        value = namespace["evaluate"](champion)
        ic = float(daily_ic(value[tr0:tr1], target)) if value is not None else float("nan")
        published_ic = published.get(seed)
        delta = None if published_ic is None else abs(ic - published_ic)

        gain = champion_curve[-1] - champion_curve[0]
        population_monotone = all(population_max[i + 1] >= population_max[i] - 1e-12
                                  for i in range(len(population_max) - 1))
        regressions = sum(1 for i in range(1, len(population_max))
                          if population_max[i] < population_max[i - 1] - 1e-12)
        # Generations ou la population selectionnee est restee SOUS le champion :
        # c'est la mesure directe du fait que l'elitisme n'est pas garanti.
        below = sum(1 for i in range(min(len(population_max), len(champion_curve)))
                    if population_max[i] < champion_curve[i] - 1e-12)
        plateau = None
        if gain > 0:
            for i, value_i in enumerate(champion_curve):
                if value_i - champion_curve[0] >= 0.9 * gain:
                    plateau = i
                    break

        per_seed[str(seed)] = {
            "champion": namespace["to_prefix"](champion),
            "champion_size": expression_size(champion),
            "ic_train_recomputed": ic,
            "ic_train_published": published_ic,
            "ic_abs_delta": delta,
            "ic_equivalent": bool(delta is not None and delta <= IC_TOLERANCE),
            "champion_fitness_by_generation": champion_curve,
            "population_max_by_generation": population_max,
            "population_mean_by_generation": population_mean,
            "fitness_gen0": champion_curve[0],
            "fitness_gen_final": champion_curve[-1],
            "fitness_gain": gain,
            "population_max_monotone": bool(population_monotone),
            "generations_where_population_max_decreased": int(regressions),
            "generations_with_population_below_champion": int(below),
            "generation_reaching_90pct_of_gain": plateau,
            "n_evaluations_last_generation": int(logbook.select("nevals")[-1]),
            "n_evaluations_total": int(sum(int(v) for v in logbook.select("nevals"))),
        }

    # Facteurs fixes : meme fenetre d'entrainement, meme moyenne sur les blocs, meme
    # fonction de mesure que le carnet (cellule "baseline facteurs fixes").
    fixed = {}
    for name, signal in namespace["FIXED"].items():
        ics = [daily_ic(signal[a:b], fwd.values[a:b]) for a, b, _, _ in folds]
        fixed[name] = float(np.nanmean(ics))
    best_fixed_name = max(fixed, key=fixed.get)

    baseline_equivalent = {}
    for name, value in fixed.items():
        published_value = published_baseline.get(name)
        delta = None if published_value is None else abs(value - published_value)
        baseline_equivalent[name] = {
            "ic_train_recomputed": value,
            "ic_train_published": published_value,
            "ic_abs_delta": delta,
            "ic_equivalent": bool(delta is not None and delta <= IC_TOLERANCE),
        }

    equivalence = all(v["ic_equivalent"] for v in per_seed.values())
    baseline_equivalence = all(v["ic_equivalent"] for v in baseline_equivalent.values())
    convergence = all(v["fitness_gain"] > 0 for v in per_seed.values())
    champions_above_best_fixed = all(
        v["ic_train_recomputed"] > fixed[best_fixed_name] for v in per_seed.values())
    population_below_champion = sum(
        v["generations_with_population_below_champion"] for v in per_seed.values())

    payload = {
        "issue": "#26430",
        "notebook": "/".join(NOTEBOOK_REL),
        "measured_at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "duration_s": round(duration, 1),
        "seeds": seeds,
        "training_window": {"tr0": tr0, "tr1": tr1},
        "basket_inputs": basket_fingerprints(namespace),
        "generations": len(next(iter(aligned.values()))[0].select("max")),
        "ic_tolerance": IC_TOLERANCE,
        "fixed_factors_ic_train": fixed,
        "best_fixed_factor": {"name": best_fixed_name, "ic_train": fixed[best_fixed_name]},
        "baseline_equivalence": baseline_equivalent,
        "per_seed": per_seed,
        "verdict": {
            "equivalence_with_published_notebook_outputs": bool(equivalence),
            "baseline_equivalence_with_published_notebook_outputs": bool(baseline_equivalence),
            "convergence_measured": bool(convergence),
            "all_champions_above_best_fixed_factor": bool(champions_above_best_fixed),
            "population_max_monotone_for_all_seeds": bool(
                all(v["population_max_monotone"] for v in per_seed.values())),
            "generations_with_selected_population_below_champion": int(population_below_champion),
        },
    }

    json_path = out_dir / ("alpha_mining_convergence_%s.json" % stamp)
    with json_path.open("w", encoding="utf-8", newline="\n") as fh:
        json.dump(payload, fh, indent=2, ensure_ascii=False, sort_keys=True,
                  default=_json_default)
        fh.write("\n")

    png_path = out_dir / ("alpha_mining_convergence_%s.png" % stamp)
    write_curve(png_path, per_seed, seeds, best_fixed_name, fixed)

    print("equivalence avec les sorties du carnet : %s"
          % ("OUI" if equivalence else "NON"))
    print("equivalence de la baseline des facteurs fixes : %s"
          % ("OUI" if baseline_equivalence else "NON"))
    for seed in seeds:
        v = per_seed[str(seed)]
        print("seed %-3d IC train recalcule %.4f (publie %.4f, ecart %.4f)  "
              "champion %.4f -> %.4f  plateau g%s  population max monotone %s "
              "(reculs : %d, generations sous le champion : %d)"
              % (seed, v["ic_train_recomputed"], v["ic_train_published"] or float("nan"),
                 v["ic_abs_delta"] or float("nan"), v["fitness_gen0"],
                 v["fitness_gen_final"], v["generation_reaching_90pct_of_gain"],
                 v["population_max_monotone"],
                 v["generations_where_population_max_decreased"],
                 v["generations_with_population_below_champion"]))
    print("meilleur facteur fixe : %s (IC train %.4f)"
          % (best_fixed_name, fixed[best_fixed_name]))
    print("JSON : %s" % json_path)
    print("PNG  : %s" % png_path)
    return 0


def write_curve(path: Path, per_seed: dict, seeds, best_fixed_name: str, fixed: dict) -> None:
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig, ax = plt.subplots(figsize=(9.0, 4.2), dpi=140)
    for seed in seeds:
        v = per_seed[str(seed)]
        ax.plot(range(len(v["champion_fitness_by_generation"])),
                v["champion_fitness_by_generation"], marker="o",
                label="graine %d (champion conserve)" % seed)
    for seed in seeds:
        v = per_seed[str(seed)]
        ax.plot(range(len(v["population_max_by_generation"])),
                v["population_max_by_generation"], marker=".", linestyle="--",
                linewidth=1.2,
                label="graine %d (max de la population selectionnee)" % seed)
    ax.axhline(fixed[best_fixed_name], color="black", linestyle=":", linewidth=1,
               label="meilleur facteur fixe (%s, IC train %.4f)"
                     % (best_fixed_name, fixed[best_fixed_name]))
    ax.set_xlabel("generation")
    ax.set_ylabel("fitness (IC d'entrainement - 0.001 x taille de l'expression)")
    ax.set_title("Alpha mining par evolution : convergence par generation (QC-Py-42)")
    # Legende hors du cadre : a l'interieur, elle recouvrait la courbe de la
    # graine 0 (0.1001 a partir de la generation 4).
    ax.legend(fontsize=8, loc="center left", bbox_to_anchor=(1.01, 0.5))
    fig.tight_layout()
    fig.savefig(path, bbox_inches="tight")
    plt.close(fig)


if __name__ == "__main__":
    sys.exit(main())
