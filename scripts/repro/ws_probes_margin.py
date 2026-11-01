"""Marge de decision de la sonde WS-00c : le chiffre cite peut-il bouger d'un item ?

Motivation mesuree. `scripts/repro/ws_probes_repro.py` rend, pour la sonde WS-00c
(test translate), `0.4350` sur le siege `po-2024` et `0.4300` sur `po-2025`, sous
**la meme** version de scikit-learn (1.8.0) et le meme Python (3.13.14). L'ecart
vaut un item sur 200. Ce script repond a une question, et a une seule :

    quelle amplitude de perturbation faut-il pour deplacer la valeur d'un item ?

La reponse n'est pas une opinion. La classe predite d'un item ne change que si son
ecart `score(top1) - score(top2)` traverse zero. Le plus petit ecart observe sur le
jeu de test est donc l'amplitude **minimale** qu'un mecanisme doit atteindre pour
changer le compte. Deux consequences, mesurees separement :

1. `--observed` compare cette amplitude au bruit d'arrondi float64 (~1e-16 relatif).
   Si la perturbation requise vaut 1e-2, l'ecart entre sieges n'est pas un effet
   d'ordre de reduction : il faut que le modele ajuste differe reellement.
2. `--tol` rejoue l'ajustement a des tolerances de solveur plus serrees. C'est le
   mecanisme candidat : `LogisticRegression` s'arrete sur une norme de gradient
   (`tol`, defaut 1e-4), pas sur un optimum unique, donc deux chemins numeriques
   peuvent s'arreter a des points differents. Le script rapporte, pour chaque
   tolerance, l'exactitude obtenue et **quels items changent de classe** — ce qui
   transforme une inference en mesure.

Usage :

    python scripts/repro/ws_probes_margin.py
    python scripts/repro/ws_probes_margin.py --observed 0.4300
    python scripts/repro/ws_probes_margin.py --observed 0.7900 --observed-state clean
    python scripts/repro/ws_probes_margin.py --observed 0.4300 --strict
    python scripts/repro/ws_probes_margin.py --tol 1e-4 --tol 1e-6 --tol 1e-8
    python scripts/repro/ws_probes_margin.py --out marges.json

Sortie de code : `0` si la mesure aboutit. Avec `--strict` et `--observed`, `1` si
l'ecart observe exige une perturbation superieure a `--noise-bound` (donc s'il ne
s'explique pas par de l'arithmetique), `0` sinon.
"""

from __future__ import annotations

import argparse
import json
import sys

import numpy as np
from sklearn.linear_model import LogisticRegression
from sklearn.model_selection import train_test_split

try:
    from ws_probes_repro import SEED, load_fashion_mnist
except ImportError:  # execution depuis la racine du depot
    from scripts.repro.ws_probes_repro import SEED, load_fashion_mnist

# Amplitude en deca de laquelle on considere un desaccord comme de l'arithmetique :
# une reduction de somme en float64 deplace un score de l'ordre de 1e-16 relatif.
DEFAULT_NOISE_BOUND = 1e-9


def prepare(ims_tr, labs_tr):
    """Le geste de `probe_ws00c`, jusqu'aux matrices d'entrainement et de test.

    Le carnet ne fige rien de plus : 80 images par classe, pad 28 -> 32, split 75/25
    stratifie sur `SEED`. Le decalage alterne selon la parite de `te_i` (indices dans
    le corpus entier), convention propre a WS-00c.
    """
    idx = np.concatenate([np.where(labs_tr == c)[0][:80] for c in range(10)])
    ims, labs = ims_tr[idx], labs_tr[idx]
    ims = np.pad(ims, ((0, 0), (2, 2), (2, 2)), mode="constant")

    tr_i, te_i = train_test_split(
        np.arange(len(ims)), test_size=0.25, stratify=labs, random_state=SEED
    )
    x_tr = ims[tr_i].reshape(len(tr_i), -1)
    x_te = ims[te_i].reshape(len(te_i), -1)
    # Le decalage porte sur l'image paddee, puis on remet a plat : l'ordre des
    # operations compte, `np.roll` sur une matrice deja aplatie n'a pas de sens.
    ims_dec = np.stack(
        [np.roll(ims[i], (2 if i % 2 else -2, -2 if i % 2 else 2), axis=(0, 1)) for i in te_i]
    )
    x_dec = ims_dec.reshape(len(te_i), -1)
    return x_tr, labs[tr_i], x_te, x_dec, labs[te_i]


def fit(x_tr, y_tr, tol=None):
    """L'ajustement du carnet. `tol=None` laisse le defaut de scikit-learn (1e-4).

    Le carnet ne passe ni `random_state` ni `tol` : la sonde doit rester fidele,
    sinon elle mesure autre chose. `tol` n'est la que pour le balayage.
    """
    kwargs = {} if tol is None else {"tol": tol}
    return LogisticRegression(max_iter=3000, C=1.0, **kwargs).fit(x_tr, y_tr)


def predictions(clf, x):
    """Classes predites et marges top1 - top2, dans l'ordre des colonnes de `x`."""
    scores = clf.decision_function(x)
    ranked = np.argsort(scores, axis=1)
    rows = np.arange(len(scores))
    top1, top2 = ranked[:, -1], ranked[:, -2]
    return {
        "pred": clf.classes_[top1],
        "gap": scores[rows, top1] - scores[rows, top2],
        "runner_up_is_true": None,  # rempli par l'appelant qui connait `y`
        "top1": top1,
        "top2": top2,
    }


def measure(clf, x, y):
    """Une mesure complete pour un classifieur ajuste et un jeu de test."""
    out = predictions(clf, x)
    out["accuracy"] = float((out["pred"] == y).mean())
    out["runner_up_is_true"] = clf.classes_[out["top2"]] == y
    out["y"] = y
    out["n_test"] = int(len(y))
    return out


def analyse(state_name, data, other_accuracy=None):
    """Structure de marge d'un etat, et cout en perturbation d'un ecart observe."""
    gap = data["gap"]
    order = np.argsort(gap)
    runner_up_is_true = data["runner_up_is_true"]

    report = {
        "state": state_name,
        "accuracy": round(data["accuracy"], 4),
        "n_test": data["n_test"],
        "min_gap": float(gap.min()),
        "min_gap_index": int(order[0]),
        "min_gap_overall": float(gap[order[0]]),
        "second_min_gap": float(gap[order[1]]),
        "n_below_1e-2": int((gap < 1e-2).sum()),
        "n_below_1e-3": int((gap < 1e-3).sum()),
    }
    # Un item ne peut APPORTER un point que si sa classe reelle est le second score.
    # Un item peut FAIRE PERDRE un point des qu'il est correct : le second score,
    # quel qu'il soit, n'a qu'a depasser le premier.
    wrong = data["pred"] != data["y"]
    winnable = order[runner_up_is_true[order]]
    losable = order[~wrong[order]]
    report["cheapest_gain_margin"] = float(gap[winnable[0]])
    report["cheapest_loss_margin"] = float(gap[losable[0]])
    # Plancher de perturbation : le moins cher des deux sens.
    report["cheapest_perturbation"] = min(
        report["cheapest_gain_margin"], report["cheapest_loss_margin"]
    )

    if other_accuracy is not None:
        delta_items = round((data["accuracy"] - other_accuracy) * data["n_test"])
        report["observed_other"] = round(other_accuracy, 4)
        report["delta_items"] = int(delta_items)
        # `delta_items > 0` veut dire que NOUS sommes plus haut : pour rejoindre
        # l'autre environnement, il faut donc DETRUIRE |delta| items que nous
        # reussissons, donc puiser dans les perdables. Le sens s'inverse quand
        # l'autre environnement est au-dessus : il faut GAGNER des items, et le
        # vivier est celui des items dont la classe reelle est le second score.
        pool = losable if delta_items > 0 else winnable
        k = abs(int(delta_items))
        report["direction"] = "PERDRE" if delta_items > 0 else "GAGNER"
        report["required_perturbation"] = float(gap[pool[k - 1]]) if k and len(pool) >= k else None
    return report


def tol_sweep(x_tr, y_tr, x_te, x_dec, y, tols, reference):
    """Rejoue l'ajustement a plusieurs `tol` et rapporte ce qui bouge.

    Le point de comparaison est l'ajustement par defaut, celui du carnet. Pour
    chaque tolerance : exactitude, iterations, deplacement maximal des coefficients
    contre la reference, et la liste des items dont la classe predite change.
    """
    rows = []
    for tol in tols:
        clf = fit(x_tr, y_tr, tol=tol)
        row = {"tol": tol, "n_iter": int(clf.n_iter_[0])}
        row["dcoef_vs_default"] = float(np.abs(clf.coef_ - reference["coef"]).max())
        for state, x in (("clean", x_te), ("translated", x_dec)):
            data = measure(clf, x, y)
            ref = reference["data"][state]
            moved = np.flatnonzero(data["pred"] != ref["pred"])
            gaps = data["gap"]
            order = np.argsort(gaps)
            wrong = data["pred"] != y
            gainable = order[data["runner_up_is_true"][order]]
            losable = order[~wrong[order]]
            row[state] = {
                "accuracy": round(data["accuracy"], 4),
                "n_iter": row["n_iter"],
                "cheapest_gain_margin": float(gaps[gainable[0]]),
                "cheapest_loss_margin": float(gaps[losable[0]]),
                "changed_items": [int(i) for i in moved],
                "changed_kinds": [
                    "GAIN" if data["pred"][i] == y[i] else "PERTE" for i in moved
                ],
            }
        rows.append(row)
    return rows


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--cache",
        default=None,
        help="racine du cache torchvision (defaut : celui du script frere)",
    )
    parser.add_argument(
        "--source",
        choices=("auto", "torchvision", "openml"),
        default="auto",
        help="source du corpus, meme semantique que ws_probes_repro.py",
    )
    parser.add_argument(
        "--observed",
        type=float,
        default=None,
        help="exactitude observee dans un AUTRE environnement, pour mesurer l'ecart en items",
    )
    parser.add_argument(
        "--observed-state",
        choices=("translated", "clean"),
        default="translated",
        help="etat auquel se rapporte --observed (defaut : translated, celui de l'ecart mesure) ;"
        " l'appliquer a l'autre etat compare deux tests differents et ne veut rien dire",
    )
    parser.add_argument(
        "--noise-bound",
        type=float,
        default=DEFAULT_NOISE_BOUND,
        help="amplitude en deca de laquelle un desaccord est de l'arithmetique",
    )
    parser.add_argument(
        "--tol",
        type=float,
        action="append",
        default=None,
        metavar="TOL",
        help="rejouer l'ajustement a cette tolerance de solveur (repetable)",
    )
    parser.add_argument("--strict", action="store_true", help="sortir 1 si l'ecart n'est pas arithmetique")
    parser.add_argument("--out", default=None, help="chemin d'ecriture du rapport JSON")
    args = parser.parse_args(argv)

    import os

    cache = args.cache or os.path.join(os.path.expanduser("~"), ".cache", "ft00a")
    ims_tr, labs_tr, _ims_te, _labs_te, source_used = load_fashion_mnist(cache, args.source)
    x_tr, y_tr, x_te, x_dec, y = prepare(ims_tr, labs_tr)

    reference = {"coef": None, "data": {}}
    clf = fit(x_tr, y_tr)
    reference["coef"] = clf.coef_
    for state, x in (("clean", x_te), ("translated", x_dec)):
        reference["data"][state] = measure(clf, x, y)

    reports = {
        state: analyse(
            state,
            reference["data"][state],
            args.observed if state == args.observed_state else None,
        )
        for state in ("clean", "translated")
    }

    print(f"source du corpus : {source_used} | graine {SEED}")
    print("ajustement du carnet : LogisticRegression(max_iter=3000, C=1.0), sans random_state ni tol")
    print()
    for state, rep in reports.items():
        print(f"[{state}] exactitude {rep['accuracy']:.4f} sur {rep['n_test']} items")
        print(
            f"  marge minimale {rep['min_gap']:.6e} (item {rep['min_gap_index']})"
            f" | seconde {rep['second_min_gap']:.6e}"
            f" | items < 1e-3 : {rep['n_below_1e-3']} | < 1e-2 : {rep['n_below_1e-2']}"
        )
        print(
            f"  item le moins cher a GAGNER : {rep['cheapest_gain_margin']:.6e}"
            f" | a PERDRE : {rep['cheapest_loss_margin']:.6e}"
        )
        if "required_perturbation" in rep:
            req = rep["required_perturbation"]
            d = rep["delta_items"]
            print(
                f"  ecart observe {rep['observed_other']:.4f} -> il faut"
                f" {rep['direction']} {abs(d)} item(s)"
            )
            if req is None:
                print("  perturbation requise : non atteignable par bascule d'items seuls")
            else:
                ratio = req / args.noise_bound if args.noise_bound else float("inf")
                print(
                    f"  perturbation minimale requise : {req:.6e}"
                    f" ({ratio:.1e} fois le seuil de bruit {args.noise_bound:.0e})"
                )
                verdict = "ARITHMETIQUE" if req <= args.noise_bound else "MODELE-DIFFERE"
                print(f"  verdict : {verdict}")
        print()

    sweep = None
    if args.tol:
        sweep = tol_sweep(x_tr, y_tr, x_te, x_dec, y, args.tol, reference)
        print("balayage de la tolerance de solveur (reference = ajustement du carnet)")
        print(f"{'tol':>8} | {'translated':>10} | {'n_iter':>6} | {'dcoef':>9} | items qui changent")
        print("-" * 78)
        for row in sweep:
            tr = row["translated"]
            moved = ", ".join(
                f"{i}({k})" for i, k in zip(tr["changed_items"], tr["changed_kinds"])
            ) or "aucun"
            print(
                f"{row['tol']:>8.0e} | {tr['accuracy']:>10.4f} | {row['n_iter']:>6d} | "
                f"{row['dcoef_vs_default']:>9.2e} | {moved}"
            )
        print()
        sane = [r for r in sweep if r["translated"]["accuracy"] != reports["translated"]["accuracy"]]
        if sane:
            print(
                "verdict du balayage : SENSIBLE-AU-SOLVEUR — la valeur citee depend de la"
                " tolerance d'arret, pas seulement des donnees."
            )
        else:
            print(
                "verdict du balayage : INSENSIBLE-AU-SOLVEUR — la valeur ne bouge pas sur"
                " cette plage ; chercher ailleurs."
            )
        print()

    verdicts = [
        r.get("required_perturbation") is not None
        and r["required_perturbation"] > args.noise_bound
        for r in reports.values()
    ]
    not_arithmetic = any(verdicts)

    if args.out:
        payload = {
            "script": "scripts/repro/ws_probes_margin.py",
            "seed": SEED,
            "corpus_source": source_used,
            "noise_bound": args.noise_bound,
            "states": reports,
            "tol_sweep": sweep,
            "not_arithmetic": not_arithmetic,
        }
        with open(args.out, "w", encoding="utf-8") as fh:
            json.dump(payload, fh, ensure_ascii=False, indent=2)
        print(f"rapport ecrit : {args.out}")

    if args.strict and args.observed is not None and not_arithmetic:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
