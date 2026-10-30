"""Reproduction hors carnet des sondes de la serie wavelet scattering (WS-00c, WS-03).

Les quatre valeurs citees par la serie sont produites par des cellules de code de
notebook, donc non verifiables hors de leur ordre d'execution. Ce script rejoue les
deux sondes de facon autonome, avec les parametres releves dans les carnets, et
compare le resultat aux valeurs citees.

Sondes reproduites :
  - WS-00c-Scattering-from-scratch.ipynb, cellule 20-21 (§6) : pixels bruts paddes
    32x32, 80 images par classe, split 75/25 stratifie, LogisticRegression
    (max_iter=3000, C=1.0) sans random_state.
  - WS-03-Synthese-Scattering-vs-ResNet.ipynb, cellule 8 : pixels bruts 28x28,
    150 images d'entrainement / 75 de test par classe, StandardScaler ajuste sur
    le train seul, LogisticRegression (max_iter=3000, C=1.0, random_state=42).

Valeurs citees a confirmer : 0.790 / 0.425 (WS-00c) et 0.780 / 0.311 (WS-03).
"""

from __future__ import annotations

import argparse
import json
import os
import platform
import sys

import numpy as np
import sklearn
from sklearn.linear_model import LogisticRegression
from sklearn.model_selection import train_test_split
from sklearn.preprocessing import StandardScaler

SEED = 42

CITED = {
    "WS-00c": {"clean": 0.790, "translated": 0.425},
    "WS-03": {"clean": 0.780, "translated": 0.311},
}


def load_fashion_mnist(cache_root: str, source: str = "auto"):
    """Charge Fashion-MNIST. `auto` suit l'ordre de la cellule WS-00c: torchvision, sinon openml.

    Les deux sources ne rangent pas les images dans le meme ordre. La sonde WS-00c
    selectionne `np.where(labs == c)[0][:80]`: les 80 premieres images de chaque
    classe, donc un sous-ensemble DIFFERENT selon la source. C'est pourquoi la
    source est exposee explicitement au lieu d'etre laissee a un `try/except`.
    """
    if source in ("auto", "torchvision"):
        try:
            from torchvision.datasets import FashionMNIST

            ds_tr = FashionMNIST(cache_root, train=True, download=True)
            ds_te = FashionMNIST(cache_root, train=False, download=True)
            ims_tr = ds_tr.data.numpy().astype(np.float64) / 255.0
            labs_tr = ds_tr.targets.numpy()
            ims_te = ds_te.data.numpy().astype(np.float64) / 255.0
            labs_te = ds_te.targets.numpy()
            return ims_tr, labs_tr, ims_te, labs_te, "torchvision"
        except Exception as exc:  # meme repli que le carnet
            if source == "torchvision":
                raise
            print(f"torchvision indisponible ({exc.__class__.__name__}), repli openml")

    from sklearn.datasets import fetch_openml

    data = fetch_openml("Fashion-MNIST", version=1, as_frame=False)
    ims = data.data.reshape(-1, 28, 28).astype(np.float64) / 255.0
    labs = data.target.astype(int)
    # openml ne distingue pas train/test: on reprend la coupure du carnet,
    # qui n'utilise que la premiere source. Diviser 70000 en 60000/10000
    # garde la sonde WS-03 executable sur cette source.
    return ims[:60000], labs[:60000], ims[60000:], labs[60000:], "openml"


def alternating_shift(images: np.ndarray) -> np.ndarray:
    """Decalage +-2 px alterne, periodique aux bords: la convention de WS-03, parite
    LOCALE (enumerate sur le test). WS-00c alterne selon la parite GLOBALE de te_i
    (indices dans le corpus entier) : meme decalage, index different — voir probe_ws00c."""
    return np.stack(
        [
            np.roll(img, (2 if i % 2 else -2, -2 if i % 2 else 2), axis=(0, 1))
            for i, img in enumerate(images)
        ]
    )


def probe_ws00c(ims_tr, labs_tr):
    """WS-00c §6: pixels bruts, 80/Classe, pad 28->32, split 75/25 stratifie."""
    idx = np.concatenate([np.where(labs_tr == c)[0][:80] for c in range(10)])
    ims, labs = ims_tr[idx], labs_tr[idx]
    ims = np.pad(ims, ((0, 0), (2, 2), (2, 2)), mode="constant")

    tr_i, te_i = train_test_split(
        np.arange(len(ims)), test_size=0.25, stratify=labs, random_state=SEED
    )
    x_tr = ims[tr_i].reshape(len(tr_i), -1)
    x_te = ims[te_i].reshape(len(te_i), -1)

    ims_dec = np.stack(
        [
            np.roll(ims[i], (2 if i % 2 else -2, -2 if i % 2 else 2), axis=(0, 1))
            for i in te_i
        ]
    )
    x_dec = ims_dec.reshape(len(te_i), -1)

    clf = LogisticRegression(max_iter=3000, C=1.0).fit(x_tr, labs[tr_i])
    return {
        "clean": float(clf.score(x_te, labs[te_i])),
        "translated": float(clf.score(x_dec, labs[te_i])),
        "n_train": int(len(tr_i)),
        "n_test": int(len(te_i)),
        "n_features": int(x_tr.shape[1]),
        "random_state": None,
    }


def probe_ws03(ims_tr, labs_tr, ims_te, labs_te):
    """WS-03 cellule 8: pixels bruts 28x28, 150/75 par classe, StandardScaler train seul."""
    rng = np.random.default_rng(SEED)
    n_tr, n_te = 150, 75
    idx_tr = np.concatenate(
        [rng.choice(np.where(labs_tr == c)[0], n_tr, replace=False) for c in range(10)]
    )
    idx_te = np.concatenate(
        [rng.choice(np.where(labs_te == c)[0], n_te, replace=False) for c in range(10)]
    )
    x_tr, y_tr = ims_tr[idx_tr], labs_tr[idx_tr]
    x_te, y_te = ims_te[idx_te], labs_te[idx_te]
    x_dec = alternating_shift(x_te)

    x_tr = x_tr.reshape(len(x_tr), -1)
    x_te = x_te.reshape(len(x_te), -1)
    x_dec = x_dec.reshape(len(x_dec), -1)

    scaler = StandardScaler().fit(x_tr)
    clf = LogisticRegression(max_iter=3000, C=1.0, random_state=SEED).fit(
        scaler.transform(x_tr), y_tr
    )
    return {
        "clean": float(clf.score(scaler.transform(x_te), y_te)),
        "translated": float(clf.score(scaler.transform(x_dec), y_te)),
        "n_train": int(len(x_tr)),
        "n_test": int(len(x_te)),
        "n_features": int(x_tr.shape[1]),
        "random_state": SEED,
    }


def compare(observed: dict, cited: dict, decimals: int = 3) -> dict:
    """Verdict a la precision d'affichage: un ecart arrondi non nul est un ecart."""
    out = {}
    for key in ("clean", "translated"):
        delta = observed[key] - cited[key]
        out[key] = {
            "observed": round(observed[key], 4),
            "cited": cited[key],
            "delta": round(delta, 4),
            "match": abs(delta) < 0.5 * 10 ** (-decimals),
        }
    out["verdict"] = "MATCH" if all(out[k]["match"] for k in ("clean", "translated")) else "MISMATCH"
    return out


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--cache",
        default=os.path.join(os.path.expanduser("~"), ".cache", "ft00a"),
        help="racine du cache torchvision FashionMNIST",
    )
    parser.add_argument("--out", default=None, help="chemin d'ecriture du JSON de resultats")
    parser.add_argument(
        "--source",
        choices=("auto", "torchvision", "openml"),
        default="auto",
        help="source du corpus: auto = torchvision puis repli openml (ordre du carnet WS-00c)",
    )
    args = parser.parse_args(argv)

    ims_tr, labs_tr, ims_te, labs_te, source_used = load_fashion_mnist(
        args.cache, args.source
    )

    results = {}
    for name, probe in (
        ("WS-00c", lambda: probe_ws00c(ims_tr, labs_tr)),
        ("WS-03", lambda: probe_ws03(ims_tr, labs_tr, ims_te, labs_te)),
    ):
        observed = probe()
        results[name] = {"observed": observed, "comparison": compare(observed, CITED[name])}

    report = {
        "script": "scripts/repro/ws_probes_repro.py",
        "seed": SEED,
        "platform": platform.platform(),
        "python": sys.version.split()[0],
        "numpy": np.__version__,
        "scikit_learn": sklearn.__version__,
        "cache_root": args.cache,
        "corpus_source": source_used,
        "probes": results,
    }

    print(
        f"python {report['python']} | numpy {report['numpy']} | scikit-learn {report['scikit_learn']}"
    )
    print(f"graine {SEED} | source {source_used} | cache {args.cache}")
    print()
    print(f"{'sonde':<8} | {'etat':<11} | {'mesure':>7} | {'cite':>7} | {'ecart':>7} | verdict")
    print("-" * 68)
    for name in ("WS-00c", "WS-03"):
        for state in ("clean", "translated"):
            c = results[name]["comparison"][state]
            print(
                f"{name:<8} | {state:<11} | {c['observed']:>7.4f} | {c['cited']:>7.3f} | "
                f"{c['delta']:>+7.4f} | {'ok' if c['match'] else 'ECART'}"
            )

    overall = all(results[n]["comparison"]["verdict"] == "MATCH" for n in results)
    print()
    print(f"VERDICT GLOBAL: {'MATCH' if overall else 'MISMATCH'}")
    report["verdict_global"] = "MATCH" if overall else "MISMATCH"

    if args.out:
        with open(args.out, "w", encoding="utf-8") as fh:
            json.dump(report, fh, ensure_ascii=False, indent=2)
        print(f"rapport ecrit: {args.out}")

    return 0 if overall else 1


if __name__ == "__main__":
    raise SystemExit(main())