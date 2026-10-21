"""Reproduction hors carnet des sondes de la sous-serie Wavelet Scattering.

Issue de suivi : #21823 (suite de la revue de la PR #21771).

Ce que mesure ce script, et pourquoi il existe
-----------------------------------------------
La revue [NanoClaw] du 2026-10-21 signalait que les valeurs citees par la
sonde de la serie ne sont verifiees qu'a l'interieur du carnet. Deux jeux de
nombres sont en jeu :

* WS-03, cellule 8, temoin « pixels bruts » : **0,780 / 0,311** ;
* WS-00c, §6, sonde « brute, sans graine » : **0,773 / 0,431**, repris dans
  le corps de la PR #21771 (tableau comparatif des deux sondes).

Le script rejoue chaque protocole **hors carnet**, sur le corpus reconstruit
depuis les fichiers IDX du cache local, et tranche deux questions :

1. les valeurs **committes** des carnets sont-elles reproductibles ?
2. la paire publiee **0,773 / 0,431** est-elle reproductible, et par quel
   protocole ?

Un piege de protocole, mesure ici
--------------------------------
Les deux carnets translatent le jeu de test de facon differente, et la
difference est silencieuse :

* WS-00c (cellule 21) itere sur les **index d'origine** (`for i in te_i`) :
  la parite du decalage +-2 px suit l'index de l'image dans le corpus ;
* WS-03 (cellule 2) itere sur `enumerate(X_te)` : la parite suit la
  **position** dans le tableau de test.

Rejouer l'un avec la recette de l'autre decale le test de quelques images et
fait varier le score translate de ~0,015 sans qu'aucune erreur ne soit
visible. Ce script reproduit chaque carnet avec SA recette, et garde les
deux recettes explicites (`translate_by_index` / `translate_by_position`).

Sortie
------
Un agregat JSON (option `--json`) : mesures, ecarts aux valeurs committes,
dispersion du protocole non deterministe, et position de la paire publiee
dans cette dispersion.

Usage :
    python scripts/ml/reproduce_ws_probes.py [--cache DIR] [--json OUT]
                                            [--repeats N] [--no-sweep]

Mesures du 2026-10-21 (numpy 2.2.6, scikit-learn 1.9.1, cache local) :
    A. WS-00c §6 protocole exact    -> 0,790 / 0,425  (committes, reproduit)
    B. WS-03 protocole exact        -> 0,780 / 0,311  (committes, reproduit)
    C. WS-00c §6 sans graine (x40) -> enveloppe [0,755 ; 0,855] x [0,390 ; 0,490]
    D. 16 variantes balayees        -> 0 reproduisant exactement 0,773 / 0,431
"""

from __future__ import annotations

import argparse
import gzip
import json
import struct
import time
from pathlib import Path

import numpy as np
from sklearn.linear_model import LogisticRegression
from sklearn.model_selection import train_test_split
from sklearn.preprocessing import StandardScaler

# ---- constantes des protocoles -------------------------------------------------

SEED = 42
N_PER_CLASS_WS00C = 80          # WS-00c §6 : 80 images par classe
N_TR_WS03, N_TE_WS03 = 150, 75  # WS-03 §1 : 150 / 75 images par classe
PAD_WS00C = 2                   # WS-00c §6 : 28 -> 32 (bord constant)
MAX_ITER, C_REG = 3000, 1.0

# valeurs de reference, avec leur provenance
VALEURS_COMMITTES = {
    "ws00c_pixels": {"propre": 0.790, "translate": 0.425,
                     "source": "WS-00c cellule 21 (sorties committes)"},
    "ws03_pixels": {"propre": 0.780, "translate": 0.311,
                    "source": "WS-03 cellule 8 (sorties committes)"},
}
PAIRE_PUBLIEE = {"propre": 0.773, "translate": 0.431,
                 "source": "corps de la PR #21771, tableau comparatif des deux sondes"}

TOLERANCE = 5e-4   # une valeur affichee a 3 decimales est un multiple de 0,001


# ---- lecture du corpus ---------------------------------------------------------

def _read_idx(path: Path) -> np.ndarray:
    """Lit un fichier IDX (magic 0x00000803 images, 0x00000801 labels)."""
    with gzip.open(path, "rb") as fh:
        magic, = struct.unpack(">I", fh.read(4))
        if magic == 0x00000803:
            n, r, c = struct.unpack(">III", fh.read(12))
            return np.frombuffer(fh.read(), dtype=np.uint8).reshape(n, r, c)
        if magic == 0x00000801:
            n, = struct.unpack(">I", fh.read(4))
            return np.frombuffer(fh.read(n), dtype=np.uint8)
        raise ValueError(f"magic IDX inconnu {magic:#x} dans {path}")


def load_fashion_mnist(raw_dir: Path):
    """Retourne (train_x, train_y, test_x, test_y) en uint8, lus depuis le cache."""
    return (
        _read_idx(raw_dir / "train-images-idx3-ubyte.gz"),
        _read_idx(raw_dir / "train-labels-idx1-ubyte.gz"),
        _read_idx(raw_dir / "t10k-images-idx3-ubyte.gz"),
        _read_idx(raw_dir / "t10k-labels-idx1-ubyte.gz"),
    )


def default_cache_dir() -> Path:
    return Path.home() / ".cache" / "ft00a" / "FashionMNIST" / "raw"


# ---- recettes de translation ----------------------------------------------------

def translate_by_index(ims: np.ndarray, indices: np.ndarray) -> np.ndarray:
    """Recette WS-00c (cellule 21) : la parite du decalage suit l'INDEX d'origine."""
    return np.stack([np.roll(ims[i], (2 if i % 2 else -2, -2 if i % 2 else 2), axis=(0, 1))
                     for i in indices])


def translate_by_position(ims: np.ndarray) -> np.ndarray:
    """Recette WS-03 (cellule 2) : la parite du decalage suit la POSITION."""
    return np.stack([np.roll(x, (2 if i % 2 else -2, -2 if i % 2 else 2), axis=(0, 1))
                     for i, x in enumerate(ims)])


# ---- sondes ---------------------------------------------------------------------

def _probe(F_tr, y_tr, F_te, y_te, F_dec, standardize: bool, random_state):
    """Regression logistique (C=1.0, max_iter=3000) ; retourne (propre, translate, n_iter)."""
    if standardize:
        scaler = StandardScaler().fit(F_tr)
        F_tr, F_te, F_dec = scaler.transform(F_tr), scaler.transform(F_te), scaler.transform(F_dec)
    clf = LogisticRegression(max_iter=MAX_ITER, C=C_REG, random_state=random_state)
    clf.fit(F_tr, y_tr)
    return (float(clf.score(F_te, y_te)), float(clf.score(F_dec, y_te)),
            int(np.max(clf.n_iter_)))


def ws00c_probe(train_x, train_y, split_seed=SEED, selection="first",
                select_seed=SEED, pad=True, standardize=False):
    """WS-00c §6, temoin pixels bruts.

    selection="first" : np.where(labs == c)[0][:80] (le carnet) ;
    selection="rng"   : default_rng(select_seed).choice(..., replace=False).
    split_seed=None   : split non deterministe (« sans graine »).
    """
    ims_all = train_x.astype(np.float64) / 255.0
    labs_all = train_y.astype(np.int64)
    if selection == "first":
        idx = np.concatenate([np.where(labs_all == c)[0][:N_PER_CLASS_WS00C] for c in range(10)])
    else:
        rng = np.random.default_rng(select_seed)
        idx = np.concatenate([rng.choice(np.where(labs_all == c)[0], N_PER_CLASS_WS00C,
                                         replace=False) for c in range(10)])
    ims, labs = ims_all[idx], labs_all[idx]
    if pad:
        ims = np.pad(ims, ((0, 0), (PAD_WS00C, PAD_WS00C), (PAD_WS00C, PAD_WS00C)),
                     mode="constant")
    tr_i, te_i = train_test_split(np.arange(len(ims)), test_size=0.25, stratify=labs,
                                  random_state=split_seed)
    F_tr = ims[tr_i].reshape(len(tr_i), -1)
    F_te = ims[te_i].reshape(len(te_i), -1)
    F_dec = translate_by_index(ims, te_i).reshape(len(te_i), -1)
    return _probe(F_tr, labs[tr_i], F_te, labs[te_i], F_dec, standardize, None)


def ws03_probe(train_x, train_y, test_x, test_y, seed=SEED):
    """WS-03, temoin pixels bruts standardise : 150/classe train, 75/classe test."""
    rng = np.random.default_rng(seed)
    ims_tr_all = train_x.astype(np.float64) / 255.0
    labs_tr_all = train_y.astype(np.int64)
    ims_te_all = test_x.astype(np.float64) / 255.0
    labs_te_all = test_y.astype(np.int64)

    idx_tr = np.concatenate([rng.choice(np.where(labs_tr_all == c)[0], N_TR_WS03,
                                        replace=False) for c in range(10)])
    idx_te = np.concatenate([rng.choice(np.where(labs_te_all == c)[0], N_TE_WS03,
                                        replace=False) for c in range(10)])
    X_tr, y_tr = ims_tr_all[idx_tr], labs_tr_all[idx_tr]
    X_te, y_te = ims_te_all[idx_te], labs_te_all[idx_te]
    F_tr = X_tr.reshape(len(X_tr), -1)
    F_te = X_te.reshape(len(X_te), -1)
    F_dec = translate_by_position(X_te).reshape(len(X_te), -1)
    return _probe(F_tr, y_tr, F_te, y_te, F_dec, standardize=True, random_state=seed)


# ---- etude de reproductibilite de la paire publiee --------------------------------

def sweep_variantes(train_x, train_y):
    """Balaye 16 variantes du protocole WS-00c ; cherche la paire publiee."""
    variantes = []
    for selection in ("first", "rng"):
        for pad in (True, False):
            for standardize in (False, True):
                for split_seed in (SEED, None):
                    variantes.append((selection, split_seed, pad, standardize))
    lignes = []
    for selection, split_seed, pad, standardize in variantes:
        p, t, ni = ws00c_probe(train_x, train_y, split_seed=split_seed, selection=selection,
                                pad=pad, standardize=standardize)
        lignes.append({
            "selection": selection, "split": split_seed, "pad_32": pad,
            "standardise": standardize, "propre": p, "translate": t, "n_iter": ni,
            "ecart_a_la_paire_publiee": round(max(abs(p - PAIRE_PUBLIEE["propre"]),
                                                  abs(t - PAIRE_PUBLIEE["translate"])), 4),
        })
    return lignes


def dispersion_sans_graine(train_x, train_y, repeats: int):
    """Occurrences du protocole exact du carnet, split non deterministe."""
    occ = [ws00c_probe(train_x, train_y, split_seed=None)[:2] for _ in range(repeats)]
    propres = np.array([o[0] for o in occ])
    trans = np.array([o[1] for o in occ])
    return {
        "occurrences": repeats,
        "propre": {"min": float(propres.min()), "max": float(propres.max()),
                   "mediane": float(np.median(propres)),
                   "ecart_type": float(propres.std(ddof=1)),
                   "percentile_de_la_cible": round(100 * float((propres <= PAIRE_PUBLIEE["propre"]).mean()))},
        "translate": {"min": float(trans.min()), "max": float(trans.max()),
                      "mediane": float(np.median(trans)),
                      "ecart_type": float(trans.std(ddof=1)),
                      "percentile_de_la_cible": round(100 * float((trans <= PAIRE_PUBLIEE["translate"]).mean()))},
        "cible_dans_l_enveloppe": bool(propres.min() <= PAIRE_PUBLIEE["propre"] <= propres.max()
                                       and trans.min() <= PAIRE_PUBLIEE["translate"] <= trans.max()),
        "occurrences_exactement_sur_la_paire": int(sum(
            1 for o in occ
            if abs(o[0] - PAIRE_PUBLIEE["propre"]) < TOLERANCE
            and abs(o[1] - PAIRE_PUBLIEE["translate"]) < TOLERANCE
        )),
    }


# ---- main -------------------------------------------------------------------------

def main() -> int:
    ap = argparse.ArgumentParser(description="Reproduction hors carnet des sondes WS.")
    ap.add_argument("--cache", default=None, help="repertoire raw IDX du cache Fashion-MNIST")
    ap.add_argument("--json", default=None, help="fichier de sortie JSON (agregat)")
    ap.add_argument("--repeats", type=int, default=40, help="occurrences du protocole sans graine")
    ap.add_argument("--no-sweep", action="store_true", help="ne pas balayer les variantes")
    args = ap.parse_args()

    import sklearn

    raw = Path(args.cache) if args.cache else default_cache_dir()
    if not (raw / "train-images-idx3-ubyte.gz").exists():
        print(f"cache Fashion-MNIST absent : {raw}", file=__import__("sys").stderr)
        return 2

    t0 = time.perf_counter()
    train_x, train_y, test_x, test_y = load_fashion_mnist(raw)
    print(f"corpus lu depuis {raw} : train {train_x.shape}, test {test_x.shape}")
    print(f"numpy {np.__version__} | scikit-learn {sklearn.__version__}\n")

    res = {
        "environnement": {"numpy": np.__version__, "scikit_learn": sklearn.__version__,
                          "cache": str(raw)},
        "references": {**VALEURS_COMMITTES, "paire_publiee": PAIRE_PUBLIEE},
    }

    a_p, a_t, a_ni = ws00c_probe(train_x, train_y)
    ref = VALEURS_COMMITTES["ws00c_pixels"]
    print("A. WS-00c §6, protocole exact du carnet (graine 42, 80/classe, pad 32)")
    print(f"   test propre {a_p:.3f} | test +-2px {a_t:.3f}   (committes : "
          f"{ref['propre']:.3f} / {ref['translate']:.3f})")
    res["A_ws00c_carnet"] = {"propre": a_p, "translate": a_t, "n_iter": a_ni,
                             "ecart_vs_committes": [round(a_p - ref["propre"], 4),
                                                    round(a_t - ref["translate"], 4)],
                             "reproduit": abs(a_p - ref["propre"]) < TOLERANCE
                                          and abs(a_t - ref["translate"]) < TOLERANCE}

    b_p, b_t, b_ni = ws03_probe(train_x, train_y, test_x, test_y)
    ref = VALEURS_COMMITTES["ws03_pixels"]
    print("\nB. WS-03, pixels bruts standardises (graine 42, 150/75 par classe)")
    print(f"   test propre {b_p:.3f} | test +-2px {b_t:.3f}   (committes : "
          f"{ref['propre']:.3f} / {ref['translate']:.3f})")
    res["B_ws03_carnet"] = {"propre": b_p, "translate": b_t, "n_iter": b_ni,
                            "ecart_vs_committes": [round(b_p - ref["propre"], 4),
                                                   round(b_t - ref["translate"], 4)],
                            "reproduit": abs(b_p - ref["propre"]) < TOLERANCE
                                         and abs(b_t - ref["translate"]) < TOLERANCE}

    disp = dispersion_sans_graine(train_x, train_y, args.repeats)
    print(f"\nC. WS-00c §6, protocole « sans graine » (split non deterministe), "
          f"{args.repeats} occurrences")
    print(f"   test propre : min {disp['propre']['min']:.3f} | max {disp['propre']['max']:.3f} "
          f"| mediane {disp['propre']['mediane']:.3f} | ecart-type {disp['propre']['ecart_type']:.4f}")
    print(f"   test +-2px  : min {disp['translate']['min']:.3f} | max {disp['translate']['max']:.3f} "
          f"| mediane {disp['translate']['mediane']:.3f} | ecart-type {disp['translate']['ecart_type']:.4f}")
    print(f"   paire publiee {PAIRE_PUBLIEE['propre']:.3f} / {PAIRE_PUBLIEE['translate']:.3f} : "
          f"percentile {disp['propre']['percentile_de_la_cible']} / "
          f"{disp['translate']['percentile_de_la_cible']}, "
          f"dans l'enveloppe = {disp['cible_dans_l_enveloppe']}, "
          f"occurrences exactes {disp['occurrences_exactement_sur_la_paire']}/{args.repeats}")
    res["C_ws00c_sans_graine"] = disp

    if not args.no_sweep:
        lignes = sweep_variantes(train_x, train_y)
        exacte = [l for l in lignes if l["ecart_a_la_paire_publiee"] < TOLERANCE]
        proches = sorted(lignes, key=lambda l: l["ecart_a_la_paire_publiee"])[:3]
        print("\nD. balayage de 16 variantes du protocole WS-00c")
        for l in lignes:
            print(f"   selection={l['selection']:>5} split={str(l['split']):>4} "
                  f"pad32={str(l['pad_32']):>5} std={str(l['standardise']):>5} | "
                  f"{l['propre']:.3f} / {l['translate']:.3f} | ecart {l['ecart_a_la_paire_publiee']:.4f}")
        print(f"   variante reproduisant exactement la paire publiee : {len(exacte)}")
        print(f"   plus proches : {[(l['selection'], l['split'], l['pad_32'], l['standardise'], l['propre'], l['translate']) for l in proches]}")
        res["D_balayage_variantes"] = {"variantes": lignes,
                                       "variantes_reproduisant_la_paire": len(exacte)}

    res["duree_s"] = round(time.perf_counter() - t0, 1)
    if args.json:
        Path(args.json).write_text(json.dumps(res, ensure_ascii=False, indent=2), encoding="utf-8")
        print(f"\nagregat ecrit : {args.json}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())