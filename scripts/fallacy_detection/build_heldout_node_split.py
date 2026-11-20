#!/usr/bin/env python3
"""Split « nœud tenu à part » : retirer des nœuds de train/val, les garder au test.

Sous-grain de l'EPIC #10355, section 2(c) et section 3 de la revue EPITA du
2026-10-21/22 (commentaire c.6344505010) :

- section 2 : « Aucun facteur n'est tenu à part : les mêmes étiquettes sont
  présentes dans train, val et test. Le gate mesure donc des décors inédits,
  jamais un sophisme inédit. » Proposition (c) : « un nœud tenu à part ».
- section 3 : « le niveau nœud du gate reste non mesurable par construction
  tant que ce filtre s'applique ».

Ce que l'organe mesure, avant de construire quoi que ce soit
------------------------------------------------------------
Sur l'inventaire de paires committé (``data/phase2/{train,val,test}.csv``), la
prémisse du consultant se vérifie exactement : chaque ``node_pk`` du test est
aussi dans le train, donc aucun nœud n'est jamais inédit à l'entraînement. Un
split « nœud tenu à part » se construit donc en **retirant** des nœuds du train
et du val, et en les **laissant** au test : c'est le seul sens dans lequel le
test peut porter un sophisme que le train n'a jamais vu.

Ce que l'organe ne décide pas
-----------------------------
Le choix des nœuds tenus à part est un arbitrage de protocole, pas une
constante d'organe : il est exposé en paramètres (``--holdout-count``,
``--strategy``, ``--seed``, ``--min-test-pairs``) et le rapport publie la
distribution de support qui rend cet arbitrage décidable. L'organe ne tranche
aucun seuil de mesurabilité : il publie les comptes, le gate existant
(``gate_phase3.py``) garde son refus documenté ``node_level.measurable``.

Sorties
-------
- ``--out-dir`` : ``train.csv``/``val.csv``/``test.csv`` filtrés, au format
  octet-pour-octet du builder (mêmes colonnes, UTF-8, LF). **Hors dépôt par
  défaut** : ``train.csv`` est gitignoré par politique d'artefacts, un split
  dérivé l'est aussi.
- ``--report`` : l'agrégat anonymisé (paramètres, SHA-256 des entrées, comptes
  avant/après, distribution de support des nœuds tenus à part, familles par
  nœud et paires de test) — lui seul est citable dans une PR.

Usage :
  python scripts/fallacy_detection/build_heldout_node_split.py --report r.json
  python scripts/fallacy_detection/build_heldout_node_split.py \
      --holdout-count 222 --strategy top-support --out-dir /tmp/phase2-holdout \
      --report /tmp/phase2-holdout/report.json
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import random
import sys
from collections import Counter
from pathlib import Path
from typing import Iterable, Optional

CSV_COLUMNS = [
    "pair_id",
    "split",
    "polarity",
    "node_pk",
    "family",
    "depth",
    "is_leaf",
    "scenario_path",
]

DEFAULT_SPLIT_DIR = (
    Path(__file__).resolve().parents[2]
    / "MyIA.AI.Notebooks"
    / "GenAI"
    / "FallacyDetection"
    / "data"
    / "phase2"
)

SPLITS = ("train", "val", "test")
STRATEGIES = ("top-support", "seeded")


def read_split(path: Path) -> list[dict[str, str]]:
    """Lit un split CSV en dicts, colonnes de CSV_COLUMNS preservees."""
    with path.open(encoding="utf-8", newline="") as fh:
        reader = csv.DictReader(fh)
        missing = [c for c in CSV_COLUMNS if c not in (reader.fieldnames or [])]
        if missing:
            raise SystemExit(f"{path}: colonnes manquantes {missing}")
        return [dict(row) for row in reader]


def split_support(rows: Iterable[dict[str, str]]) -> Counter:
    """Nombre de paires par ``node_pk``."""
    return Counter(row["node_pk"] for row in rows)


def select_holdout(
    candidates: list[str],
    train_support: Counter,
    count: int,
    strategy: str,
    seed: int,
) -> list[str]:
    """Choisit ``count`` noeuds parmi ``candidates``, de facon reproductible.

    ``top-support`` : les noeuds les mieux servis au train d'abord (le test y
    trouve le plus de paires, donc la mesure y est la moins bruitee).
    ``seeded`` : tirage aleatoire a graine fixe, pour un ensemble
    representatif plutot que les tetes de distribution.
    """
    if count <= 0:
        return []
    if count > len(candidates):
        raise SystemExit(
            f"holdout-count {count} > {len(candidates)} noeuds candidats"
        )
    pool = sorted(candidates)
    if strategy == "top-support":
        ordered = sorted(pool, key=lambda n: (-train_support[n], n))
        return sorted(ordered[:count])
    if strategy == "seeded":
        rng = random.Random(seed)
        return sorted(rng.sample(pool, count))
    raise SystemExit(f"strategie inconnue: {strategy}")


def write_split(path: Path, rows: Iterable[dict[str, str]]) -> None:
    """Ecrit un split au format du builder (mêmes colonnes, UTF-8, LF)."""
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as fh:
        writer = csv.DictWriter(fh, fieldnames=CSV_COLUMNS, lineterminator="\n")
        writer.writeheader()
        for row in rows:
            writer.writerow({k: row[k] for k in CSV_COLUMNS})


def sha256_file(path: Path) -> str:
    """SHA-256 d'un fichier, lu par blocs."""
    digest = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 16), b""):
            digest.update(chunk)
    return digest.hexdigest()


def support_histogram(values: Iterable[int]) -> dict[str, int]:
    """Histogramme de support en cles triees, pour un rapport lisible."""
    return {str(k): v for k, v in sorted(Counter(values).items())}


def build(
    split_dir: Path,
    out_dir: Optional[Path],
    holdout_count: int,
    strategy: str,
    seed: int,
    min_test_pairs: int,
    min_train_support: int,
) -> dict[str, object]:
    """Construit le split tenu a part et rend le rapport (dicte le geste, jamais l'inverse)."""
    if not split_dir.is_dir():
        raise SystemExit(f"repertoire de splits introuvable: {split_dir}")
    rows = {s: read_split(split_dir / f"{s}.csv") for s in SPLITS}
    sources = {s: sha256_file(split_dir / f"{s}.csv") for s in SPLITS}

    train_support = split_support(rows["train"])
    test_support = split_support(rows["test"])
    val_support = split_support(rows["val"])
    families_by_node: dict[str, set[str]] = {}
    for row in rows["train"]:
        families_by_node.setdefault(row["node_pk"], set()).add(row["family"])

    candidates = sorted(
        node
        for node in train_support
        if train_support[node] >= min_train_support
        and test_support[node] >= min_test_pairs
    )
    heldout = select_holdout(candidates, train_support, holdout_count, strategy, seed)
    heldout_set = set(heldout)

    kept = {
        "train": [r for r in rows["train"] if r["node_pk"] not in heldout_set],
        "val": [r for r in rows["val"] if r["node_pk"] not in heldout_set],
        "test": list(rows["test"]),
    }

    if out_dir is not None:
        for name in SPLITS:
            write_split(Path(out_dir) / f"{name}.csv", kept[name])

    heldout_test = Counter(r["node_pk"] for r in rows["test"] if r["node_pk"] in heldout_set)
    heldout_train = Counter(r["node_pk"] for r in rows["train"] if r["node_pk"] in heldout_set)

    # Familles des noeuds tenus a part, comptees depuis les lignes elles-memes
    # (un noeud peut porter plusieurs familles au train : la derniere ligne ne
    # doit pas ecraser les autres). Publication par famille : noeuds distincts
    # et paires de test, pour qu'un arbitrage de protocole voie si le split
    # retire une famille entiere du train.
    heldout_family_nodes: dict[str, set[str]] = {}
    for node in heldout:
        for family in sorted(families_by_node.get(node, ())):
            heldout_family_nodes.setdefault(family, set()).add(node)
    heldout_family_test_pairs = Counter(
        r["family"] for r in rows["test"] if r["node_pk"] in heldout_set
    )
    families_report = {
        family: {
            "nodes": len(heldout_family_nodes.get(family, ())),
            "test_pairs": heldout_family_test_pairs.get(family, 0),
        }
        for family in sorted(
            set(heldout_family_nodes) | set(heldout_family_test_pairs)
        )
    }
    report: dict[str, object] = {
        "params": {
            "holdout_count": holdout_count,
            "strategy": strategy,
            "seed": seed,
            "min_test_pairs": min_test_pairs,
            "min_train_support": min_train_support,
        },
        "sources": {
            "split_dir": str(split_dir),
            "sha256": sources,
        },
        "population": {
            "candidate_nodes": len(candidates),
            "nodes_in_train": len(train_support),
            "nodes_in_val": len(val_support),
            "nodes_in_test": len(test_support),
            "nodes_in_all_three": len(
                set(train_support) & set(val_support) & set(test_support)
            ),
            "rows": {s: len(rows[s]) for s in SPLITS},
            "support_train": {
                "min": min(train_support.values()),
                "median": sorted(train_support.values())[len(train_support) // 2],
                "max": max(train_support.values()),
            },
            "support_test_histogram": support_histogram(test_support.values()),
        },
        "heldout": {
            "nodes": len(heldout),
            "node_pks": heldout,
            "families": families_report,
            "ambiguous_family_nodes": sum(
                1 for node in heldout if len(families_by_node.get(node, ())) > 1
            ),
            "train_support_histogram": support_histogram(heldout_train.values()),
            "test_support_histogram": support_histogram(heldout_test.values()),
            "test_pairs_total": sum(heldout_test.values()),
        },
        "after": {
            "rows": {s: len(kept[s]) for s in SPLITS},
            "nodes": {s: len(split_support(kept[s])) for s in SPLITS},
            "test_carries_heldout_nodes": bool(
                heldout_set & set(split_support(kept["test"]))
            ),
            "train_and_val_free_of_heldout": not (
                heldout_set & (set(split_support(kept["train"])) | set(split_support(kept["val"])))
            ),
        },
        "output_dir": str(out_dir) if out_dir is not None else None,
    }
    return report


def main(argv: Optional[list[str]] = None) -> int:
    """Point d'entree CLI."""
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--split-dir", type=Path, default=DEFAULT_SPLIT_DIR)
    parser.add_argument("--out-dir", type=Path, default=None)
    parser.add_argument("--report", type=Path, default=None)
    parser.add_argument("--holdout-count", type=int, default=0)
    parser.add_argument("--strategy", choices=STRATEGIES, default="top-support")
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--min-test-pairs", type=int, default=2)
    parser.add_argument("--min-train-support", type=int, default=1)
    args = parser.parse_args(argv)

    report = build(
        split_dir=args.split_dir,
        out_dir=args.out_dir,
        holdout_count=args.holdout_count,
        strategy=args.strategy,
        seed=args.seed,
        min_test_pairs=args.min_test_pairs,
        min_train_support=args.min_train_support,
    )
    payload = json.dumps(report, ensure_ascii=False, indent=1) + "\n"
    if args.report is not None:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(payload, encoding="utf-8")
    else:
        sys.stdout.write(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())