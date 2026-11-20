#!/usr/bin/env python3
"""Tests du split « nœud tenu à part » (#10355, sections 2(c) et 3 de la revue EPITA).

Ce que ces tests epinglent, et pourquoi :

- **le sens du split** : les noeuds tenus a part disparaissent du train ET du
  val, et restent au test -- c'est la seule configuration ou le test porte un
  sophisme que le train n'a jamais vu. Un split qui les retirerait aussi du
  test ne mesurerait plus rien ;
- **le determinisme** : meme graine, meme ensemble ; deux strategies distinctes
  doivent rendre des ensembles distincts sur une population ou elles le peuvent,
  sinon le parametre est inerte ;
- **le plancher de support** : aucun noeud tenu a part sous ``--min-test-pairs``
  (sinon la mesure sur ce noeud est faite de une ou deux paires) ;
- **le refus explicite** : demander plus de noeuds que de candidats echoue
  bruyamment plutot que de rendre silencieusement un split plus court ;
- **le mode rapport seul** : sans ``--out-dir`` aucun fichier de split n'est
  ecrit (l'inventaire ``train.csv`` est gitignore, un split derive ne se
  committe pas) ;
- **l'integrite du CSV rendu** : colonnes et ordre du builder, LF, UTF-8 --
  un split relu par les organes existants doit etre indistinguishable d'un
  split du builder.

Les fixtures sont synthetiques : ``data/phase2/train.csv`` est gitignore (14 000
paires, politique d'artefacts), donc un test qui lirait le repertoire par
defaut echouerait en CI.
"""
from __future__ import annotations

import csv
import importlib.util
import json
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[3]
SCRIPT = REPO_ROOT / "scripts/fallacy_detection/build_heldout_node_split.py"

COLUMNS = [
    "pair_id",
    "split",
    "polarity",
    "node_pk",
    "family",
    "depth",
    "is_leaf",
    "scenario_path",
]


def _load_module():
    spec = importlib.util.spec_from_file_location("build_heldout_node_split", SCRIPT)
    mod = importlib.util.module_from_spec(spec)
    sys.modules.setdefault("build_heldout_node_split", mod)
    spec.loader.exec_module(mod)
    return mod


@pytest.fixture(scope="module")
def mod():
    return _load_module()


def _row(split: str, node: int, idx: int, family: str = "Famille") -> dict[str, str]:
    return {
        "pair_id": f"{split}-F{node}-{idx}",
        "split": split,
        "polarity": "fallacy",
        "node_pk": str(node),
        "family": family,
        "depth": "2",
        "is_leaf": "0",
        "scenario_path": f"2.{node}.{idx}",
    }


def _write_fixture(root: Path, support_train: dict[int, int], support_test: dict[int, int]) -> Path:
    """Ecrit train/val/test synthetiques : un noeud = ``support`` paires par split."""
    root.mkdir(parents=True, exist_ok=True)
    rows = {"train": [], "val": [], "test": []}
    for node, n in support_train.items():
        rows["train"].extend(_row("train", node, i) for i in range(n))
    for node in sorted(set(support_train) | set(support_test)):
        rows["val"].append(_row("val", node, 0))
    for node, n in support_test.items():
        rows["test"].extend(_row("test", node, i) for i in range(n))
    for split, split_rows in rows.items():
        with (root / f"{split}.csv").open("w", encoding="utf-8", newline="") as fh:
            writer = csv.DictWriter(fh, fieldnames=COLUMNS, lineterminator="\n")
            writer.writeheader()
            writer.writerows(split_rows)
    return root


@pytest.fixture()
def splits(tmp_path):
    """Cinq noeuds : 3 bien servis (test 4 paires), 2 faiblement (test 1 paire)."""
    return _write_fixture(
        tmp_path / "phase2",
        support_train={10: 8, 11: 6, 12: 5, 13: 3, 14: 2},
        support_test={10: 4, 11: 4, 12: 4, 13: 1, 14: 1},
    )


def test_holdout_removes_nodes_from_train_and_val_only(mod, splits, tmp_path):
    out = tmp_path / "out"
    report = mod.build(
        split_dir=splits,
        out_dir=out,
        holdout_count=2,
        strategy="top-support",
        seed=42,
        min_test_pairs=2,
        min_train_support=1,
    )
    assert report["heldout"]["nodes"] == 2
    assert report["after"]["train_and_val_free_of_heldout"] is True
    assert report["after"]["test_carries_heldout_nodes"] is True

    heldout = set(report["heldout"]["node_pks"])
    for split in ("train", "val"):
        with (out / f"{split}.csv").open(encoding="utf-8", newline="") as fh:
            nodes = {r["node_pk"] for r in csv.DictReader(fh)}
        assert heldout.isdisjoint(nodes), f"{split} porte encore un noeud tenu a part"
    with (out / "test.csv").open(encoding="utf-8", newline="") as fh:
        test_nodes = {r["node_pk"] for r in csv.DictReader(fh)}
    assert heldout <= test_nodes


def test_top_support_takes_the_best_served_nodes(mod, splits, tmp_path):
    report = mod.build(
        split_dir=splits,
        out_dir=tmp_path / "o",
        holdout_count=2,
        strategy="top-support",
        seed=42,
        min_test_pairs=2,
        min_train_support=1,
    )
    assert report["heldout"]["node_pks"] == ["10", "11"]


def test_same_seed_same_selection_and_strategies_differ(mod, splits, tmp_path):
    common = dict(
        split_dir=splits,
        out_dir=None,
        holdout_count=2,
        min_test_pairs=2,
        min_train_support=1,
    )
    # Graine 42 : sur cette population (candidats 10/11/12), le tirage
    # aleatoire (10, 12) differait des tetes de support (10, 11). La graine 7
    # y collisionne -- l'ancienne echappatoire ``or len(...) < 3`` masquait
    # cette collision au lieu de l'epingler.
    a = mod.build(strategy="seeded", seed=42, **common)
    b = mod.build(strategy="seeded", seed=42, **common)
    assert a["heldout"]["node_pks"] == b["heldout"]["node_pks"]
    assert len(a["heldout"]["node_pks"]) == 2

    top = mod.build(strategy="top-support", seed=42, **common)
    assert top["heldout"]["node_pks"] != a["heldout"]["node_pks"]


def test_min_test_pairs_excludes_thin_nodes(mod, splits, tmp_path):
    report = mod.build(
        split_dir=splits,
        out_dir=None,
        holdout_count=3,
        strategy="top-support",
        seed=42,
        min_test_pairs=2,
        min_train_support=1,
    )
    assert set(report["heldout"]["node_pks"]) == {"10", "11", "12"}
    assert report["population"]["candidate_nodes"] == 3


def test_asking_more_than_candidates_fails_loudly(mod, splits, tmp_path):
    with pytest.raises(SystemExit):
        mod.build(
            split_dir=splits,
            out_dir=None,
            holdout_count=4,
            strategy="top-support",
            seed=42,
            min_test_pairs=2,
            min_train_support=1,
        )


def test_report_only_writes_no_split(mod, splits, tmp_path, monkeypatch):
    monkeypatch.chdir(tmp_path)
    mod.build(
        split_dir=splits,
        out_dir=None,
        holdout_count=1,
        strategy="top-support",
        seed=42,
        min_test_pairs=2,
        min_train_support=1,
    )
    # Sans --out-dir, aucun CSV n'est ecrit nulle part sous le cwd : le
    # repertoire de splits (train.csv gitignore) ne doit pas se voir doubler
    # d'un split derive dans un coin du disque.
    written = [p for p in tmp_path.rglob("*.csv") if not p.is_relative_to(splits)]
    assert written == []


def test_family_counts_come_from_rows_not_last_row(mod, tmp_path):
    """Un noeud multi-familles au train publie TOUTES ses familles.

    Regression du comptage ``derniere-ligne-gagnante`` : l'ancien dict
    ``{node: family}`` ecrasait les familles precedentes du meme noeud, donc
    le rapport pouvait annoncer une famille retiree du train qui ne l'etait
    pas (et en omettre une qui l'etait).
    """
    root = tmp_path / "phase2"
    root.mkdir(parents=True)
    rows = {"train": [], "val": [], "test": []}
    # Noeud 10 : deux familles au train (A puis B), une seule au test (B).
    rows["train"].append(_row("train", 10, 0, family="FamilleA"))
    rows["train"].append(_row("train", 10, 1, family="FamilleB"))
    rows["train"].append(_row("train", 10, 2, family="FamilleB"))
    # Noeud 11 : une famille unique, pour que le holdout de 1 noeud soit stable.
    rows["train"].extend(_row("train", 11, i, family="FamilleC") for i in range(3))
    rows["val"].extend(_row("val", n, 0) for n in (10, 11))
    rows["test"].extend(_row("test", 10, i, family="FamilleB") for i in range(2))
    rows["test"].append(_row("test", 11, 0, family="FamilleC"))
    for split, split_rows in rows.items():
        with (root / f"{split}.csv").open("w", encoding="utf-8", newline="") as fh:
            writer = csv.DictWriter(fh, fieldnames=COLUMNS, lineterminator="\n")
            writer.writeheader()
            writer.writerows(split_rows)

    report = mod.build(
        split_dir=root,
        out_dir=None,
        holdout_count=1,
        strategy="top-support",
        seed=42,
        min_test_pairs=2,
        min_train_support=1,
    )
    assert report["heldout"]["node_pks"] == ["10"]
    families = report["heldout"]["families"]
    # Les DEUX familles du noeud 10 sont publiees (l'ancien dict n'en
    # gardait que FamilleB, derniere ligne).
    assert families["FamilleA"] == {"nodes": 1, "test_pairs": 0}
    assert families["FamilleB"] == {"nodes": 1, "test_pairs": 2}
    # FamilleC vit hors du holdout : elle n'apparait pas.
    assert "FamilleC" not in families
    assert report["heldout"]["ambiguous_family_nodes"] == 1


def test_written_csv_matches_builder_format(mod, splits, tmp_path):
    out = tmp_path / "out"
    mod.build(
        split_dir=splits,
        out_dir=out,
        holdout_count=1,
        strategy="top-support",
        seed=42,
        min_test_pairs=2,
        min_train_support=1,
    )
    raw = (out / "train.csv").read_bytes()
    assert b"\r\n" not in raw, "le builder ecrit en LF"
    assert raw.decode("utf-8").splitlines()[0].split(",") == COLUMNS


def test_report_is_json_serialisable(mod, splits, tmp_path):
    report = mod.build(
        split_dir=splits,
        out_dir=None,
        holdout_count=1,
        strategy="top-support",
        seed=42,
        min_test_pairs=2,
        min_train_support=1,
    )
    loaded = json.loads(json.dumps(report, ensure_ascii=False))
    assert loaded["population"]["nodes_in_all_three"] == 5
    assert loaded["heldout"]["test_pairs_total"] == 4


def test_cli_writes_report_file(mod, splits, tmp_path):
    report_path = tmp_path / "r.json"
    rc = mod.main(
        [
            "--split-dir",
            str(splits),
            "--holdout-count",
            "1",
            "--min-test-pairs",
            "2",
            "--report",
            str(report_path),
        ]
    )
    assert rc == 0
    payload = json.loads(report_path.read_text(encoding="utf-8"))
    assert payload["heldout"]["nodes"] == 1
    assert payload["output_dir"] is None