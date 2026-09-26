#!/usr/bin/env python3
"""Tests du constructeur de dataset de Phase 2 (EPIC #10355, issue #17578).

Les tests hermetiques construisent une mini-taxonomie et un mini-paquet de
scenarii dans tmp_path. Le dernier bloc relit les vraies sources du depot et
verifie que la regeneration est bit-identique au manifeste committe.
"""
from __future__ import annotations

import csv
import hashlib
import json
import sys
from collections import Counter
from pathlib import Path

import pytest

_SCRIPTS = Path(__file__).resolve().parents[2]
if str(_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(_SCRIPTS))

from fallacy_detection import cartesian_dataset_builder as B  # noqa: E402

REPO = Path(__file__).resolve().parents[3]
PHASE2 = REPO / "MyIA.AI.Notebooks/GenAI/FallacyDetection/data/phase2"


# --------------------------------------------------------------------------
# Donnees synthetiques
# --------------------------------------------------------------------------

def _fallacy_rows():
    rows = [{"PK": "0", "path": "0", "depth": "0", "Famille": "", "text_en": "Root"}]
    pk = 1
    # famille A : tete + 5 enfants (6 noeuds) ; famille B : tete + 1 enfant (2 noeuds)
    for fam, top, n_children in (("A", "1", 5), ("B", "2", 1)):
        rows.append({"PK": str(pk), "path": top, "depth": "1", "Famille": fam,
                     "text_en": f"{fam} head", "desc_en": f"{fam} definition",
                     "example_en": f"Example sentence number {pk} that must never leak."})
        pk += 1
        for i in range(1, n_children + 1):
            rows.append({"PK": str(pk), "path": f"{top}.{i}", "depth": "2", "Famille": fam,
                         "text_en": f"{fam}{i}", "desc_en": f"definition {fam}{i}",
                         "example_en": f"Example sentence number {pk} that must never leak."})
            pk += 1
    return rows


def _virtue_rows():
    rows = [{"pk": "0", "path": "0", "depth": "0", "family_fr": ""}]
    pk = 1
    for fam, top, n_children in (("C", "1", 2), ("D", "2", 1)):
        rows.append({"pk": str(pk), "path": top, "depth": "1", "family_fr": fam,
                     "title_en": f"{fam} head", "description_en": f"{fam} virtue"})
        pk += 1
        for i in range(1, n_children + 1):
            rows.append({"pk": str(pk), "path": f"{top}.{i}", "depth": "2", "family_fr": fam,
                         "title_en": f"{fam}{i}", "description_en": f"virtue {fam}{i}"})
            pk += 1
    return rows


def _scenario_rows():
    rows = []
    for c in range(1, 4):
        for s in range(1, 8):
            rows.append({"path": f"{c}.1.{s}", "category": f"cat{c}", "title": f"T{c}{s}",
                         "titre": f"T{c}{s}", "smoothTalker": f"talker{c}{s}",
                         "baratineur": f"baratineur{c}{s}", "drawer": f"drawer{c}{s}",
                         "piocheur": f"piocheur{c}{s}", "context": f"context {c}{s}",
                         "contexte": f"contexte {c}{s}", "issue": f"issue {c}{s}",
                         "enjeu": f"enjeu {c}{s}", "CCby": "Argumentum"})
    return rows


def _write(path: Path, rows: list[dict]) -> Path:
    fields = sorted({k for r in rows for k in r})
    with open(path, "w", encoding="utf-8", newline="") as f:
        w = csv.DictWriter(f, fieldnames=fields)
        w.writeheader()
        w.writerows(rows)
    return path


@pytest.fixture()
def mini(tmp_path):
    fal = _write(tmp_path / "fal.csv", _fallacy_rows())
    vir = _write(tmp_path / "vir.csv", _virtue_rows())
    sce = _write(tmp_path / "sce.csv", _scenario_rows())
    nodes = B.load_fallacies(fal) + B.load_virtues(vir)
    scen = B.load_scenarios(sce, expected_sha1=None)
    return {"fal": fal, "vir": vir, "sce": sce, "nodes": nodes, "scen": scen}


def _pairs(mini, seed=0, alpha=0.5, budgets=None):
    split = B.split_scenarios(mini["scen"], seed=seed)
    return B.build_pairs(mini["nodes"], split, budgets or {"fallacy": 40, "virtue": 12},
                         alpha=alpha, seed=seed)


# --------------------------------------------------------------------------
# Chargement
# --------------------------------------------------------------------------

def test_git_blob_sha1_matches_git(tmp_path):
    # valeur de reference : `printf 'hello\n' | git hash-object --stdin`
    p = tmp_path / "probe"
    p.write_bytes(b"hello\n")
    assert B.git_blob_sha1(p) == "ce013625030ba8dba906f756967f9e9ca394464a"


def test_loaders_drop_root_and_flag_leaves(mini):
    nodes = mini["nodes"]
    assert Counter(n.polarity for n in nodes) == {"fallacy": 8, "virtue": 5}
    assert all(n.pk > 0 for n in nodes)
    leaves = {n.key for n in nodes if n.is_leaf}
    # une tete de famille a des enfants : elle n'est pas une feuille
    assert "F1" not in leaves and "F7" not in leaves and "F2" in leaves


def test_load_scenarios_refuses_a_modified_copy(mini):
    good = B.git_blob_sha1(mini["sce"])
    assert len(B.load_scenarios(mini["sce"], expected_sha1=good)) == 21
    with pytest.raises(ValueError, match="divergente"):
        B.load_scenarios(mini["sce"], expected_sha1="0" * 40)


# --------------------------------------------------------------------------
# Splits de scenarii
# --------------------------------------------------------------------------

def test_split_is_stratified_and_deterministic(mini):
    a = B.split_scenarios(mini["scen"], seed=3)
    assert a == B.split_scenarios(mini["scen"], seed=3)
    by_cat = Counter((s.category, a[s.path]) for s in mini["scen"])
    for c in ("cat1", "cat2", "cat3"):
        assert by_cat[(c, "train")] == 5 and by_cat[(c, "val")] == 1 and by_cat[(c, "test")] == 1
    assert a != B.split_scenarios(mini["scen"], seed=4)


# --------------------------------------------------------------------------
# Equilibrage
# --------------------------------------------------------------------------

def _two_families(n_big=40, n_small=10):
    return ([B.Node("fallacy", i, f"1.{i}", 2, "big", True) for i in range(1, n_big + 1)]
            + [B.Node("fallacy", 100 + i, f"2.{i}", 2, "small", True)
               for i in range(1, n_small + 1)])


@pytest.mark.parametrize("alpha", [0.25, 0.5, 0.75])
def test_family_and_node_imbalances_multiply_to_size_ratio(alpha):
    nodes = _two_families()
    counts = B.allocate_counts(nodes, 200_000, alpha)
    im = B.imbalance(nodes, counts)
    assert im["size_ratio"] == 4.0
    assert im["family_ratio"] == pytest.approx(4.0 ** (1 - alpha), rel=1e-3)
    assert im["node_ratio"] == pytest.approx(4.0 ** alpha, rel=1e-3)
    assert im["family_ratio"] * im["node_ratio"] == pytest.approx(4.0, rel=2e-3)


def test_allocation_hits_budget_and_floor():
    nodes = _two_families()
    counts = B.allocate_counts(nodes, 123, 0.5)
    assert sum(counts.values()) == 123
    assert min(counts.values()) >= 1
    # budget inferieur au nombre de noeuds : le plancher d'une paire l'emporte
    assert B.allocate_counts(nodes, 10, 0.5) == {n.key: 1 for n in nodes}


# --------------------------------------------------------------------------
# Paires
# --------------------------------------------------------------------------

def test_no_scenario_leak_and_full_label_coverage(mini):
    pairs = _pairs(mini)
    rep = B.leak_report(pairs, mini["nodes"])
    assert rep["scenario_overlap"] == {"train&val": 0, "train&test": 0, "val&test": 0}
    assert rep["labels_missing"] == {"train": 0, "val": 0, "test": 0}
    assert rep["duplicate_pairs"] == 0


def test_eval_splits_hold_each_label_a_fixed_number_of_times(mini):
    pairs = _pairs(mini)
    for split, k in (("val", 1), ("test", 2)):
        c = Counter((p.polarity, p.node_pk) for p in pairs if p.split == split)
        assert set(c.values()) == {k}
        assert len(c) == len(mini["nodes"])
    assert sum(p.split == "train" for p in pairs) == 52


def test_scenarios_are_used_uniformly(mini):
    usage = B.scenario_usage(_pairs(mini))
    for split in B.SPLITS:
        assert usage[split]["max"] - usage[split]["min"] <= 1


def test_too_many_pairs_per_node_is_refused(mini):
    split = B.split_scenarios(mini["scen"])
    with pytest.raises(ValueError, match="scenarii dans le split test"):
        B.build_pairs(mini["nodes"], split, {"fallacy": 8, "virtue": 5}, test_per_node=4)


def test_split_files_are_byte_stable(mini, tmp_path):
    a = _pairs(mini, seed=1)
    b = _pairs(mini, seed=1)
    for s in B.SPLITS:
        assert B.split_csv_bytes(a, s) == B.split_csv_bytes(b, s)
    paths = B.write_splits(a, tmp_path / "out")
    with open(paths["val"], encoding="utf-8", newline="") as f:
        rows = list(csv.DictReader(f))
    assert tuple(rows[0]) == B.CSV_COLUMNS
    assert b"\r\n" not in paths["train"].read_bytes()
    manifest = B.write_manifest({"k": [1, 2]}, tmp_path / "out")
    assert manifest.read_bytes() == b'{\n "k": [\n  1,\n  2\n ]\n}\n'


# --------------------------------------------------------------------------
# Prompts
# --------------------------------------------------------------------------

def test_prompt_never_carries_a_node_example_and_swaps_roles(mini):
    texts = B.load_texts(mini["fal"], mini["vir"], mini["sce"])
    pairs = _pairs(mini)
    assert not any(B.prompt_contains_example(p, texts, "en") for p in pairs)
    fal = next(p for p in pairs if p.polarity == "fallacy")
    vir = next(p for p in pairs if p.polarity == "virtue")
    pf, pv = B.render_prompt(fal, texts, "en"), B.render_prompt(vir, texts, "en")
    assert "Speaker: talker" in pf and "commits the fallacy" in pf
    assert "Speaker: drawer" in pv and "shows the argumentative virtue" in pv
    assert "Speaker: baratineur" in B.render_prompt(fal, texts, "fr")


def test_example_detector_is_not_blind(mini):
    """Controle positif : le detecteur voit un exemple quand il est bien la."""
    texts = B.load_texts(mini["fal"], mini["vir"], mini["sce"])
    p = next(p for p in _pairs(mini) if p.polarity == "fallacy")
    key = f"F{p.node_pk}"
    title, _, examples = texts["nodes"][key]["en"]
    texts["nodes"][key]["en"] = (title, examples[0], examples)
    assert B.prompt_contains_example(p, texts, "en")


def test_tagged_card_definition_keeps_only_the_explanation():
    # forme mesuree au commit amont sur desc_fa de F944 : [nom] / [explication] / [exemple]
    card = "[name] Sound bite\n[explanation] A catchy quote.\n[example] You are surprised by it."
    assert B._definition(card) == "A catchy quote."
    assert B._definition("A plain definition [with brackets].") == "A plain definition [with brackets]."


def test_load_texts_refuses_a_definition_carrying_an_example(mini, tmp_path):
    rows = _fallacy_rows()
    rows[2]["desc_en"] = f"Definition then {rows[2]['example_en']}"
    fal = _write(tmp_path / "fal_leak.csv", rows)
    with pytest.raises(ValueError, match=r"F2 \[en\]"):
        B.load_texts(fal, mini["vir"], mini["sce"])


# --------------------------------------------------------------------------
# Sources reelles : regeneration bit-identique au manifeste committe
# --------------------------------------------------------------------------

@pytest.mark.skipif(not (PHASE2 / "manifest.json").exists(), reason="manifeste absent")
def test_real_build_matches_committed_manifest():
    manifest = json.loads((PHASE2 / "manifest.json").read_text(encoding="utf-8"))
    nodes, _, _, pairs, fresh = B.build(manifest["params"])
    assert fresh["sources"] == manifest["sources"]
    assert fresh["files"] == manifest["files"]
    assert fresh["leaks"]["duplicate_pairs"] == 0
    assert set(fresh["leaks"]["scenario_overlap"].values()) == {0}
    for s in ("val", "test"):
        committed = (PHASE2 / f"{s}.csv").read_bytes()
        assert committed == B.split_csv_bytes(pairs, s)
        assert hashlib.sha256(committed).hexdigest() == manifest["files"][f"{s}.csv"]["sha256"]
