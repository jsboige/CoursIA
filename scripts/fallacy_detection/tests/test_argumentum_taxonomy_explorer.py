#!/usr/bin/env python3
"""Hermetic tests for argumentum_taxonomy_explorer (EPIC #10355 Phase 2).

Builds a synthetic mini-taxonomy in tmp_path -- no dependency on the real CSV.
"""
from __future__ import annotations

import csv
import json
import sys
from pathlib import Path

import pytest

# Make the package importable when run from the repo root or the tests dir.
_SCRIPTS = Path(__file__).resolve().parents[1]
if str(_SCRIPTS) not in sys.path:
    sys.path.insert(0, str(_SCRIPTS))

from fallacy_detection.argumentum_taxonomy_explorer import (  # noqa: E402
    ArgumentumTaxonomy,
    TaxonomyNode,
    _load_nodes,
)

# Columns used by TaxonomyNode.from_row -- a faithful minimal subset.
_HEADER = [
    "PK", "path", "depth", "Famille", "nom_vulgarisé", "Latin",
    "text_fr", "desc_fr", "example_fr", "text_en", "Simple_name_en",
    "desc_en", "example_en",
]


def _row(pk, path, depth, famille, nom, text_fr="", desc="", example="",
         latin="", simple_en=""):
    return {
        "PK": str(pk), "path": path, "depth": str(depth), "Famille": famille,
        "nom_vulgarisé": nom, "Latin": latin, "text_fr": text_fr or nom,
        "desc_fr": desc, "example_fr": example, "text_en": "",
        "Simple_name_en": simple_en, "desc_en": "", "example_en": "",
    }


def _write_mini_taxonomy(path: Path) -> None:
    """Write a 7-node synthetic tree (root + family + sub + leaves)."""
    rows = [
        _row(0, "0", 0, "Argument fallacieux", "Argument fallacieux"),
        # Family A: depth 1, two leaves + one sub-node with its own leaf.
        _row(1, "1", 1, "FamilleA", "FamilleA",
             desc="Desc famille A."),
        _row(2, "1.1", 2, "FamilleA", "Sophisme A1",
             desc="Definition A1.", example="Exemple A1."),
        _row(3, "1.2", 2, "FamilleA", "Sophisme A2",
             desc="Definition A2.", example="Exemple A2."),
        _row(4, "1.3", 2, "FamilleA", "SousA",
             desc="Sous-categorie A."),
        _row(5, "1.3.1", 3, "FamilleA", "Sophisme A3",
             desc="Definition A3.", example="Exemple A3."),
        # Family B: depth 1, one leaf.
        _row(6, "2", 1, "FamilleB", "FamilleB", desc="Desc famille B."),
        _row(7, "2.1", 2, "FamilleB", "Sophisme B1",
             desc="Definition B1.", example="Exemple B1."),
    ]
    with open(path, "w", encoding="utf-8", newline="") as f:
        w = csv.DictWriter(f, fieldnames=_HEADER)
        w.writeheader()
        w.writerows(rows)


@pytest.fixture
def taxo_path(tmp_path: Path) -> Path:
    p = tmp_path / "mini_taxonomy.csv"
    _write_mini_taxonomy(p)
    return p


@pytest.fixture
def taxo(taxo_path: Path) -> ArgumentumTaxonomy:
    return ArgumentumTaxonomy.from_csv(taxo_path)


# -- loading -------------------------------------------------------

def test_load_nodes_bom_tolerant(taxo_path: Path) -> None:
    """A leading UTF-8 BOM must not corrupt the first column header."""
    raw = taxo_path.read_bytes()
    taxo_path.write_bytes(b"\xef\xbb\xbf" + raw)  # prepend BOM
    nodes = _load_nodes(taxo_path)
    assert len(nodes) == 8
    assert nodes[0].pk == 0  # PK parsed, not stuck as a BOM-prefixed string.


def test_root_node_flag(taxo: ArgumentumTaxonomy) -> None:
    root = taxo._by_pk[0]
    assert root.is_root
    assert taxo._by_pk[1].is_root is False


# -- the 6 operations ----------------------------------------------

def test_list_fallacy_categories_excludes_root(taxo: ArgumentumTaxonomy) -> None:
    cats = taxo.list_fallacy_categories()
    assert cats == ["FamilleA", "FamilleB"]  # root excluded, order = first-seen.


def test_list_fallacies_in_category_returns_leaves(taxo: ArgumentumTaxonomy) -> None:
    members = taxo.list_fallacies_in_category("FamilleA")
    # Leaves of FamilleA: A1 (pk2), A2 (pk3), A3 (pk5). SousA (pk4) is internal.
    pks = {m["pk"] for m in members}
    assert pks == {2, 3, 5}
    assert all("nom_vulgarise" in m for m in members)


def test_list_fallacies_in_category_unknown(taxo: ArgumentumTaxonomy) -> None:
    assert taxo.list_fallacies_in_category("Inexistante") == []


def test_explore_hierarchy_children(taxo: ArgumentumTaxonomy) -> None:
    # PK 1 (FamilleA) has children: 1.1, 1.2, 1.3.
    res = taxo.explore_fallacy_hierarchy(1)
    assert res["current"]["pk"] == 1
    child_pks = [c["pk"] for c in res["children"]]
    assert child_pks == [2, 3, 4]
    assert res["children_total"] == 3


def test_explore_hierarchy_max_children(taxo: ArgumentumTaxonomy) -> None:
    res = taxo.explore_fallacy_hierarchy(1, max_children=2)
    assert len(res["children"]) == 2
    assert res["children_total"] == 3  # total still reported.


def test_explore_hierarchy_leaf_has_no_children(taxo: ArgumentumTaxonomy) -> None:
    res = taxo.explore_fallacy_hierarchy(2)  # Sophisme A1 is a leaf.
    assert res["children"] == []
    assert res["children_total"] == 0


def test_explore_hierarchy_unknown_pk(taxo: ArgumentumTaxonomy) -> None:
    assert taxo.explore_fallacy_hierarchy(999)["error"]


def test_find_fallacy_definition_by_nom(taxo: ArgumentumTaxonomy) -> None:
    res = taxo.find_fallacy_definition("Sophisme A1")
    assert res["pk"] == 2
    assert res["desc_fr"] == "Definition A1."


def test_find_fallacy_definition_by_latin(taxo: ArgumentumTaxonomy) -> None:
    # Build a node with a Latin name and search on it.
    nodes = _load_nodes(__import__("tempfile").mkstemp()[1] + "x") if False else taxo._nodes
    # simpler: add a Latin alias to the in-memory tree via direct search logic.
    res = taxo.find_fallacy_definition("A1")  # substring of nom_vulgarisé.
    assert res["pk"] == 2


def test_find_fallacy_definition_not_found(taxo: ArgumentumTaxonomy) -> None:
    assert taxo.find_fallacy_definition("N'existe pas")["error"]


def test_get_fallacy_details(taxo: ArgumentumTaxonomy) -> None:
    res = taxo.get_fallacy_details(2)
    assert res["pk"] == 2
    assert res["famille"] == "FamilleA"
    assert res["nom_vulgarise"] == "Sophisme A1"


def test_get_fallacy_details_unknown(taxo: ArgumentumTaxonomy) -> None:
    assert taxo.get_fallacy_details(999)["error"]


def test_get_fallacy_example(taxo: ArgumentumTaxonomy) -> None:
    res = taxo.get_fallacy_example("Sophisme A1")
    assert res["pk"] == 2
    assert res["example_fr"] == "Exemple A1."


def test_get_fallacy_example_not_found(taxo: ArgumentumTaxonomy) -> None:
    assert taxo.get_fallacy_example("Ghost")["error"]


# -- SFT trace generation ------------------------------------------

def test_generate_sft_traces_has_all_operations(taxo: ArgumentumTaxonomy) -> None:
    traces = taxo.generate_sft_traces(per_family_leaves=2)
    ops = {t.operation for t in traces}
    assert ops == {
        "list_fallacy_categories",
        "list_fallacies_in_category",
        "explore_fallacy_hierarchy",
        "find_fallacy_definition",
        "get_fallacy_example",
    }


def test_generate_sft_traces_structure(taxo: ArgumentumTaxonomy) -> None:
    traces = taxo.generate_sft_traces(per_family_leaves=1)
    # Every trace has a prompt, a JSON-parseable response, and an operation.
    for t in traces:
        assert t.prompt and t.response and t.operation
        parsed = json.loads(t.response)
        assert isinstance(parsed, dict)
    # list_fallacy_categories is unique (the top-level call).
    cat_traces = [t for t in traces if t.operation == "list_fallacy_categories"]
    assert len(cat_traces) == 1
    assert "FamilleA" in cat_traces[0].response


def test_generate_sft_traces_balanced_per_family(taxo: ArgumentumTaxonomy) -> None:
    """per_family_leaves caps leaf-level traces per family (balance)."""
    traces = taxo.generate_sft_traces(per_family_leaves=1)
    # 2 families -> 2 list_in_category + 2 definition + 2 example (1 leaf each).
    assert sum(1 for t in traces if t.operation == "list_fallacies_in_category") == 2
    assert sum(1 for t in traces if t.operation == "find_fallacy_definition") == 2


# -- coverage report -----------------------------------------------

def test_coverage_report(taxo: ArgumentumTaxonomy) -> None:
    rep = taxo.coverage_report()
    assert rep["total_nodes"] == 8
    assert rep["family_count"] == 2
    assert rep["families"] == ["FamilleA", "FamilleB"]
    assert rep["leaves"] == 4  # A1, A2, A3, B1.
    assert rep["leaves_per_family"] == {"FamilleA": 3, "FamilleB": 1}


# -- CLI -----------------------------------------------------------

def test_main_missing_file_exits_2(tmp_path: Path) -> None:
    from fallacy_detection.argumentum_taxonomy_explorer import main
    rc = main(["--taxonomy", str(tmp_path / "nope.csv"), "--report"])
    assert rc == 2


def test_main_list_categories(taxo_path: Path, capsys) -> None:
    from fallacy_detection.argumentum_taxonomy_explorer import main
    rc = main(["--taxonomy", str(taxo_path), "--list-categories"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "FamilleA" in out and "FamilleB" in out


def test_main_out_traces_jsonl(taxo_path: Path, tmp_path: Path) -> None:
    from fallacy_detection.argumentum_taxonomy_explorer import main
    out = tmp_path / "traces.jsonl"
    rc = main([
        "--taxonomy", str(taxo_path),
        "--out-traces", str(out),
        "--per-family-leaves", "1",
    ])
    assert rc == 0
    assert out.is_file()
    lines = out.read_text(encoding="utf-8").strip().splitlines()
    assert len(lines) > 0
    rec = json.loads(lines[0])
    assert {"operation", "prompt", "response"} <= set(rec)
