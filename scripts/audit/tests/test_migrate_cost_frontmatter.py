#!/usr/bin/env python3
"""Tests pour migrate_cost_frontmatter_to_metadata.py — Issues #8904/#8056/#9089.

Couvre les 3 shapes :
  - QC (cell#0, metadata.cost present) -> UNION merge, strip-keep H1 (regression).
  - GenAI well-formed (cell#1, metadata.cost absent) -> CREATE, remove cell.
  - GenAI malformed (cell#1, closer `---` avale par `notes: |`) -> tolerant parse,
    CREATE, remove cell.
Plus : datetime sanitization, idempotence (re-run skip), cell#0|cell#1 scan order.
"""

import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
AUDIT_DIR = HERE.parent
sys.path.insert(0, str(AUDIT_DIR))

import migrate_cost_frontmatter_to_metadata as mig  # noqa: E402


# === Helpers : construction de notebooks factices par shape ===

def _dump(nb, path):
    """Dump byte-stable (indent=1, LF-only) — match le format canonique du script."""
    path.write_bytes((json.dumps(nb, indent=1, ensure_ascii=False) + "\n").encode("utf-8"))


def _make_qc_shape(tmp_path):
    """Shape QC : frontmatter cell#0 (well-formed) + metadata.cost present (union)."""
    nb = {
        "cells": [
            {"cell_type": "markdown", "metadata": {},
             "source": ["---\n",
                        "title: \"QC Demo\"\n",
                        "cost:\n",
                        "  api_usd_est: 0.5\n",
                        "  cpu_min: 2\n",
                        "  metadata_written: 2026-07-23T09:30Z\n",
                        "---\n",
                        "# Titre QC\n",
                        "\n",
                        "Contenu pedagogique.\n"]},
            {"cell_type": "code", "execution_count": 1, "metadata": {},
             "outputs": [], "source": ["qb = QuantBook()\n"]},
        ],
        "metadata": {"kernelspec": {"name": "python3"},
                     "cost": {"api_usd_est": 0.0, "cpu_min": 0,
                              "qcc_tokens_est": 980, "reproducibility": "MED"}},
        "nbformat": 4, "nbformat_minor": 5,
    }
    p = tmp_path / "qc_demo.ipynb"
    _dump(nb, p)
    return p


def _make_genai_strict_shape(tmp_path):
    """Shape GenAI well-formed : frontmatter cell#1 (apres titre), metadata.cost ABSENT."""
    nb = {
        "cells": [
            {"cell_type": "markdown", "metadata": {}, "source": ["# Titre GenAI\n"]},
            {"cell_type": "markdown", "metadata": {},
             "source": ["---\n",
                        "title: \"GenAI Demo\"\n",
                        "cost:\n",
                        "  api_usd_est: 0.2\n",
                        "  gpu_required: false\n",
                        "  metadata_written: 2026-07-23T09:30Z\n",
                        "---\n"]},
            {"cell_type": "code", "execution_count": 1, "metadata": {},
             "outputs": [], "source": ["print('hi')\n"]},
        ],
        "metadata": {"kernelspec": {"name": "python3"}},
        "nbformat": 4, "nbformat_minor": 5,
    }
    p = tmp_path / "genai_strict.ipynb"
    _dump(nb, p)
    return p


def _make_genai_malformed_shape(tmp_path):
    """Shape GenAI malformed : closer `---` avale par un bloc `notes: |` (indenté),
    pas de closer en colonne 0 — reproduit les 3 notebooks Audio de #9089."""
    source = [
        "---\n",
        "title: \"GenAI Malformed Demo\"\n",
        "cost:\n",
        "  api_usd_est: 0.4\n",
        "  gpu_required: false\n",
        "  metadata_written: 2026-07-23T09:30Z\n",
        "notes: |\n",
        "  Benchmark comparatif multi-modeles.\n",
        "  Cout reel depend du nombre de generations.\n",
        "  ---\n",  # <-- closer avale : indenté sous notes:|, pas en colonne 0
    ]
    nb = {
        "cells": [
            {"cell_type": "markdown", "metadata": {}, "source": ["# Titre GenAI\n"]},
            {"cell_type": "markdown", "metadata": {}, "source": source},
            {"cell_type": "code", "execution_count": 1, "metadata": {},
             "outputs": [], "source": ["print('hi')\n"]},
        ],
        "metadata": {"kernelspec": {"name": "python3"}},
        "nbformat": 4, "nbformat_minor": 5,
    }
    p = tmp_path / "genai_malformed.ipynb"
    _dump(nb, p)
    return p


# === Shape QC : UNION merge + strip-keep H1 (regression) ===

def test_qc_shape_union_merge_and_strip_keep(tmp_path):
    p = _make_qc_shape(tmp_path)
    rep = mig.migrate_notebook(p, apply=True, by="test")
    assert rep["status"] == "migrated"
    assert rep["mode"] == "strict"
    assert rep["merge_kind"] == "union"
    assert rep["remove_cell"] is False  # strip-keep : cell#0 garde le H1 trailing
    nb = json.loads(p.read_text(encoding="utf-8"))
    cost = nb["metadata"]["cost"]
    # UNION : frontmatter gagne sur overlap (api_usd_est 0.0->0.5, cpu_min 0->2),
    # metadata.cost garde ses champs propres (qcc_tokens_est absent du frontmatter).
    assert cost["api_usd_est"] == 0.5
    assert cost["cpu_min"] == 2
    assert cost["qcc_tokens_est"] == 980  # preserved (meta_only)
    # cell#0 toujours present (strip-keep), demarre par le H1.
    assert nb["cells"][0]["source"][0].startswith("# Titre QC")
    assert len(nb["cells"]) == 2  # pas de removal


# === Shape GenAI well-formed : CREATE + remove cell ===

def test_genai_strict_create_and_remove_cell(tmp_path):
    p = _make_genai_strict_shape(tmp_path)
    rep = mig.migrate_notebook(p, apply=True, by="test")
    assert rep["status"] == "migrated"
    assert rep["mode"] == "strict"
    assert rep["merge_kind"] == "create-from-frontmatter"
    assert rep["remove_cell"] is True
    assert rep["frontmatter_cell"] == 1  # detecte en cell#1
    nb = json.loads(p.read_text(encoding="utf-8"))
    assert len(nb["cells"]) == 2  # cell#1 frontmatter supprimee (3->2)
    cost = nb["metadata"]["cost"]
    assert cost["api_usd_est"] == 0.2
    assert cost["gpu_required"] is False
    assert nb["cells"][0]["source"][0].startswith("# Titre GenAI")  # titre preserve


# === Shape GenAI malformed : tolerant parse + CREATE + remove cell ===

def test_genai_malformed_tolerant_parse(tmp_path):
    p = _make_genai_malformed_shape(tmp_path)
    rep = mig.migrate_notebook(p, apply=True, by="test")
    assert rep["status"] == "migrated"
    assert rep["mode"] == "tolerant"  # pas de closer col-0 -> tolerant
    assert rep["merge_kind"] == "create-from-frontmatter"
    assert rep["remove_cell"] is True
    nb = json.loads(p.read_text(encoding="utf-8"))
    cost = nb["metadata"]["cost"]
    assert cost["api_usd_est"] == 0.4
    assert cost["gpu_required"] is False


def test_find_cell_strict_wins_over_tolerant(tmp_path):
    """Un frontmatter well-formed doit etre detecte en mode strict (pas tolerant)."""
    p = _make_genai_strict_shape(tmp_path)
    nb = json.loads(p.read_text(encoding="utf-8"))
    info = mig.find_cost_frontmatter_cell(nb)
    assert info is not None
    assert info["mode"] == "strict"
    assert info["idx"] == 1


# === datetime sanitization (#9089 point 5) ===

def test_datetime_sanitized_to_iso_string(tmp_path):
    """yaml parse `metadata_written: 2026-07-23T09:30Z` en datetime ; la migration
    doit le convertir en ISO string (JSON-serializable)."""
    for maker in (_make_genai_strict_shape, _make_genai_malformed_shape, _make_qc_shape):
        p = maker(tmp_path)
        rep = mig.migrate_notebook(p, apply=True, by="test")
        assert rep["status"] == "migrated", (maker.__name__, rep)
        nb = json.loads(p.read_text(encoding="utf-8"))
        mw = nb["metadata"]["cost"]["metadata_written"]
        assert isinstance(mw, str), (maker.__name__, type(mw))
        assert mw == "2026-07-23T09:30Z", (maker.__name__, mw)
        # le notebook re-dumpé reste JSON-valide (sanitization evite le TypeError).
        json.loads(p.read_text(encoding="utf-8"))
        p.unlink()


# === Idempotence : re-run sur migre -> skip ===

def test_idempotent_skip_after_migration(tmp_path):
    p = _make_genai_strict_shape(tmp_path)
    assert mig.migrate_notebook(p, apply=True, by="test")["status"] == "migrated"
    rep2 = mig.migrate_notebook(p, apply=True, by="test")
    assert rep2["status"] == "skip-already-migrated"


def test_skip_when_no_frontmatter(tmp_path):
    nb = {"cells": [{"cell_type": "markdown", "metadata": {},
                     "source": ["# Pas de frontmatter\n"]}],
          "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    p = tmp_path / "clean.ipynb"
    _dump(nb, p)
    rep = mig.migrate_notebook(p, apply=True, by="test")
    assert rep["status"] == "skip-already-migrated"


# === byte-stable baseline + minimal-diff gates ===

def test_qc_shape_byte_stable_and_minimal_diff(tmp_path):
    p = _make_qc_shape(tmp_path)
    rep = mig.migrate_notebook(p, apply=False, by="test")
    assert rep["byte_stable_baseline"] is True
    assert rep["minimal_diff"] is True
    assert rep["field_equivalent"] is True


def test_genai_create_minimal_diff_allows_one_cell_removal(tmp_path):
    """Le gate minimal-diff autorise exactement 1 cellule supprimee (GenAI rm-cell)."""
    p = _make_genai_strict_shape(tmp_path)
    rep = mig.migrate_notebook(p, apply=False, by="test")
    assert rep["minimal_diff"] is True
    assert rep["remove_cell"] is True
