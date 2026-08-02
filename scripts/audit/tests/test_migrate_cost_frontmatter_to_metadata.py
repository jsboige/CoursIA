#!/usr/bin/env python3
"""Tests pour migrate_cost_frontmatter_to_metadata.py — route QC (régression,
prouve migrate_notebook inchangé) + route GenAI (#9089 : frontmatter
cell#0|cell#1, metadata.cost créé, YAML malformé toléré)."""

import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
AUDIT_DIR = HERE.parent
sys.path.insert(0, str(AUDIT_DIR))

import migrate_cost_frontmatter_to_metadata as m  # noqa: E402


def _dump(nb, trailing_nl=True):
    """Sérialise un notebook en indent=1 (byte-stable avec le script)."""
    s = json.dumps(nb, indent=1, ensure_ascii=False)
    return s + "\n" if trailing_nl else s


def _write_nb(tmp_path, name, nb, trailing_nl=True):
    p = tmp_path / name
    p.write_text(_dump(nb, trailing_nl), encoding="utf-8")
    return p


def _md(source_lines):
    """Cellule markdown avec source en list (format nbformat canonique)."""
    return {"cell_type": "markdown", "metadata": {}, "source": source_lines}


# --------------------------------------------------------------------------
# Helpers GenAI (#9089)
# --------------------------------------------------------------------------

def test_sanitize_yaml_scalars_datetime_to_iso():
    import datetime
    d = {"metadata_written": datetime.datetime(2026, 7, 23, 9, 30),
         "plain": datetime.date(2026, 7, 24), "n": 5, "s": "x",
         "nested": {"d": datetime.datetime(2026, 1, 1)}, "lst": [datetime.date(2026, 2, 2)]}
    out = m._sanitize_yaml_scalars(d)
    assert out["metadata_written"] == "2026-07-23T09:30:00"
    assert out["plain"] == "2026-07-24"
    assert out["nested"]["d"] == "2026-01-01T00:00:00"
    assert out["lst"][0] == "2026-02-02"
    # Passthrough scalaires inchangés.
    assert out["n"] == 5 and out["s"] == "x"


def test_col0_closer_index_detects_second_col0_delim():
    lines = "---\n".splitlines(keepends=True)  # un seul -> pas de closer
    assert m._col0_closer_index(["---\n", "a: 1\n", "---\n", "# H1\n"]) == 2


def test_col0_closer_index_ignores_indented_delim():
    # Le `  ---` indenté (avalé dans un bloc notes: |) n'est PAS un closer col0.
    lines = ["---\n", "notes: |\n", "  texte\n", "  ---\n"]
    assert m._col0_closer_index(lines) is None


# --------------------------------------------------------------------------
# Route GenAI — _parse_genai_frontmatter_cell : 3 formes
# --------------------------------------------------------------------------

def _audio_malformed_source():
    """Forme Audio : cell#1, pas de closer col0 (`  ---` indenté dans notes)."""
    return [
        "---\n",
        'title: "Audio"\n',
        "cost:\n",
        "  api_usd_est: 0.40\n",
        "  cpu_min: 4\n",
        "  reproducibility: MED\n",
        "  metadata_written: 2026-07-23T09:30Z\n",
        "notes: |\n",
        "  Benchmark multi-modeles.\n",
        "  ---\n",
    ]


def test_parse_genai_malformed_remove_cell():
    cost, disposition, new_source = m._parse_genai_frontmatter_cell(_audio_malformed_source())
    assert cost is not None
    assert disposition == "remove_cell"
    assert new_source is None
    # datetime sanitize : `2026-07-23T09:30Z` (suffixe Z) n'est PAS reconnu comme
    # timestamp par yaml -> reste une chaîne JSON-safe (pas de conversion nécessaire).
    assert cost["metadata_written"] == "2026-07-23T09:30Z"
    assert cost["api_usd_est"] == 0.40


def test_parse_genai_well_formed_empty_remove_cell():
    src = ["---\n", "cost:\n", "  cpu_min: 2\n", "---\n", "\n"]
    cost, disposition, new_source = m._parse_genai_frontmatter_cell(src)
    assert disposition == "remove_cell"
    assert new_source is None
    assert cost == {"cpu_min": 2}


def test_parse_genai_well_formed_h1_strip_keep():
    src = ["---\n", "cost:\n", "  cpu_min: 1\n", "---\n", "\n", "# Titre\n", "\n", "Suite.\n"]
    cost, disposition, new_source = m._parse_genai_frontmatter_cell(src)
    assert disposition == "strip_keep_h1"
    assert new_source == ["# Titre\n", "\n", "Suite.\n"]
    assert cost == {"cpu_min": 1}


def test_parse_genai_no_frontmatter_returns_none():
    assert m._parse_genai_frontmatter_cell(["# Titre\n", "texte\n"]) == (None, None, None)


def test_parse_genai_no_cost_block_returns_none():
    src = ["---\n", "title: x\n", "---\n", "# H1\n"]
    assert m._parse_genai_frontmatter_cell(src) == (None, None, None)


def test_detect_genai_finds_cell1_not_cell0():
    cells = [
        _md(["# Titre\n"]),                       # cell#0 titre (pas frontmatter)
        _md(_audio_malformed_source()),            # cell#1 frontmatter
        _md(["suite\n"]),
    ]
    idx, cost, disposition, new_source = m._detect_genai_cost_cell(cells)
    assert idx == 1
    assert disposition == "remove_cell"
    assert cost["cpu_min"] == 4


# --------------------------------------------------------------------------
# Route GenAI — migrate_notebook_genai : apply end-to-end
# --------------------------------------------------------------------------

def test_genai_malformed_apply_removes_cell_and_creates_cost(tmp_path):
    nb = {"cells": [_md(["# Titre\n"]), _md(_audio_malformed_source()), _md(["suite\n"])],
          "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    p = _write_nb(tmp_path, "a.ipynb", nb)
    rep = m.migrate_notebook_genai(p, apply=True, by="t:CoursIA")
    assert rep["status"] == "migrated"
    assert rep["created_metadata_cost"] is True
    assert rep["disposition"] == "remove_cell"
    out = json.loads(p.read_text(encoding="utf-8"))
    # cell#1 (frontmatter) retirée -> 2 cellules restantes (titre + suite).
    assert len(out["cells"]) == 2
    assert out["cells"][0]["source"] == ["# Titre\n"]
    assert out["cells"][1]["source"] == ["suite\n"]
    # metadata.cost créé depuis le frontmatter ; metadata_written reste chaîne
    # (suffixe Z non reconnu par yaml -> JSON-safe, pas de conversion).
    assert out["metadata"]["cost"]["cpu_min"] == 4
    assert out["metadata"]["cost"]["metadata_written"] == "2026-07-23T09:30Z"


def test_genai_well_formed_h1_apply_strips_and_unions(tmp_path):
    fm = ["---\n", "cost:\n", "  cpu_min: 1\n", "  free_alternative: other.ipynb\n",
          "---\n", "\n", "# SK-1\n", "\n", "Intro.\n"]
    nb = {"cells": [_md(fm), _md(["code cell\n", ""])],
          "metadata": {"cost": {"cpu_min": 0, "qcc_tokens_est": 42}},
          "nbformat": 4, "nbformat_minor": 5}
    p = _write_nb(tmp_path, "s.ipynb", nb)
    rep = m.migrate_notebook_genai(p, apply=True, by="t:CoursIA")
    assert rep["status"] == "migrated"
    assert rep["created_metadata_cost"] is False  # metadata.cost pré-existant
    assert rep["disposition"] == "strip_keep_h1"
    out = json.loads(p.read_text(encoding="utf-8"))
    # cell#0 source = H1 + trailing, frontmatter strippé.
    assert out["cells"][0]["source"] == ["# SK-1\n", "\n", "Intro.\n"]
    # UNION : frontmatter gagne (cpu_min 0->1), metadata garde qcc_tokens_est.
    assert out["metadata"]["cost"]["cpu_min"] == 1
    assert out["metadata"]["cost"]["free_alternative"] == "other.ipynb"
    assert out["metadata"]["cost"]["qcc_tokens_est"] == 42


def test_genai_trailing_newline_preserved_on_off(tmp_path):
    fm = ["---\n", "cost:\n", "  cpu_min: 2\n", "---\n", "\n"]
    nb = {"cells": [_md(["# T\n"]), _md(fm)], "metadata": {},
          "nbformat": 4, "nbformat_minor": 5}
    # Sans trailing newline.
    p = _write_nb(tmp_path, "no_nl.ipynb", nb, trailing_nl=False)
    before = p.read_bytes()
    assert not before.endswith(b"\n")
    rep = m.migrate_notebook_genai(p, apply=True, by="t:CoursIA")
    assert rep["byte_stable_baseline"] is True
    after = p.read_bytes()
    assert not after.endswith(b"\n")  # convention préservée
    # Avec trailing newline.
    p2 = _write_nb(tmp_path, "nl.ipynb", nb, trailing_nl=True)
    rep2 = m.migrate_notebook_genai(p2, apply=True, by="t:CoursIA")
    assert rep2["byte_stable_baseline"] is True
    assert p2.read_bytes().endswith(b"\n")


def test_genai_skip_already_migrated(tmp_path):
    nb = {"cells": [_md(["# Titre\n", "texte\n"])], "metadata": {},
          "nbformat": 4, "nbformat_minor": 5}
    p = _write_nb(tmp_path, "ok.ipynb", nb)
    rep = m.migrate_notebook_genai(p, apply=True, by="t:CoursIA")
    assert rep["status"] == "skip-already-migrated"


def test_genai_dry_run_does_not_write(tmp_path):
    nb = {"cells": [_md(["# T\n"]), _md(_audio_malformed_source())],
          "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    p = _write_nb(tmp_path, "d.ipynb", nb)
    before = p.read_bytes()
    rep = m.migrate_notebook_genai(p, apply=False, by="t:CoursIA")
    assert rep["status"] == "dry-run"
    assert p.read_bytes() == before  # inchangé


# --------------------------------------------------------------------------
# Route QC (régression) — migrate_notebook : prouve le chemin QC intact
# --------------------------------------------------------------------------

def _qc_nb():
    """Forme QC : cell#0 = frontmatter avec cost, metadata.cost présent (squelette)."""
    fm = ["---\n", "cost:\n", "  api_usd_est: 0.1\n", "  cpu_min: 3\n",
          "  reproducibility: HIGH\n", "---\n", "\n", "# QC Title\n"]
    return {"cells": [_md(fm), _md(["code\n"])],
            "metadata": {"cost": {"cpu_min": 0, "qcc_tokens_est": 7}},
            "nbformat": 4, "nbformat_minor": 5}


def test_qc_dry_run_report_fields(tmp_path):
    p = _write_nb(tmp_path, "q.ipynb", _qc_nb())
    rep = m.migrate_notebook(p, apply=False, by="t:CoursIA")
    assert rep["status"] == "dry-run"
    assert rep["field_equivalent"] is True
    assert rep["minimal_diff"] is True
    # frontmatter gagne sur cpu_min (0->3).
    assert "cpu_min" in rep["overwritten_fields"]


def test_qc_apply_migrates_and_strips(tmp_path):
    p = _write_nb(tmp_path, "q.ipynb", _qc_nb())
    rep = m.migrate_notebook(p, apply=True, by="t:CoursIA")
    assert rep["status"] == "migrated"
    out = json.loads(p.read_text(encoding="utf-8"))
    # cell#0 strippée -> H1 seul.
    assert out["cells"][0]["source"] == ["# QC Title\n"]
    # UNION : cpu_min pris au frontmatter, qcc_tokens_est conservé.
    assert out["metadata"]["cost"]["cpu_min"] == 3
    assert out["metadata"]["cost"]["api_usd_est"] == 0.1
    assert out["metadata"]["cost"]["qcc_tokens_est"] == 7


def test_qc_refused_when_no_metadata_cost(tmp_path):
    fm = ["---\n", "cost:\n", "  cpu_min: 3\n", "---\n", "\n", "# QC\n"]
    nb = {"cells": [_md(fm)], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    p = _write_nb(tmp_path, "r.ipynb", nb)
    rep = m.migrate_notebook(p, apply=True, by="t:CoursIA")
    # Route QC : metadata.cost absent -> refused (contrairement à GenAI qui crée).
    assert rep["status"] == "refused-no-metadata-cost"
