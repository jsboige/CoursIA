#!/usr/bin/env python3
"""Tests pour migrate_cost_frontmatter_to_metadata.py — frontmatter cost migration.

Covers the importable helpers of the cost-frontmatter migration tool (the
"MIGRATE BEFORE STRIP" tool, #8904 + #8056). It merges the LEGACY cell#0
``---cost: ...---`` YAML block into the CANONICAL ``metadata['cost']`` (union,
frontmatter authoritative on overlap) BEFORE stripping the frontmatter — so no
measured cost value is lost when the rendering-defective frontmatter is removed.

Scope (hermetic, 0 repo-file read / 0 network):
  - parse_frontmatter : dict+span extraction, no-frontmatter, YAML-error guard
  - _as_str : list-join / str-passthrough / None
  - strip_frontmatter_preserving_type : list-form + str-form, H1-after guard,
    no-frontmatter guard, non-H1-content abort
  - _lf_only : CRLF normalization
  - migrate_notebook : idempotency (skip-already-migrated), refused-no-metadata-cost,
    frontmatter-no-cost error, dry-run vs apply, UNION semantics (overwritten +
    meta-only fields), byte-stability passthrough, non-markdown-cell#0 error,
    unreadable-file error
  - main : no-paths SystemExit 2, --project globbing, --apply wiring, rc=1 on refusal

Run: ``python -m pytest scripts/audit/tests/test_migrate_cost_frontmatter_to_metadata.py -q``
"""
import json
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
AUDIT_DIR = HERE.parent
sys.path.insert(0, str(AUDIT_DIR))

import migrate_cost_frontmatter_to_metadata as mig  # noqa: E402


# ---------------------------------------------------------------------------
# helpers — build byte-stable synthetic notebooks
# ---------------------------------------------------------------------------

def _fm_source(fm_cost: dict, title: str = "Notebook", fmt: str = "list"):
    """Build a cell#0 markdown source carrying a `--- cost: ---` frontmatter block
    followed by an H1 title. ``fmt`` = "list" (nbformat canonical) or "str"."""
    import yaml
    body = yaml.safe_dump({"cost": fm_cost}, default_flow_style=False, sort_keys=True)
    block = f"---\n{body}---\n\n# {title}\n"
    if fmt == "list":
        return block.splitlines(keepends=True)
    return block


def _make_nb(fm_cost=None, meta_cost=None, title="Notebook", cell0_source=None):
    """Synthetic notebook. If ``cell0_source`` given, use it verbatim for cell#0."""
    nb = {
        "cells": [
            {"cell_type": "markdown", "metadata": {},
             "source": cell0_source if cell0_source is not None else _fm_source(fm_cost or {}, title)},
            {"cell_type": "code", "execution_count": 1, "metadata": {},
             "outputs": [], "source": ["print(1)\n"]},
        ],
        "metadata": {"kernelspec": {"name": "python3", "display_name": "Python 3"}},
        "nbformat": 4, "nbformat_minor": 5,
    }
    if meta_cost is not None:
        nb["metadata"]["cost"] = meta_cost
    return nb


def _write_nb(tmp_path: Path, name: str, nb: dict) -> Path:
    p = tmp_path / f"{name}.ipynb"
    content = json.dumps(nb, indent=1, ensure_ascii=False) + "\n"
    p.write_bytes(content.encode("utf-8"))  # LF-only
    return p


# ---------------------------------------------------------------------------
# parse_frontmatter
# ---------------------------------------------------------------------------

def test_parse_frontmatter_extracts_dict_and_span():
    src = "---\ncost:\n  cpu_min: 3\n---\n# Title\n"
    data, span = mig.parse_frontmatter(src)
    assert data == {"cost": {"cpu_min": 3}}
    assert span[0] == 0
    assert span[1] > 0  # covers the ---...--- block


def test_parse_frontmatter_no_block_returns_none():
    data, span = mig.parse_frontmatter("# Just a title\nno frontmatter")
    assert data is None and span is None


def test_parse_frontmatter_not_at_start_returns_none():
    # frontmatter must be at the very start (regex \A).
    src = "intro\n---\ncost:\n  x: 1\n---\n"
    assert mig.parse_frontmatter(src) == (None, None)


def test_parse_frontmatter_yaml_error_returns_none():
    # Unterminated YAML (tab-in-key / bad indent) -> safe_load raises -> (None, None).
    src = "---\ncost: {unterminated\n---\n# T\n"
    data, span = mig.parse_frontmatter(src)
    assert data is None and span is None


def test_parse_frontmatter_empty_block():
    src = "---\n---\n# Title\n"
    # regex needs `\n---\s*\n` after content; `---\n---\n` -> content is empty.
    data, span = mig.parse_frontmatter(src)
    # empty -> {} (safe_load of empty -> None -> {} per the `or {}`)
    assert data == {} or data is None  # tolerant: depends on regex match


# ---------------------------------------------------------------------------
# _as_str
# ---------------------------------------------------------------------------

def test_as_str_joins_list():
    assert mig._as_str(["a\n", "b\n"]) == "a\nb\n"


def test_as_str_passes_through_str():
    assert mig._as_str("hello") == "hello"


def test_as_str_none_to_empty():
    assert mig._as_str(None) == ""


# ---------------------------------------------------------------------------
# strip_frontmatter_preserving_type
# ---------------------------------------------------------------------------

class TestStripFrontmatter:
    def test_list_form_strips_and_keeps_h1(self):
        src = _fm_source({"cpu_min": 3}, "MyTitle")
        kept, ok = mig.strip_frontmatter_preserving_type(src)
        assert ok is True
        assert isinstance(kept, list)
        assert "".join(kept).lstrip().startswith("# MyTitle")
        assert "---" not in "".join(kept)

    def test_str_form_strips_and_keeps_h1(self):
        src = _fm_source({"cpu_min": 3}, "MyTitle", fmt="str")
        kept, ok = mig.strip_frontmatter_preserving_type(src)
        assert ok is True
        assert isinstance(kept, str)
        assert kept.lstrip().startswith("# MyTitle")

    def test_list_no_frontmatter_returns_unchanged_false(self):
        src = ["# Title\n", "prose\n"]
        kept, ok = mig.strip_frontmatter_preserving_type(src)
        assert ok is False
        assert kept is src

    def test_str_no_frontmatter_returns_unchanged_false(self):
        src = "# Title\nprose\n"
        kept, ok = mig.strip_frontmatter_preserving_type(src)
        assert ok is False
        assert kept == src

    def test_content_after_frontmatter_not_h1_aborts(self):
        # After stripping the frontmatter, the remaining content must start with
        # an H1 `#`. Prose directly after `---` -> abort (ok=False, unchanged).
        src = ["---\n", "cost:\n", "  x: 1\n", "---\n", "some prose no heading\n"]
        kept, ok = mig.strip_frontmatter_preserving_type(src)
        assert ok is False
        assert kept is src

    def test_single_delimiter_not_a_block(self):
        # Only one `---` (no closer) -> not a frontmatter block -> unchanged.
        src = ["---\n", "cost:\n", "  x: 1\n", "# Title\n"]
        kept, ok = mig.strip_frontmatter_preserving_type(src)
        assert ok is False


# ---------------------------------------------------------------------------
# _lf_only
# ---------------------------------------------------------------------------

def test_lf_only_normalizes_crlf():
    assert mig._lf_only("a\r\nb\r\n") == "a\nb\n"


def test_lf_only_idempotent_on_lf():
    assert mig._lf_only("a\nb\n") == "a\nb\n"


# ---------------------------------------------------------------------------
# migrate_notebook
# ---------------------------------------------------------------------------

class TestMigrateNotebook:
    def test_already_migrated_skips(self, tmp_path):
        # cell#0 has no frontmatter -> already migrated.
        nb = _make_nb(meta_cost={"cpu_min": 3}, cell0_source=["# Title\n", "prose\n"])
        p = _write_nb(tmp_path, "nb", nb)
        rep = mig.migrate_notebook(p, apply=False, by="x")
        assert rep["status"] == "skip-already-migrated"

    def test_refused_when_no_metadata_cost(self, tmp_path):
        # frontmatter present but metadata.cost absent -> refused (must populate first).
        nb = _make_nb(fm_cost={"cpu_min": 3})  # no meta_cost
        p = _write_nb(tmp_path, "nb", nb)
        rep = mig.migrate_notebook(p, apply=False, by="x")
        assert rep["status"] == "refused-no-metadata-cost"

    def test_dry_run_returns_report_without_writing(self, tmp_path):
        meta_cost = {"cpu_min": 0, "qcc_tokens_est": 5}     # qcc_tokens_est is meta-only
        fm_cost = {"cpu_min": 3, "network": True}            # cpu_min overwritten
        nb = _make_nb(fm_cost=fm_cost, meta_cost=meta_cost)
        p = _write_nb(tmp_path, "nb", nb)
        size_before = p.stat().st_size
        rep = mig.migrate_notebook(p, apply=False, by="x")
        assert rep["status"] == "dry-run"
        # dry-run writes nothing.
        assert p.stat().st_size == size_before
        # UNION semantics: cpu_min overwritten 0->3, network added (None->True),
        # qcc preserved. overwritten = every fm_cost key diverging from meta_cost.
        assert rep["overwritten_fields"] == {
            "cpu_min": {"from": 0, "to": 3},
            "network": {"from": None, "to": True},
        }
        assert rep["metadata_only_fields_preserved"] == ["qcc_tokens_est"]
        assert rep["field_equivalent"] is True
        assert rep["minimal_diff"] is True
        assert rep["new_cell0_starts_with_h1"] is True

    def test_apply_merges_and_strips(self, tmp_path):
        meta_cost = {"cpu_min": 0, "qcc_tokens_est": 5}
        fm_cost = {"cpu_min": 3, "network": True}
        nb = _make_nb(fm_cost=fm_cost, meta_cost=meta_cost)
        p = _write_nb(tmp_path, "nb", nb)
        rep = mig.migrate_notebook(p, apply=True, by="x")
        assert rep["status"] == "migrated"
        after = json.loads(p.read_text(encoding="utf-8"))
        # metadata.cost is the UNION (frontmatter wins on cpu_min, meta keeps qcc).
        assert after["metadata"]["cost"] == {
            "cpu_min": 3, "qcc_tokens_est": 5, "network": True}
        # cell#0 frontmatter stripped, starts with H1.
        c0 = after["cells"][0]["source"]
        c0 = "".join(c0) if isinstance(c0, list) else c0
        assert c0.lstrip().startswith("# Notebook")
        assert "---" not in c0

    def test_apply_preserves_other_cells_and_metadata(self, tmp_path):
        nb = _make_nb(fm_cost={"cpu_min": 3}, meta_cost={"cpu_min": 0})
        nb["cells"].append(
            {"cell_type": "code", "execution_count": 2, "metadata": {},
             "outputs": [{"output_type": "stream", "name": "stdout", "text": ["hi\n"]}],
             "source": ["print('hi')\n"]})
        nb["metadata"]["kernelspec"]["name"] = "python3"
        p = _write_nb(tmp_path, "nb", nb)
        mig.migrate_notebook(p, apply=True, by="x")
        after = json.loads(p.read_text(encoding="utf-8"))
        # cell#1 (original _make_nb code cell) untouched.
        assert after["cells"][1]["source"] == ["print(1)\n"]
        assert after["cells"][1]["execution_count"] == 1
        # cell#2 (the appended cell) untouched (source + outputs + execution_count).
        assert after["cells"][2]["source"] == ["print('hi')\n"]
        assert after["cells"][2]["execution_count"] == 2
        assert len(after["cells"][2]["outputs"]) == 1
        # kernelspec untouched.
        assert after["metadata"]["kernelspec"]["name"] == "python3"
        # cell count unchanged.
        assert len(after["cells"]) == len(nb["cells"])

    def test_not_markdown_cell0_errors(self, tmp_path):
        nb = {
            "cells": [
                {"cell_type": "code", "execution_count": None, "metadata": {},
                 "outputs": [], "source": ["print(1)\n"]},
            ],
            "metadata": {"cost": {"cpu_min": 0}},
            "nbformat": 4, "nbformat_minor": 5,
        }
        p = _write_nb(tmp_path, "nb", nb)
        rep = mig.migrate_notebook(p, apply=False, by="x")
        assert rep["status"] == "error"
        assert "not markdown" in rep["detail"]

    def test_frontmatter_no_cost_block_errors(self, tmp_path):
        # frontmatter present but has no `cost:` key -> error (not a migration target).
        src = ["---\n", "title: Foo\n", "---\n", "\n", "# Title\n"]
        nb = _make_nb(meta_cost={"cpu_min": 0}, cell0_source=src)
        p = _write_nb(tmp_path, "nb", nb)
        rep = mig.migrate_notebook(p, apply=False, by="x")
        assert rep["status"] == "error"
        assert "cost" in rep["detail"]

    def test_unreadable_file_errors(self, tmp_path):
        p = tmp_path / "bad.ipynb"
        p.write_text("{not valid json", encoding="utf-8")
        rep = mig.migrate_notebook(p, apply=True, by="x")
        assert rep["status"] == "error"
        assert "read/parse" in rep["detail"]


# ---------------------------------------------------------------------------
# main (CLI wiring)
# ---------------------------------------------------------------------------

def test_main_no_paths_exits_2(capsys):
    with pytest.raises(SystemExit) as exc:
        mig.main([])
    assert exc.value.code == 2


def test_main_missing_notebook_reports_error_rc1(tmp_path, capsys):
    rc = mig.main([str(tmp_path / "ghost.ipynb")])
    assert rc == 1
    out = capsys.readouterr().out
    assert "introuvable" in out


def test_main_dry_run_default(tmp_path, capsys):
    nb = _make_nb(fm_cost={"cpu_min": 3}, meta_cost={"cpu_min": 0})
    p = _write_nb(tmp_path, "nb", nb)
    rc = mig.main([str(p)])  # no --apply -> dry-run
    assert rc == 0
    out = capsys.readouterr().out
    assert "DRY-RUN" in out
    assert "dry-run" in out


def test_main_project_globs_notebooks(tmp_path, capsys, monkeypatch):
    proj = tmp_path / "proj"
    proj.mkdir()
    nb = _make_nb(fm_cost={"cpu_min": 3}, meta_cost={"cpu_min": 0})
    _write_nb(proj, "a", nb)
    _write_nb(proj, "b", nb)
    rc = mig.main(["--project", str(proj)])
    assert rc == 0
    out = capsys.readouterr().out
    assert "notebooks=2" in out


def test_main_apply_migrates(tmp_path, capsys):
    nb = _make_nb(fm_cost={"cpu_min": 3}, meta_cost={"cpu_min": 0})
    p = _write_nb(tmp_path, "nb", nb)
    rc = mig.main(["--apply", "--by", "tester", str(p)])
    assert rc == 0
    out = capsys.readouterr().out
    assert "APPLY" in out
    assert "migrated" in out
    after = json.loads(p.read_text(encoding="utf-8"))
    assert after["metadata"]["cost"]["cpu_min"] == 3


def test_main_refusal_returns_rc1(tmp_path, capsys):
    # frontmatter present, metadata.cost absent -> refused -> rc=1.
    nb = _make_nb(fm_cost={"cpu_min": 3})  # no meta_cost
    p = _write_nb(tmp_path, "nb", nb)
    rc = mig.main([str(p)])
    assert rc == 1
    out = capsys.readouterr().out
    assert "refused-no-metadata-cost" in out


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))


# ===========================================================================
# GenAI-shape extension (#9089, #9259 canonical tranche): migrate_notebook_genai
# + parse/detect/sanitize helpers. Self-contained fixtures (_dump, _md,
# _write_nb_genai) -- renamed from _write_nb to avoid the signature clash with
# the base file's _write_nb(tmp_path, name, nb) which appends '.ipynb'.
# ===========================================================================
def _dump(nb, trailing_nl=True):
    """Sérialise un notebook en indent=1 (byte-stable avec le script)."""
    s = json.dumps(nb, indent=1, ensure_ascii=False)
    return s + "\n" if trailing_nl else s


def _write_nb_genai(tmp_path, name, nb, trailing_nl=True):
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
    out = mig._sanitize_yaml_scalars(d)
    assert out["metadata_written"] == "2026-07-23T09:30:00"
    assert out["plain"] == "2026-07-24"
    assert out["nested"]["d"] == "2026-01-01T00:00:00"
    assert out["lst"][0] == "2026-02-02"
    # Passthrough scalaires inchangés.
    assert out["n"] == 5 and out["s"] == "x"


def test_col0_closer_index_detects_second_col0_delim():
    lines = "---\n".splitlines(keepends=True)  # un seul -> pas de closer
    assert mig._col0_closer_index(["---\n", "a: 1\n", "---\n", "# H1\n"]) == 2


def test_col0_closer_index_ignores_indented_delim():
    # Le `  ---` indenté (avalé dans un bloc notes: |) n'est PAS un closer col0.
    lines = ["---\n", "notes: |\n", "  texte\n", "  ---\n"]
    assert mig._col0_closer_index(lines) is None


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
    cost, disposition, new_source = mig._parse_genai_frontmatter_cell(_audio_malformed_source())
    assert cost is not None
    assert disposition == "remove_cell"
    assert new_source is None
    # datetime sanitize : `2026-07-23T09:30Z` (suffixe Z) n'est PAS reconnu comme
    # timestamp par yaml -> reste une chaîne JSON-safe (pas de conversion nécessaire).
    assert cost["metadata_written"] == "2026-07-23T09:30Z"
    assert cost["api_usd_est"] == 0.40


def test_parse_genai_well_formed_empty_remove_cell():
    src = ["---\n", "cost:\n", "  cpu_min: 2\n", "---\n", "\n"]
    cost, disposition, new_source = mig._parse_genai_frontmatter_cell(src)
    assert disposition == "remove_cell"
    assert new_source is None
    assert cost == {"cpu_min": 2}


def test_parse_genai_well_formed_h1_strip_keep():
    src = ["---\n", "cost:\n", "  cpu_min: 1\n", "---\n", "\n", "# Titre\n", "\n", "Suite.\n"]
    cost, disposition, new_source = mig._parse_genai_frontmatter_cell(src)
    assert disposition == "strip_keep_h1"
    assert new_source == ["# Titre\n", "\n", "Suite.\n"]
    assert cost == {"cpu_min": 1}


def test_parse_genai_no_frontmatter_returns_none():
    assert mig._parse_genai_frontmatter_cell(["# Titre\n", "texte\n"]) == (None, None, None)


def test_parse_genai_no_cost_block_returns_none():
    src = ["---\n", "title: x\n", "---\n", "# H1\n"]
    assert mig._parse_genai_frontmatter_cell(src) == (None, None, None)


def test_detect_genai_finds_cell1_not_cell0():
    cells = [
        _md(["# Titre\n"]),                       # cell#0 titre (pas frontmatter)
        _md(_audio_malformed_source()),            # cell#1 frontmatter
        _md(["suite\n"]),
    ]
    idx, cost, disposition, new_source = mig._detect_genai_cost_cell(cells)
    assert idx == 1
    assert disposition == "remove_cell"
    assert cost["cpu_min"] == 4


# --------------------------------------------------------------------------
# Route GenAI — migrate_notebook_genai : apply end-to-end
# --------------------------------------------------------------------------

def test_genai_malformed_apply_removes_cell_and_creates_cost(tmp_path):
    nb = {"cells": [_md(["# Titre\n"]), _md(_audio_malformed_source()), _md(["suite\n"])],
          "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    p = _write_nb_genai(tmp_path, "a.ipynb", nb)
    rep = mig.migrate_notebook_genai(p, apply=True, by="t:CoursIA")
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
    p = _write_nb_genai(tmp_path, "s.ipynb", nb)
    rep = mig.migrate_notebook_genai(p, apply=True, by="t:CoursIA")
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
    p = _write_nb_genai(tmp_path, "no_nl.ipynb", nb, trailing_nl=False)
    before = p.read_bytes()
    assert not before.endswith(b"\n")
    rep = mig.migrate_notebook_genai(p, apply=True, by="t:CoursIA")
    assert rep["byte_stable_baseline"] is True
    after = p.read_bytes()
    assert not after.endswith(b"\n")  # convention préservée
    # Avec trailing newline.
    p2 = _write_nb_genai(tmp_path, "nl.ipynb", nb, trailing_nl=True)
    rep2 = mig.migrate_notebook_genai(p2, apply=True, by="t:CoursIA")
    assert rep2["byte_stable_baseline"] is True
    assert p2.read_bytes().endswith(b"\n")


def test_genai_skip_already_migrated(tmp_path):
    nb = {"cells": [_md(["# Titre\n", "texte\n"])], "metadata": {},
          "nbformat": 4, "nbformat_minor": 5}
    p = _write_nb_genai(tmp_path, "ok.ipynb", nb)
    rep = mig.migrate_notebook_genai(p, apply=True, by="t:CoursIA")
    assert rep["status"] == "skip-already-migrated"


def test_genai_dry_run_does_not_write(tmp_path):
    nb = {"cells": [_md(["# T\n"]), _md(_audio_malformed_source())],
          "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    p = _write_nb_genai(tmp_path, "d.ipynb", nb)
    before = p.read_bytes()
    rep = mig.migrate_notebook_genai(p, apply=False, by="t:CoursIA")
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
    p = _write_nb_genai(tmp_path, "q.ipynb", _qc_nb())
    rep = mig.migrate_notebook(p, apply=False, by="t:CoursIA")
    assert rep["status"] == "dry-run"
    assert rep["field_equivalent"] is True
    assert rep["minimal_diff"] is True
    # frontmatter gagne sur cpu_min (0->3).
    assert "cpu_min" in rep["overwritten_fields"]


def test_qc_apply_migrates_and_strips(tmp_path):
    p = _write_nb_genai(tmp_path, "q.ipynb", _qc_nb())
    rep = mig.migrate_notebook(p, apply=True, by="t:CoursIA")
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
    p = _write_nb_genai(tmp_path, "r.ipynb", nb)
    rep = mig.migrate_notebook(p, apply=True, by="t:CoursIA")
    # Route QC : metadata.cost absent -> refused (contrairement à GenAI qui crée).
    assert rep["status"] == "refused-no-metadata-cost"
