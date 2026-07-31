"""Tests for scripts/audit/migrate_cost_frontmatter_to_metadata.py.

Covers two shapes via the --shape flag:
  - QC path (migrate_notebook): cell#0 well-formed frontmatter, metadata.cost
    PRESENT (union), strip keep H1. Regression guard for the original contract
    (issues #8904 / #8056).
  - GenAI path (migrate_genai_notebook, #9089 follow-up of #9088): cell#0 OR
    cell#1, malformed YAML tolerated, metadata.cost ABSENT -> CREATE, top-level
    `notes:` -> metadata.cost.notes (guard #8921-4), frontmatter-only cell ->
    REMOVE, datetime sanitization.
  - auto dispatch (GenAI-first superset, QC fallback).

Fixtures are built as raw nb dicts dumped with the script's own byte-stable
serializer (json.dumps(indent=1, ensure_ascii=False)+'\\n'), so the
byte_stable_baseline gate holds without depending on nbformat.write formatting.
"""
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
SCRIPT_PATH = HERE.parent / "migrate_cost_frontmatter_to_metadata.py"


def _load():
    spec = importlib.util.spec_from_file_location("migrate_cost_frontmatter", SCRIPT_PATH)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _cell(ct, src, **kw):
    c = {"cell_type": ct, "source": src, "metadata": {}}
    if ct == "code":
        c["execution_count"] = kw.get("execution_count", 1)
        c["outputs"] = kw.get("outputs", [])
    return c


def _write_nb(path, cells, metadata=None):
    nb = {"cells": cells, "metadata": metadata or {}, "nbformat": 4, "nbformat_minor": 5}
    path.write_bytes((json.dumps(nb, indent=1, ensure_ascii=False) + "\n").encode("utf-8"))
    return path


# ---------------------------------------------------------------------------
# QC path (regression)
# ---------------------------------------------------------------------------

def test_qc_union_and_strip(tmp_path):
    """cell#0 well-formed frontmatter + metadata.cost present -> union + strip keep H1."""
    mod = _load()
    fm = "---\ncost:\n  api_provider: openai\n  api_usd_est: 0.5\n---\n# Title\n"
    cells = [_cell("markdown", fm), _cell("code", "x=1")]
    p = _write_nb(tmp_path / "qc.ipynb", cells, metadata={"cost": {"qcc_tokens_est": 1200, "api_provider": "local"}})
    rep = mod.migrate_notebook(p, apply=False, by="test")
    assert rep["status"] == "dry-run"
    assert rep["field_equivalent"] is True
    assert rep["minimal_diff"] is True
    assert rep["new_cell0_starts_with_h1"] is True
    # frontmatter api_provider overwrites metadata local; qcc_tokens_est preserved.
    assert "api_provider" in rep["overwritten_fields"]
    assert "qcc_tokens_est" in rep["metadata_only_fields_preserved"]


def test_qc_refuses_when_metadata_cost_absent(tmp_path):
    mod = _load()
    fm = "---\ncost:\n  api_provider: openai\n---\n# Title\n"
    p = _write_nb(tmp_path / "q.ipynb", [_cell("markdown", fm), _cell("code", "x=1")])
    rep = mod.migrate_notebook(p, apply=False, by="test")
    assert rep["status"] == "refused-no-metadata-cost"


def test_qc_skip_already_migrated(tmp_path):
    mod = _load()
    p = _write_nb(tmp_path / "q.ipynb", [_cell("markdown", "# Title\n"), _cell("code", "x=1")])
    rep = mod.migrate_notebook(p, apply=False, by="test")
    assert rep["status"] == "skip-already-migrated"


def test_qc_apply_byte_stable(tmp_path):
    mod = _load()
    fm = "---\ncost:\n  api_usd_est: 0.5\n---\n# Title\n"
    cells = [_cell("markdown", fm), _cell("code", "x=1")]
    p = _write_nb(tmp_path / "q.ipynb", cells, metadata={"cost": {"cpu_min": 1}})
    rep = mod.migrate_notebook(p, apply=True, by="test")
    assert rep["status"] == "migrated"
    out = json.loads(p.read_text(encoding="utf-8"))
    assert out["metadata"]["cost"] == {"cpu_min": 1, "api_usd_est": 0.5}
    assert out["cells"][0]["source"].startswith("# Title")


# ---------------------------------------------------------------------------
# GenAI path (new, #9089)
# ---------------------------------------------------------------------------

def test_genai_cell1_frontmatter_only_remove(tmp_path):
    """Audio/Image shape: frontmatter in cell#1, no trailing -> REMOVE the cell,
    CREATE metadata.cost (was absent)."""
    mod = _load()
    fm = "---\ntitle: Audio\ncost:\n  api_provider: openai\n  api_usd_est: 0.3\n---\n"
    cells = [_cell("markdown", "# Title\n"), _cell("markdown", fm), _cell("code", "x=1")]
    p = _write_nb(tmp_path / "g.ipynb", cells)
    rep = mod.migrate_genai_notebook(p, apply=True, by="test")
    assert rep["status"] == "migrated-genai"
    assert rep["fm_cell"] == "#1"
    assert rep["action"] == "remove-cell"
    out = json.loads(p.read_text(encoding="utf-8"))
    assert len(out["cells"]) == 2  # frontmatter cell removed
    assert out["cells"][0]["source"] == "# Title\n"
    assert out["metadata"]["cost"]["api_provider"] == "openai"
    assert out["metadata"]["cost"]["api_usd_est"] == 0.3


def test_genai_cell0_trailing_strip_keep_h1(tmp_path):
    """Claudish/SK shape: frontmatter + trailing H1 in cell#0 -> strip, keep H1."""
    mod = _load()
    fm = "---\ntitle: X\ncost:\n  api_provider: anthropic\n---\n# Real Title\nintro.\n"
    p = _write_nb(tmp_path / "g.ipynb", [_cell("markdown", fm), _cell("code", "x=1")])
    rep = mod.migrate_genai_notebook(p, apply=True, by="test")
    assert rep["status"] == "migrated-genai"
    assert rep["action"] == "strip-keep-trailing"
    assert rep["kept_cell_starts_with_h1"] is True
    out = json.loads(p.read_text(encoding="utf-8"))
    assert out["cells"][0]["source"].startswith("# Real Title")


def test_genai_malformed_yaml_tolerant(tmp_path):
    """Malformed frontmatter: closing `---` indented, swallowed by `notes: |`.
    yaml.safe_load is tolerant; whole cell is frontmatter -> remove-cell."""
    mod = _load()
    # The closing --- is indented (2 spaces) -> no col-0 closer -> malformed.
    fm = "---\ntitle: Audio\ncost:\n  api_provider: openai\nnotes: |\n  some note\n  ---\n"
    p = _write_nb(tmp_path / "g.ipynb", [_cell("markdown", "# T\n"), _cell("markdown", fm), _cell("code", "x=1")])
    rep = mod.migrate_genai_notebook(p, apply=False, by="test")
    assert rep["status"] == "dry-run-genai"
    assert rep["fm_cell"] == "#1"
    assert rep["action"] == "remove-cell"
    assert rep["notes_migrated"] is True


def test_genai_notes_migrated_to_metadata_cost_notes(tmp_path):
    """Guard #8921-4 ('cas Claudish'): a top-level notes: block migrates to
    metadata.cost.notes, not dropped."""
    mod = _load()
    fm = "---\ncost:\n  api_provider: openai\nnotes: |\n  This is a substantive note.\n---\n# T\n"
    p = _write_nb(tmp_path / "g.ipynb", [_cell("markdown", fm), _cell("code", "x=1")])
    rep = mod.migrate_genai_notebook(p, apply=True, by="test")
    assert rep["status"] == "migrated-genai"
    out = json.loads(p.read_text(encoding="utf-8"))
    assert "notes" in out["metadata"]["cost"]
    assert "substantive note" in out["metadata"]["cost"]["notes"]


def test_genai_notes_not_overwritten_when_metadata_has_it(tmp_path):
    """If metadata.cost.notes already exists, frontmatter notes does NOT overwrite."""
    mod = _load()
    fm = "---\ncost:\n  api_provider: openai\nnotes: frontmatter note\n---\n# T\n"
    p = _write_nb(tmp_path / "g.ipynb", [_cell("markdown", fm), _cell("code", "x=1")],
                  metadata={"cost": {"api_provider": "openai", "notes": "existing note"}})
    rep = mod.migrate_genai_notebook(p, apply=True, by="test")
    assert rep["status"] == "migrated-genai"
    out = json.loads(p.read_text(encoding="utf-8"))
    assert out["metadata"]["cost"]["notes"] == "existing note"


def test_genai_metadata_cost_present_union(tmp_path):
    """metadata.cost present -> union (existing fields preserved, frontmatter wins on overlap)."""
    mod = _load()
    fm = "---\ncost:\n  api_provider: openai\n  api_usd_est: 0.5\n---\n# T\n"
    p = _write_nb(tmp_path / "g.ipynb", [_cell("markdown", fm), _cell("code", "x=1")],
                  metadata={"cost": {"api_provider": "local", "extra_field": 42}})
    rep = mod.migrate_genai_notebook(p, apply=True, by="test")
    out = json.loads(p.read_text(encoding="utf-8"))
    assert out["metadata"]["cost"]["api_provider"] == "openai"  # frontmatter wins
    assert out["metadata"]["cost"]["extra_field"] == 42  # existing preserved
    assert out["metadata"]["cost"]["api_usd_est"] == 0.5


def test_genai_datetime_sanitized(tmp_path):
    """ISO timestamp metadata_written auto-parsed by yaml -> datetime -> sanitized to ISO string."""
    mod = _load()
    fm = "---\ncost:\n  api_provider: openai\n  metadata_written: 2026-07-23T09:30:00Z\n---\n# T\n"
    p = _write_nb(tmp_path / "g.ipynb", [_cell("markdown", fm), _cell("code", "x=1")])
    rep = mod.migrate_genai_notebook(p, apply=True, by="test")
    assert rep["status"] == "migrated-genai"
    out = json.loads(p.read_text(encoding="utf-8"))
    # Must be a JSON string, not a datetime object.
    assert isinstance(out["metadata"]["cost"]["metadata_written"], str)
    assert "2026-07-23" in out["metadata"]["cost"]["metadata_written"]


def test_genai_code_sha_and_output_count_unchanged(tmp_path):
    """Removing the frontmatter cell must not touch code source or outputs."""
    mod = _load()
    fm = "---\ncost:\n  api_provider: openai\n---\n"
    code_out = [{"output_type": "stream", "name": "stdout", "text": ["hello\n"]}]
    cells = [_cell("markdown", "# T\n"), _cell("markdown", fm),
             _cell("code", "print('hello')", execution_count=1, outputs=code_out)]
    p = _write_nb(tmp_path / "g.ipynb", cells)
    rep = mod.migrate_genai_notebook(p, apply=True, by="test")
    assert rep["code_sha_unchanged"] is True
    assert rep["output_count_unchanged"] is True
    assert rep["minimal_diff"] is True
    out = json.loads(p.read_text(encoding="utf-8"))
    # The single code cell kept byte-identical with its output.
    code_cells = [c for c in out["cells"] if c["cell_type"] == "code"]
    assert len(code_cells) == 1
    assert code_cells[0]["outputs"] == code_out
    assert code_cells[0]["source"] == "print('hello')"


def test_genai_idempotent_skip(tmp_path):
    """Re-running on an already-migrated notebook -> skip."""
    mod = _load()
    p = _write_nb(tmp_path / "g.ipynb", [_cell("markdown", "# T\n"), _cell("code", "x=1")])
    rep = mod.migrate_genai_notebook(p, apply=False, by="test")
    assert rep["status"] == "skip-no-genai-frontmatter"


def test_genai_source_list_type_preserved(tmp_path):
    """When source is a list, the kept trailing content stays a list (no collapse churn)."""
    mod = _load()
    fm_list = ["---\n", "cost:\n", "  api_provider: openai\n", "---\n", "# Title\n", "body\n"]
    p = _write_nb(tmp_path / "g.ipynb", [_cell("markdown", fm_list), _cell("code", "x=1")])
    rep = mod.migrate_genai_notebook(p, apply=True, by="test")
    assert rep["status"] == "migrated-genai"
    out = json.loads(p.read_text(encoding="utf-8"))
    assert isinstance(out["cells"][0]["source"], list)
    assert out["cells"][0]["source"][0].startswith("# Title")


# ---------------------------------------------------------------------------
# auto dispatch
# ---------------------------------------------------------------------------

def test_auto_routes_genai_cell1(tmp_path):
    """auto (GenAI-first) routes a cell#1 GenAI notebook to the GenAI path."""
    mod = _load()
    fm = "---\ncost:\n  api_provider: openai\n---\n"
    p = _write_nb(tmp_path / "g.ipynb", [_cell("markdown", "# T\n"), _cell("markdown", fm), _cell("code", "x=1")])
    rep = mod._dispatch(p, apply=False, by="test", shape="auto")
    assert rep["status"] == "dry-run-genai"


def test_auto_fallback_qc_for_already_migrated(tmp_path):
    """auto falls back to QC (skip-already-migrated) when no GenAI frontmatter."""
    mod = _load()
    p = _write_nb(tmp_path / "g.ipynb", [_cell("markdown", "# T\n"), _cell("code", "x=1")])
    rep = mod._dispatch(p, apply=False, by="test", shape="auto")
    assert rep["status"] == "skip-already-migrated"


def test_auto_handles_qc_quantbook_via_superset(tmp_path):
    """auto handles a QC quantbook (cell#0 + metadata.cost present) via the GenAI
    superset path -> same union result as QC."""
    mod = _load()
    fm = "---\ncost:\n  api_provider: openai\n  api_usd_est: 0.5\n---\n# Title\n"
    p = _write_nb(tmp_path / "q.ipynb", [_cell("markdown", fm), _cell("code", "x=1")],
                  metadata={"cost": {"qcc_tokens_est": 1200}})
    rep = mod._dispatch(p, apply=True, by="test", shape="auto")
    assert rep["status"] == "migrated-genai"
    out = json.loads(p.read_text(encoding="utf-8"))
    assert out["metadata"]["cost"]["qcc_tokens_est"] == 1200
    assert out["metadata"]["cost"]["api_provider"] == "openai"
