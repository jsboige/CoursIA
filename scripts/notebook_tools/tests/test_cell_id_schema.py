"""Régressions pour la réparation et le ratchet des ids nbformat."""

import json
import re
import subprocess
import sys
from pathlib import Path

TOOLS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TOOLS))

from check_cell_id_invalid_ratchet import compare, invalid_count, main as ratchet_main  # noqa: E402
import fix_cell_ids as fixer  # noqa: E402
from fix_cell_ids import repair_text  # noqa: E402


def _notebook(cells):
    return '{\n "cells": [\n' + ",\n".join(cells) + '\n ],\n "metadata": {"k": "v"},\n "nbformat": 4,\n "nbformat_minor": 5\n}\n'


def _cell(cell_type="code", id_line=None):
    prefix = '  {\n   "cell_type": "' + cell_type + '",\n'
    if id_line is not None:
        prefix += '   "id": ' + id_line + ',\n'
    return prefix + '   "metadata": {"tag": "keep"},\n   "execution_count": 3,\n   "outputs": [{"output_type": "stream", "text": "keep\\n"}],\n   "source": ["print(1)\\n"]\n  }'


def test_fixer_changes_only_id_lines_preserves_other_bytes_and_is_idempotent(monkeypatch):
    monkeypatch.setattr(fixer, "_external_references", lambda *_: [])
    raw = _notebook([
        _cell(id_line=None),
        _cell("markdown", '"bad id!"'),
        _cell("code", '""'),
        _cell("code", "42"),
        _cell("code", '"kept0001"'),
        _cell("code", '"kept0001"'),
    ])
    fixed = repair_text(raw, Path("fixture.ipynb"))
    assert repair_text(fixed, Path("fixture.ipynb")) == fixed
    assert invalid_count(fixed) == 0
    before = raw.splitlines()
    after = fixed.splitlines()
    assert len(after) == len(before) + 1  # one missing id property was added
    # All non-id lines, including source, outputs and metadata, are byte-identical.
    strip_ids = lambda lines: [line for line in lines if '"id":' not in line]
    assert strip_ids(before) == strip_ids(after)
    id_lines = [line for line in after if '"id":' in line]
    assert all(re.fullmatch(r'\s*"id": "[A-Za-z0-9_-]{1,64}",?', line) for line in id_lines)
    ids = [cell["id"] for cell in json.loads(fixed)["cells"]]
    assert ids[4] == "kept0001" and ids[5] != "kept0001"


def test_external_reference_blocks_renaming_existing_invalid_id(monkeypatch):
    monkeypatch.setattr(fixer, "_external_references", lambda *_: ["translations.csv:1:bad id!"])
    raw = _notebook([_cell(id_line='"bad id!"')])
    try:
        repair_text(raw, Path("fixture.ipynb"))
    except ValueError as exc:
        assert "référencé hors du carnet" in str(exc)
    else:
        raise AssertionError("une référence externe doit bloquer le renommage")


def test_fixer_cli_preserves_crlf_bytes_and_is_idempotent(tmp_path):
    raw = _notebook([_cell(id_line=None)]).replace("\n", "\r\n").encode("utf-8")
    path = tmp_path / "crlf.ipynb"
    path.write_bytes(raw)
    assert fixer.main([str(path)]) == 0
    fixed = path.read_bytes()
    assert b"\r\n" in fixed
    assert not re.search(rb"(?<!\r)\n", fixed)
    assert [line for line in raw.split(b"\r\n") if b'"id":' not in line] == [
        line for line in fixed.split(b"\r\n") if b'"id":' not in line
    ]
    assert fixer.main([str(path)]) == 0
    assert path.read_bytes() == fixed
    assert invalid_count(fixed.decode("utf-8")) == 0


def test_fixer_uses_top_level_cells_when_metadata_also_has_cells():
    raw = '{"metadata":{"cells":[{"cell_type":"markdown","source":["keep"]}]},' \
          '"cells":[{"cell_type":"code","metadata":{"keep":true},"source":[]}],' \
          '"nbformat":4,"nbformat_minor":5}'
    fixed = repair_text(raw, Path("metadata-cells.ipynb"))
    result = json.loads(fixed)
    assert result["metadata"]["cells"] == [{"cell_type": "markdown", "source": ["keep"]}]
    assert len(result["cells"]) == 1
    assert result["cells"][0]["id"]
    assert result["cells"][0]["source"] == []


def test_fixer_supports_compact_json_without_corrupting_prefix(tmp_path):
    raw = '{"cells":[{"cell_type":"code","metadata":{"keep":true},"source":[]}],' \
          '"metadata":{"keep":"root"},"nbformat":4,"nbformat_minor":5}'
    path = tmp_path / "compact.ipynb"
    path.write_text(raw, encoding="utf-8", newline="")
    assert fixer.main([str(path)]) == 0
    with path.open("r", encoding="utf-8", newline="") as handle:
        fixed = handle.read()
    assert json.loads(fixed)["cells"][0]["metadata"] == {"keep": True}
    assert json.loads(fixed)["metadata"] == {"keep": "root"}
    assert invalid_count(fixed) == 0
    assert fixer.main([str(path)]) == 0
    with path.open("r", encoding="utf-8", newline="") as handle:
        assert handle.read() == fixed


def test_absolute_notebook_path_is_excluded_but_external_csv_blocks(tmp_path, monkeypatch):
    def git(*args):
        subprocess.run(["git", *args], cwd=tmp_path, check=True,
                       capture_output=True, text=True, encoding="utf-8")

    monkeypatch.chdir(tmp_path)
    git("init", "-q")
    git("config", "user.email", "cell-id@example.invalid")
    git("config", "user.name", "cell-id test")
    path = tmp_path / "nb.ipynb"
    raw = _notebook([_cell(id_line='"bad id!"')])
    path.write_text(raw, encoding="utf-8")
    git("add", "nb.ipynb")
    git("commit", "-q", "-m", "carnet")

    # Le grep voit l'id dans le carnet lui-même, qui doit être exclu même si
    # le CLI reçoit un chemin absolu.
    assert invalid_count(repair_text(raw, path)) == 0
    (tmp_path / "translations.csv").write_text("nb.ipynb,bad id!\n", encoding="utf-8")
    git("add", "translations.csv")
    git("commit", "-q", "-m", "référence de traduction")
    try:
        repair_text(raw, path)
    except ValueError as exc:
        assert "référencé hors du carnet" in str(exc)
    else:
        raise AssertionError("la référence du CSV doit bloquer le renommage")


def test_ratchet_allows_clean_base_corruption_and_improvement():
    assert invalid_count(_notebook([_cell(id_line='"ok000001"')])) == 0
    assert invalid_count(_notebook([_cell(id_line=None)])) == 1
    assert compare(0, 0)
    assert not compare(0, 1)  # nouvelle corruption
    assert compare(2, 1)      # amélioration de l'historique du carnet
    assert compare(2, 2)      # base historique inchangée


def test_ratchet_preserves_legacy_contract_but_rejects_format_downgrade():
    legacy = json.loads(_notebook([_cell(id_line=None)]))
    legacy["nbformat_minor"] = 4
    legacy_text = json.dumps(legacy)
    modern_clean = _notebook([_cell(id_line='"ok000001"')])
    modern_invalid = _notebook([_cell(id_line=None)])

    assert invalid_count(legacy_text) is None
    assert compare(None, None)  # ancien carnet non migré
    assert compare(None, 0)      # migration valide vers un format à ids
    assert not compare(None, 1)  # migration sans ids conformes
    assert not compare(0, None)  # retour 4.5 -> 4.4 ne contourne pas le ratchet
    assert compare(0, invalid_count(modern_clean))
    assert not compare(0, invalid_count(modern_invalid))


def test_ratchet_cli_compares_each_changed_notebook_to_its_git_base(tmp_path, monkeypatch):
    def git(*args):
        subprocess.run(["git", *args], cwd=tmp_path, check=True,
                       capture_output=True, text=True, encoding="utf-8")

    monkeypatch.chdir(tmp_path)
    git("init", "-q")
    git("config", "user.email", "cell-id@example.invalid")
    git("config", "user.name", "cell-id test")
    nb_path = tmp_path / "nb.ipynb"
    nb_path.write_text(_notebook([_cell(id_line='"valid001"')]), encoding="utf-8")
    git("add", "nb.ipynb")
    git("commit", "-q", "-m", "base saine")
    clean_base = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
    assert ratchet_main([clean_base]) == 0

    nb_path.write_text(_notebook([_cell(id_line=None)]), encoding="utf-8")
    git("add", "nb.ipynb")
    git("commit", "-q", "-m", "corruption nouvelle")
    broken_base = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
    assert ratchet_main([clean_base]) == 1

    nb_path.write_text(_notebook([_cell(id_line='"valid001"')]), encoding="utf-8")
    git("add", "nb.ipynb")
    git("commit", "-q", "-m", "correction")
    assert ratchet_main([broken_base]) == 0

    legacy = json.loads(nb_path.read_text(encoding="utf-8"))
    legacy["nbformat_minor"] = 4
    nb_path.write_text(json.dumps(legacy), encoding="utf-8")
    git("add", "nb.ipynb")
    git("commit", "-q", "-m", "retour au format ancien")
    assert ratchet_main([broken_base]) == 1
