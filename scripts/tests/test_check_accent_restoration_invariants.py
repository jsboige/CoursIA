"""Tests for check_accent_restoration_invariants (ruling #16638 point 1).

Validated by false negatives: the #18814 capitalisation defect MUST be
flagged, a clean restoration MUST pass, a code edit MUST be reported.
"""

import json
import subprocess as subprocess_mod
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "notebook_tools"))
import check_accent_restoration_invariants as cri  # noqa: E402


def _nb(cells: list[dict]) -> dict:
    return {"cells": cells}


def _md(src: str) -> dict:
    return {"cell_type": "markdown", "source": [src]}


def _code(src: str) -> dict:
    return {"cell_type": "code", "source": [src]}


class TestCellInvariantViolations:
    def test_clean_restoration_passes(self):
        """theoreme -> théorème: accents only, no finding."""
        base = _nb([_md("Le theoreme de Bayes s'applique ici."), _code("x = 1")])
        head = _nb([_md("Le théorème de Bayes s'applique ici."), _code("x = 1")])
        assert cri._cell_invariant_violations(base, head) == []

    def test_18814_capitalisation_defect_is_flagged(self):
        """The founding defect: 'la meme convention' -> 'la Même convention'."""
        base = _nb([_md("On suit la meme convention que precedemment.")])
        head = _nb([_md("On suit la Même convention que precedemment.")])
        findings = cri._cell_invariant_violations(base, head)
        assert len(findings) == 1
        assert findings[0]["kind"] == "MARKDOWN_INVARIANT"
        assert findings[0]["cell"] == 0

    def test_case_preserved_by_strip_means_case_change_breaks_invariant(self):
        """Lowercase->capital mid-word, no accent involved at all."""
        base = _nb([_md("le second parametre vaut 2")])
        head = _nb([_md("le second Parametre vaut 2")])
        findings = cri._cell_invariant_violations(base, head)
        assert [f["kind"] for f in findings] == ["MARKDOWN_INVARIANT"]

    def test_rewording_is_flagged(self):
        """A real word change (not accents) breaks the invariant."""
        base = _nb([_md("Le modele est simple")])
        head = _nb([_md("Le modèle est très simple")])
        assert [f["kind"] for f in cri._cell_invariant_violations(base, head)] == [
            "MARKDOWN_INVARIANT"
        ]

    def test_code_cell_edit_is_flagged(self):
        """A code edit produces no markdown diff but must be reported."""
        base = _nb([_md("texte"), _code("resultat = 1")])
        head = _nb([_md("texte"), _code("resultat = 2")])
        findings = cri._cell_invariant_violations(base, head)
        assert [f["kind"] for f in findings] == ["CODE_MODIFIED"]
        assert findings[0]["cell"] == 1

    def test_cell_count_change_is_flagged(self):
        base = _nb([_md("a")])
        head = _nb([_md("a"), _md("b")])
        findings = cri._cell_invariant_violations(base, head)
        assert [f["kind"] for f in findings] == ["CELL_COUNT_CHANGED"]

    def test_cell_type_change_is_flagged(self):
        base = _nb([_md("theoreme")])
        head = _nb([_code("theoreme")])
        assert [f["kind"] for f in cri._cell_invariant_violations(base, head)] == [
            "TYPE_CHANGED"
        ]

    def test_list_and_string_sources_both_handled(self):
        """nbformat source is list-of-lines; some tools emit a plain string."""
        base = _nb([{"cell_type": "markdown", "source": "theoreme ok"}])
        head = _nb([{"cell_type": "markdown", "source": ["théorème ok"]}])
        assert cri._cell_invariant_violations(base, head) == []


class TestLoadBaseNotebook:
    def test_git_show_roundtrip(self, tmp_path, monkeypatch):
        """base notebook is read via git show sha:relpath from the repo root."""
        nb = {"cells": [{"cell_type": "markdown", "source": ["theoreme"]}]}

        def fake_run(cmd, **kwargs):
            if cmd[:3] == ["git", "rev-parse", "--show-toplevel"]:
                return subprocess_mod.CompletedProcess(cmd, 0, stdout=str(tmp_path))
            assert cmd[:4] == ["git", "-C", str(tmp_path), "show"]
            assert cmd[4] == "abc123:dir/nb.ipynb"
            return subprocess_mod.CompletedProcess(
                cmd, 0, stdout=json.dumps(nb, ensure_ascii=False)
            )

        monkeypatch.setattr(subprocess_mod, "run", fake_run)
        nb_path = tmp_path / "dir" / "nb.ipynb"
        loaded = cri._load_base_notebook(nb_path, "abc123")
        assert loaded == nb

    def test_git_show_failure_raises(self, tmp_path, monkeypatch):
        """A missing sha at the base path surfaces as CalledProcessError."""

        def fake_run(cmd, **kwargs):
            if cmd[:3] == ["git", "rev-parse", "--show-toplevel"]:
                return subprocess_mod.CompletedProcess(cmd, 0, stdout=str(tmp_path))
            raise subprocess_mod.CalledProcessError(128, cmd)

        monkeypatch.setattr(subprocess_mod, "run", fake_run)
        with pytest.raises(subprocess_mod.CalledProcessError):
            cri._load_base_notebook(tmp_path / "nb.ipynb", "deadbeef")


class TestMain:
    def _write_nb(self, tmp_path, cells: list[dict]) -> Path:
        path = tmp_path / "nb.ipynb"
        path.write_text(json.dumps(_nb(cells), ensure_ascii=False), encoding="utf-8")
        return path

    def test_clean_trancho_exits_zero(self, tmp_path, monkeypatch, capsys):
        path = self._write_nb(tmp_path, [_md("Le théorème tient.")])
        monkeypatch.setattr(
            cri, "_load_base_notebook", lambda p, sha: _nb([_md("Le theoreme tient.")])
        )
        rc = cri.main([str(path), "--base-sha", "abc", "--fail-on-findings"])
        assert rc == 0
        assert "TOTAL 0" in capsys.readouterr().out

    def test_finding_exits_two(self, tmp_path, monkeypatch, capsys):
        """The #18814 defect, end to end through main."""
        path = self._write_nb(tmp_path, [_md("la Même convention")])
        monkeypatch.setattr(
            cri, "_load_base_notebook", lambda p, sha: _nb([_md("la meme convention")])
        )
        rc = cri.main([str(path), "--base-sha", "abc", "--fail-on-findings"])
        assert rc == 2
        out = capsys.readouterr().out
        assert "MARKDOWN_INVARIANT cell #0" in out

    def test_json_report_shape(self, tmp_path, monkeypatch, capsys):
        path = self._write_nb(tmp_path, [_md("le Parametre")])
        monkeypatch.setattr(
            cri, "_load_base_notebook", lambda p, sha: _nb([_md("le parametre")])
        )
        rc = cri.main([str(path), "--base-sha", "abc", "--json"])
        assert rc == 0
        report = json.loads(capsys.readouterr().out)
        assert report["total"] == 1
        assert report["findings"][0]["kind"] == "MARKDOWN_INVARIANT"
        assert report["base_sha"] == "abc"

    def test_missing_file_exits_one(self, tmp_path):
        rc = cri.main([str(tmp_path / "nope.ipynb"), "--base-sha", "abc"])
        assert rc == 1
