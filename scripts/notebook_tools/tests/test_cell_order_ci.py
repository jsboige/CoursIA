"""Tests for scripts/notebook_tools/cell_order_ci.py — per-PR regression gate.

The gate fails only on a *regression* (a HIGH finding in head that was not in
base). Pre-existing findings do not block; a new notebook (no base) must be clean.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from cell_order_ci import regressions, high_signatures, main  # noqa: E402


def _md(source: str) -> dict:
    return {"cell_type": "markdown", "source": [source]}


def _write(path: Path, cells: list[dict]) -> Path:
    nb = {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    path.write_text(json.dumps(nb), encoding="utf-8")
    return path


# A notebook with a genuine backwards section jump (## 2 after ## 3).
_BAD = [_md("## 2. A"), _md("## 3. B"), _md("## 2. oops")]
# A clean notebook.
_CLEAN = [_md("## 1. A"), _md("## 2. B"), _md("## 3. C")]


class TestHighSignatures:
    def test_none_base_is_empty(self):
        assert high_signatures("NONE") == set()
        assert high_signatures(None) == set()

    def test_missing_path_raises(self, tmp_path):
        # A provided path that does not exist is a usage error (git refs are
        # not file paths): fail loudly, never report "no regression" silently.
        with pytest.raises(SystemExit, match="n'existe pas"):
            high_signatures(str(tmp_path / "absent.ipynb"))

    def test_clean_has_no_high(self, tmp_path):
        p = _write(tmp_path / "c.ipynb", _CLEAN)
        assert high_signatures(str(p)) == set()

    def test_bad_has_high(self, tmp_path):
        p = _write(tmp_path / "b.ipynb", _BAD)
        sigs = high_signatures(str(p))
        assert any(cat == "SECTION_ORDER" for cat, _ in sigs)


class TestRegressions:
    def test_new_clean_notebook_no_regression(self, tmp_path):
        head = _write(tmp_path / "h.ipynb", _CLEAN)
        assert regressions("NONE", str(head)) == []

    def test_new_bad_notebook_is_regression(self, tmp_path):
        head = _write(tmp_path / "h.ipynb", _BAD)
        assert len(regressions("NONE", str(head))) >= 1

    def test_preexisting_high_does_not_block(self, tmp_path):
        # Same HIGH finding in base and head -> not a regression.
        base = _write(tmp_path / "base.ipynb", _BAD)
        head = _write(tmp_path / "head.ipynb", _BAD)
        assert regressions(str(base), str(head)) == []

    def test_new_high_introduced_is_regression(self, tmp_path):
        base = _write(tmp_path / "base.ipynb", _CLEAN)
        head = _write(tmp_path / "head.ipynb", _BAD)
        assert len(regressions(str(base), str(head))) >= 1

    def test_fixing_high_is_not_regression(self, tmp_path):
        base = _write(tmp_path / "base.ipynb", _BAD)
        head = _write(tmp_path / "head.ipynb", _CLEAN)
        assert regressions(str(base), str(head)) == []

    def test_malformed_head_is_graceful(self, tmp_path):
        base = _write(tmp_path / "base.ipynb", _CLEAN)
        head = tmp_path / "head.ipynb"
        head.write_text("{not json", encoding="utf-8")
        assert regressions(str(base), str(head)) == []


class TestMainExitCodes:
    def test_exit_zero_on_clean(self, tmp_path):
        head = _write(tmp_path / "h.ipynb", _CLEAN)
        assert main(["--base", "NONE", "--head", str(head)]) == 0

    def test_exit_one_on_regression(self, tmp_path):
        head = _write(tmp_path / "h.ipynb", _BAD)
        assert main(["--base", "NONE", "--head", str(head)]) == 1

    def test_ref_git_head_raises(self, tmp_path):
        # --head HEAD (a git ref, not a path) must fail loudly, not exit 0.
        with pytest.raises(SystemExit, match="n'existe pas"):
            main(["--base", "NONE", "--head", "HEAD"])


def _nb_bytes(cells: list[dict]) -> bytes:
    return json.dumps(
        {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    ).encode("utf-8")


def _fake_git_show(monkeypatch, *, rc=0, blob=b""):
    """Remplace subprocess.run pour `git show <ref>:<path>`.

    Enregistre les appels et rend le blob (ou l'echec rc!=0 = blob absent de
    la ref). Les autres usages de subprocess ne sont pas attendus par ces
    tests : tout appel imprévu fait echouer le test (args inattendus).
    """
    import cell_order_ci

    calls = []

    def fake_run(args, **kwargs):
        calls.append(args)
        import subprocess as _sp
        return _sp.CompletedProcess(args, rc, blob, b"")

    monkeypatch.setattr(cell_order_ci.subprocess, "run", fake_run)
    return calls


class TestBaseRefMode:
    """#22209 -- le mode `--base-ref` de la voie rapide : la base est lue dans
    le blob `<ref>:<head path>`, reproduisant la boucle du workflow d'origine
    (`git cat-file -e` puis `git show $BASE:$nb`)."""

    def test_absent_blob_is_a_new_file(self, monkeypatch, tmp_path):
        # rc!=0 de git show = blob absent de la ref = NOUVEAU carnet : base
        # vide, chaque HIGH compte (semantique NONE de la boucle d'origine).
        import cell_order_ci

        _fake_git_show(monkeypatch, rc=128, blob=b"fatal: path not in ref")
        head = _write(tmp_path / "h.ipynb", _BAD)
        assert cell_order_ci.high_signatures_from_ref(
            "origin/main", str(head)) == set()
        assert main(["--base-ref", "origin/main", "--head", str(head)]) == 1

    def test_blob_present_is_scanned_as_base(self, monkeypatch, tmp_path):
        # La base portait deja le defect, la tete l'a corrigee -> pas de
        # regression : le blob EST la base, pas un fichier vide.
        import cell_order_ci

        _fake_git_show(monkeypatch, rc=0, blob=_nb_bytes(_BAD))
        head = _write(tmp_path / "h.ipynb", _CLEAN)
        assert main(["--base-ref", "origin/main", "--head", str(head)]) == 0

    def test_blob_clean_base_with_bad_head_is_regression(self, monkeypatch, tmp_path):
        import cell_order_ci

        _fake_git_show(monkeypatch, rc=0, blob=_nb_bytes(_CLEAN))
        head = _write(tmp_path / "h.ipynb", _BAD)
        assert main(["--base-ref", "origin/main", "--head", str(head)]) == 1

    def test_blob_unreadable_yields_empty_base(self, monkeypatch, tmp_path):
        # Blob present mais illisible (JSON casse) : meme grace que
        # high_signatures sur un fichier illisible -- base vide, pas d'echec.
        import cell_order_ci

        _fake_git_show(monkeypatch, rc=0, blob=b"{not json")
        head = _write(tmp_path / "h.ipynb", _BAD)
        assert main(["--base-ref", "origin/main", "--head", str(head)]) == 1

    def test_git_show_reads_the_head_path_under_the_ref(self, monkeypatch, tmp_path):
        import cell_order_ci

        calls = _fake_git_show(monkeypatch, rc=0, blob=_nb_bytes(_CLEAN))
        head = _write(tmp_path / "h.ipynb", _BAD)
        main(["--base-ref", "origin/main", "--head", str(head)])
        assert calls and calls[0] == [
            "git", "show", f"origin/main:{head}"
        ], "la base doit etre lue a <ref>:<head path>, comme la boucle d'origine"

    def test_base_and_base_ref_are_exclusive(self, tmp_path):
        head = _write(tmp_path / "h.ipynb", _CLEAN)
        with pytest.raises(SystemExit) as exc:
            main(["--base", "NONE", "--base-ref", "origin/main",
                  "--head", str(head)])
        assert exc.value.code == 2, "argparse refuse la double specification de base"
