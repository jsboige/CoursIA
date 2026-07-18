#!/usr/bin/env python3
"""Tests for detect_caps_regression.py (#2876 markdown caps-regression gate).

Covers : accent-stripping helpers, positional line check, scan_pair end-to-end
on synthetic notebooks, main() exit codes + JSON mode. The regression class is
the one caught firsthand on PRs #7191 / #7185 (tiebreaker c.484) : an accent
cure that lowercases the initial capital of a token.
"""
import json
import sys
from pathlib import Path

import pytest  # noqa: E402 -- for pytest.raises in the no-args guard test

# Allow ``import detect_caps_regression`` when run from the tests/ dir.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import detect_caps_regression as dcr  # noqa: E402


# --------------------------------------------------------------------------
# Helpers : build synthetic notebooks.
# --------------------------------------------------------------------------
def _nb(md_source_lines: list[str], code_source_lines: list[str] | None = None) -> dict:
    """Build a minimal nbformat notebook with one markdown + one code cell."""
    cells = [{"cell_type": "markdown", "source": md_source_lines, "metadata": {}}]
    if code_source_lines is not None:
        cells.append({"cell_type": "code", "source": code_source_lines,
                      "metadata": {}, "execution_count": None, "outputs": []})
    return {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


def _write_nb(path: Path, nb: dict) -> Path:
    path.write_text(json.dumps(nb, ensure_ascii=False), encoding="utf-8")
    return path


# --------------------------------------------------------------------------
# Accent-stripping helpers.
# --------------------------------------------------------------------------
class TestStripAccents:
    def test_strips_common_accents(self):
        assert dcr._strip_accents("système") == "systeme"
        assert dcr._strip_accents("précédent") == "precedent"
        assert dcr._strip_accents("Équipes") == "Equipes"
        assert dcr._strip_accents("modèles") == "modeles"

    def test_passes_through_ascii(self):
        assert dcr._strip_accents("Systeme") == "Systeme"
        assert dcr._strip_accents("abc123") == "abc123"
        assert dcr._strip_accents("") == ""

    def test_has_accent_true_only_when_mark_present(self):
        assert dcr._has_accent("système") is True
        assert dcr._has_accent("Systeme") is False
        assert dcr._has_accent("Équipes") is True


# --------------------------------------------------------------------------
# Positional line check : the core signal.
# --------------------------------------------------------------------------
class TestCheckLine:
    def test_heading_capital_lost_flagged(self):
        # The defect : cure restored the accent but lowercased the initial capital.
        base = "## 3. Modele Deux Joueurs"
        head = "## 3. modèle Deux Joueurs"  # wrong : should be "Modèle"
        regs = list(dcr._check_line(base, head))
        assert len(regs) == 1
        assert regs[0][0] == "Modele"  # base token (capital preserved in main)
        assert regs[0][1] == "modèle"  # head token (accent restored, capital lost)

    def test_nav_capital_lost_flagged(self):
        base = "| Precedent | Suivant |"
        head = "| précédent | Suivant |"
        regs = list(dcr._check_line(base, head))
        assert len(regs) == 1
        assert regs[0][0] == "Precedent"
        assert regs[0][1] == "précédent"

    def test_table_bold_capital_lost_flagged(self):
        base = "| **Equipes** | Moyenne |"
        head = "| **équipes** | Moyenne |"
        regs = list(dcr._check_line(base, head))
        assert len(regs) == 1
        assert regs[0][0] == "Equipes"
        assert regs[0][1] == "équipes"

    def test_list_item_capital_lost_flagged(self):
        base = "1. **Parametres** : Definition"
        head = "1. **paramètres** : Definition"
        regs = list(dcr._check_line(base, head))
        assert len(regs) == 1
        assert regs[0][0] == "Parametres"
        assert regs[0][1] == "paramètres"

    def test_correct_cure_capital_preserved_not_flagged(self):
        """The happy path : cure restored the accent AND kept the capital."""
        base = "## 3. Modele Deux Joueurs"
        head = "## 3. Modèle Deux Joueurs"
        assert list(dcr._check_line(base, head)) == []

    def test_mid_sentence_lowercase_cure_not_flagged(self):
        """A legit lowercase cure (base was lowercase) is NOT a regression."""
        base = "Le systeme de classement est pret."
        head = "Le système de classement est pret."
        assert list(dcr._check_line(base, head)) == []

    def test_unrelated_word_change_not_flagged(self):
        """A non-accent word change is out of scope (no accent on head token)."""
        base = "Le Modele ici"
        head = "Le Modele la"  # "ici" -> "la", no accent involved
        assert list(dcr._check_line(base, head)) == []

    def test_structural_count_mismatch_skipped(self):
        """Word-count differs (token added/removed) -> not a pure cure, skip."""
        base = "Le Modele de classement"
        head = "Le modèle"  # 2 words vs 4 -- structural, skip
        assert list(dcr._check_line(base, head)) == []

    def test_identical_line_not_flagged(self):
        assert list(dcr._check_line("Le systeme", "Le systeme")) == []

    def test_full_uppercase_preserved_not_flagged(self):
        """ALL-CAPS acronym cured to all-caps accented is NOT a regression."""
        base = "JSON Modeles"
        head = "JSON Modèles"  # base Mod-eles -> Mod-èles, capital preserved
        assert list(dcr._check_line(base, head)) == []


# --------------------------------------------------------------------------
# scan_pair end-to-end on synthetic notebooks.
# --------------------------------------------------------------------------
class TestScanPair:
    def test_clean_notebook_zero_regressions(self, tmp_path):
        base = _nb(["## Le Modele", "Le systeme fonctionne."])
        head = _nb(["## Le Modèle", "Le système fonctionne."])  # correct cures
        bp = _write_nb(tmp_path / "base.ipynb", base)
        hp = _write_nb(tmp_path / "head.ipynb", head)
        res = dcr.scan_pair(bp, hp)
        assert res["error"] is None
        assert res["regressions"] == []

    def test_multiple_regressions_found(self, tmp_path):
        base = _nb(["## 3. Modele Deux Joueurs",
                    "| Precedent | Suivant |",
                    "| **Equipes** | Moyenne |"])
        head = _nb(["## 3. modèle Deux Joueurs",
                    "| précédent | Suivant |",
                    "| **équipes** | Moyenne |"])
        bp = _write_nb(tmp_path / "base.ipynb", base)
        hp = _write_nb(tmp_path / "head.ipynb", head)
        res = dcr.scan_pair(bp, hp)
        assert res["error"] is None
        assert len(res["regressions"]) == 3
        toks = {(r["base_token"], r["head_token"]) for r in res["regressions"]}
        assert ("Modele", "modèle") in toks
        assert ("Precedent", "précédent") in toks
        assert ("Equipes", "équipes") in toks

    def test_code_cells_ignored(self, tmp_path):
        """Code cells are the identifier gate's scope (#7157), not this tool's."""
        base = _nb(["Le systeme"],
                   code_source_lines=["Parametres = 42  # code identifier"])
        head = _nb(["Le système"],
                   code_source_lines=["parametres = 42  # would be an ident regression"])
        bp = _write_nb(tmp_path / "base.ipynb", base)
        hp = _write_nb(tmp_path / "head.ipynb", head)
        res = dcr.scan_pair(bp, hp)
        assert res["regressions"] == []  # markdown cure correct, code ignored

    def test_unreadable_base_returns_error(self, tmp_path):
        hp = _write_nb(tmp_path / "head.ipynb", _nb(["ok"]))
        res = dcr.scan_pair(tmp_path / "missing.ipynb", hp)
        assert res["error"] is not None
        assert "base unreadable" in res["error"]

    def test_unreadable_head_returns_error(self, tmp_path):
        bp = _write_nb(tmp_path / "base.ipynb", _nb(["ok"]))
        res = dcr.scan_pair(bp, tmp_path / "missing.ipynb")
        assert res["error"] is not None
        assert "head unreadable" in res["error"]

    def test_regression_dict_shape(self, tmp_path):
        base = _nb(["## Modele X"])
        head = _nb(["## modèle X"])
        bp = _write_nb(tmp_path / "base.ipynb", base)
        hp = _write_nb(tmp_path / "head.ipynb", head)
        r = dcr.scan_pair(bp, hp)["regressions"][0]
        for key in ("cell_index", "line_no", "column", "base_token",
                    "head_token", "position", "base_line"):
            assert key in r


# --------------------------------------------------------------------------
# main() exit codes + JSON mode.
# --------------------------------------------------------------------------
class TestMainExitCodes:
    def test_clean_exit_0(self, tmp_path, capsys):
        base = _nb(["Le systeme"])
        head = _nb(["Le système"])
        bp = _write_nb(tmp_path / "base.ipynb", base)
        hp = _write_nb(tmp_path / "head.ipynb", head)
        rc = dcr.main(["--base", str(bp), "--head", str(hp), "--quiet"])
        assert rc == 0

    def test_regression_exit_1(self, tmp_path, capsys):
        base = _nb(["## Modele X"])
        head = _nb(["## modèle X"])
        bp = _write_nb(tmp_path / "base.ipynb", base)
        hp = _write_nb(tmp_path / "head.ipynb", head)
        rc = dcr.main(["--base", str(bp), "--head", str(hp), "--quiet"])
        assert rc == 1

    def test_unreadable_exit_2(self, tmp_path):
        hp = _write_nb(tmp_path / "head.ipynb", _nb(["ok"]))
        rc = dcr.main(["--base", str(tmp_path / "missing.ipynb"),
                       "--head", str(hp), "--quiet"])
        assert rc == 2

    def test_json_mode_emits_valid_json(self, tmp_path, capsys):
        base = _nb(["## Modele X"])
        head = _nb(["## modèle X"])
        bp = _write_nb(tmp_path / "base.ipynb", base)
        hp = _write_nb(tmp_path / "head.ipynb", head)
        rc = dcr.main(["--base", str(bp), "--head", str(hp), "--json"])
        out = json.loads(capsys.readouterr().out)
        assert rc == 1
        assert out["error"] is None
        assert len(out["regressions"]) == 1

    def test_human_report_clean_and_hit(self, tmp_path, capsys):
        base = _nb(["## Modele X"])
        head_clean = _nb(["## Modèle X"])
        bp = _write_nb(tmp_path / "base.ipynb", base)
        hp = _write_nb(tmp_path / "head.ipynb", head_clean)
        dcr.main(["--base", str(bp), "--head", str(hp)])
        assert "OK" in capsys.readouterr().out


# --------------------------------------------------------------------------
# Position classification (annotation only, not the verdict).
# --------------------------------------------------------------------------
class TestPositionClassification:
    def test_heading_detected(self):
        assert dcr._classify_position("## Modele", 3, "Modele") == "heading"

    def test_table_detected(self):
        # "Equipes" in "| **Equipes** |" starts at column 4 (after "| **").
        assert dcr._classify_position("| **Equipes** |", 4, "Equipes") in ("table", "bold")

    def test_list_detected(self):
        assert dcr._classify_position("1. Parametres ici", 3, "Parametres") == "list"

    def test_sentence_start_detected(self):
        assert dcr._classify_position("Apres inference", 0, "Apres") == "sentence-start"

    def test_prose_default(self):
        assert dcr._classify_position("Le systeme ici", 3, "systeme") == "prose"


# --------------------------------------------------------------------------
# Git-ref mode : scan_ref_mode (unit tests via monkeypatch, no real git).
# --------------------------------------------------------------------------
class TestScanRefMode:
    def test_success_both_refs(self, tmp_path, monkeypatch):
        base_nb = {"cells": [{"cell_type": "markdown",
                              "source": ["## Modele X"]}], "metadata": {}}
        head_nb = {"cells": [{"cell_type": "markdown",
                              "source": ["## modèle X"]}], "metadata": {}}
        calls = {"base": base_nb, "head": head_nb}

        def fake_show(ref, path, cwd=None):
            return calls.get("base") if "main" in ref else calls.get("head")
        monkeypatch.setattr(dcr, "_git_show_notebook", fake_show)
        res = dcr.scan_ref_mode(tmp_path / "nb.ipynb", "origin/main", "origin/branch")
        assert res["error"] is None
        assert len(res["regressions"]) == 1

    def test_base_ref_unreadable(self, tmp_path, monkeypatch):
        monkeypatch.setattr(dcr, "_git_show_notebook",
                            lambda ref, path, cwd=None: None)
        res = dcr.scan_ref_mode(tmp_path / "nb.ipynb", "origin/main", "origin/branch")
        assert res["error"] is not None
        assert "base unreadable at git ref" in res["error"]
        assert res["regressions"] == []

    def test_head_ref_unreadable(self, tmp_path, monkeypatch):
        base_nb = {"cells": [], "metadata": {}}

        def fake_show(ref, path, cwd=None):
            return base_nb if "main" in ref else None
        monkeypatch.setattr(dcr, "_git_show_notebook", fake_show)
        res = dcr.scan_ref_mode(tmp_path / "nb.ipynb", "origin/main", "origin/branch")
        assert res["error"] is not None
        assert "head unreadable at git ref" in res["error"]

    def test_head_defaults_to_disk(self, tmp_path, monkeypatch):
        """head_ref=None -> head notebook read from the on-disk file."""
        base_nb = {"cells": [{"cell_type": "markdown",
                              "source": ["## Modele X"]}], "metadata": {}}
        monkeypatch.setattr(dcr, "_git_show_notebook",
                            lambda ref, path, cwd=None: base_nb)
        head_nb = {"cells": [{"cell_type": "markdown",
                              "source": ["## modèle X"]}], "metadata": {}}
        disk_path = tmp_path / "nb.ipynb"
        disk_path.write_text(json.dumps(head_nb), encoding="utf-8")
        res = dcr.scan_ref_mode(disk_path, "origin/main", None)
        assert res["error"] is None
        assert len(res["regressions"]) == 1

    def test_head_disk_missing_no_ref(self, tmp_path, monkeypatch):
        """head_ref=None AND notebook not on disk -> precise error."""
        base_nb = {"cells": [], "metadata": {}}
        monkeypatch.setattr(dcr, "_git_show_notebook",
                            lambda ref, path, cwd=None: base_nb)
        res = dcr.scan_ref_mode(tmp_path / "ghost.ipynb", "origin/main", None)
        assert res["error"] is not None
        assert "not on disk" in res["error"]


# --------------------------------------------------------------------------
# Git-ref mode : real tmp git repo integration (confirms the git show plumbing).
# --------------------------------------------------------------------------
class TestGitRefIntegration:
    def _commit(self, repo, nb_dict, msg):
        import subprocess as sp
        (repo / "nb.ipynb").write_text(json.dumps(nb_dict), encoding="utf-8")
        sp.run(["git", "add", "nb.ipynb"], cwd=repo, check=True,
               capture_output=True)
        sp.run(["git", "commit", "-m", msg], cwd=repo, check=True,
               capture_output=True)

    def test_real_repo_detects_regression(self, tmp_path):
        import subprocess as sp
        repo = tmp_path / "repo"
        repo.mkdir()
        sp.run(["git", "init"], cwd=repo, check=True, capture_output=True)
        # Force the default branch to 'main' (CI runners may default to 'master').
        sp.run(["git", "branch", "-m", "main"], cwd=repo, capture_output=True)
        for k, v in {"user.name": "t", "user.email": "t@t"}.items():
            sp.run(["git", "config", k, v], cwd=repo, check=True, capture_output=True)
        base = {"cells": [{"cell_type": "markdown",
                           "source": ["## Modele X"]}], "metadata": {}}
        self._commit(repo, base, "base")
        sp.run(["git", "branch", "branch"], cwd=repo, check=True, capture_output=True)
        sp.run(["git", "checkout", "branch"], cwd=repo, check=True, capture_output=True)
        head = {"cells": [{"cell_type": "markdown",
                           "source": ["## modèle X"]}], "metadata": {}}
        self._commit(repo, head, "head")
        res = dcr.scan_ref_mode(Path("nb.ipynb"), "main", "branch", cwd=repo)
        assert res["error"] is None
        assert len(res["regressions"]) == 1
        assert res["regressions"][0]["base_token"] == "Modele"

    def test_real_repo_clean_cure(self, tmp_path):
        import subprocess as sp
        repo = tmp_path / "repo"
        repo.mkdir()
        sp.run(["git", "init"], cwd=repo, check=True, capture_output=True)
        # Force the default branch to 'main' (CI runners may default to 'master').
        sp.run(["git", "branch", "-m", "main"], cwd=repo, capture_output=True)
        for k, v in {"user.name": "t", "user.email": "t@t"}.items():
            sp.run(["git", "config", k, v], cwd=repo, check=True, capture_output=True)
        base = {"cells": [{"cell_type": "markdown",
                           "source": ["## Modele X"]}], "metadata": {}}
        self._commit(repo, base, "base")
        sp.run(["git", "branch", "branch"], cwd=repo, check=True, capture_output=True)
        sp.run(["git", "checkout", "branch"], cwd=repo, check=True, capture_output=True)
        head = {"cells": [{"cell_type": "markdown",
                           "source": ["## Modèle X"]}], "metadata": {}}
        self._commit(repo, head, "head")
        res = dcr.scan_ref_mode(Path("nb.ipynb"), "main", "branch", cwd=repo)
        assert res["error"] is None
        assert res["regressions"] == []  # correct cure : capital preserved

    def test_real_repo_bad_ref_error(self, tmp_path):
        import subprocess as sp
        repo = tmp_path / "repo"
        repo.mkdir()
        sp.run(["git", "init"], cwd=repo, check=True, capture_output=True)
        # Force the default branch to 'main' (CI runners may default to 'master').
        sp.run(["git", "branch", "-m", "main"], cwd=repo, capture_output=True)
        for k, v in {"user.name": "t", "user.email": "t@t"}.items():
            sp.run(["git", "config", k, v], cwd=repo, check=True, capture_output=True)
        base = {"cells": [], "metadata": {}}
        self._commit(repo, base, "base")
        res = dcr.scan_ref_mode(Path("nb.ipynb"), "nonexistent-ref", "main", cwd=repo)
        assert res["error"] is not None
        assert "base unreadable at git ref" in res["error"]


# --------------------------------------------------------------------------
# main() git-ref-mode dispatch + --check alias + no-args guard.
# --------------------------------------------------------------------------
class TestMainGitRefMode:
    def test_git_ref_mode_dispatch(self, tmp_path, capsys, monkeypatch):
        base_nb = {"cells": [{"cell_type": "markdown",
                              "source": ["## Modele X"]}], "metadata": {}}
        head_nb = {"cells": [{"cell_type": "markdown",
                              "source": ["## modèle X"]}], "metadata": {}}

        def fake_scan(notebook_path, base_ref, head_ref, cwd=None):
            assert base_ref == "origin/main"
            assert head_ref == "origin/branch"
            return {"path": str(notebook_path),
                    "regressions": [{"cell_index": 0, "line_no": 0, "column": 3,
                                     "base_token": "Modele", "head_token": "modèle",
                                     "position": "heading", "base_line": "## Modele X"}],
                    "error": None}
        monkeypatch.setattr(dcr, "scan_ref_mode", fake_scan)
        rc = dcr.main(["nb.ipynb", "--base", "origin/main", "--head", "origin/branch"])
        assert rc == 1
        assert "Modele" in capsys.readouterr().out

    def test_git_ref_mode_base_default_origin_main(self, tmp_path, monkeypatch):
        """Positional notebook + no --base -> defaults to origin/main."""
        seen = {}

        def fake_scan(notebook_path, base_ref, head_ref, cwd=None):
            seen["base_ref"] = base_ref
            return {"path": str(notebook_path), "regressions": [], "error": None}
        monkeypatch.setattr(dcr, "scan_ref_mode", fake_scan)
        dcr.main(["nb.ipynb", "--quiet"])
        assert seen["base_ref"] == "origin/main"

    def test_check_alias_is_quiet(self, tmp_path, capsys, monkeypatch):
        """--check (the #7197 muscle-memory alias) suppresses stdout like --quiet."""
        monkeypatch.setattr(dcr, "scan_ref_mode",
                            lambda p, b, h, cwd=None: {
                                "path": str(p),
                                "regressions": [{"cell_index": 0, "line_no": 0,
                                                 "column": 0, "base_token": "X",
                                                 "head_token": "x", "position": "prose",
                                                 "base_line": "X"}],
                                "error": None})
        rc = dcr.main(["nb.ipynb", "--base", "origin/main", "--head", "origin/branch",
                       "--check"])
        out = capsys.readouterr().out
        assert rc == 1
        assert out == ""  # --check writes nothing, exit code only

    def test_no_args_errors_exit_2(self, tmp_path, monkeypatch, capsys):
        """No positional AND no --base/--head -> parser.error (exit 2)."""
        with pytest.raises(SystemExit) as ei:
            dcr.main([])
        assert ei.value.code == 2
