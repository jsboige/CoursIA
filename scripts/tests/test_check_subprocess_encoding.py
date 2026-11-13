"""Tests for check_subprocess_encoding (ratchet gate, #13140).

Unit tests target the pure scan_source() parser (balanced-paren call spans,
the text/universal_newlines/encoding discrimination, multiline kwargs); the
integration tests drive main(argv) directly (per the cli-surface lesson:
running _run_check or scan_source through a bypassed argv hides CLI bugs).
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "audit"))

import check_subprocess_encoding as cse  # noqa: E402
import git_index_renames  # noqa: E402

# Kept before any fixture replaces it: the #24039 parsing tests below restore
# the real git layer to exercise it against a synthetic git payload. Since
# #24068 the probe lives in scripts/audit/git_index_renames.py (shared with the
# four sibling hooks); main() reads it through the module, so the hermetic
# pin patches the shared module's git_out -- the single source both probes
# read.
_REAL_GIT_OUT = git_index_renames.git_out


@pytest.fixture(autouse=True)
def _hermetic_renames(monkeypatch):
    """Pin the rename probe to "no rename": a unit test must not read the
    contributor's staging area, which would make the suite depend on whatever
    happens to be ``git add``-ed at the time it runs. The #24039 tests below
    patch it again themselves."""
    monkeypatch.setattr(git_index_renames, "git_out", lambda *a: "")


def test_clean_text_with_encoding():
    src = 'out = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8")\n'
    assert cse.scan_source(src) == []


def test_violation_text_without_encoding():
    src = "out = subprocess.run(cmd, capture_output=True, text=True)\n"
    findings = cse.scan_source(src)
    assert len(findings) == 1
    assert findings[0][0] == 1


def test_violation_universal_newlines():
    src = "out = subprocess.check_output(cmd, universal_newlines=True)\n"
    assert len(cse.scan_source(src)) == 1


def test_multiline_encoding_on_separate_line_is_clean():
    # #13140 methodology: the false-negative class -- encoding= on its own
    # line of a multiline call must count as fixed.
    src = (
        "proc = subprocess.run(\n"
        "    ['gh', 'pr', 'view', str(n), '--json', 'body'],\n"
        "    capture_output=True,\n"
        "    text=True,\n"
        '    encoding="utf-8", errors="replace",\n'
        ")\n"
    )
    assert cse.scan_source(src) == []


def test_multiline_violation_reports_call_line():
    src = (
        "proc = subprocess.run(\n"
        "    ['git', 'log'],\n"
        "    capture_output=True,\n"
        "    text=True,\n"
        ")\n"
    )
    findings = cse.scan_source(src)
    assert len(findings) == 1
    assert findings[0][0] == 1  # the line of the call, not of text=True


def test_bytes_mode_without_text_is_clean():
    src = "out = subprocess.run(cmd, capture_output=True)\n"
    assert cse.scan_source(src) == []


def test_text_false_is_clean():
    src = "out = subprocess.run(cmd, capture_output=True, text=False)\n"
    assert cse.scan_source(src) == []


def test_fstring_single_quote_variant_is_clean():
    src = (
        "print(f\"v: {subprocess.run(['git','config','x'], capture_output=True, "
        "text=True, encoding='utf-8', errors='replace').stdout.strip()}\")\n"
    )
    assert cse.scan_source(src) == []


def test_docstring_prose_mentioning_pattern_is_not_flagged():
    # The guard's own docstring (and any prose) mentions the defect pattern;
    # tokenize suppression keeps prose out of the findings (self-scan green).
    src = (
        '"""Gate doc: subprocess.run(cmd, text=True) without encoding= is bad.\n'
        'Also universal_newlines=True.\n'
        '"""\n'
        "import subprocess\n"
        "subprocess.run(['x'], text=True)\n"
    )
    findings = cse.scan_source(src)
    assert len(findings) == 1
    assert findings[0][0] == 5


def test_comment_prose_mentioning_pattern_is_not_flagged():
    src = (
        "# legacy: subprocess.run(cmd, text=True) -- fixed in #12813\n"
        "import subprocess\n"
        "subprocess.run(['x'], text=True)\n"
    )
    findings = cse.scan_source(src)
    assert len(findings) == 1
    assert findings[0][0] == 3


def test_fstring_defect_site_is_detected():
    # setup_hooks.py L225 class (#13140 tranche 2): the defect lived INSIDE an
    # f-string expression. f-strings are exempt from prose suppression.
    src = (
        'print(f"cfg: {subprocess.run([\'git\',\'config\',\'x\'], '
        "capture_output=True, text=True).stdout.strip()}\" )\n"
    )
    assert len(cse.scan_source(src)) == 1


def test_nested_parentheses_span_is_balanced():
    # The call contains a nested parenthesized expression (a lambda default);
    # the span must close on the CALL's closing paren, not the inner one.
    src = (
        "p = subprocess.run(cmd, capture_output=True, text=True,\n"
        "                   check=lambda r: (r or 0))\n"
        "q = subprocess.run(cmd2, text=True)\n"
    )
    findings = cse.scan_source(src)
    assert len(findings) == 2  # BOTH calls violate: balanced parse works
    assert findings[1][0] == 3


def test_line_numbers_count_from_file_start():
    src = "x = 1\ny = 2\nz = subprocess.run(cmd, text=True)\n"
    findings = cse.scan_source(src)
    assert findings[0][0] == 3


def test_excluded_markers():
    assert cse.excluded("_peters/foo/bar.py")
    assert cse.excluded("MyIA.AI.Notebooks/x/.lake/packages/Foo.lean.py")
    assert not cse.excluded("scripts/pr_gate.py")


def test_main_files_mode_exit_codes(tmp_path, capsys):
    bad = tmp_path / "bad.py"
    bad.write_text("import subprocess\nsubprocess.run(['x'], text=True)\n",
                   encoding="utf-8")
    good = tmp_path / "good.py"
    good.write_text('import subprocess\nsubprocess.run(["x"], text=True, encoding="utf-8")\n',
                    encoding="utf-8")
    assert cse.main([str(good)]) == 0
    assert cse.main([str(bad)]) == 1
    out = capsys.readouterr().out
    assert "text=True without encoding=" in out


def test_main_files_mode_skips_vendored_and_non_py(tmp_path):
    vendored = tmp_path / "_peters" / "lib.py"
    vendored.parent.mkdir()
    vendored.write_text("import subprocess\nsubprocess.run(['x'], text=True)\n",
                        encoding="utf-8")
    assert cse.main([str(vendored)]) == 0


def test_main_base_mode(monkeypatch, capsys):
    monkeypatch.setattr(cse, "git_out", lambda *a: {
        ("merge-base", "origin/main", "HEAD"): "abc123\n",
        ("diff", "--name-only", "--diff-filter=AM", "abc123", "HEAD"):
            "scripts/a.py\n_peters/b.py\nnotebook.ipynb\n",
    }[a])
    # No files on disk with those names -> 0 violations, exit 0, paths filtered.
    # .ipynb now in scope (#19475): the diff yields 2 files (a.py + notebook.ipynb);
    # both are non-existent on disk so neither is read -> 0 violations.
    assert cse.main(["--base", "origin/main"]) == 0
    out = capsys.readouterr().out
    assert "= 2 changed file(s)" in out
    assert ".ipynb" in out


# ---- #24039: a pure rename cannot introduce a site ----

def test_staged_pure_renames_keeps_only_r100_destination(monkeypatch):
    payload = ("R100\0old/dir/x.py\0new/dir/x.py\0"
               "R087\0a.py\0b.py\0"
               "M\0c.py\0"
               "A\0d.py\0")
    monkeypatch.setattr(git_index_renames, "git_out", lambda *a: payload)
    # R087 is a rename *with edits*: its content did change, so it is scanned.
    assert cse.staged_pure_renames() == {"new/dir/x.py"}


def test_staged_pure_renames_without_git_is_empty(monkeypatch):
    monkeypatch.setattr(git_index_renames, "git_out", lambda *a: None)
    assert cse.staged_pure_renames() == set()


def test_main_files_mode_skips_pure_rename(tmp_path, capsys, monkeypatch):
    moved = tmp_path / "moved.py"
    moved.write_text("import subprocess\nsubprocess.run(['x'], text=True)\n",
                     encoding="utf-8")
    monkeypatch.setattr(git_index_renames, "git_out", lambda *a:
                        f"R100\0old.py\0{moved.as_posix()}\0")
    assert cse.main([str(moved)]) == 0
    out = capsys.readouterr().out
    assert "pure rename(s) ignored" in out
    assert "#24039" in out


def test_main_files_mode_still_scans_non_rename(tmp_path, capsys, monkeypatch):
    """The skip must not become a blanket silence: a file that is not a pure
    rename keeps its own sites reported."""
    bad = tmp_path / "bad.py"
    bad.write_text("import subprocess\nsubprocess.run(['x'], text=True)\n",
                   encoding="utf-8")
    monkeypatch.setattr(git_index_renames, "git_out", lambda *a:
                        "R100\0old.py\0/elsewhere.py\0")
    assert cse.main([str(bad)]) == 1
    assert "text=True without encoding=" in capsys.readouterr().out



# ---- #19475: ipynb code-cell extraction ----

def _nb_for_write(cells, path):
    """Tiny nbformat-shape writer for pre-commit testing. not Papermill 1:1,
    only the keys scan_ipynb() reads (cells[*].cell_type and source list)."""
    import json
    path.write_text(json.dumps({"cells": cells}), encoding="utf-8")


def test_scan_ipynb_clean_code_cell(tmp_path):
    nb = tmp_path / "good.ipynb"
    _nb_for_write([
        {"cell_type": "markdown", "source": ["# prose about subprocess.run\n"]},
        {"cell_type": "code",
         "source": ["import subprocess\n",
                    "subprocess.run(['x'], text=True, encoding='utf-8')\n"]},
    ], nb)
    assert cse.scan_ipynb(str(nb)) == []


def test_scan_ipynb_violation_in_code_cell(tmp_path):
    nb = tmp_path / "bad.ipynb"
    _nb_for_write([
        {"cell_type": "code",
         "source": ["import subprocess\n",
                    "subprocess.run(['x'], text=True)\n"]},
    ], nb)
    findings = cse.scan_ipynb(str(nb))
    assert len(findings) == 1
    cell_idx, line_no, _ = findings[0]
    assert cell_idx == 0
    assert line_no == 2  # the line of the call


def test_scan_ipynb_skips_markdown_cells(tmp_path):
    nb = tmp_path / "md.ipynb"
    _nb_for_write([
        {"cell_type": "markdown",
         "source": ["def fake_subprocess_run(*a, text=True): pass\n",
                    "fake_subprocess_run('x', text=True)\n"]},
        {"cell_type": "code",
         "source": ["# clean cell\n"]},
    ], nb)
    # The markdown cell's source IS valid Python in this test, but we don't
    # care: scan_ipynb only walks code cells, so the markdown is skipped
    # regardless of its content. The defect lives where it can be executed.
    assert cse.scan_ipynb(str(nb)) == []


def test_scan_ipynb_unparseable_is_skipped(tmp_path):
    nb = tmp_path / "corrupt.ipynb"
    nb.write_text("{not json", encoding="utf-8")
    assert cse.scan_ipynb(str(nb)) == []


def test_scan_ipynb_multiline_call_reports_call_line(tmp_path):
    nb = tmp_path / "multi.ipynb"
    _nb_for_write([
        {"cell_type": "code",
         "source": ["import subprocess\n",
                    "proc = subprocess.run(\n",
                    "    ['git', 'log'],\n",
                    "    capture_output=True,\n",
                    "    text=True,\n",
                    ")\n"]},
    ], nb)
    findings = cse.scan_ipynb(str(nb))
    assert len(findings) == 1
    cell_idx, line_no, _ = findings[0]
    assert cell_idx == 0
    assert line_no == 2  # the line of the call, not of text=True


def test_main_files_mode_mixed_py_ipynb(tmp_path, capsys):
    bad_py = tmp_path / "bad.py"
    bad_py.write_text("import subprocess\nsubprocess.run(['x'], text=True)\n",
                      encoding="utf-8")
    good_nb = tmp_path / "good.ipynb"
    _nb_for_write([
        {"cell_type": "code",
         "source": ["import subprocess\n",
                    "subprocess.run(['x'], text=True, encoding='utf-8')\n"]},
    ], good_nb)
    bad_nb = tmp_path / "bad.ipynb"
    _nb_for_write([
        {"cell_type": "code",
         "source": ["import subprocess\n",
                    "subprocess.run(['x'], text=True)\n"]},
    ], bad_nb)
    assert cse.main([str(bad_py), str(good_nb), str(bad_nb)]) == 1
    out = capsys.readouterr().out
    assert f"{bad_py}" in out
    assert f"{good_nb}" not in out
    assert f"{bad_nb}:cell_00:2" in out  # cell index in the report


# ---- #24068: the probe now lives in the shared module -------------------

def test_shared_module_staged_pure_renames_matches_shim(monkeypatch):
    """The check_subprocess_encoding.staged_pure_renames shim delegates to
    scripts/audit/git_index_renames.py; both must return the same set."""
    payload = "R100\0old/x.py\0new/x.py\0R087\0a.py\0b.py\0"
    monkeypatch.setattr(git_index_renames, "git_out", lambda *a: payload)
    assert cse.staged_pure_renames() == git_index_renames.staged_pure_renames()
    assert cse.staged_pure_renames() == {"new/x.py"}


def test_shared_module_renames_with_old_carries_all_renames(monkeypatch):
    """The delta half of #24066: staged_renames_with_old returns EVERY rename
    (any similarity) as destination -> source, not only R100."""
    payload = ("R100\0old/pure.py\0new/pure.py\0"
               "R042\0src/edited.py\0dst/edited.py\0"
               "C100\0orig.py\0copy.py\0"
               "M\0plain.py\0")
    monkeypatch.setattr(git_index_renames, "git_out", lambda *a: payload)
    renames = git_index_renames.staged_renames_with_old()
    assert renames == {
        "new/pure.py": "old/pure.py",
        "dst/edited.py": "src/edited.py",
        "copy.py": "orig.py",  # copy: content also comes from an existing blob
    }


# ---- #24066: rename WITH edits reports only the delta -------------------

def test_main_files_mode_rename_with_edits_reports_only_new_sites(
        tmp_path, capsys, monkeypatch):
    """The issue's measured scenario: R100 rename, then a retouche adds one
    new call. Expected after fix: only the new site (line 8) is reported;
    the inherited one (line 5) is silent."""
    moved = tmp_path / "new" / "x.py"
    moved.parent.mkdir()
    moved.write_text(
        "import subprocess\n"
        "cmd = ['echo']\n"
        "\n"
        "def f1():\n"
        "    return subprocess.run(cmd, capture_output=True, text=True)\n"
        "\n"
        "def f2():\n"
        "    return subprocess.run(cmd, text=True)\n",
        encoding="utf-8")
    renames = {moved.as_posix(): "old/dir/x.py"}
    old_blob = (
        "import subprocess\n"
        "cmd = ['echo']\n"
        "def f1():\n"
        "    return subprocess.run(cmd, capture_output=True, text=True)\n",
    )
    monkeypatch.setattr(git_index_renames, "staged_renames_with_old",
                        lambda: renames)
    monkeypatch.setattr(git_index_renames, "staged_pure_renames", lambda: set())
    # The source blob: same content WITHOUT f2 -- the inherited site is f1's
    # call, whose normalized text the new file carries verbatim.
    monkeypatch.setattr(cse, "git_out", lambda *a:
                        old_blob[0] if a[:2] == ("show", "HEAD:old/dir/x.py")
                        else _REAL_GIT_OUT(*a))
    assert cse.main([str(moved)]) == 1
    out = capsys.readouterr().out
    assert "(cmd, text=True)" in out                            # the new site
    assert "capture_output=True, text=True" not in out          # inherited: silent
    # One reported site only (the summary line also carries the phrase).
    reports = [ln for ln in out.splitlines()
               if ln.startswith(str(moved)) and "text=True without encoding=" in ln]
    assert len(reports) == 1


def test_main_files_mode_rename_with_edits_and_unreadable_blob_reports_all(
        tmp_path, capsys, monkeypatch):
    """Fail-open: if the previous blob cannot be read (orphan rename), no
    site is proven inherited and everything stays reportable."""
    moved = tmp_path / "x.py"
    moved.write_text("import subprocess\nsubprocess.run(['x'], text=True)\n",
                     encoding="utf-8")
    monkeypatch.setattr(git_index_renames, "staged_renames_with_old",
                        lambda: {moved.as_posix(): "old/x.py"})
    monkeypatch.setattr(git_index_renames, "staged_pure_renames", lambda: set())
    monkeypatch.setattr(cse, "git_out", lambda *a: None)  # blob unreadable
    assert cse.main([str(moved)]) == 1
    assert "text=True without encoding=" in capsys.readouterr().out


def test_main_files_mode_rename_delta_still_blocks_new_violation(
        tmp_path, capsys, monkeypatch):
    """The delta is a ratchet, not an amnesty: an edited rename that ADDS a
    violating call still exits 1."""
    moved = tmp_path / "x.py"
    moved.write_text("import subprocess\nsubprocess.run(['new'], text=True)\n",
                     encoding="utf-8")
    monkeypatch.setattr(git_index_renames, "staged_renames_with_old",
                        lambda: {moved.as_posix(): "old/x.py"})
    monkeypatch.setattr(git_index_renames, "staged_pure_renames", lambda: set())
    monkeypatch.setattr(cse, "git_out", lambda *a:
                        "import subprocess\nsubprocess.run(['old'], text=True, encoding='utf-8')\n"
                        if a[:2] == ("show", "HEAD:old/x.py") else _REAL_GIT_OUT(*a))
    assert cse.main([str(moved)]) == 1
    assert "(['new'], text=True)" in capsys.readouterr().out


def test_inherited_sites_matches_normalized_snippet(monkeypatch):
    """The comparison key is scan_source's snippet (whitespace collapsed):
    a call reformatted across lines still counts as inherited."""
    monkeypatch.setattr(cse, "git_out", lambda *a:
                        "subprocess.run(cmd,\n   capture_output=True,\n   text=True)\n")
    sites = cse.inherited_sites("old/x.py")
    assert sites == {"(cmd, capture_output=True, text=True)"}
